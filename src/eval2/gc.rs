// Copyright 2021 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! The garbage collector.
//!
//! Alkyne's heap is mapped out thus:
//! - Page descriptor pages, which contain [`Pd`]s. Not all of them are
//!   allocated at the start; pages of [`Pd`]s are allocated on-demand when
//!   the free list is empty.
//! - The pages that follow are those described by the [`Pd`]s. This is where
//!   the blocks live.
//!
//! Note that the first few [`Pd`]s are never used; they are used as roots
//! for the free lists to simplify some code.
//!
//! ## Free Lists
//!
//! The allocator classifies "blocks" (sized regions of memory) into two kinds:
//! - "Small" allocations smaller than a page. These are rounded up to the next
//!   power of two and allocated onto pages that serve that specific allocation
//!   size. These size classes are 8, 16, 32, 64, 128, 256, 512, 1024, 2048, and
//!   4096.
//! - "Large" allocations larger than a page. These are rounded up to the page
//!   boundary.
//!
//! The allocator operates on two kinds of memory ranges: pages and reams.
//! Pages are ordinary 4K RAM pages. Reams are contiguous spans of two or more
//! pages. Note that there are no single-page reams. Each [`Pd`] represents a
//! page, a ream, or neither (i.e., it is part of a larger ream).
//!
//! These three requests are served by three kinds of free lists:
//! - The main free list, which contains empty reams.
//! - The page free list, which contains empty pages.
//! - The small free lists, which contain partially-filled pages, one for each
//!   size class.
//!
//! There are additionally shadow free lists that contain filled pages:
//! - The filled ream list.
//! - The filled page list (all size classes go here).
//!
//! Pages are moved back into their respective free lists as allocation and
//! garbage collection move them between the empty, partially filled, and full
//! states.
//!
//! ## Small Object Pages
//!
//! Floats and small objects use the same pages. Floats use a different pointer
//! type, so they do not need headers; they use the 8-byte size class.
//!
//! The `gc_bits` field of [`Pd`] tracks which blocks are allocated: the
//! `i`th ream is allocated iff the `i`th bit is set. This is used for finding
//! an unused block, checking if the page is full, and the marking part of
//! garbage collection.
//!
//! Most size classes have 64 or less blocks; however, the 8, 16, and 32 byte
//! classes do not. These spill the `gc_bits` vector into the first few words
//! of their pages, using seven, three, or one words, respectively. This means
//! that they hold slightly less blocks than they otherwise would: 505, 254, and
//! 127, respectively.
//!
//! # Malloc Algorithm
//!
//! Without garbage collection, this heap works as a fairly vanilla malloc.
//! Serving an allocation is done thus:
//! - If it's a large allocation, walk the main free list for a big enough
//!   ream; split the ream and place the allocated portion into the filled
//!   ream list.
//!   - If the tail portion is a single page, put it in the page free list.
//!   - If no large enough ream was found, allocate page descriptors for one
//!     max-size ream and start over.
//! - If it's a small allocation, take a page from the relevant small free list.
//!   Find an unallocated block in `gc_bits` and set it.
//!   - If the page is now filled, place it into the filled page list.
//!   - If the relevant free list is empty, take a page from the page free list
//!     and use that.
//!     - If the page free list is also empty, allocate a one-page "ream" and
//!       use that as the page.
//!       
//! Once broken up, we currently make no effort to defragment reams.
//!       
//! Freeing is the reverse process:
//! - If it's a large allocation, simply put it back into the main free list.
//! - If it's a small allocation; clear the relevant bit in the control word.
//!   - If it causes the page to become empty, place it into the page free list.
//!   - If it causes the page to become non-full, place it into the size class's
//!     free list.
//!     
//! It is a simple matter determining if an allocation is large or small: simply
//! look at the page descriptor for its page. In practice, this algorithm is not
//! used, but a modified form of it occurs at the sweep stage.
//!
//! # GC Algorithm
//!
//! If we enter a GC pause, the following occurs:
//! - Walk through the entire page region and clear all of their `gc_bits`
//!   words, without actually moving them between free lists. This is
//!   [`Heap::start_gc()`].
//! - Trace objects from the interpreter stack, setting `gc_bits` words along
//!   the way as necessary. This is [`Heap::mark()`].
//! - Rebuild the free lists based off of the new `gc_bits`. This is
//!   [`Heap::sweep()`].

#![allow(rustdoc::private_intra_doc_links)]

use std::cell::Cell;
use std::fmt;
use std::io;
use std::iter;
use std::marker::PhantomData;
use std::mem;
use std::mem::MaybeUninit;
use std::num::NonZeroU16;
use std::num::NonZeroU32;
use std::num::NonZeroU8;
use std::ptr;
use std::slice;

/// A "virtual" pointer into a [`AddrSpace`].
#[repr(transparent)]
pub struct Vptr<T>(NonZeroU32, PhantomData<*mut T>);

impl<T> Vptr<T> {
  pub fn cast<U>(self) -> Vptr<U> {
    Vptr(self.0, PhantomData)
  }
}

impl<T> fmt::Debug for Vptr<T> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "Vptr({:#010x})", self.0)
  }
}

impl<T> Clone for Vptr<T> {
  fn clone(&self) -> Self {
    Self(self.0, self.1)
  }
}
impl<T> Copy for Vptr<T> {}

impl<T> PartialEq for Vptr<T> {
  fn eq(&self, that: &Self) -> bool {
    self.0 == that.0
  }
}
impl<T> Eq for Vptr<T> {}

/// Returns the number of pages needed for `n` bytes (rounding up).
const fn bytes_to_pages(n: usize) -> usize {
  if n % AddrSpace::PAGE_BYTES != 0 {
    n / AddrSpace::PAGE_BYTES + 1
  } else {
    n / AddrSpace::PAGE_BYTES
  }
}

/// A raw 32-bit address space.
///
/// This type encapsulates operations for looking up [`Pd`]s with respect to
/// it.
struct AddrSpace {
  // TODO: roll this ourselves.
  mem: mmap::MemoryMap,

  /// The number of `Pd`s that have actually be created so far.
  materialized_pds: Cell<u32>,
}

impl AddrSpace {
  /// The number of bytes in a `AddrSpace` address space, currently 4 gigabytes.
  ///
  /// TODO: this value is not correct for 32-bit systems; one or two GB is
  /// probably more appropriate?
  const TOTAL_BYTES: usize = 4 * 1024 * 1024 * 1024; // 4G.

  /// The length of a page, currently 4 kilobytes.
  const PAGE_BYTES: usize = 4096;

  /// The number of pages in the `AddrSpace` address space.
  const TOTAL_PAGES: usize = Self::TOTAL_BYTES / Self::PAGE_BYTES;

  /// The number of pages requires to hold all of the page descriptors we will
  /// ever allocate.
  const PD_PAGES: usize =
    bytes_to_pages(Self::TOTAL_PAGES * mem::size_of::<Pd>());

  /// The number of bytes the page descriptor region takes up.
  const PD_BYTES: usize = Self::PD_PAGES * Self::PAGE_BYTES;

  /// The maximum allocation size we can service.
  const MAX_BLOCK_PAGES: usize = u16::MAX as usize + 1;

  /// The maximum allocation size we can service.
  const MAX_BLOCK_BYTES: usize = Self::MAX_BLOCK_PAGES * Self::PAGE_BYTES;

  /// Creates a new address space.
  ///
  /// Returns `None` if this somehow fails.
  pub fn create() -> Option<Self> {
    use mmap::*;
    Some(Self {
      mem: MemoryMap::new(
        Self::TOTAL_BYTES,
        &[MapOption::MapReadable, MapOption::MapWritable],
      )
      .unwrap(),
      materialized_pds: Cell::new(0),
    })
  }

  /// Asserts that `vptr` is a valid virtual pointer in this address space.
  fn assert_vptr_in_range<T>(&self, vptr: Vptr<T>) {
    let offset = vptr.0.get() as usize;
    debug_assert!(offset < self.mem.len());
    debug_assert!(offset % mem::align_of::<T>() == 0);
  }

  /// Asserts that `ptr` is a valid pointer in this address space.
  fn assert_ptr_in_range<T>(&self, ptr: *const T) {
    let addr = ptr as usize;
    let base = self.mem.data() as usize;
    debug_assert!(addr >= base);
    debug_assert!(addr < base + self.mem.len());
  }

  /// Creates a new maximum-size ream by creating pages for it.
  pub fn materialize_new_ream(&self) -> PdRef {
    let mut pages = self.materialized_pds.get();
    unsafe {
      let start = self.mem.data().add(pages as usize);
      start.cast::<Pd>().write_bytes(0, Self::MAX_BLOCK_PAGES);
    }
    self
      .materialized_pds
      .set(pages + Self::MAX_BLOCK_PAGES as u32);

    let first_ream = unsafe { self.pd_at(pages as usize) };
    first_ream.pd.len.set(u16::MAX);
    first_ream
  }

  /// Constructs a [`PdRef`] for a specific `Pd` in this address space.
  ///
  /// # Safety
  ///
  /// Many functions on [`PdRef`] are safe, because they assume the resulting
  /// [`Pd`] is a genuine page descriptor, whose linked list links lead to
  /// _other_ genuine page descriptors.
  pub unsafe fn pd(&self, vptr: Vptr<Pd>) -> PdRef {
    PdRef {
      pd: self.ref_from(vptr),
      raw: self,
    }
  }

  /// Constructs a [`PdRef`] for a specific indexed page.
  ///
  /// # Safety
  ///
  /// Many functions on [`PdRef`] are safe, because they assume the resulting
  /// [`Pd`] is a genuine page descriptor, whose linked list links lead to
  /// _other_ genuine page descriptors.
  pub unsafe fn pd_at(&self, idx: usize) -> PdRef {
    PdRef {
      pd: &*self.mem.data().cast::<Pd>().add(idx),
      raw: self,
    }
  }

  /// Constructs a [`PdRef`] for the page `ptr` is in.
  ///
  /// # Safety
  ///
  /// Many functions on [`PdRef`] are safe, because they assume the resulting
  /// [`Pd`] is a genuine page descriptor, whose linked list links lead to
  /// _other_ genuine page descriptors.
  ///
  /// Additionally, `vptr` must land inside of the block region, rather than
  /// the [`Pd`] region, of the address space.
  pub unsafe fn pd_of(&self, ptr: Vptr<u8>) -> PdRef {
    let idx =
      (ptr.0.get() as usize - AddrSpace::PD_BYTES) / AddrSpace::PAGE_BYTES;
    self.pd_at(idx)
  }

  /// Returns an iterator over all current [`Pd`]s.
  pub fn pds(&self) -> impl Iterator<Item = PdRef> {
    (0..self.materialized_pds.get())
      .map(move |i| unsafe { self.pd_at(i as usize) })
  }

  /// Creates a real reference in this address space corresponding to the
  /// virtual pointer `vptr`.
  ///
  /// # Safety
  ///
  /// `vptr` must, in fact, be a pointer into this address space, and point to
  /// initialized memory.
  pub unsafe fn ref_from<T>(&self, vptr: Vptr<T>) -> &T {
    &*self.ptr_from(vptr)
  }

  /// Creates a real pointer in this address space corresponding to the
  /// virtual pointer `vptr`.
  ///
  /// # Safety
  ///
  /// `vptr` must, in fact, be a pointer into this address space.
  pub unsafe fn ptr_from<T>(&self, vptr: Vptr<T>) -> *mut T {
    self.assert_vptr_in_range(vptr);
    self.mem.data().add(vptr.0.get() as usize).cast::<T>()
  }

  /// Creates a virtual pointer in this address space corresponding to the
  /// real pointer `actual.
  ///
  /// # Safety
  ///
  /// `actual` must, in fact, be a pointer into this address space.
  pub unsafe fn vptr_from<T>(&self, actual: *const T) -> Vptr<T> {
    self.assert_ptr_in_range(actual);
    Vptr(
      NonZeroU32::new_unchecked(
        (actual as *const u8).offset_from(self.mem.data()) as u32,
      ),
      PhantomData,
    )
  }
}

/// Size classes for a `Pd`.
///
/// There is one size class for each power of two from 8 to 4096, plus an
/// extra `Ream` class that represents multi-page blocks.
#[repr(u8)]
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum SizeClass {
  Ream = 0,
  B8 = 3,
  B16 = 4,
  B32 = 5,
  B64 = 6,
  B128 = 7,
  B256 = 8,
  B512 = 9,
  B1024 = 10,
  B2048 = 11,
  B4096 = 12,
}

impl SizeClass {
  #[rustfmt::skip]
  const SMALL_CLASSES: [Self; 10] = [
    Self::B8, Self::B16, Self::B32, Self::B64, Self::B128,
    Self::B256, Self::B512, Self::B1024, Self::B2048, Self::B4096
  ];

  /// The number of bytes in a block of this class.
  ///
  /// Not defined for `Ream`.
  pub fn block_bytes(self) -> Option<usize> {
    if let Self::Ream = self {
      return None;
    }

    Some(1 << (self as usize))
  }

  /// The number of usable blocks in an allocation of this class.
  pub fn total_blocks(self) -> usize {
    let gc_bits = (self.gc_words() - 1) * 8;
    self
      .block_bytes()
      .map(|s| (4096 - gc_bits) / s)
      .unwrap_or(1)
  }

  /// The number of blocks that are skipped for book-keeping purposes.
  pub fn skipped_blocks(self) -> usize {
    self.block_bytes().map(|s| 4096 / s).unwrap_or(1) - self.total_blocks()
  }

  /// The number of 64-bit words necessary to track the state of every slot
  /// for this class.
  pub fn gc_words(self) -> usize {
    #[rustfmt::skip]
    const WORDS: [usize; 13] = [
      1, 1, 1,
      8, 4, 2, 1, 1,
      1, 1, 1, 1, 1,
    ];
    WORDS[self as usize]
  }
}

/// A page descriptor, i.e., a free list node in a [`Heap`].
///
/// The address of a `Pd` within the [`Heap`] defines which page it
/// describes, so it is not included among the fields.
///
/// `Pd` has the property that `memset`ing an allocation for one will
/// initialize it to a good default value. Its size is guaranteed to be a
/// power of two.
#[repr(C)]
struct Pd {
  /// See the module docs for how this value is used.
  ///
  /// Tl;dr: a bitset representing which blocks in the page are used, unless
  /// this is a ream, in which case it indicates if the ream is in use when
  /// nonzero.
  gc_bits: Cell<u64>,

  /// A pointer to the previous page in whatever list this descriptor is in.
  ///
  /// Pointers in a linked list always have this value set to `None`.
  prev: Cell<Option<Vptr<Self>>>,
  /// A pointer to the next page in whatever list this descriptor is in.
  next: Cell<Option<Vptr<Self>>>,

  /// The length of the ream, in pages, minus one; only the first `Pd` in a
  /// ream has a valid `len`.
  ///
  /// Single pages will have a value of zero.
  len: Cell<u16>,

  /// The size class this descriptor is for.
  class: Cell<SizeClass>,

  _padding: [u8; 9],
}

// Ensure the power-of-two size invariant.
const _: () = {
  let isp2 = mem::size_of::<Pd>().is_power_of_two();
  let _ = 1 / isp2 as i32;
};

/// A convenience wrapper around a [`Pd`] and the [`AddrSpace`] it lives in.
///
/// Most of the methods are safe, assuming nothing else reaches into the
/// prev/next pointers inappropriately.
#[derive(Copy, Clone)]
struct PdRef<'mmap> {
  // NOTE: `pd` is a valid `Pd` within `raw`.
  pd: &'mmap Pd,
  raw: &'mmap AddrSpace,
}

impl fmt::Debug for PdRef<'_> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(
      f,
      "Pd({:#010x} in {:p})",
      self.as_vptr().0,
      self.raw.mem.data()
    )
  }
}

impl<'mmap> PdRef<'mmap> {
  /// Gets the number of pages in this ream.
  pub fn pages(self) -> usize {
    self.pd.len.get() as usize + 1
  }

  /// Gets the number of bytes in this ream.
  pub fn bytes(self) -> usize {
    self.pages() * AddrSpace::PAGE_BYTES
  }

  /// Gets the size class for this ream.
  pub fn class(self) -> SizeClass {
    self.pd.class.get()
  }

  /// Sets the size class for this ream.
  pub fn set_class(self, class: SizeClass) {
    self.pd.class.set(class)
  }

  /// Returns true if this page descriptor is in a linked list.
  pub fn is_linked(self) -> bool {
    self.pd.prev.get().is_some()
  }

  /// Returns true if this is a single page.
  pub fn is_single_page(self) -> bool {
    self.pd.len.get() == 0
  }

  /// Converts this `PdRef` back into a virtual pointer.
  pub fn as_vptr(self) -> Vptr<Pd> {
    unsafe { self.raw.vptr_from(self.pd) }
  }

  // Gets the index of this page descriptor.
  pub fn index(self) -> usize {
    self.as_vptr().0.get() as usize / mem::size_of::<Pd>()
  }

  /// Returns a real pointer to the actual managed allocation.
  ///
  /// # Panics
  ///
  /// Panics if the size of `T` is not a power of two or greater than 8.
  pub fn data<T>(self) -> &'mmap [Cell<MaybeUninit<T>>] {
    assert!(mem::size_of::<T>().is_power_of_two() && mem::size_of::<T>() <= 8);

    let skipped_bytes =
      self.class().skipped_blocks() * self.class().block_bytes().unwrap_or(0);
    let start = unsafe { self.raw.ptr_from(self.vdata()).add(skipped_bytes) };

    let len = self.bytes() - skipped_bytes;
    unsafe { slice::from_raw_parts(start.cast(), len / mem::size_of::<T>()) }
  }

  /// Returns a virtual pointer to the start of the managed page.
  pub fn vdata(self) -> Vptr<u8> {
    Vptr(
      NonZeroU32::new(
        (AddrSpace::PD_BYTES + self.index() * AddrSpace::PAGE_BYTES) as u32,
      )
      .unwrap(),
      PhantomData,
    )
  }

  /// Frees all allocations in this page, for use during GC.
  pub fn set_empty(self) {
    self.pd.gc_bits.set(0);
    unsafe {
      let ptr = self.data::<u64>().as_ptr() as *mut u64;
      ptr.write_bytes(0, self.class().gc_words() - 1);
    }
  }

  /// Returns an iterator over this page or ream's GC words.
  ///
  /// # Safety
  ///
  /// This function may only be called after [`PdRef::set_empty()`] has been
  /// called at least once for this page's size class.
  pub unsafe fn gc_words<'a>(&'a self) -> impl Iterator<Item = &'a Cell<u64>> {
    let extra_words = &self.data::<u64>()[..self.class().gc_words() - 1];

    // SAFETY: This transmute is just a `MaybeUninit::assume_init()`.
    iter::once(&self.pd.gc_bits)
      .chain(mem::transmute::<_, &'a [Cell<u64>]>(extra_words).iter())
  }

  /// Returns true if this page or ream is currently empty.
  ///
  /// # Safety
  ///
  /// This function may only be called after [`PdRef::set_empty()`] has been
  /// called at least once for this page's size class.
  pub unsafe fn is_empty(self) -> bool {
    self.gc_words().all(|x| x.get() == 0)
  }

  /// Returns true if this page or ream is currently completely full.
  ///
  /// # Safety
  ///
  /// This function may only be called after [`PdRef::set_empty()`] has been
  /// called at least once for this page's size class.
  pub unsafe fn is_full(self) -> bool {
    let mut blocks = self.class().total_blocks();
    let mut mask = || {
      let mask = if blocks >= 64 {
        !0
      } else {
        (1u64 << blocks) - 1
      };

      blocks = blocks.saturating_sub(64);
      mask
    };

    let mut is_full = true;
    for word in self.gc_words() {
      is_full &= word.get() == mask();
    }
    is_full
  }

  /// Returns the index of the next empty block in this page, if any exists.
  ///
  /// # Safety
  ///
  /// This function may only be called after [`PdRef::set_empty()`] has been
  /// called at least once for this page's size class.
  pub unsafe fn take_next_block(self) -> Option<usize> {
    let mut blocks = self.class().total_blocks();
    let mut mask = || {
      let mask = if blocks >= 64 {
        !0
      } else {
        (1u64 << blocks) - 1
      };

      blocks = blocks.saturating_sub(64);
      mask
    };

    let mut words = self.gc_words();

    words.skip_while(|w| w.get() == mask()).next().map(|w| {
      let idx = w.get().trailing_ones() as usize;
      w.set(w.get() | 1 << idx);
      idx
    })
  }

  /// Marks the given block `idx` as allocated, as part of a GC pause.
  pub unsafe fn mark(self, idx: usize) {
    debug_assert!(idx < self.class().total_blocks());

    let word = idx / 64;
    let bit = idx % 64;

    let word = match word {
      0 => &self.pd.gc_bits,
      _ => mem::transmute::<_, &Cell<u64>>(&self.data::<u64>()[word]),
    };
    word.set(word.get() | (1 << bit))
  }

  /// Splits this ream in two, with the first ream having `prefix` pages in
  /// it.
  ///
  /// Returns `None` for the suffix if it would be empty; returns `None` if
  /// `self` is too small.
  ///
  /// # Panics
  ///
  /// Panics if `self` is a single page, or if `prefix` is zero.
  pub fn split(self, prefix: usize) -> Option<(Self, Option<Self>)> {
    assert!(!self.is_single_page());
    assert!(prefix != 0);
    assert!(prefix <= AddrSpace::MAX_BLOCK_PAGES);

    if self.pages() == prefix {
      Some((self, None))
    } else if self.pages() < prefix {
      None
    } else {
      let suffix_len = self.pages() - prefix - 1;
      let suffix = unsafe { self.offset(prefix as isize) };
      suffix.pd.len.set(suffix_len as u16);

      self.pd.len.set((prefix - 1) as u16);
      Some((self, Some(suffix)))
    }
  }

  /// Unlinks this page descriptor from whatever linked list it happens to be
  /// in.
  pub fn unlink(self) -> Self {
    let prev = match self.prev() {
      Some(p) => p,
      None => panic!("can't unlink {:?}; already unlinked", self),
    };

    if let Some(next) = self.next() {
      next.pd.prev.set(self.pd.prev.get());
    }
    prev.pd.next.set(self.pd.next.get());

    self.pd.prev.set(None);
    self.pd.next.set(None);
    self
  }

  /// Gets the previous descriptor in the list.
  pub fn prev(self) -> Option<Self> {
    self.pd.prev.get().map(|v| unsafe { self.raw.pd(v) })
  }

  /// Gets the next descriptor in the list.
  pub fn next(self) -> Option<Self> {
    self.pd.next.get().map(|v| unsafe { self.raw.pd(v) })
  }

  /// Gets the descriptor for the page at the given offset from this one.
  ///
  /// # Safety
  ///
  /// Same rules as for `<*const u8>::offset()`: don't underflow or overflow the
  /// [`Pd`] array (given its current size).
  pub unsafe fn offset(mut self, offset: isize) -> Self {
    self.pd = unsafe { &*(self.pd as *const Pd).offset(offset) };
    self
  }

  /// Returns an iterator over the rest of the linked list this `Pd` is part
  /// of.
  ///
  /// Behavior is unspecified if `self` is unlinked.
  pub fn walk(mut self) -> impl Iterator<Item = PdRef<'mmap>> {
    let mut current = Some(self);
    let mut next = self.next();
    iter::from_fn(move || {
      let ret = current?;
      current = next;
      next = current.and_then(PdRef::next);
      Some(ret)
    })
  }
}

/// A free list root.
///
/// Free lists are intrusively-linked lists which use the `prev`/`next` pointers
/// in the [`Pd`]s.
struct FreeList {
  /// Sacrificial root node. This `Pd` will never be allocated.
  root: Vptr<Pd>,
}

impl FreeList {
  /// Pushes a descriptor onto this list.
  ///
  /// # Safety
  ///
  /// `pd` must come from the same address space as this `FreeList`.
  pub unsafe fn push(&self, pd: PdRef) {
    debug_assert!(
      !pd.is_linked(),
      "tried to link {:?}, but it was already linked!",
      pd
    );
    debug_assert!(
      pd.as_vptr() != self.root,
      "tried to link root node {:?} to itself",
      pd
    );

    let root = pd.raw.pd(self.root);
    if let Some(first) = root.next() {
      pd.pd.next.set(Some(first.as_vptr()));
      first.pd.prev.set(Some(pd.as_vptr()));
    }
    root.pd.next.set(Some(pd.as_vptr()));
    pd.pd.prev.set(Some(self.root));
  }

  /// Gets the first element of the list, if any.
  ///
  /// # Safety
  ///
  /// `raw` must be this list's address space; see [`AddrSpace::pd()`].
  pub unsafe fn first<'mmap>(
    &self,
    raw: &'mmap AddrSpace,
  ) -> Option<PdRef<'mmap>> {
    raw.pd(self.root).next()
  }
}

/// An Alkyne heap. This type manages all aspects of a garbage-collected heap.
///
/// See the [module docs][`self`] for more information.
pub struct Heap {
  raw: AddrSpace,

  ream_free_list: FreeList,

  page_free_list: FreeList,
  sized_free_lists: [FreeList; SizeClass::SMALL_CLASSES.len()],

  ream_full_list: FreeList,
  page_full_list: FreeList,
}

impl Heap {
  /// Creates a new heap.
  ///
  /// This function requests a large `mmap()` of memory from the operating
  /// system and sets up book-keeping data structures on it.
  pub fn create() -> Option<Heap> {
    let raw = AddrSpace::create()?;
    let first_ream = raw.materialize_new_ream();

    let mut idx = 0;
    let mut next_page = || {
      idx += mem::size_of::<Pd>() as u32;
      FreeList {
        root: Vptr(NonZeroU32::new(idx).unwrap(), PhantomData),
      }
    };

    let heap = Heap {
      raw,

      ream_free_list: next_page(),
      page_free_list: next_page(),

      #[rustfmt::skip]
      sized_free_lists: [
        next_page(), next_page(), next_page(), next_page(), next_page(),
        next_page(), next_page(), next_page(), next_page(), next_page(),
      ],

      ream_full_list: next_page(),
      page_full_list: next_page(),
    };

    unsafe {
      let first_ream = heap.raw.pd_at(0);
      let (_, actual_first) = first_ream.split(idx as usize + 1).unwrap();
      heap.ream_free_list.push(actual_first.unwrap());
    }

    Some(heap)
  }

  /// Allocate a ream with the given number of pages (possibly only one).
  unsafe fn alloc_ream(&self, pages: usize) -> PdRef {
    if self.ream_free_list.first(&self.raw).is_none() {
      unsafe {
        self.ream_free_list.push(self.raw.materialize_new_ream());
      }
    }

    loop {
      let list = unsafe { self.ream_free_list.first(&self.raw) }.unwrap();
      for pd in list.walk() {
        let (ream, rest) = match pd.split(pages) {
          Some(r) => r,
          None => continue,
        };

        match rest {
          Some(rest) if rest.is_single_page() => unsafe {
            self.page_free_list.push(rest)
          },
          Some(rest) => unsafe { self.ream_free_list.push(rest) },
          None => {}
        }

        return ream.unlink();
      }

      // We seem to be out of memory, so push some more and try again.
      unsafe {
        self.ream_free_list.push(self.raw.materialize_new_ream());
      }
    }
  }

  /// Allocate a small block of the given `class`.
  unsafe fn alloc_small(&self, class: SizeClass) -> Vptr<u8> {
    let free_list = &self.sized_free_lists[class as usize - 3];

    let page = unsafe {
      match free_list.first(&self.raw) {
        Some(first) => first,
        None => {
          let page = match self.page_free_list.first(&self.raw) {
            Some(first) => first.unlink(),
            None => self.alloc_ream(1),
          };
          free_list.push(page);
          page.set_class(class);
          page.set_empty();
          page
        }
      }
    };

    let idx = match unsafe { page.take_next_block() } {
      Some(idx) => idx,
      None => panic!("full page found in free list: {:?}", page),
    };
    if page.is_full() {
      unsafe { self.page_full_list.push(page.unlink()) }
    }

    let start = idx * class.block_bytes().unwrap();
    page.vdata()
  }

  /// Allocate a block of at least `bytes` length. The returned pointer will be
  /// 64-bit aligned.
  ///
  /// Currently, this function is infallible, but it is likely to change in the
  /// future.
  pub fn alloc(&self, mut bytes: usize) -> Vptr<u8> {
    if bytes <= 4096 {
      let bin_log = bytes.next_power_of_two().trailing_zeros();
      let class = SizeClass::SMALL_CLASSES[bin_log.saturating_sub(3) as usize];
      unsafe { self.alloc_small(class) }
    } else if bytes <= AddrSpace::MAX_BLOCK_BYTES {
      unsafe {
        let ream = self.alloc_ream(bytes_to_pages(bytes));
        ream.set_class(SizeClass::Ream);
        ream.take_next_block();
        self.ream_full_list.push(ream);
        ream.vdata()
      }
    } else {
      panic!("unreasonable allocation request: {} bytes", bytes);
    }
  }

  /// Begins a garbage collection pause.
  ///
  /// This function walks every relevant free list and clears the `gc_bits` of
  /// each page or ream.
  ///
  /// # Safety
  ///
  /// This function leaves the heap in a broken state. [`Heap::mark()`] and
  /// [`Heap::sweep()`] should be used to bring the heap back into the correct
  /// state.
  ///
  /// During a GC pause, calling `alloc()` is forbidden.
  pub unsafe fn start_gc(&self) {
    for pd in self.raw.pds().filter(|pd| pd.is_linked()) {
      pd.set_empty()
    }
  }

  /// Marks the allocation corresponding to `ptr` as "allocated" as part of the
  /// "mark" portion of garbage collection.
  ///
  /// # Safety
  ///
  /// `ptr` must have been created with [`Heap::alloc()`]; this function has the
  /// same behavior as `free()` in this respect.
  pub unsafe fn mark(&self, ptr: Vptr<u8>) {
    let pd = self.raw.pd_of(ptr);
    debug_assert!(pd.is_linked());

    let offset = ptr.0.get() - pd.vdata().0.get();
    pd.mark(offset as usize / pd.class().block_bytes().unwrap_or(1));
  }

  /// Completes a garbage collection pause by reaping unused memory.
  ///
  /// # Safety
  ///
  /// This function should only be called once all appropriate calls to
  /// [`Heap::mark()`] are complete.
  pub unsafe fn sweep(&self) {
    for pd in self.raw.pds().filter(|pd| pd.is_linked()) {
      if pd.is_empty() {
        pd.unlink();
        if pd.is_single_page() {
          unsafe { self.page_free_list.push(pd) }
        } else {
          unsafe { self.ream_free_list.push(pd) }
        }
      } else if pd.is_full() {
        // We can assume that full `Pd`s are already in the correct lists and
        // don't need to be moved.
      } else {
        // Non-empty, non-full lists cannot be reams.
        debug_assert!(pd.class() != SizeClass::Ream);
        pd.unlink();
        unsafe { self.sized_free_lists[pd.class() as usize - 3].push(pd) }
      }
    }
  }

  /// Dump debugging information about the heap into `out`.
  pub fn debug_dump(&self, out: &mut dyn io::Write) -> io::Result<()> {
    #[derive(Default)]
    struct Stats {
      pages: usize,
      bytes: usize,
    }

    fn dump_free_list(
      list: Option<PdRef>,
      stats_out: &mut Stats,
      out: &mut dyn io::Write,
    ) -> io::Result<()> {
      let mut stats = Stats::default();
      let list = match list {
        Some(list) => list,
        None => return writeln!(out, "  <empty>"),
      };
      for (i, pd) in list.walk().enumerate() {
        let in_use: u32 =
          unsafe { pd.gc_words() }.map(|w| w.get().count_ones()).sum();

        stats.pages += pd.pages() as usize;
        stats.bytes += match pd.class() {
          SizeClass::Ream if in_use != 0 => pd.bytes(),
          class => in_use as usize * pd.class().block_bytes().unwrap_or(0),
        };

        writeln!(
          out,
          "  {:>5}: {:#010x}/{:#010x} {{ pages: {:>5}, bytes: {:>9}, blocks: {}/{} }}",
          i,
          pd.as_vptr().0,
          pd.vdata().0,
          pd.pages(),
          pd.bytes(),
          in_use,
          pd.class().total_blocks()
        )?;
      }

      writeln!(
        out,
        "  pages: {:>9}\n  bytes: {:>9}",
        stats.pages, stats.bytes
      )?;
      stats_out.pages += stats.pages;
      stats_out.bytes += stats.bytes;
      return Ok(());
    }

    let mut stats = Stats::default();

    writeln!(out, "{:/<80}", "//// gc::Heap::debug_dump() ")?;

    writeln!(out, "/// ream_free_list ///")?;
    dump_free_list(
      unsafe { self.ream_free_list.first(&self.raw) },
      &mut stats,
      out,
    )?;
    writeln!(out, "")?;

    writeln!(out, "/// page_free_list ///")?;
    dump_free_list(
      unsafe { self.page_free_list.first(&self.raw) },
      &mut stats,
      out,
    )?;
    writeln!(out, "")?;

    for (i, list) in self.sized_free_lists.iter().enumerate() {
      writeln!(out, "/// sized_free_list ({} bytes) ///", 8u32 << i)?;
      dump_free_list(unsafe { list.first(&self.raw) }, &mut stats, out)?;
      writeln!(out, "")?;
    }

    writeln!(out, "/// ream_full_list ///")?;
    dump_free_list(
      unsafe { self.ream_full_list.first(&self.raw) },
      &mut stats,
      out,
    )?;
    writeln!(out, "")?;

    writeln!(out, "/// page_full_list ///")?;
    dump_free_list(
      unsafe { self.page_full_list.first(&self.raw) },
      &mut stats,
      out,
    )?;
    writeln!(out, "")?;

    writeln!(
      out,
      "  total pages: {:>9}\n  total bytes: {:>9}",
      stats.pages, stats.bytes
    )?;
    writeln!(out, "{:/<80}\n", "")
  }
}

/*#[cfg(test)]
mod test {
  use super::*;
  use std::io::Write;

  #[test]
  fn sanity() {
    let heap = Heap::create().unwrap();

    for _ in 0..2 {
      let mut marked = Vec::new();
      let mut i = 1;
      for _ in 0..16 {
        i *= 3;
        for j in 0..2000 / i + 1 {
          let blob = heap.alloc(i);
          if j == 1 {
            marked.push(blob);
          }
          /*writeln!(
            io::stdout(),
            "heap.alloc({:>9}) = [{:#010x}, {:p}, {:>9}]",
            i,
            unsafe { heap.raw.vptr_from(blob.as_ptr()).0 },
            blob,
            blob.len()
          );*/
        }
      }

      heap.debug_dump(&mut io::stdout());

      unsafe {
        heap.begin_gc();
        for p in marked { heap.mark(p) }
        heap.sweep();
      }
      heap.debug_dump(&mut io::stdout());
    }

    panic!()
  }
}*/
