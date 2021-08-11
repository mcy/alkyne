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

//! Alkyne list-like values.

use std::borrow::Borrow;
use std::fmt;
use std::hash::Hash;
use std::hash::Hasher;
use std::ops::Deref;
use std::ops::Range;
use std::sync::Arc;

use crate::eval::escaping;
use crate::eval::value::DebugInfo;
use crate::eval::value::Value;

/// A Alkyne string, i.e., an immutable, reference-counted slice of UTF-8 bytes.
pub type Str<'i> = ArcSlice<'i, str>;

/// A Alkyne list, i.e., an immutable, reference-counted slice of Alkyne values.
pub type List<'i> = ArcSlice<'i, [Value<'i>]>;

/// Represents a block of data that can be put into an `ArcSlice`.
///
/// For example, `[T]` implements this trait.
#[allow(clippy::len_without_is_empty)]
pub trait Seq {
  /// Slices along `range`.
  ///
  /// Returns `None` if the range is invalid.
  fn slice(&self, range: Range<usize>) -> Option<&Self>;

  /// Returns the length of the underlying data block.
  fn len(&self) -> usize;

  /// Creates an empty value of `Self` with any lifetime.
  fn empty<'a>() -> &'a Self;

  /// Converts a reference to `Self` into a unique integer.
  fn ptr_value(&self) -> usize;
}

impl<T> Seq for [T] {
  #[inline]
  fn slice(&self, range: Range<usize>) -> Option<&Self> {
    self.get(range)
  }

  #[inline]
  fn len(&self) -> usize {
    <[T]>::len(self)
  }

  #[inline]
  fn empty<'a>() -> &'a Self {
    &[]
  }

  #[inline]
  fn ptr_value(&self) -> usize {
    self.as_ptr() as usize
  }
}

impl Seq for str {
  #[inline]
  fn slice(&self, range: Range<usize>) -> Option<&Self> {
    self.get(range)
  }

  #[inline]
  fn len(&self) -> usize {
    str::len(self)
  }

  #[inline]
  fn empty<'a>() -> &'a Self {
    ""
  }

  #[inline]
  fn ptr_value(&self) -> usize {
    self.as_ptr() as usize
  }
}

/// An `ArcSlice` is a slice of a reference-counted block of data.
///
/// `ArcSlice`es contain an `Arc` pointing to the complete block of data, and
/// a range of that data. This means that slicing an `ArcSlice` is as cheap as
/// am atomic increment.
///
/// An `ArcSlice` can also point to static data, bounded by the lifetime `'i`.
///
/// `ArcSlice` implements `Deref<Target = S>`, but only returns the subrange it
/// points to, not the whole block of data.
#[derive(Debug)]
pub struct ArcSlice<'i, S: ?Sized> {
  inner: Inner<'i, S>,
  start: usize,
  end: usize,
}

#[derive(Debug)]
enum Inner<'i, S: ?Sized> {
  Empty,
  Static(&'i S),
  Dynamic(Arc<S>),
}

impl<'i, S: Seq + ?Sized> Inner<'i, S> {
  fn as_ref(&self) -> &S {
    match self {
      Inner::Empty => S::empty(),
      Inner::Static(s) => s,
      Inner::Dynamic(s) => s.as_ref(),
    }
  }
}

/// The allocation type of an `ArcSlice`.
#[derive(Eq, PartialEq, Copy, Clone, Hash, Debug)]
pub enum AllocType {
  /// An empty data block.
  Empty,
  /// A "static" data block, whose lifetime outlives the interpreter lifetime.
  Static,
  /// A "dynamic" data block, which was created by the interpreter and needs to
  /// be ref-counted; includes the current ref-count.
  Dynamic(usize),
}

impl fmt::Display for AllocType {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      AllocType::Empty => write!(f, "empty"),
      AllocType::Static => write!(f, "static"),
      AllocType::Dynamic(count) => write!(f, "arc = {}", count),
    }
  }
}

/// A `DebugInfoSeq` provides debug information for a Alkyne "sequence" type.
#[derive(Copy, Clone, Debug)]
pub struct DebugInfoSeq {
  /// The address of the underlying data.
  pub addr: usize,
  /// The type of allocation this `ArcSlice` is using.
  pub alloc_ty: AllocType,
  /// The start of the subrange of the allocation this `ArcSlice` points to.
  pub start: usize,
  /// The end of the subrange of the allocation this `ArcSlice` points to.
  pub end: usize,
}

impl fmt::Display for DebugInfoSeq {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(
      f,
      "<{:#x}[{}..{}], {}>",
      self.addr, self.start, self.end, self.alloc_ty
    )
  }
}

impl<S: Seq + ?Sized> DebugInfo for ArcSlice<'_, S> {
  type Info = DebugInfoSeq;

  fn debug_info(&self) -> Self::Info {
    DebugInfoSeq {
      addr: self.inner.as_ref().ptr_value(),
      alloc_ty: match &self.inner {
        Inner::Empty => AllocType::Empty,
        Inner::Static(..) => AllocType::Static,
        Inner::Dynamic(arc) => AllocType::Dynamic(Arc::strong_count(arc)),
      },
      start: self.start,
      end: self.end,
    }
  }
}

impl<'i, S: Seq + ?Sized> ArcSlice<'i, S> {
  /// Creates a new `ArcSlice` pointing to all of `values`.
  pub fn new(values: impl Into<Arc<S>>) -> Self {
    let values = values.into();
    let len = values.len();
    if len == 0 {
      return Self::empty();
    }
    Self {
      inner: Inner::Dynamic(values),
      start: 0,
      end: len,
    }
  }

  /// Creates an empty `ArcSlice`.
  pub fn empty() -> Self {
    Self {
      inner: Inner::Empty,
      start: 0,
      end: 0,
    }
  }

  /// Creates an `ArcSlice` that points to a static, rather than ref-counted,
  /// value.
  pub fn new_static(ptr: &'i S) -> Self {
    if ptr.len() == 0 {
      return Self::empty();
    }
    Self {
      inner: Inner::Static(ptr),
      start: 0,
      end: ptr.len(),
    }
  }

  /// Slices the underlying data according to the start and end indices.
  pub fn as_sliced(&self) -> &S {
    self
      .inner
      .as_ref()
      .slice(self.start..self.end)
      .expect("ArcSlice range cannot be out of bounds")
  }

  /// Reslices the underlying data, returning a copy of `self` with the indices
  /// further constrained.
  ///
  /// Note that indexing is local:
  /// ```
  /// let xs = ArcSlice::new([1, 2, 3, 4, 5]);
  /// assert_eq!(xs.slice(2..5).slice(1..2).as_sliced(), &[4]);
  /// ```
  pub fn slice(&self, range: Range<usize>) -> Option<Self> {
    let inner = self.inner.as_ref();

    let start = range.start + self.start;
    let end = range.end + self.start;
    inner.slice(start..end)?;

    if range.start == range.end {
      return Some(Self::empty());
    }

    Some(ArcSlice {
      start,
      end,
      ..self.clone()
    })
  }

  /// Returns the subrange of the underlying data that this `ArcSlice` points
  /// to.
  pub fn range(&self) -> Range<usize> {
    self.start..self.end
  }

  /// Returns the length of the subrange that this `ArcSlice` points to.
  pub fn len(&self) -> usize {
    self.end - self.start
  }

  /// Returns whether this `ArcSlice` is empty.
  pub fn is_empty(&self) -> bool {
    self.len() == 0
  }

  /// Compares `self` and `other` for pointer equality, i.e., they point to the
  /// same subrange of the same block of data.
  pub fn ptr_eq(&self, other: &Self) -> bool {
    self.start == other.start
      && self.end == other.end
      && self.inner.as_ref().ptr_value() == other.inner.as_ref().ptr_value()
  }
}

impl<S: Seq + ?Sized> Deref for ArcSlice<'_, S> {
  type Target = S;

  fn deref(&self) -> &Self::Target {
    self.as_sliced()
  }
}

impl<S: Seq + ?Sized> Borrow<S> for ArcSlice<'_, S> {
  fn borrow(&self) -> &S {
    self.as_sliced()
  }
}

impl<S: Seq + ?Sized, T: Into<Arc<S>>> From<T> for ArcSlice<'_, S> {
  fn from(seq: T) -> Self {
    Self::new(seq)
  }
}

impl<S: Seq + ?Sized + Hash> Hash for ArcSlice<'_, S> {
  #[inline]
  fn hash<H: Hasher>(&self, state: &mut H) {
    self.as_sliced().hash(state)
  }
}

impl<S: Seq + ?Sized + PartialEq> PartialEq for ArcSlice<'_, S> {
  #[inline]
  fn eq(&self, other: &Self) -> bool {
    self.as_sliced().eq(other.as_sliced())
  }
}

impl<S: Seq + ?Sized + Eq> Eq for ArcSlice<'_, S> {}

impl<S: ?Sized> Clone for ArcSlice<'_, S> {
  fn clone(&self) -> Self {
    ArcSlice {
      inner: match &self.inner {
        Inner::Empty => Inner::Empty,
        Inner::Static(p) => Inner::Static(p),
        Inner::Dynamic(arc) => Inner::Dynamic(arc.clone()),
      },
      start: self.start,
      end: self.end,
    }
  }
}

impl fmt::Display for Str<'_> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    let mut buf = String::new();
    escaping::escape_alkyne_string(&*self, false, &mut buf);
    write!(f, "{}", buf)
  }
}

impl fmt::Display for List<'_> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "[")?;
    let mut first = false;
    for v in self.iter() {
      if first {
        write!(f, "{}", v)?;
        first = false;
      } else {
        write!(f, ", {}", v)?;
      }
    }
    write!(f, "]")
  }
}
