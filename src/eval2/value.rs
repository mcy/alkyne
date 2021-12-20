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

//! Alkyne values.
//! 
//! Values in the Alkyne interpreter can exist in three places, with distinct
//! representations:
//! - On the operand stack.
//! - On the heap.
//! - Outside of an interpreter in an "interchange" form.
//! 
//! There are eight Alkyne types we need to represent: null, booleans, numbers,
//! strings, lists, objects, functions, and myriad "opaque" objects.
//! 
//! Throughout, we assume little-endian representation.
//!
//! # Stack Representation
//! 
//! On the stack, values are split into an 8-bit type and a 64-bit payload;
//! the stack consists of a *type stack* and a *payload stack*.
//! 
//! Compared to the heap representations, which mostly only exist to be elements
//! of lists and objects, stack representations are far more diverse. They are
//! as follows:
//! 
//! - `Null`. Payload is unused.
//! - `Poison`. A special value that some instructions produce to signal an
//!   exceptional condition. Not directly observable by users.
//! - `Bool`. Only the lowest bit of the payload is used.
//! 
//! - `SmallInt`. Low 31 bits of the payload are used. These `i31`s are used
//!   to optimize arithmetic operations, since they represent the vast majority
//!   of numbers used in practice.
//! - `Float`. Full IEEE double-precision floats, which `SmallInt`s widen to as
//!   necessary.
//! 
//! - `InlineStrN`. Nine distinct string types for strings that have between 0 or
//!   eight UTF-8 code units. The payload is the string data.
//! - `ConstStr`. A string constant. The first 24 bits of the payload are the
//!   constant address.
//! - `SmallConstStr`. A small substring of a constant string. The first 24 bits
//!   of the payload are the constant address; the next two 20-bit integers are
//!   the offset and length.
//! - `HeapStr`. A string on the heap. The first 32 bits are a [`gc::Vptr`].
//! - `SmallHeapStr`. A small substring of a heap string. The first 32 bits are a
//!   [`gc::Vptr`], and the next two 16-bit integers are the offset and length.
//! 
//! - `InlineListN`. Three distinct list types for lists that have between 0 to 2
//!   elements, each encoded in 32-bit heap form.
//! - `HeapList`. A list on the heap. The first 32 bits are a [`gc::Vptr`].
//! - `SmallList`. A small slice of a heap list. The first 32 bits are a
//!   [`gc::Vptr`], and the next two 16-bit integers are the offset and length.
//! 
//! - `HeapObject`. An object on the heap. The first 32 bits are a [`gc::Vptr`].
//! 
//! - `InlineFnN`. Two distinct function types which capture exactly zero or one
//!   value, which is in 32-bit heap form. The first 24 bits are the function
//!   address, while the next 32 are the capture (if present).
//! - `HeapFn`. A function value on the heap. The first 32 bits are a
//!   [`gc::Vptr`].
//!   
//! - `ExternPtr`. An external Rust object. All 64 bits form a pointer into Rust's
//!   ordinary heap, where it points to data plus some kind of inline vtable
//!   (not a `dyn` vtable) that Alkyne knows how to call. The pointer is
//!   wholly-owned by Alkyne and is freed during garbage collection.
//! 
//! # Heap Representation
//! 
//! On the heap, every value is encoded as a 32-bit integer. A `v: u32`
//! value is classified thus:
//! 
//! - If the low bit is clear (i.e., `v & 1 == 0`), then it is 31-bit `SmallInt`,
//!   with the value `(v as i32) >> 1`. Small integers are `i31`s semantically.
//!   These small integers are an optimization to represent the vast majority
//!   of numbers used in practice.
//! 
//! - If the low three bits are `0b001`, then it is an object pointer. These
//!   represent all of the variable-length types.
//! 
//! - If the low three bits are `0b011`, then it is a float pointer. These
//!   represent all other numbers.
//! 
//! - If the low three bits are `0b111`, then...
//! 
//!   - If the low eight bits are `0b0000_1111`, then the top 24 bits refer to a
//!     module constant, such as an unbound function.
//!     
//!   - If the low eight bits are `0b1111_1111`, then it is one of the following
//!     special values:
//!     - `0b11111111_11111111_11111111_11111111` is `null`.
//!     - `0b01111111_11111111_11111111_11111111` is `true`.
//!     - `0b10111111_11111111_11111111_11111111` is `false`.
//!     - `0b00011111_11111111_11111111_11111111` is `""`, the empty string.
//!     - `0b01011111_11111111_11111111_11111111` is `[]`, the empty list.
//!   
//!   - All other values are reserved. In particular, values ending with
//!     `0b0110` will never be valid, so they can be used to compress object
//!     representations.
//!
//! If it is a float pointer, it points to a 64-bit IEEE float on the heap.
//! Floats use their own pointer type to avoid having to store type information
//! for them on the heap directly.
//!
//! If it is an object pointer, it must be one of the remaining Alkyne types:
//! - A string.
//! - A list.
//! - An object (as in `{x: 5}`, specifically).
//! - A bound function (i.e., a function with non-trivial captures).
//! - An external Rust value.
//!
//! We'll now discuss how these are each represented.
//!   
//! ## Object Types
//!
//! The first 32-bit word of each object's low three bits specify its "object
//! type" (distinct from an Alkyne type). Note that the size of an allocation
//! can be inferred from its address, so we don't store it.
//!
//! These object types are as follows:
//!
//! ### Arrays
//!
//! Arrays have allocation type 0. Each array looks like this:
//!
//! ```text
//! struct Array {
//!   type: u3,
//!   count: u29,
//!   elements: [HeapVal; self.count],
//! }
//! ```
//!
//! Arrays represent Alkyne lists that are not part of a larger array. `count`
//! is the number of `elements` that are actually part of that array.
//!
//! ### Slices
//!
//! Slices have allocation type 1. Each slice looks like this:
//!
//! ```text
//! struct Slice {
//!   type: u3,
//!   array: u29,
//!   length: u31,
//!   has_offset: u1,
//!   offset: [u32; self.has_offset],
//! }
//! ```
//!
//! `array` is a pointer to some other array on the heap; `length` is the length
//! of of the slice; `offset` is the offset from the start of `*array`. Both
//! the length and the offset are given in bytes.
//! 
//! If the `has_offset` bit is cleared, though, this is a "prefix" slice, and
//! the `offset` portion is omitted.
//!
//! ### Objects
//!
//! Objects have allocation type 2. Each object looks like this:
//! 
//! ```text
//! struct Object {
//!   type: u3,
//!   parent: u29,
//!   count: u32,
//!   pairs: [(HeapVal, HeapVal); ...],
//! }
//! ```
//!
//! Objects are implemented as open-addressing hashtables, where each pair is
//! a 64-aligned pair of [`HeapVal`]s. There are `count` inhabited pairs in
//! the map. The precise algorithm isn't important to the representation.
//! 
//! Empty pairs in the map are filled with all-ones (because elements can't be
//! deleted, we don't make use of tombstones). Although this would normally make
//! both entries `null`, objects can only have string keys, so we can use this
//! as the "empty" marker.
//!
//! Objects may have parents; `parent` is the address of another object in that
//! case. `count` does not include elements from the parent chain; this value is
//! only used for monitoring the load factor of the hashtable.
//! 
//! If `count` is all-ones, this means that the object was resized at some
//! point; this means that to find the real object, `parent` needs to be
//! followed.
//!
//! ### Bound Functions
//!
//! Bound functions use allocation type 3. A bound function is a function which
//! has a number of *captures*, which are prepended to the function's argument
//! list when it is called. Bound functions look like this:
//! ```text
//! struct BoundFn {
//!   type: u3,
//!   capture_count: u5,
//!   fn_addr: u24,
//!   union {
//!     captures: [HeapVal; self.capture_count],
//!     extended: struct {
//!       capture_count: u32,
//!       captures: [HeapVal; self.capture_count],
//!     },
//!   },
//! }
//! ```
//!
//! `fn_addr` is a 24-bit `call` instruction immediate. `capture_count` is the
//! number of captured values that follow, minus one (since zero captures would
//! not use a bound function).
//! 
//! If `captures_count` is exactly `31`, then the header is instead followed by
//! a `u32` that indicates the number of captures which follow. This is
//! expressed as the union above.
//!
//! ### Strings
//!
//! For now, strings use object types 4 and 5 analogously to arrays and slices,
//! except that all lengths are in bytes rather than 32-bit elements. I'd like
//! to aggressively intern strings in the future.
//!
//! ### External Values
//!
//! External values use object type 6, and look like this:
//! ```type
//! struct ExternPtr {
//!   type: u3,
//!   ptr: u61,
//! }
//! ```
//! 
//! `ptr` is a 64-bit aligned pointer into Rust's ordinary heap, where it points
//! to data plus some kind of inline vtable (not a `dyn` vtable) that Alkyne
//! knows how to call. The pointer is wholly-owned by Alkyne and is freed
//! during garbage collection.
//! 
//! # Interchange Representation
//! 
//! TODO

use std::mem;
use std::mem::MaybeUninit;
use std::marker::PhantomData;

use crate::eval2::gc;

#[derive(Copy, Clone, Debug)]
#[repr(transparent)]
pub struct ConstPtr(u32);

#[derive(Copy, Clone, Debug)]
#[repr(C, u8)]
pub enum StackVal {
  Null,
  Poison,
  Bool(bool),
  SmallInt(i32),
  Float(f64),

  EmptyStr,
  InlineStr1([u8; 1]),
  InlineStr2([u8; 2]),
  InlineStr3([u8; 3]),
  InlineStr4([u8; 4]),
  InlineStr5([u8; 5]),
  InlineStr6([u8; 6]),
  InlineStr7([u8; 7]),
  InlineStr8([u8; 8]),
  ConstStr(ConstPtr),
  SmallConstStr(ConstPtr, u16, u16),
  HeapStr(gc::Vptr<u8>),
  SmallHeapStr(gc::Vptr<u8>, u16, u16),

  EmptyList,
  InlineList1([HeapVal; 1]),
  InlineList2([HeapVal; 2]),
  HeapList(gc::Vptr<u8>),
  SmallList(gc::Vptr<u8>, u16, u16),

  HeapObj(gc::Vptr<u8>),

  ConstFn(ConstPtr),
  InlineFn(ConstPtr, HeapVal),
  HeapFn(gc::Vptr<u8>),

  ExternPtr(*mut u8),
}

impl StackVal {
  pub fn into_raw_parts(self) -> (u8, MaybeUninit<u64>) {
    #[repr(C)]
    struct Exploded(u8, MaybeUninit<u64>);
    let Exploded(ty, payload) = unsafe { mem::transmute(self) };
    (ty, payload)
  }

  pub unsafe fn from_raw_parts(ty: u8, payload: MaybeUninit<u64>) -> Self {
    #[repr(C)]
    struct Exploded(u8, MaybeUninit<u64>);
    mem::transmute(Exploded(ty, payload))
  }
}

#[derive(Copy, Clone, Debug)]
#[repr(transparent)]
pub struct HeapVal(u32);

pub struct HeapPtr<'gc, T: ?Sized>(*mut u32, PhantomData<&'gc T>);

impl<T> Clone for HeapPtr<'_, T> {
  fn clone(&self) -> Self {
    Self(self.0, self.1)
  }
}
impl<T> Copy for HeapPtr<'_, T> {}

pub struct HeapArray([()]);

impl HeapPtr<'_, HeapArray> {
  pub fn len(self) -> usize {
    let word = unsafe { self.0.read() };
    word as usize >> 3
  }
}