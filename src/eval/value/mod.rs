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

//! Alkyne runtime values. These consist of eight types:
//! - `null`, the singleton, default value.
//! - `bool`, a boolean.
//! - `number`, a floating-point number.
//! - `string`, an immutable string.
//! - `list`, an array of values.
//! - `object`, a hashtable with inheritance.
//! - `fn`, a callable function.
//! - `opaque`, an opaque value with a fixed set of operations.

use std::fmt::Debug;
use std::fmt::Display;

use crate::eval::encode::alkyne::UclEncoding;
use crate::eval::encode::Encoder;

#[macro_use]
pub mod native_macros;

pub mod fns;
pub use fns::Fn;
pub use fns::NativeFn;

pub mod seq;
pub use seq::List;
pub use seq::Str;

pub mod object;
pub use object::Object;

pub mod convert;
pub use convert::IntoValue;

/// A `Value` is a Alkyne value. `Value`s can be safely shared across threads,
/// though execution of a Alkyne file is single-threaded.
#[derive(Clone, Debug)]
pub enum Value<'i> {
  Null,
  Bool(bool),
  Number(f64),
  String(Str<'i>),
  List(List<'i>),
  Object(Object<'i>),
  Fn(Fn<'i>),
  NativeFn(NativeFn<'i>),
  Std,
  Range { start: i64, end: i64, step: i64 },
}

impl<'i> Value<'i> {
  /// Returns the `Type` of this `Value`.
  pub fn ty(&self) -> Type {
    match self {
      Value::Null => Type::Null,
      Value::Bool(..) => Type::Bool,
      Value::Number(..) => Type::Number,
      Value::String(..) => Type::String,
      Value::List(..) => Type::List,
      Value::Object(..) => Type::Object,
      Value::Fn(..) | Value::NativeFn(..) => Type::Fn,
      _ => Type::Opaque,
    }
  }

  /// The "machine epsilon", the smallest value tolerated for the fractional
  /// part of an "integer" number.
  pub const EPSILON: f64 = 1e-12;

  /// Attempts to convert this value into an integer, assuming that it is a
  /// number with sufficiently small fractional part.
  ///
  /// If the conversion fails, the type of the value is returned instead.
  pub fn as_int(&self) -> Result<i64, Type> {
    match self {
      Value::Number(f) if f.fract().abs() < Self::EPSILON => Ok(*f as i64),
      v => Err(v.ty()),
    }
  }
}

impl Display for Value<'_> {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    let buf = Encoder::<UclEncoding>::new().encode(self);
    write!(
      f,
      "{}",
      buf
        .as_ref()
        .map(|s| s.as_str())
        .unwrap_or("<encoding error>")
    )
  }
}

/// A type implementing `DebugInfo` can provide a user-displayable value
/// containing debug information about itself (such as pointer values and
/// ref-count information).
pub trait DebugInfo {
  /// A user-displayable record type containing type-specific debug information.
  type Info: Display;

  /// Creates a value of `Info` describing `self` at this instant in time.
  fn debug_info(&self) -> Self::Info;
}

/// A `DebugInfoScalar` provides debug information for all of Alkyne's "scalar"
/// types (null, bool, and number).
#[derive(Copy, Clone, Debug)]
pub struct DebugInfoScalar {
  /// A pile of bytes derived from a scalar value.
  pub bytes: u64,
}

impl Display for DebugInfoScalar {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    write!(f, "<{:#x}>", self.bytes)
  }
}

impl DebugInfo for () {
  type Info = DebugInfoScalar;

  fn debug_info(&self) -> Self::Info {
    DebugInfoScalar { bytes: 0 }
  }
}

impl DebugInfo for bool {
  type Info = DebugInfoScalar;

  fn debug_info(&self) -> Self::Info {
    DebugInfoScalar { bytes: *self as _ }
  }
}

impl DebugInfo for f64 {
  type Info = DebugInfoScalar;

  fn debug_info(&self) -> Self::Info {
    DebugInfoScalar {
      bytes: self.to_bits(),
    }
  }
}

/// A `Type` represents one of the seven Alkyne value types.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum Type {
  Null,
  Bool,
  Number,
  String,
  List,
  Object,
  Fn,
  Opaque,
}

impl Type {
  pub fn name(self) -> &'static str {
    match self {
      Type::Null => "null",
      Type::Bool => "bool",
      Type::Number => "number",
      Type::String => "string",
      Type::List => "list",
      Type::Object => "object",
      Type::Fn => "function",
      Type::Opaque => "opaque",
    }
  }
}

impl Display for Type {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    write!(f, "{}", self.name())
  }
}

/// A Alkyne-wrapped native Rust object.
///
/// Types implementing this trait can be inserted into a Alkyne runtime as vtables,
/// allowing for the runtime to interact with the underlying platform.
///
/// The reported type is always `opaque`.
pub trait Native: Send + Sync {
  /// Performs an indexing operation into `self`.
  ///
  /// Returns `None` if the operation fails for any reason.
  #[allow(unused)]
  fn index<'i>(&self, args: &[Value<'i>]) -> Option<Value<'i>> {
    None
  }

  /// Performs a function call on `self`.
  ///
  /// Returns `None` if the function call is not supported.
  #[allow(unused)]
  fn call<'i>(&self, args: &[Value<'i>]) -> Option<Value<'i>> {
    None
  }

  /// Begins an iteration operation on `self`, returning an iterator over
  /// itself.
  ///
  /// Returns `None` if this type does not support iteration.
  #[allow(unused)]
  fn iter<'i>(&self) -> Option<Box<dyn Iterator<Item = Vec<Value<'i>>>>> {
    None
  }
}
