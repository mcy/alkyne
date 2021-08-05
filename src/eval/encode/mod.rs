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

//! Encoding functions for JSON.

use std::collections::HashSet;
use std::fmt;
use std::ops::Deref;
use std::ops::DerefMut;

use crate::eval::error::EvalError;
use crate::eval::escaping;
use crate::eval::stdlib::ENCODE_AS;
use crate::eval::value::Type;
use crate::eval::value::Value;
use crate::eval::Context as UclContext;
use crate::eval::ControlFlow;
use crate::syn::Span;

pub mod alkyne;
pub mod json;

/// `Encode` represents an encoding of Alkyne values. Types which implement
/// `Encode` can be used to create a textual representation of a Alkyne value.
pub trait Encode<'i>: Sized {
  /// Convert `val` into text.
  ///
  /// The `Context` value can be used to access `self`, as well as to recurse
  /// further into the Alkyne value tree.
  fn encode(ctx: Context<Self>, val: &Value<'i>)
    -> Result<(), EncodeError<'i>>;
}

/// An `Encoder` gradually constructs a textual representation of a Alkyne value.
///
/// The type parameter `E` represents the choice of encoding.
pub struct Encoder<E> {
  buf: String,
  cycle_detector: HashSet<usize>,
  path: Vec<PathComponent>,
  encode: E,
}

/// A `Context` is an encoding context, granting limited access to the inner
/// state of an `Encoder`.
///
/// It is also a smart pointer over `E`, so fields and methods of `E` can be
/// accessed directly in the `Encode::encode()` implementation.
pub struct Context<'a, E>(&'a mut Encoder<E>);

impl<'i, 'a, E: Encode<'i>> Context<'a, E> {
  /// Returns the buffer to which text should be written to.
  pub fn buf(&mut self) -> &mut String {
    &mut self.0.buf
  }

  /// Returns the current path down the Alkyne tree.
  pub fn path(&self) -> &[PathComponent] {
    &self.0.path[..]
  }

  /// Recurse the encoding process, encoding `val` at the given `key`.
  ///
  /// This function should be called instead of doing manual recursion in
  /// `Encode::encode`, since it will automatically handle cycles and
  /// `std.EncodeAs` functions.
  pub fn recurse(
    &mut self,
    key: PathComponent,
    val: &Value<'i>,
  ) -> Result<(), EncodeError<'i>> {
    self.0.with_path(key, |this| this.subencode(val))
  }
}

impl<E> Deref for Context<'_, E> {
  type Target = E;

  fn deref(&self) -> &E {
    &self.0.encode
  }
}

impl<E> DerefMut for Context<'_, E> {
  fn deref_mut(&mut self) -> &mut E {
    &mut self.0.encode
  }
}

/// A `PathComponent` is used to track the path down a Alkyne value, consisting
/// of the keys and indices of objects and lists.
#[derive(Clone, Debug)]
pub enum PathComponent {
  Index(usize),
  Ident(String),
}

impl<'i, E: Encode<'i> + Default> Encoder<E> {
  /// Creates a new `Encoder`, with the given encoding.
  pub fn new() -> Self {
    Self::with(E::default())
  }
}

impl<'i, E: Encode<'i>> Encoder<E> {
  /// Creates a new `Encoder` with the given encoding value.
  pub fn with(encode: E) -> Self {
    Encoder {
      buf: String::new(),
      cycle_detector: HashSet::new(),
      path: Vec::new(),
      encode,
    }
  }

  /// Encode the given value, consuming this encoder.
  pub fn encode(mut self, val: &Value<'i>) -> Result<String, EncodeError<'i>> {
    self.subencode(val)?;
    Ok(self.buf)
  }

  /// Call `f`, but with `ptr` marked as "visited". This function is used
  /// for cycle detection.
  #[inline]
  fn with_indirection(
    &mut self,
    ptr: usize,
    f: impl FnOnce(&mut Self) -> Result<(), EncodeError<'i>>,
  ) -> Result<(), EncodeError<'i>> {
    if self.cycle_detector.contains(&ptr) {
      return Err(EncodeError::Cycle {
        path: self.path.clone(),
      });
    }
    self.cycle_detector.insert(ptr);
    let res = f(self);
    self.cycle_detector.remove(&ptr);
    res
  }

  /// Call `f`, but with `path` pushed onto the path stack.
  #[inline]
  fn with_path(
    &mut self,
    path: PathComponent,
    f: impl FnOnce(&mut Self) -> Result<(), EncodeError<'i>>,
  ) -> Result<(), EncodeError<'i>> {
    self.path.push(path);
    let res = f(self);
    self.path.pop();
    res
  }

  /// Encode `v` by performing cycle detection and then calling into
  /// `Encode::encode()`.
  fn subencode(&mut self, v: &Value<'i>) -> Result<(), EncodeError<'i>> {
    match v {
      Value::Object(val) => {
        let ptr = val.ptr_value();
        self.with_indirection(ptr, |this| {
          if let Some(mut encode_as) = val.lookup(ENCODE_AS) {
            if let Value::Fn(fnc) = &mut encode_as {
              fnc.bind(val.clone());
              fnc.rename(ENCODE_AS.into());
            }
            let mut ctx = UclContext::new();
            return match ctx.call(
              Span::synthetic("encode.alkyne".as_ref()),
              encode_as,
              Vec::new(),
            ) {
              Ok(obj) => this.subencode(&obj),
              Err(ControlFlow::Error(e)) => Err(EncodeError::EvalError {
                eval_error: e,
                path: this.path.clone(),
              }),
              _ => unreachable!(),
            };
          }
          Encode::encode(Context(this), v)
        })
      }
      v => Encode::encode(Context(self), v),
    }
  }
}

/// An `EncodeError` is an error produced during encoding.
#[derive(Clone, Debug)]
pub enum EncodeError<'i> {
  /// Represents a cycle; obviously, cycles cannot be cleanly encoded without
  /// using infinite space.
  Cycle { path: Vec<PathComponent> },
  /// Represents encountering a type which the given encoding does not support.
  BadType {
    bad_type: Type,
    path: Vec<PathComponent>,
  },
  /// Represents an evaluation error that happened during encoding.
  EvalError {
    eval_error: EvalError<'i>,
    path: Vec<PathComponent>,
  },
}

impl fmt::Display for EncodeError<'_> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    fn write_path(
      path: &[PathComponent],
      f: &mut fmt::Formatter,
    ) -> fmt::Result {
      if path.is_empty() {
        return write!(f, ".");
      }

      for p in path {
        match p {
          PathComponent::Index(n) => write!(f, "[{}]", n)?,
          PathComponent::Ident(i) => {
            let mut buf = String::new();
            escaping::escape_alkyne_string(i, true, &mut buf);
            write!(f, ".{}", buf)?
          }
        }
      }

      Ok(())
    }

    match self {
      EncodeError::Cycle { path } => {
        write!(f, "error: cycle detected at ")?;
        write_path(path, f)
      }
      EncodeError::BadType { bad_type, path } => {
        write!(f, "error: unsupported type {} at ", bad_type)?;
        write_path(path, f)
      }
      EncodeError::EvalError { eval_error, path } => {
        write!(f, "error: std.EncodeAs evaluation error at ")?;
        write_path(path, f)?;
        write!(f, "\n{}", eval_error)
      }
    }
  }
}
