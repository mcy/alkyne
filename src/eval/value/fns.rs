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

//! Alkyne Functions

use std::fmt::Debug;
use std::fmt::Display;

use crate::eval::escaping;
use crate::eval::value::Object;
use crate::eval::value::Str;
use crate::eval::value::Value;
use crate::eval::Context;
use crate::eval::Result;
use crate::syn;
use crate::syn::Spanned;

/// A `Fn` is a Alkyne function. It is implemented as a capture of the scope it
/// was defined in, and a copy of its AST for later evaluation.
#[derive(Clone, Debug)]
pub struct Fn<'i> {
  src: &'i syn::Fn<'i>,
  name: Option<Str<'i>>,
  captures: Object<'i>,
  referent: Option<Object<'i>>,
}

impl<'i> Fn<'i> {
  /// Creates a new `Fn` with the given source code and captured scope.
  pub fn new(src: &'i syn::Fn<'i>, captures: Object<'i>) -> Self {
    Fn {
      src,
      name: None,
      referent: None,
      captures,
    }
  }

  /// Returns the source code for this function.
  pub fn src(&self) -> &'i syn::Fn<'i> {
    self.src
  }

  /// Returns this function's name.
  pub fn name(&self) -> Option<Str<'i>> {
    self.name.clone()
  }

  /// Returns this function's captured scope.
  pub fn captures(&self) -> Object<'i> {
    self.captures.clone()
  }

  /// Renames this function to the given name.
  pub fn rename(&mut self, name: Str<'i>) {
    self.name = Some(name);
  }

  /// Returns this function's referent, i.e., the value of `self` during the
  /// function call.
  pub fn referent(&self) -> Option<Object<'i>> {
    self.referent.clone()
  }

  /// Binds the given object to this function, giving it a referent.
  pub fn bind(&mut self, referent: Object<'i>) {
    self.referent = Some(referent);
  }
}

impl Display for Fn<'_> {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    if let Some(name) = &self.name {
      let mut buf = String::new();
      escaping::escape_alkyne_string(name, true, &mut buf);
      write!(f, "{}() ", buf)?;
    } else {
      write!(f, "<fn> ")?;
    }

    let span = self.src.span();
    if !span.is_synthetic() {
      let (line, col) = span.start_position().unwrap();
      write!(f, "({}:{}:{})", span.file_name().display(), line, col)
    } else {
      write!(f, "({})", span.file_name().display())
    }
  }
}

type NativeFnHandle =
  for<'i> fn(&mut Context<'i>, Vec<Value<'i>>) -> Result<'i, Value<'i>>;

/// A `NativeFn` is a Alkyne function implemented as a native Rust function.
#[derive(Clone)]
pub struct NativeFn<'i> {
  name: Option<Str<'i>>,
  fnc: NativeFnHandle,
  location: (&'static str, u32, u32),
}

impl<'i> NativeFn<'i> {
  /// Creates a new `NativeFn`.
  ///
  /// The preferred method to bind native functions is the `native_fn!()` macro.
  pub fn new(fnc: NativeFnHandle, location: (&'static str, u32, u32)) -> Self {
    Self {
      name: None,
      fnc,
      location,
    }
  }

  /// Returns this function's name.
  pub fn name(&self) -> Option<Str<'i>> {
    self.name.clone()
  }

  /// Renames this function to the given name.
  pub fn rename(&mut self, name: Str<'i>) {
    self.name = Some(name);
  }

  /// Calls this function's handle.
  ///
  /// Note that this function does not do anything to the stack in `ctx`;
  /// setting up a sane stack is the caller's responsibility.
  pub fn call(
    &self,
    ctx: &mut Context<'i>,
    args: Vec<Value<'i>>,
  ) -> Result<'i, Value<'i>> {
    (self.fnc)(ctx, args)
  }

  /// Returns a unique value identifying the contained function pointer, which
  /// is used for recursion detection.
  pub fn ptr_value(&self) -> usize {
    self.fnc as usize
  }
}

impl<'i> Debug for NativeFn<'i> {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    f.debug_struct("NativeFn")
      .field("name", &self.name)
      .field("location", &self.location)
      .finish()
  }
}

impl<'i> Display for NativeFn<'i> {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    if let Some(name) = &self.name {
      let mut buf = String::new();
      escaping::escape_alkyne_string(name, true, &mut buf);
      write!(
        f,
        "{}() ({}:{}:{})",
        buf, self.location.0, self.location.1, self.location.2
      )
    } else {
      write!(
        f,
        "<native> ({}:{}:{})",
        self.location.0, self.location.1, self.location.2
      )
    }
  }
}
