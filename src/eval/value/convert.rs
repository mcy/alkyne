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

//! Traits for converting Rust types into Alkyne values.

use crate::eval::value::Fn;
use crate::eval::value::List;
use crate::eval::value::NativeFn;
use crate::eval::value::Object;
use crate::eval::value::Str;
use crate::eval::value::Value;
use crate::eval::Result;

/// Represents a type that can be converted into a `Value`.
///
/// This trait mostly exists to be different from `Into` to avoid coherence
/// issues, and `Into::into()` should generally be preferred instead.
pub trait IntoValue<'i> {
  fn into_value(self) -> Value<'i>;
}

impl<'i, T: IntoValue<'i>> From<T> for Value<'i> {
  #[inline]
  fn from(x: T) -> Self {
    x.into_value()
  }
}

impl<'i> IntoValue<'i> for () {
  fn into_value(self) -> Value<'i> {
    Value::Null
  }
}

impl<'i> IntoValue<'i> for bool {
  fn into_value(self) -> Value<'i> {
    Value::Bool(self)
  }
}

impl<'i> IntoValue<'i> for f64 {
  fn into_value(self) -> Value<'i> {
    Value::Number(self)
  }
}

impl<'i> IntoValue<'i> for String {
  fn into_value(self) -> Value<'i> {
    Value::String(self.into())
  }
}

impl<'i> IntoValue<'i> for &'i str {
  fn into_value(self) -> Value<'i> {
    Value::String(Str::new_static(self))
  }
}

impl<'i> IntoValue<'i> for Str<'i> {
  fn into_value(self) -> Value<'i> {
    Value::String(self)
  }
}

impl<'i> IntoValue<'i> for Vec<Value<'i>> {
  fn into_value(self) -> Value<'i> {
    Value::List(self.into())
  }
}

impl<'i> IntoValue<'i> for &'i [Value<'i>] {
  fn into_value(self) -> Value<'i> {
    Value::List(List::new_static(self))
  }
}

impl<'i> IntoValue<'i> for List<'i> {
  fn into_value(self) -> Value<'i> {
    Value::List(self)
  }
}

impl<'i> IntoValue<'i> for Object<'i> {
  fn into_value(self) -> Value<'i> {
    Value::Object(self)
  }
}

impl<'i> IntoValue<'i> for Fn<'i> {
  fn into_value(self) -> Value<'i> {
    Value::Fn(self)
  }
}

impl<'i> IntoValue<'i> for NativeFn<'i> {
  fn into_value(self) -> Value<'i> {
    Value::NativeFn(self)
  }
}

/// Represents a type that can be converted into a `Result<Value>`.
///
/// This trait mostly exists to be different from `Into` to avoid coherence
/// issues. It is exclusively used by `native_fn!()`.
#[doc(hidden)]
pub trait IntoValueResult<'i> {
  fn into_value_result(self) -> Result<'i, Value<'i>>;
}

impl<'i, I> IntoValueResult<'i> for I
where
  I: IntoValue<'i>,
{
  fn into_value_result(self) -> Result<'i, Value<'i>> {
    Ok(self.into_value())
  }
}

impl<'i> IntoValueResult<'i> for Value<'i> {
  fn into_value_result(self) -> Result<'i, Value<'i>> {
    Ok(self)
  }
}

impl<'i> IntoValueResult<'i> for Result<'i, Value<'i>> {
  fn into_value_result(self) -> Result<'i, Value<'i>> {
    self
  }
}
