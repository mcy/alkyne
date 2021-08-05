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

//! Macros for creating native functions.

/// Generates a span pointing at the current Rust source location, for use in
/// errors originating from native code.
#[macro_export]
macro_rules! native_span {
  () => {
    $crate::syn::Span::synthetic(file!().as_ref())
  };
}

/// Generates a specialized native error, and returns immediately.
///
/// Compare `alkyne::eval::value::error!()`.
#[macro_export]
macro_rules! native_err {
  ($ctx:expr, $($tt:tt)*) => {{
    error!($ctx, native_span!(), $($tt)*)
  }}
}

/// Generates a specialized native error, but emits it to stderr rather than
/// returning immediately.
#[macro_export]
macro_rules! native_err_no_return {
  ($ctx:expr, $($tt:tt)*) => {{
    eprintln!("{}", $crate::eval::error::EvalError::new(
      $ctx, native_span!(), format!($($tt)*)));
  }}
}

/// Asserts that a Alkyne value is of a particular type:
/// ```
/// let my_obj = assert_alkyne_type!(ctx, val: obj);
/// ```
/// Note that `val` must be an identifier.
///
/// Supported types are: `any`, `null`, `bool`, `number`, `integer`, `string`,
/// `list`, `object`, and `fn`. Of these, `any` simply always succeeds,
/// `integer` tests for a number with zero functional part, and `fn` matches
/// both Alkyne and native functions (and as such returns a `Value`).
#[macro_export]
macro_rules! assert_alkyne_type {
  ($ctx:ident, $arg:ident: any) => {$arg};
  ($ctx:ident, $arg:ident: null) => {
    assert_alkyne_type!(@match $ctx, $arg, Null, null)
  };
  ($ctx:ident, $arg:ident: bool) => {
    assert_alkyne_type!(@match $ctx, $arg, Bool, bool)
  };
  ($ctx:ident, $arg:ident: number) => {
    assert_alkyne_type!(@match $ctx, $arg, Number, number)
  };
  ($ctx:ident, $arg:ident: integer) => {
    match $arg.as_int() {
      Ok(x) => x,
      Err(t) => native_err!($ctx, "expected integer, got {}", t),
    }
  };
  ($ctx:ident, $arg:ident: string) => {
    assert_alkyne_type!(@match $ctx, $arg, String, string)
  };
  ($ctx:ident, $arg:ident: list) => {
    assert_alkyne_type!(@match $ctx, $arg, List, list)
  };
  ($ctx:ident, $arg:ident: object) => {
    assert_alkyne_type!(@match $ctx, $arg, Object, object)
  };

  ($ctx:ident, $arg:ident: fn) => {
    match $arg {
      f @ $crate::eval::value::Value::Fn(_) => f,
      f @ $crate::eval::value::Value::NativeFn(_) => f,
      v => native_err!($ctx, "expected fn, got {}", v.ty()),
    }
  };

  (@match $ctx:ident, $arg:ident, $variant:ident, $expected:ident) => {
    match $arg {
      $crate::eval::value::Value::$variant(x) => x,
      v => native_err!($ctx, "expected {}, got {}",
                       stringify!($expected), v.ty()),
    }
  }
}

/// Generates a native Alkyne function, saving users significant boilerplate.
///
/// Syntax is as follows:
/// ```
/// native_fn!((ctx, arg1: number, arg2: string) {
///   // `ctx` is the current Alkyne interpreter context, and is optional.
///   // `arg1` and `arg2` are of types `f64` and `Str`, respectively.
///   // ...
/// })
/// ```
///
/// The generated function automatically performs type-assertions on arguments,
/// and checks that the argument list is of the right size. The body may have
/// any type which can be converted to a `Value` (by `IntoValueResult`), or it
/// can explictly `return` a `Result`.
#[macro_export]
macro_rules! native_fn {
  (($($arg:ident: $ty:ident),* $(,)?) $block:block) => {
    native_fn!((_, $($arg: $ty,)*) $block)
  };
  (($ctx:tt $(, $arg:ident: $ty:ident)* $(,)?) $block:block) => {{
    #[allow(unreachable_code)]
    let f = $crate::eval::value::NativeFn::new(|ctx, args| {
      const __ARG_COUNT: usize = native_fn!(@arg_count $($arg)*);
      if args.len() != __ARG_COUNT {
        native_err!(ctx, "expected {} arguments, got {}",
                    __ARG_COUNT, args.len())
      }

      let count = 0;
      let _ = count;
      native_fn!(@arg_bind count, ctx, args, $($arg $ty)*);

      let $ctx = ctx;
      $crate::eval::value::convert::IntoValueResult::into_value_result($block)
    }, (file!(), line!(), column!()));
    f
  }};

  (@arg_bind $count:ident, $ctx:ident, $args:ident,) => {};
  (@arg_bind $count:ident, $ctx:ident, $args:ident,
    $arg:ident $ty:ident $($rest:tt)*) => {
    let $arg = {
      let arg = $args[$count].clone();
      assert_alkyne_type!($ctx, arg: $ty)
    };
    let $count = $count + 1;
    let _ = $count;
    native_fn!(@arg_bind $count, $ctx, $args, $($rest)*)
  };

  (@arg_count) => {0};
  (@arg_count $_:ident $($rest:ident)*) => {
    1 + native_fn!(@arg_count $($rest)*)
  };
}
