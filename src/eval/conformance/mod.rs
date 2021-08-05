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

//! Conformance tests for the interpreter.
//!
//! A conformance test consists of a Alkyne file; for each conformance conformance, the
//! file is parsed, loaded into the interpreter, and executed.
//!
//! Tests should import the magic "test lib" file to get access to assertions.
//! This can be done with
//! ```
//! use t = "test_lib.ak";
//! ```

use std::cell::Cell;

use crate::eval;
use crate::eval::value::Object;
use crate::eval::value::Value;
use crate::syn;

const TEST_LIB: &str = "test_lib.ak";

/// Macro for generating conformance tests.
macro_rules! conf_test {
  ($test_name:ident) => {
    #[test]
    fn $test_name() {
      conformance_test(
        concat!(stringify!($test_name), ".ak"),
        include_str!(concat!(stringify!($test_name), ".ak")),
      )
    }
  };
}

thread_local! {
  static FAILURE_FLAG: Cell<bool> = Cell::new(false);
}

fn test_lib<'a>() -> Value<'a> {
  let test_lib = Object::new();

  test_lib.define(
    "fail",
    native_fn!((ctx) {
      FAILURE_FLAG.with(|f| f.set(true));
      native_err_no_return!(ctx, "unconditional failure")
    }),
    false,
  );

  test_lib.define(
    "expect",
    native_fn!((ctx, cond: bool) {
      if !cond {
        FAILURE_FLAG.with(|f| f.set(true));
        native_err_no_return!(ctx, "assertion failed")
      }
    }),
    false,
  );

  test_lib.define(
    "assert",
    native_fn!((ctx, cond: bool) {
      if !cond {
        native_err!(ctx, "assertion failed")
      }
    }),
    false,
  );

  test_lib.define(
    "expect_death",
    native_fn!((ctx, body: fn) {
      if ctx.call(native_span!(), body, vec![]).is_ok() {
        FAILURE_FLAG.with(|f| f.set(true));
        native_err_no_return!(ctx, "body failed to die")
      }
    }),
    false,
  );

  Value::Object(test_lib)
}

/// Basic fixture for all conformance conformance.
fn conformance_test(name: &'static str, text: &'static str) {
  FAILURE_FLAG.with(|f| f.set(false));

  let arena = syn::Arena::new();
  let ast = match syn::parse(name.as_ref(), text, &arena) {
    Ok(ast) => ast,
    Err(e) => {
      eprintln!("{}", e);
      panic!("failed to parse testcase")
    }
  };

  let mut ctx = eval::Context::new();
  let result = ctx.eval(&ast, |file| match file {
    TEST_LIB => Some(test_lib()),
    _ => None,
  });

  if let Err(e) = result {
    eprintln!("{}", e);
    FAILURE_FLAG.with(|f| f.set(true));
  }

  if FAILURE_FLAG.with(|f| f.get()) {
    panic!("unexpected failure")
  }
}

conf_test!(must_pass);

conf_test!(variables);
conf_test!(fns);
conf_test!(blocks);
conf_test!(conditionals);
conf_test!(loops);

conf_test!(nulls);
conf_test!(bools);
conf_test!(numbers);
conf_test!(strings);
conf_test!(lists);
conf_test!(objects);
