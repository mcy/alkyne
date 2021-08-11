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

//! Error generation for Alkyne evalution.

#![allow(dead_code)]

use std::fmt;

use crate::eval::value::Value;
use crate::eval::Context;
use crate::syn::Span;

/// An `EvalError` is any error raised during evaluation; it records an error
/// message and a stack trace.
#[derive(Clone, Debug)]
pub struct EvalError<'i> {
  pub message: String,
  pub trace: Vec<Frame<'i>>,
}

impl<'i> EvalError<'i> {
  /// Creates a new `EvalError`, recording an error at the given span with the
  /// given message.
  pub fn new(ctx: &Context<'i>, span: Span<'i>, message: String) -> Self {
    let height = ctx.call_stack.len();
    let mut trace = Vec::with_capacity(height);

    // Each stack frame (except the first) contains (fnc, caller_span).
    // We want to get (fnc, callee_span).
    for i in (0..ctx.call_stack.len()).rev() {
      let fn_name = if i == 0 {
        "<start> (<start>)".to_string()
      } else {
        match &ctx.call_stack[i].fnc {
          Value::Fn(f) => format!("{}", f),
          Value::NativeFn(f) => format!("{}", f),
          _ => "<unknown> (??)".to_string(),
        }
      };

      let error_span = if i == height - 1 {
        span
      } else {
        ctx.call_stack[i + 1].call_site
      };

      trace.push(Frame {
        fn_name,
        error_span,
      })
    }

    EvalError { message, trace }
  }

  pub fn symbolize(&self, w: &mut impl fmt::Write) -> fmt::Result {
    writeln!(w, "error: {}", self.message)?;
    // Find the first "ok" frame.
    if self
      .trace
      .iter()
      .map(|f| f.error_span)
      .any(|s| !s.is_synthetic())
    {
      //span.pretty(w)?;
    }
    writeln!(w, "stack dump:")?;

    for frame in &self.trace {
      write!(w, "* {} at ", frame.fn_name)?;
      if frame.error_span.is_synthetic() {
        writeln!(w, "({})", frame.error_span.file_name().display())?;
      } else {
        let (line, col) = frame.error_span.start_position().unwrap();
        writeln!(
          w,
          "({}:{}:{})",
          frame.error_span.file_name().display(),
          line,
          col
        )?;
      }
    }

    Ok(())
  }
}

impl fmt::Display for EvalError<'_> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    self.symbolize(f)
  }
}

/// A `Frame` is stack frame information relating to an evaluation error.
#[derive(Clone, Debug)]
pub struct Frame<'i> {
  fn_name: String,
  error_span: Span<'i>,
}

/// Generates, and returns, an `EvalError` given a `Context`, a `Spanned`, and
/// a formatted message.
macro_rules! error {
  ($ctx:expr, $expr:expr, $($tt:tt)*) => {{
    #[allow(unused_imports)]
    use $crate::syn::Spanned;
    #[allow(unused_imports)]
    use $crate::eval::error::*;
    return Err(EvalError::new($ctx, $expr.span(), format!($($tt)*)).into())
  }}
}

macro_rules! bug {
  ($($tt:tt)*) => {{
    eprintln!("error: internal interpreter error; this is a bug\nerror: ");
    eprintln!($($tt)*);
    panic!()
  }}
}
