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

//! Native code implementations of the Alkyne standard library.

use std::cmp::Ordering;

use crate::eval::value::Object;
use crate::eval::value::Type;
use crate::eval::value::Value;
use crate::syn::Spanned;

pub const ENCODE_AS: &str = "__encode_as";

/// Macro for generating the giant stdlib switch-case below.
macro_rules! stdlib {
  ($key:expr => $(
    fn $fn_name:ident ($($args:tt)*) $body:block
    $(let $let_name:ident = $expr:expr;)*
  )*) => {
    match $key {$(
      stringify!($fn_name) => stdlib!(@fn $fn_name ($($args)*) $body),
      $(stringify!($let_name) => stdlib!(@let $let_name = $expr;),)*
    )* _ => None, }
  };

  (@fn $ident:ident($($args:tt)*) $body:block) => {{
      let mut fnc = native_fn!(($($args)*) $body);
      fnc.rename($crate::eval::value::Str::new_static(stringify!($ident)));
      Some(fnc.into())
  }};

  (@let $ident:ident = $expr:expr;) => {Some($expr.into())};
}

/// Looks up `key` in the Alkyne standard library.
///
/// Returns `None` if `key` is undefined.
pub fn lookup_std<'i>(key: &str) -> Option<Value<'i>> {
  stdlib! { key =>
    // -- General reflection utilities. --

    // Returns the name of the file currently being executed. Note
    // that this information is derived from the stack, so functions will only
    // ever see the name of the file they were defined in.
    fn file_name(ctx) {
      let prev_frame = &ctx.call_stack[ctx.call_stack.len() - 2];
      match &prev_frame.fnc {
        Value::Fn(fnc) => fnc.src().span().file_name().to_str().unwrap_or("<unknown>"),
        _ => "<unknown>",
      }
    }

    // EncodeAs represents an implementation-defined object key. If this key is
    // set on an object, at encoding time, instead of encoding the object
    // directly, this key will be looked up, called with no arguments, and the
    // return value will be encoded, instead.
    let EncodeAs = ENCODE_AS;

    // Returns an implementation-defined string representing the type of `x`.
    fn type_of(x: any) { x.ty().name() }

    // Returns whether `x` has a JSON encoding value, i.e., any
    // of null, bool, number, string, list, or object.
    fn is_json(x: any) {
      matches!(x.ty(),
        Type::Null | Type::Bool | Type::Number |
        Type::String | Type::List | Type::Object)
    }

    // Returns whether `x` is of type null.
    fn is_null(x: any) { x.ty() == Type::Null }

    // Returns whether `x` is of type bool.
    fn is_bool(x: any) { x.ty() == Type::Bool }

    // Returns whether `x` is of type number.
    fn is_number(x: any) { x.ty() == Type::Number }

    // Returns whether `x` is of type string.
    fn is_string(x: any) { x.ty() == Type::String }

    // Returns whether `x` is of type list.
    fn is_list(x: any) { x.ty() == Type::List }

    // Returns whether `x` is of type object.
    fn is_object(x: any) { x.ty() == Type::Object }

    // Returns whether `x` is of type function.
    fn is_fn(x: any) { x.ty() == Type::Fn }

    // Returns whether `x` has a non-opaque type
    fn has_type(x: any) { x.ty() != Type::Opaque }

    // Compares `a` and `b` for "pointer equality". What this means is
    // implementation-defined, but if `same(a, b)` holds, then so must
    // `a == b` if they are primitives. Furthermore, for JSON-like types,
    // `same(x, x)` always holds.
    fn same(a: any, b: any) {
      match (a, b) {
        (Value::Null, Value::Null) => true,
        (Value::Bool(a), Value::Bool(b)) => a == b,
        #[allow(clippy::float_cmp)]
        (Value::Number(a), Value::Number(b)) => a == b,
        (Value::String(a), Value::String(b)) => a.ptr_eq(&b),
        (Value::List(a), Value::List(b)) => a.ptr_eq(&b),
        (Value::Object(a), Value::Object(b)) => a.ptr_value() == b.ptr_value(),
        _ => false,
      }
    }

    // Binds `zelf` as the referent of `fnc`, so that it is the object
    // produced by `self` when `fnc` is called. Returns the re-bound `fnc`.
    fn bind(ctx, fnc: any, zelf: object) {
      match fnc {
        Value::Fn(mut fnc) => {
          fnc.bind(zelf);
          Value::Fn(fnc)
        }
        f @ Value::NativeFn(..) => f,
        t => native_err!(ctx, "expected function, got {}", t),
      }
    }

    // Constants for the various type names.
    let Null = Type::Null.name();
    let Bool = Type::Bool.name();
    let Number = Type::Number.name();
    let String = Type::String.name();
    let List = Type::List.name();
    let Object = Type::Object.name();
    let Function = Type::Fn.name();

    // -- General functions. --
    // Triggers an error when `cond` is not satisfied, printing
    // `msg`. Otherwise, it returns `null`.
    fn assert(ctx, cond: bool, msg: string) {
      if !cond {
        native_err!(ctx, "assertion failed: {}", msg)
      }
    }

    // Just like `assert`, but does not display an error message.
    fn check(ctx, cond: bool) {
      if !cond {
        native_err!(ctx, "assertion failed")
      }
    }

    // Unconditionally returns an error with message `msg`.
    fn error(ctx, msg: string) { native_err!(ctx, "{}", msg) }

    // Returns true if `c[idx]` would succeed, i.e., if `c?[idx]` is nonnull.
    fn has(ctx, container: any, index: any) {
      ctx.index(native_span!(), container, vec![index]).is_ok()
    }

    // Returns a range with step one, form `start` to `end`, exclusive.
    // The arguments to this function *must* be integers.
    fn range(start: integer, end: integer) {
      Value::Range { start, end, step: 1 }
    }

    // Returns a range with step one, form `start` to `end`,
    // exclusive, with step `step`. The arguments to this function *must* be
    // integers; `step` must also be positive.
    fn range_step(ctx, start: integer, end: integer, step: integer) {
      if step <= 0 {
        native_err!(ctx, "expected positive step; got {}", step)
      }

      Value::Range { start, end, step }
    }

    // Returns the first index at which `needle` appears in `haystack`.
    // This function will execute a comparision against each element of
    // `haystack`; comparing incomparable values will error. If the element is
    // not found, returns null.
    fn index_of(ctx, haystack: list, needle: any) {
      for (i, val) in haystack.iter().enumerate() {
        if ctx.compare_eq(native_span!(), val.clone(), needle.clone())? {
          return Ok(Value::Number(i as f64))
        }
      }
      Value::Null
    }

    // Returns the number of elements in the list `xs` or the number of
    // bytes in the string `xs`, and returns an error in all other cases.
    fn len(ctx, x: any) {
      let len = match x {
        Value::String(s) => s.len(),
        Value::List(xs) => xs.len(),
        v => native_err!(ctx, "cannot take length of value of type {}", v.ty()),
      };
      len as f64
    }

    // Takes a list of lists, and flattens it into a single list.
    fn flatten(ctx, xss: list) {
      let mut buf = Vec::new();
      for v in xss.iter() {
        match v {
          Value::List(xs) => buf.extend_from_slice(&*xs),
          v => native_err!(ctx, "expected list of lists, got {}", v.ty()),
        }
      }
      buf
    }

    // Concatenates a list of strings into one string.
    fn concat(ctx, strs: list) {
      let mut buf = String::new();
      for v in strs.iter() {
        match v {
          Value::String(s) => buf.push_str(&*s),
          v => native_err!(ctx, "expected list of strings, got {}", v.ty()),
        }
      }
      buf
    }

    // Takes a format string, and a list of arguments, and printf-formats them.
    // Supported verbs are:
    // - %%: a literal % character.
    // - %s: a string, as-is.
    // - %q: a string, but quoted and escaped.
    // - %d: an integer.
    // - %f: a number.
    //
    // All other cases will scribble some error message on the resulting
    // string, but this function itself will always succeed.
    fn fmt(fmt_str: string, args: list) {
      use std::fmt::Write;
      let mut buf = String::with_capacity(fmt_str.len());

      let mut arg_idx = 0;
      let mut chars = fmt_str.chars().peekable();
      while let Some(c) = chars.next() {
        match (c, chars.peek(), args.get(arg_idx)) {
          ('%', Some('%'), _) => buf.push('%'),

          ('%', Some('s'), Some(Value::String(val))) => {
            arg_idx += 1;
            let _ = write!(buf, "{}", val.as_sliced());
          }

          ('%', Some('q'), Some(Value::String(val))) => {
            arg_idx += 1;
            let _ = write!(buf, "{}", val);
          }

          ('%', Some('d'), Some(val)) if val.as_int().is_ok() => {
            arg_idx += 1;
            let _ = write!(buf, "{}", val.as_int().unwrap());
          }

          ('%', Some('f'), Some(Value::Number(val))) => {
            arg_idx += 1;
            let _ = write!(buf, "{}", val);
          }

          ('%', Some(c), Some(v)) => {
            arg_idx += 1;
            let _ = write!(buf, "%{}<INVALID={}>", c, v.ty());
          }

          ('%', Some(c), None) => {
            arg_idx += 1;
            let _ = write!(buf, "%{}<MISSING>", c,);
          }

          ('%', None, _) => {
            let _ = write!(buf, "%<INVALID=EOF>");
          }

          (c, _, _) => buf.push(c),
        }

        if c == '%' {
          let _ = chars.next();
        }
      }
      if arg_idx < args.len() {
        let _ = write!(buf, "%<EXTRA={}>", args.len() - arg_idx);
      }
      buf
    }

    // Merges the objects `a` and `b`, resulting in a super-less object with all
    // of the transitive fields of `a` and `b`.
    fn merge(a: object, b: object) {
      let new_obj = Object::new();

      for (k, v, _) in a.iter() {
        new_obj.define(k.clone(), v.clone(), true);
      }

      for (k, v, _) in b.iter() {
        new_obj.define(k.clone(), v.clone(), true);
      }

      new_obj.freeze();
      new_obj
    }

    // -- Math stuff. --
    // All mathematical functions return an indeterminate value when called
    // with values outside of their domain.

    // Computes the minimum of `a` and `b`, if they are comparable.
    fn min(ctx, a: any, b: any) {
      match ctx.compare_ord(native_span!(), a.clone(), b.clone())? {
        Some(Ordering::Greater) => b,
        _ => a,
      }
    }

    // Computes the maximum of `a` and `b`, if they are comparable.
    fn max(ctx, a: any, b: any) {
      match ctx.compare_ord(native_span!(), a.clone(), b.clone())? {
        Some(Ordering::Less) => b,
        _ => a,
      }
    }

    // Archimedes' constant to some precision.
    let Pi = std::f64::consts::PI;
    // Euler's constant to some precision.
    let Euler = std::f64::consts::E;

    // Computes the absolute value of `x`.
    fn abs(x: number) { x.abs() }

    // Computes the square root of `x`.
    fn sqrt(x: number) { x.sqrt() }

    // Computes the exponential of `x`.
    fn exp(x: number) { x.exp() }
    // Computes the natural logarithm of `x`.
    fn ln(x: number) { x.ln() }

    // Computes `x` raised to the `e`th power.
    fn pow(x: number, e: number) { x.powf(e) }
    // Computes the logarithm of `x` at base `b`.
    fn log(x: number, b: number) { x.log(b) }

    // Converts the angle `t` to degrees (as if it were in radians).
    fn deg(x: number) { x.to_degrees() }
    // Converts the angle `t` to radians (as if it were in degrees).
    fn rad(x: number) { x.to_radians() }

    // Computes the sine of `x`.
    fn sin(x: number) { x.sin() }
    // Computes the cosine of `x`.
    fn cos(x: number) { x.cos() }
    // Computes the tangent of `x`.
    fn tan(x: number) { x.tan() }

    // Computes the cosecant of `x`.
    fn csc(x: number) { x.sin().recip() }
    // Computes the secant of `x`.
    fn sec(x: number) { x.cos().recip() }
    // Computes the cotangent of `x`.
    fn cot(x: number) { x.tan().recip() }

    // Computes the arcsine of `x`.
    fn asin(x: number) { x.asin() }
    // Computes the arccosine of `x`.
    fn acos(x: number) { x.acos() }
    // Computes the arctangent of `x`.
    fn atan(x: number) { x.atan() }

    // Computes the arccosecant of `x`.
    fn acsc(x: number) { x.recip().asin() }
    // Computes the arcsecant of `x`.
    fn asec(x: number) { x.recip().acos() }
    // Computes the arccotangent of `x`.
    fn acot(x: number) { x.recip().atan() }

    // Computes the hyperbolic sine of `x`.
    fn sinh(x: number) { x.sinh() }
    // Computes the hyperbolic cosine of `x`.
    fn cosh(x: number) { x.cosh() }
    // Computes the hyperbolic tangent of `x`.
    fn tanh(x: number) { x.tanh() }

    // Computes the hyperbolic cosecant of `x`.
    fn csch(x: number) { x.sinh().recip() }
    // Computes the hyperbolic secant of `x`.
    fn sech(x: number) { x.cosh().recip() }
    // Computes the hyperbolic cotangent of `x`.
    fn coth(x: number) { x.tanh().recip() }

    // Computes the hyperbolic arcsine of `x`.
    fn asinh(x: number) { x.asinh() }
    // Computes the hyperbolic arccosine of `x`.
    fn acosh(x: number) { x.acosh() }
    // Computes the hyperbolic arctangent of `x`.
    fn atanh(x: number) { x.atanh() }

    // Computes the hyperbolic arccosecant of `x`.
    fn acsch(x: number) { x.recip().asinh() }
    // Computes the hyperbolic arcsecant of `x`.
    fn asech(x: number) { x.recip().acosh() }
    // Computes the hyperbolic arccotangent of `x`.
    fn acoth(x: number) { x.recip().atanh() }
  }
}
