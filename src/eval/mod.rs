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

//! Interpreter for the Alkyne language.

use std::cmp::Ordering;
use std::collections::HashMap;
use std::collections::HashSet;

use crate::eval::error::EvalError;
use crate::eval::value::Fn;
use crate::eval::value::List;
use crate::eval::value::Object;
use crate::eval::value::Str;
use crate::eval::value::Value;
use crate::syn;
use crate::syn::Span;
use crate::syn::Spanned as _;

#[macro_use]
pub mod error;

#[macro_use]
pub mod value;

pub mod encode;
pub mod stdlib;

pub(crate) mod escaping;

#[cfg(test)]
mod conformance;

/// A `Context` represents evaluation context for a particular Alkyne file.
pub struct Context<'i> {
  top_scope: Object<'i>,
  call_stack: Vec<StackFrame<'i>>,
  called_fns: HashSet<usize>,
}

impl<'i> Context<'i> {
  fn current_frame(&mut self) -> &mut StackFrame<'i> {
    self.call_stack.last_mut().unwrap()
  }

  fn scope(&self) -> Object<'i> {
    self.call_stack.last().unwrap().current_scope()
  }

  pub fn top_scope(&self) -> &Object<'i> {
    &self.top_scope
  }
}

/// A Alkyne stack frame.
///
/// A stack consists of the following per-function-call information:
/// - The source and value of the function being called.
/// - The location at which the function was called.
/// - The stack of potential `self` references, corresponding to each object
///   literal.
/// - The stack of potential `yield` targets, corresponding to each `for` loop.
/// - The stack of `do` expressions and their corresponding `it` values.
#[allow(unused)]
struct StackFrame<'i> {
  fnc: Value<'i>,
  call_site: Span<'i>,
  scope_stack: Vec<Object<'i>>,
  self_stack: Vec<Object<'i>>,
  yield_stack: Vec<YieldFrame<'i>>,
  do_stack: Vec<Value<'i>>,
}

impl<'i> StackFrame<'i> {
  /// Creates a new stack frame from the given starting values.
  pub fn new(
    fnc: Value<'i>,
    call_site: Span<'i>,
    starting_scope: Object<'i>,
  ) -> Self {
    StackFrame {
      fnc,
      call_site,
      scope_stack: vec![starting_scope],
      self_stack: Vec::new(),
      yield_stack: Vec::new(),
      do_stack: Vec::new(),
    }
  }

  /// Creates a new scope, extending the previous one.
  pub fn start_scope(&mut self) {
    let new = self.scope_stack.last().cloned().unwrap().extend();
    self.scope_stack.push(new);
  }

  /// Ends a scope created with `start_scope()`.
  ///
  /// Calling this function more times than `start_scope()` has been called will
  /// panic.
  pub fn end_scope(&mut self) {
    if self.scope_stack.len() <= 1 {
      bug!("scope_stack empty")
    }
    self.scope_stack.pop();
  }

  /// Returns a copy of the current scope.
  ///
  /// A scope is always guaranteed to be present.
  pub fn current_scope(&self) -> Object<'i> {
    self.scope_stack.last().unwrap().clone()
  }

  /// Adds a new `Object` to the self-stack, so that references to `self` can
  /// be resolved.
  pub fn start_object(&mut self, obj: Object<'i>) {
    self.self_stack.push(obj)
  }

  /// Ends an object literal started by `start_object()`.
  ///
  /// Calling this function more times than `start_object()` has been called
  /// will panic.
  pub fn end_object(&mut self) {
    if self.self_stack.is_empty() {
      bug!("self_stack empty")
    }
    self.self_stack.pop();
  }

  /// Returns a copy of the current value of `self`, if it exists.
  pub fn current_self(&self) -> Option<Object<'i>> {
    self.self_stack.last().cloned()
  }

  /// Begins a loop by adding a new `YieldFrame` to the yield stack.
  pub fn start_loop(&mut self) {
    self.yield_stack.push(YieldFrame::None)
  }

  /// Ends a loop started by `start_loop()`.
  ///
  /// Calling this function more times than `start_loop()` has been called
  /// will panic.
  pub fn end_loop(&mut self) -> YieldFrame<'i> {
    if self.yield_stack.is_empty() {
      bug!("yield_stack empty")
    }
    self.yield_stack.pop().unwrap()
  }

  /// Returns a reference to the current `YieldFrame`, if there is one.
  pub fn current_yield(&mut self) -> Option<&mut YieldFrame<'i>> {
    self.yield_stack.last_mut()
  }

  /// Begins a `do` expression by adding a new `it` value to the yield stack.
  pub fn start_do(&mut self, it: Value<'i>) {
    self.do_stack.push(it)
  }

  /// Ends a `do` expression started by `start_do()`.
  ///
  /// Calling this function more times than `start_do()` has been called
  /// will panic.
  pub fn end_do(&mut self) -> Value<'i> {
    if self.do_stack.is_empty() {
      bug!("do_stack empty")
    }
    self.do_stack.pop().unwrap()
  }

  /// Returns a reference to the current value of `it`, if there is one.
  pub fn current_it(&self) -> Option<Value<'i>> {
    self.do_stack.last().cloned()
  }
}

/// A "yield frame", used to match `yield` expressions to their corresponding
/// `for` loops.
///
/// Each `for` loop yields `null`, until a `yield` expression is encountered,
/// at which point the type of yield is determined by the `yield` expression:
/// a list yield, or a map yield.
enum YieldFrame<'i> {
  None,
  List(Vec<Value<'i>>),
  Object(HashMap<Str<'i>, Value<'i>>),
}

impl<'i> YieldFrame<'i> {
  /// Attempts to push `val` onto this frame.
  ///
  /// Returns false if the frame is incompatible with list-like yields.
  pub fn push_value(&mut self, val: Value<'i>) -> bool {
    match self {
      y @ YieldFrame::None => *y = YieldFrame::List(vec![val]),
      YieldFrame::List(xs) => xs.push(val),
      YieldFrame::Object(_) => return false,
    }
    true
  }

  /// Attempts to push the given key-value pair onto this frame.
  ///
  /// Returns false if the frame is incompatible with object-like yields.
  pub fn push_kv(&mut self, key: Str<'i>, val: Value<'i>) -> bool {
    match self {
      y @ YieldFrame::None => {
        let mut map = HashMap::new();
        map.insert(key, val);
        *y = YieldFrame::Object(map)
      }
      YieldFrame::List(_) => return false,
      YieldFrame::Object(map) => {
        map.insert(key, val);
      }
    }
    true
  }
}

/// A `ControlFlow` represents exceptional control flow in Alkyne evaluation:
/// either user-provided control flow, such as `return` or `break`, or an error.
pub enum ControlFlow<'i> {
  Ret(Value<'i>),
  Break(Option<Value<'i>>),
  Cont,
  Error(EvalError<'i>),
}

impl<'i> From<EvalError<'i>> for ControlFlow<'i> {
  fn from(e: EvalError<'i>) -> Self {
    ControlFlow::Error(e)
  }
}

/// The result type for all Alkyne computations.
///
/// Rather than returning a plain evaluation error, a Alkyne computation can
/// return:
/// - A value, represented by the `Ok` variant.
/// - Non-trivial control flow, like an early return or loop control,
///   represented by the `Err` variant.
/// - A real error, which is a variant of `ControlFlow`.
///
/// In the future, this type will be replaced, once the `Try` trait stabilizes.
pub type Result<'i, T> = std::result::Result<T, ControlFlow<'i>>;

impl<'i> Context<'i> {
  pub fn new() -> Context<'i> {
    let top_scope = Object::new();
    Context {
      call_stack: vec![StackFrame::new(
        Value::Null,
        Span::synthetic("<start>".as_ref()),
        top_scope.clone(),
      )],
      called_fns: HashSet::new(),
      top_scope,
    }
  }

  pub fn eval(
    &mut self,
    unit: &'i syn::Unit<'i>,
    import_resolver: impl FnMut(&'i str) -> Option<Value<'i>>,
  ) -> std::result::Result<Value<'i>, EvalError<'i>> {
    match self.eval_inner(unit, import_resolver) {
      Ok(v) => Ok(v),
      Err(ControlFlow::Error(e)) => Err(e),
      Err(ControlFlow::Ret(v)) => Ok(v),
      Err(ControlFlow::Break(_)) => {
        error!(self, &unit.value, "cannot break from file")
      }
      Err(ControlFlow::Cont) => {
        error!(self, &unit.value, "cannot continue file")
      }
    }
  }

  fn eval_inner(
    &mut self,
    unit: &'i syn::Unit<'i>,
    mut import_resolver: impl FnMut(&'i str) -> Option<Value<'i>>,
  ) -> Result<'i, Value<'i>> {
    for import in unit.imports {
      let expr = import.import;
      let name = if expr.is_quoted {
        // TODO(mcyoung): maybe deal with escaping here?
        &expr.value[1..expr.value.len() - 1]
      } else {
        &expr.value
      };

      match import_resolver(name) {
        Some(val) => self.top_scope.define(import.var.name, val, false),
        None => error!(self, expr, "failed to resolve import"),
      }
    }

    for stmt in unit.stmts {
      self.eval_let(stmt)?
    }
    self.eval_expr(&unit.value)
  }

  pub fn eval_expr(
    &mut self,
    expr: &'i syn::Expr<'i>,
  ) -> Result<'i, Value<'i>> {
    let val = match expr {
      // Create scalar values out of their corresponding literals.
      syn::Expr::Null(..) => Value::Null,
      syn::Expr::Bool(syn::Bool { value, .. }) => Value::Bool(*value),
      syn::Expr::Num(syn::Num { value, .. }) => Value::Number(*value),

      // Create a new string out of a potentially quoted string literal.
      syn::Expr::Str(syn::Str {
        value,
        is_quoted,
        span,
      }) => {
        if *is_quoted {
          let unquoted = &value[1..value.len() - 1];
          match escaping::unescape_utf8_literal(unquoted) {
            Ok(ref s) if s == unquoted => unquoted.into(),
            Ok(s) => s.into(),
            Err(e) => error!(self, span, "{}", e),
          }
        } else {
          (*value).into()
        }
      }

      // Evaluate a reference to a name by looking it up in the current
      // scope.
      syn::Expr::Ref(id) => match self.scope().lookup(id.name) {
        Some(val) => val,
        None => error!(self, expr, "unknown reference: {}", id.name),
      },

      // Evaluate a builtin name:
      // - `self`, the current value of the innermost object literal; this name
      //   is not defined if there is no such literal.
      // - `super`, the "super object" of `self`. This name is not defined if
      //   `self` is not defined, or if `self` is a brand new object, not an
      //   extension.
      // - `top`, the root scope of the current scope, corresponding to the file
      //   scope of the current function.
      // - `here`, the current scope.
      // - `std`, a special object containing built-in functions and values.
      syn::Expr::Builtin(syn::Builtin { ty, .. }) => match ty {
        syn::BuiltinTy::Zelf | syn::BuiltinTy::Super => {
          let zelf = match self.current_frame().current_self() {
            Some(s) => s,
            None => error!(self, expr, "cannot access self outside of object"),
          };

          if *ty == syn::BuiltinTy::Super {
            match zelf.zuper() {
              Some(s) => Value::Object(s),
              None => error!(
                self,
                expr, "cannot access super outside of object extension"
              ),
            }
          } else {
            Value::Object(zelf)
          }
        }

        syn::BuiltinTy::It => match self.current_frame().current_it() {
          Some(v) => v,
          None => {
            error!(self, expr, "cannot access it outside of do expression")
          }
        },

        syn::BuiltinTy::Top => Value::Object(self.scope().root()),
        syn::BuiltinTy::Here => Value::Object(self.scope()),
        syn::BuiltinTy::Std => Value::Std,
      },

      // Evaluate a list literal, by successively evaluating its elements.
      syn::Expr::List(syn::List { values, .. }) => {
        let mut vals = Vec::with_capacity(values.len());
        for expr in *values {
          vals.push(self.eval_expr(expr)?);
        }

        Value::List(List::new(vals))
      }

      // Evaluate an object literal, by successively evaluating its keys.
      //
      // An object literal enters a new value of `self` for its duration. It
      // can also have another object acting as the "super-object" or
      // "prototype".
      syn::Expr::Object(syn::Object { zuper, fields, .. }) => {
        let super_val = match zuper {
          Some(expr) => match self.eval_expr(expr)? {
            Value::Object(obj) => Some(obj),
            v => error!(self, expr, "can only extend objects; got {}", v.ty()),
          },
          None => None,
        };

        Value::Object(self.eval_obj(super_val, fields)?)
      }

      // Evaluate a block. See `eval_block()` for details.
      syn::Expr::Block(bl) => self.eval_block(bl)?,

      // Create a new function out of a function literal. This captures the
      // current scope for later use.
      syn::Expr::Fn(fnc) => Value::Fn(Fn::new(fnc, self.scope())),

      // Evaluate an if-expression, by successively evaluating conditions and,
      // once one is true, evaluating the body to obtain the final value.
      //
      // A missing `else` block is implicitly replaced with `else { null }`.
      syn::Expr::If(syn::If {
        clauses,
        else_block,
        ..
      }) => {
        for (cond_expr, block) in *clauses {
          match self.eval_expr(cond_expr)? {
            Value::Bool(true) => return self.eval_block(block),
            Value::Bool(false) => continue,
            v => error!(
              self,
              cond_expr,
              "expected type bool for condition; got {}",
              v.ty()
            ),
          }
        }

        if let Some(block) = else_block {
          return self.eval_block(block);
        }

        Value::Null
      }

      // Evaluate a switch-expression, by successively evaluating the
      // left-hand-sides of cases until one matches, and then evaluating the
      // right-hand-side as the final value.
      //
      // Failure to produce a value results in an error, unlike in an
      // if-expression.
      syn::Expr::Switch(syn::Switch {
        arg,
        clauses,
        else_clause,
        ..
      }) => {
        let arg = self.eval_expr(arg)?;

        for clause in *clauses {
          for case in clause.cases {
            let val = self.eval_expr(case)?;
            if self.compare_eq(case.span(), arg.clone(), val)? {
              return self.eval_expr(&clause.value);
            }
          }
        }

        if let Some(value) = else_clause {
          return self.eval_expr(value);
        }

        error!(self, expr, "switch ended without producing a match")
      }

      // Evaluate a for-expression, by repeatedly evaluating the body for each
      // value produced by an iteration.
      //
      // The loop introduces a new yield frame, which is to be constructed by
      // successive yield expressions; each iteration happens in a brand-new
      // scope. The value of the body is ignored.
      //
      // Continuing will end an iteration prematurely; breaking with no value
      // will end the whole loop and consume the yield frame; breaking with
      // a value will discard the yield frame and produce that value.
      syn::Expr::For(syn::For {
        pats,
        is_match_required,
        iter,
        body,
        ..
      }) => {
        let iter_span = iter.span();
        let iter_val = self.eval_expr(iter)?;
        match iter_val {
          Value::Range { start, end, step } => {
            let iter = (start..end)
              .step_by(step as usize)
              .map(|i| vec![Value::Number(i as f64)]);
            self.iterate(iter_span, pats, *is_match_required, body, iter)?
          }
          Value::String(s) => {
            let iter = s.chars().enumerate().map(|(i, c)| {
              let width = c.len_utf8();
              let slice = s
                .slice(i..i + width)
                .expect("should never be out of bounds");
              let idx = Value::Number(i as f64);
              vec![idx, Value::String(slice)]
            });
            self.iterate(iter_span, pats, *is_match_required, body, iter)?
          }
          Value::List(l) => {
            let iter = l
              .iter()
              .enumerate()
              .map(|(i, v)| vec![Value::Number(i as f64), v.clone()]);
            self.iterate(iter_span, pats, *is_match_required, body, iter)?
          }
          Value::Object(o) => {
            let iter = Object::iter(&o).map(|(k, v, o)| {
              vec![
                Value::String(k.clone()),
                v.clone(),
                Value::Object(o.clone()),
              ]
            });
            self.iterate(iter_span, pats, *is_match_required, body, iter)?
          }
          v => {
            error!(self, iter, "cannot iterate over value of type {}", v.ty())
          }
        }
      }

      // Evaluate a list-like `yield` expression, evaluating the sole argument
      // and adding it to the current yield frame.
      syn::Expr::Yield(syn::Yield { value, .. }) => {
        if self.current_frame().current_yield().is_none() {
          error!(self, expr, "cannot yield outside of loop")
        }

        let value = self.eval_expr(value)?;
        if !self
          .current_frame()
          .current_yield()
          .unwrap()
          .push_value(value)
        {
          error!(
            self,
            expr, "cannot yield value while also yielding key-values"
          )
        }

        Value::Null
      }

      // Evaluate an object-like `yield` expression, similarly to a normal,
      // list-like `yield`.
      syn::Expr::YieldKv(syn::YieldKv { kv, .. }) => {
        if self.current_frame().current_yield().is_none() {
          error!(self, expr, "cannot yield outside of loop")
        }
        if kv.ty != syn::KvType::Normal {
          error!(self, expr, "cannot yield with super key")
        }

        let (key, value, nullable) = self.eval_kv(kv)?;
        match (&value, nullable) {
          (Value::Null, true) => return Ok(Value::Null),
          _ => {}
        }

        let key = match key {
          Value::String(val) => val,
          v => error!(self, kv.key, "expected string as key, got {}", v.ty()),
        };
        if !self
          .current_frame()
          .current_yield()
          .unwrap()
          .push_kv(key, value)
        {
          error!(
            self,
            expr, "cannot yield key-value while also yielding single values"
          )
        }

        Value::Null
      }

      // Break out of a loop, potentially with a value. The actual semantics are
      // handled by loop-iteration code.
      syn::Expr::Break(syn::Break { value, .. }) => {
        let value = match value {
          Some(expr) => Some(self.eval_expr(expr)?),
          None => None,
        };
        return Err(ControlFlow::Break(value));
      }

      // Continue a loop. The actual semantics are handled by loop-iteration
      // code.
      syn::Expr::Cont(..) => return Err(ControlFlow::Cont),

      // Perform an early return. The actual semantics are handled by
      // function-call code.
      syn::Expr::Ret(syn::Ret { value, .. }) => {
        return Err(ControlFlow::Ret(self.eval_expr(value)?))
      }

      // Extract a member out of an object, by performing an indexing.
      // If the extracted member is a function, bind it.
      syn::Expr::Member(syn::Member {
        value,
        member,
        nullable,
        ..
      }) => {
        let key = self.eval_expr(member)?;
        let val = self.eval_expr(value)?;

        match (
          self.index(expr.span(), val.clone(), vec![key.clone()]),
          nullable,
        ) {
          (Err(ControlFlow::Error(_)), true) => Value::Null,
          (Ok(Value::Fn(mut fnc)), _) => {
            if let Value::Object(val) = val {
              fnc.bind(val);
            }
            Value::Fn(fnc)
          }
          (val, _) => val?,
        }
      }

      // Perform an indexing; type-specific logic is handled by the indexing
      // function.
      syn::Expr::Index(syn::Index {
        value,
        args,
        nullable,
        ..
      }) => {
        let val = self.eval_expr(value)?;

        let mut idx_args = Vec::with_capacity(args.len());
        for arg in *args {
          idx_args.push(self.eval_expr(arg)?);
        }

        match (self.index(expr.span(), val, idx_args), nullable) {
          (Err(ControlFlow::Error(_)), true) => Value::Null,
          (val, _) => val?,
        }
      }

      // Perform a `do`-expression, similar to a pipe operation: push a new
      // `it` value
      syn::Expr::Do(syn::Do {
        it, body, nullable, ..
      }) => {
        let it = self.eval_expr(it)?;
        if let (Value::Null, true) = (&it, nullable) {
          return Ok(Value::Null);
        }

        self.current_frame().start_do(it);
        let val = self.eval_expr(body);
        self.current_frame().end_do();
        val?
      }

      // Perform a function call; the actual call and stack-frame manipulation
      // is handled by the call function.
      syn::Expr::Call(syn::Call { fnc, args, .. }) => {
        let fnc = self.eval_expr(fnc)?;
        let mut fnc_args = Vec::with_capacity(args.len());
        for arg in *args {
          fnc_args.push(self.eval_expr(arg)?);
        }

        self.call(expr.span(), fnc, fnc_args)?
      }

      // Perform an unary operation; type-specific logic is in a separate
      // function.
      syn::Expr::UnOp(syn::UnOp { arg, ty, .. }) => {
        let arg = self.eval_expr(arg)?;
        self.eval_unop(expr.span(), *ty, arg)?
      }

      // Perform a binary operation; type-specific logic is in a separate
      // function.
      syn::Expr::BinOp(syn::BinOp { lhs, rhs, ty, .. }) => {
        self.eval_lazy_op(expr.span(), *ty, lhs, rhs)?
      }
    };

    Ok(val)
  }

  /// Execute a loop iteration.
  ///
  /// This function takes three main arguments:
  /// - `vars`, the names of the loop variables.
  /// - `body`, the block to repeatedly execute.
  /// - `iter`, the iterator to loop over.
  ///
  /// It also requires a span for the iterator expression, for error purposes.
  fn iterate(
    &mut self,
    iter_span: Span<'i>,
    pats: &'i [syn::Pat<'i>],
    is_match_required: bool,
    body: &'i syn::Expr<'i>,
    iter: impl Iterator<Item = Vec<Value<'i>>>,
  ) -> Result<'i, Value<'i>> {
    self.current_frame().start_loop();

    'outer: for items in iter {
      if pats.len() != items.len() {
        error!(
          self,
          iter_span,
          "expected {} loop patterns, got {}",
          pats.len(),
          items.len()
        )
      }
      // NOTE: This scope must be re-created for each loop, since a function
      // could capture these variables.
      self.current_frame().start_scope();
      let scope = self.scope();
      for (pat, item) in pats.iter().zip(items.iter()) {
        let mut bindings = Vec::new();
        match (
          self.eval_pat(pat, item.clone(), &mut bindings),
          is_match_required,
        ) {
          (Ok(_), _) => {}
          (_, false) => continue 'outer,
          (Err(e), _) => return Err(e),
        }

        for (k, v) in bindings {
          scope.define(k, v, false);
        }
      }

      let val = self.eval_expr(body);
      self.current_frame().end_scope();
      match val {
        Ok(_) => continue,
        Err(ControlFlow::Cont) => continue,
        Err(ControlFlow::Break(None)) => break,
        Err(ControlFlow::Break(Some(val))) => return Ok(val),
        err => return err,
      }
    }

    let val = match self.current_frame().end_loop() {
      YieldFrame::None => Value::Null,
      YieldFrame::List(vals) => Value::List(List::new(vals)),
      YieldFrame::Object(map) => {
        let obj = Object::new();
        for (k, v) in map {
          obj.define(k, v, true);
        }
        obj.freeze();
        Value::Object(obj)
      }
    };

    Ok(val)
  }

  /// Execute a function call.
  ///
  /// This function takes three main arguments:
  /// - `fnc`, the function to call.
  /// - `args`, the function arguments.
  ///
  /// It also requires a call-site span, for stack symbolization and
  /// error-reporting.
  ///
  /// It goes without saying that `fnc` must be a function of some kind, either
  /// Alkyne or native.
  ///
  /// For the purposes of null coallesion, `null` is callable, and always
  /// produces `null` as the return value. This ensures that `x?.foo()` never
  /// produces an error.
  fn call(
    &mut self,
    call_site: Span<'i>,
    fnc: Value<'i>,
    args: Vec<Value<'i>>,
  ) -> Result<'i, Value<'i>> {
    match fnc {
      Value::Null => Ok(Value::Null),
      // Call a normal Alkyne function. This involves:
      // - Checking that this isn't an instance of recursion.
      // - Checking that the number of arguments is correct.
      // - Creating a new scope with the function arguments.
      // - Creating a new stack frame.
      // - Marking this function as "called".
      // - Calling the function.
      //
      // One all of that is done, the above all needs to get cleaned up in
      // reverse order.
      Value::Fn(fnc) => {
        let ptr_value = fnc.src() as *const syn::Fn<'i> as usize;
        if self.called_fns.contains(&ptr_value) {
          error!(self, call_site, "recursion is forbidden")
        }

        if fnc.src().args.len() != args.len() {
          error!(
            self,
            call_site,
            "expected {} args for function call, got {}",
            fnc.src().args.len(),
            args.len()
          )
        }

        let scope = fnc.captures().extend();
        for (i, arg) in args.into_iter().enumerate() {
          let pat = &fnc.src().args[i];

          let mut bindings = Vec::new();
          self.eval_pat(pat, arg, &mut bindings)?;
          for (k, v) in bindings {
            scope.define(k, v, false);
          }
        }

        self.call_stack.push(StackFrame::new(
          Value::Fn(fnc.clone()),
          call_site,
          scope,
        ));

        if let Some(zelf) = fnc.referent() {
          self.current_frame().start_object(zelf);
        }

        self.called_fns.insert(ptr_value);
        let result = self.eval_expr(&fnc.src().body);
        self.called_fns.remove(&ptr_value);
        self.call_stack.pop();

        match result {
          Ok(v) => Ok(v),
          Err(ControlFlow::Ret(v)) => Ok(v),
          Err(ControlFlow::Break(..)) => {
            error!(self, fnc.src(), "cannot not break out of function")
          }
          Err(ControlFlow::Cont) => {
            error!(self, fnc.src(), "cannot not continue out of function")
          }
          Err(e) => Err(e),
        }
      }

      // Call a native function. This is similar to calling a Alkyne function,
      // except that we don't bother checking arguments or creating a new
      // scope: those are the native function's responsibility.
      Value::NativeFn(fnc) => {
        let ptr_value = fnc.ptr_value();
        if self.called_fns.contains(&ptr_value) {
          error!(self, call_site, "recursion is forbidden")
        }

        self.call_stack.push(StackFrame::new(
          Value::NativeFn(fnc.clone()),
          call_site,
          self.scope(),
        ));

        self.called_fns.insert(ptr_value);
        let result = fnc.call(self, args);
        self.called_fns.remove(&ptr_value);
        self.call_stack.pop();

        result
      }

      v => error!(self, call_site, "cannot call value of type {}", v.ty()),
    }
  }

  /// Index into a Alkyne object.
  ///
  /// The following combinations are valid:
  /// - `string` with one or two integer arguments, performing a slice
  ///   operation. A single argument will result in slicing a single character.
  /// - `list` with one or two integer arguments. Same semantics as `string`,
  ///   though a single argument will produce a single element rather than a
  ///   one-element list.
  /// - `object` with one string argument, which performs the obvious lookup.
  /// - `std`, with the same semantics as `object`.
  /// - All other operations are errors.
  fn index(
    &mut self,
    call_site: Span<'i>,
    obj: Value<'i>,
    args: Vec<Value<'i>>,
  ) -> Result<'i, Value<'i>> {
    match obj {
      Value::String(s) => {
        let (start, end) = match args.len() {
          1 => match args[0].as_int() {
            Ok(i) => (i, i + 1),
            Err(t) => error!(
              self,
              call_site, "expected integer index for string, got {}", t
            ),
          },
          2 => {
            let start = match args[0].as_int() {
              Ok(i) => i,
              Err(t) => error!(
                self,
                call_site, "expected integer index for string, got {}", t
              ),
            };
            let end = match args[1].as_int() {
              Ok(i) => i,
              Err(t) => error!(
                self,
                call_site, "expected integer index for string, got {}", t
              ),
            };
            (start, end)
          }
          n => error!(
            self,
            call_site, "expected 1 or 2 indices for string, got {}", n
          ),
        };

        let (start, end) = (start as usize, end as usize);
        match s.slice(start..end) {
          Some(s) => Ok(Value::String(s)),
          None => error!(
            self,
            call_site,
            "range out of bounds: got indices [{}, {}) out of range [{}, {})",
            start,
            end,
            0,
            s.len()
          ),
        }
      }

      Value::List(l) => {
        match args.len() {
          1 => {
            let idx = match args[0].as_int() {
              Ok(i) => i,
              Err(t) => error!(
                self,
                call_site, "expected integer index for list, got {}", t
              ),
            };
            if idx < 0 || idx >= (l.len() as i64) {
              error!(
                self,
                call_site,
                "index out of bounds: len {}, got {}",
                l.len(),
                idx
              )
            }

            Ok(l.as_sliced()[idx as usize].clone())
          }
          2 => {
            let start = match args[0].as_int() {
              Ok(i) => i,
              Err(t) => error!(
                self,
                call_site, "expected integer index for list, got {}", t
              ),
            };
            let end = match args[1].as_int() {
              Ok(i) => i,
              Err(t) => error!(
                self,
                call_site, "expected integer index for list, got {}", t
              ),
            };
            let (start, end) = (start as usize, end as usize);
            match l.slice(start..end) {
              Some(l) => Ok(Value::List(l)),
              None =>
                error!(self, call_site,
                       "range out of bounds: got indices [{}, {}) out of range [{}, {})",
                       start, end, 0, l.len()),
            }
          }
          n => error!(
            self,
            call_site, "expected 1 or 2 indices for list, got {}", n
          ),
        }
      }
      Value::Object(obj) => {
        if args.len() != 1 {
          error!(
            self,
            call_site,
            "expected 1 index for object, got {}",
            args.len()
          )
        }

        let key = match &args[0] {
          Value::String(k) => k,
          v => error!(
            self,
            call_site,
            "expected string index for object, got {}",
            v.ty()
          ),
        };

        match obj.lookup(key) {
          Some(val) => Ok(val),
          None => error!(self, call_site, "key {} not present", &args[0]),
        }
      }
      Value::Std => {
        if args.len() != 1 {
          error!(
            self,
            call_site,
            "expected 1 index for object, got {}",
            args.len()
          )
        }

        let key = match &args[0] {
          Value::String(k) => k,
          v => error!(
            self,
            call_site,
            "expected string index for object, got {}",
            v.ty()
          ),
        };

        match stdlib::lookup_std(key) {
          Some(val) => Ok(val),
          None => error!(self, call_site, "key {} not present", &args[0]),
        }
      }
      v => error!(self, call_site, "cannot index value of type {}", v.ty()),
    }
  }

  /// Compare two values for equality.
  ///
  /// Semantics are as follows:
  /// - If either operand is an object with `oper==` defined, then that is used
  ///   as a comparison; `oper==` of the first argument is called if both
  ///   objects have one.
  /// - Otherwise, null comparse for false with everything except itself.
  /// - Otherwise, bools, numbers, and strings are compared in the usual fasion.
  /// - All other comparisions are an error.
  fn compare_eq(
    &mut self,
    call_site: Span<'i>,
    first: Value<'i>,
    second: Value<'i>,
  ) -> Result<'i, bool> {
    if let Value::Object(first) = first.clone() {
      if let Some(mut first_eq) = first.lookup("oper==") {
        if let Value::Fn(fnc) = &mut first_eq {
          fnc.bind(first.clone());
          fnc.rename("oper==".into());
        }
        match self.call(call_site, first_eq, vec![second.clone()])? {
          Value::Bool(b) => return Ok(b),
          v => error!(
            self,
            call_site,
            "expected value of type bool from oper==; got {}",
            v.ty()
          ),
        }
      }
    }

    if let Value::Object(second) = second.clone() {
      if let Some(mut second_eq) = second.lookup("oper==") {
        if let Value::Fn(fnc) = &mut second_eq {
          fnc.bind(second.clone());
          fnc.rename("oper==".into());
        }
        match self.call(call_site, second_eq, vec![first.clone()])? {
          Value::Bool(b) => return Ok(b),
          v => error!(
            self,
            call_site,
            "expected value of type bool from oper==; got {}",
            v.ty()
          ),
        }
      }
    }

    let val = match (first, second) {
      (Value::Null, Value::Null) => true,
      (Value::Null, _) | (_, Value::Null) => false,
      (Value::Bool(b1), Value::Bool(b2)) => b1 == b2,
      (Value::Number(n1), Value::Number(n2)) => n1 == n2,
      (Value::String(s1), Value::String(s2)) => {
        s1.as_sliced() == s2.as_sliced()
      }
      (first, second) => error!(
        self,
        call_site,
        "cannot compare values of types {}, {}",
        first.ty(),
        second.ty()
      ),
    };

    Ok(val)
  }

  /// Compare two values for order.
  ///
  /// Semantics are as follows:
  /// - Numbers and strings compare in the usual manner.
  /// - All other comparisions are an error.
  fn compare_ord(
    &mut self,
    call_site: Span<'i>,
    first: Value<'i>,
    second: Value<'i>,
  ) -> Result<'i, Option<Ordering>> {
    match (first, second) {
      (Value::Number(f1), Value::Number(f2)) => Ok(f1.partial_cmp(&f2)),
      (Value::String(s1), Value::String(s2)) => {
        Ok(s1.as_sliced().partial_cmp(s2.as_sliced()))
      }
      (first, second) => error!(
        self,
        call_site,
        "cannot order values of types {}, {}",
        first.ty(),
        second.ty()
      ),
    }
  }

  /// Evaluates a potentially lazy binary operator.
  ///
  /// Semantics are as follows:
  /// - Short-circuiting logic, `&&` and `||`, have their usual behavior,
  ///   though they require both operands to be booleans.
  /// - Otherwise, defer to `eval_op()`.
  fn eval_lazy_op(
    &mut self,
    call_site: Span<'i>,
    op: syn::BinOpTy,
    first: &'i syn::Expr<'i>,
    second: &'i syn::Expr<'i>,
  ) -> Result<'i, Value<'i>> {
    let first = self.eval_expr(first)?;

    if op == syn::BinOpTy::AndAnd || op == syn::BinOpTy::OrOr {
      let b1 = match first {
        Value::Bool(b) => b,
        v => error!(
          self,
          call_site,
          "cannot apply {} to values of types {}, _",
          op.name(),
          v.ty()
        ),
      };
      match (b1, op) {
        (false, syn::BinOpTy::AndAnd) | (true, syn::BinOpTy::OrOr) => {
          return Ok(b1.into())
        }
        _ => {}
      }

      let b2 = match self.eval_expr(second)? {
        Value::Bool(b) => b,
        v => error!(
          self,
          call_site,
          "cannot apply {} to values of types bool, {}",
          op.name(),
          v.ty()
        ),
      };

      let res = match op {
        syn::BinOpTy::AndAnd => b1 & b2,
        syn::BinOpTy::OrOr => b1 | b2,
        _ => unimplemented!(),
      };
      return Ok(res.into());
    }

    if op == syn::BinOpTy::Elvis {
      if let Value::Null = first {
        return self.eval_expr(second);
      }

      return Ok(first);
    }

    let second = self.eval_expr(second)?;

    self.eval_op(call_site, op, first, second)
  }

  /// Evaluate a strict binary operator.
  ///
  /// Semantics are as follows:
  /// - If the operation is overloadable (i.e. an arithmetic operation), and
  ///   either operand is an object with the relevant `oper` value, then that
  ///   will be used as the operator. The first operand's `oper` value is called
  ///   even if the second operand also has one.
  /// - Equality and comparison defer to `compare_eq()` and `compare_ord()`,
  ///   respectively.
  /// - Numbers implement all arithmetic operations; importantly, `%` is
  ///   Ealkyneidean remainder.
  /// - Strings and lists implement addition by concatenation.
  /// - All other combinations are an error.
  fn eval_op(
    &mut self,
    call_site: Span<'i>,
    op: syn::BinOpTy,
    first: Value<'i>,
    second: Value<'i>,
  ) -> Result<'i, Value<'i>> {
    if op.overloadable() && (op != syn::BinOpTy::Eq && op != syn::BinOpTy::Ne) {
      let op_name = format!("oper{}", op);
      if let Value::Object(first) = first.clone() {
        if let Some(mut first_op) = first.lookup(&op_name) {
          if let Value::Fn(fnc) = &mut first_op {
            fnc.bind(first.clone());
            fnc.rename(op_name.into());
          }
          return self.call(call_site, first_op, vec![second.clone()]);
        }
      }
      if let Value::Object(second) = second.clone() {
        if let Some(mut second_op) = second.lookup(&op_name) {
          if let Value::Fn(fnc) = &mut second_op {
            fnc.bind(second.clone());
            fnc.rename(op_name.into());
          }
          return self.call(call_site, second_op, vec![first.clone()]);
        }
      }
    }

    match (op, first, second) {
      (syn::BinOpTy::Eq, first, second) => {
        Ok(Value::Bool(self.compare_eq(call_site, first, second)?))
      }
      (syn::BinOpTy::Ne, first, second) => {
        Ok(Value::Bool(!self.compare_eq(call_site, first, second)?))
      }
      (syn::BinOpTy::Ge, first, second) => {
        let ord = self.compare_ord(call_site, first, second)?;
        Ok(Value::Bool(
          ord == Some(Ordering::Greater) || ord == Some(Ordering::Equal),
        ))
      }
      (syn::BinOpTy::Le, first, second) => {
        let ord = self.compare_ord(call_site, first, second)?;
        Ok(Value::Bool(
          ord == Some(Ordering::Less) || ord == Some(Ordering::Equal),
        ))
      }
      (syn::BinOpTy::Gt, first, second) => {
        let ord = self.compare_ord(call_site, first, second)?;
        Ok(Value::Bool(ord == Some(Ordering::Greater)))
      }
      (syn::BinOpTy::Lt, first, second) => {
        let ord = self.compare_ord(call_site, first, second)?;
        Ok(Value::Bool(ord == Some(Ordering::Less)))
      }

      (syn::BinOpTy::Add, Value::Number(n1), Value::Number(n2)) => {
        Ok(Value::Number(n1 + n2))
      }
      (syn::BinOpTy::Sub, Value::Number(n1), Value::Number(n2)) => {
        Ok(Value::Number(n1 - n2))
      }
      (syn::BinOpTy::Mul, Value::Number(n1), Value::Number(n2)) => {
        Ok(Value::Number(n1 * n2))
      }
      (syn::BinOpTy::Div, Value::Number(n1), Value::Number(n2)) => {
        Ok(Value::Number(n1 / n2))
      }
      (syn::BinOpTy::Rem, Value::Number(n1), Value::Number(n2)) => {
        Ok(Value::Number(n1.rem_euclid(n2)))
      }

      (syn::BinOpTy::Add, Value::String(s1), Value::String(s2)) => {
        let mut buf = String::new();
        buf.reserve(s1.len() + s2.len());
        buf.push_str(&*s1);
        buf.push_str(&*s2);
        Ok(buf.into())
      }
      (syn::BinOpTy::Add, Value::List(l1), Value::List(l2)) => {
        let mut buf = Vec::new();
        buf.reserve(l1.len() + l2.len());
        buf.extend_from_slice(&*l1);
        buf.extend_from_slice(&*l2);
        Ok(buf.into())
      }
      (op, first, second) => error!(
        self,
        call_site,
        "cannot apply {} to values of types {}, {}",
        op.name(),
        first.ty(),
        second.ty()
      ),
    }
  }

  /// Evaluates an unary operator.
  ///
  /// Semantics are as follows:
  /// - If the operand is an object with the appropriate `oper` value, then that
  ///   will be called. Note that it will be called with a null argument, i.e.,
  ///   `-foo` desugars to `foo.oper-(null)`.
  /// - `bool` can be negated with `!`.
  /// - `number` can be negated with `-`.
  /// - All other combinations are an error.
  fn eval_unop(
    &mut self,
    call_site: Span<'i>,
    op: syn::UnOpTy,
    arg: Value<'i>,
  ) -> Result<'i, Value<'i>> {
    if op.overloadable() {
      let op_name = format!("oper{}", op);
      if let Value::Object(arg) = arg.clone() {
        if let Some(mut arg_op) = arg.lookup(&op_name) {
          if let Value::Fn(fnc) = &mut arg_op {
            fnc.bind(arg.clone());
            fnc.rename(op_name.into());
          }
          return self.call(call_site, arg_op, vec![Value::Null]);
        }
      }
    }

    match (op, arg) {
      (syn::UnOpTy::Not, Value::Bool(b)) => Ok((!b).into()),
      (syn::UnOpTy::Neg, Value::Number(n)) => Ok((-n).into()),
      (op, arg) => error!(
        self,
        call_site,
        "cannot apply {} to values of type {}",
        op.name(),
        arg.ty()
      ),
    }
  }

  /// Evaluates a block.
  ///
  /// This creates a new scope against which to evaluate the contents of the
  /// block.
  fn eval_block(&mut self, block: &'i syn::Block<'i>) -> Result<'i, Value<'i>> {
    self.current_frame().start_scope();
    for stmt in block.lets {
      if let Err(e) = self.eval_let(stmt) {
        self.current_frame().end_scope();
        return Err(e);
      }
    }
    self.scope().freeze();
    let val = self.eval_expr(block.value);
    self.current_frame().end_scope();
    val
  }

  /// Evaluates a `let` binding.
  pub fn eval_let(&mut self, stmt: &'i syn::Let<'i>) -> Result<'i, ()> {
    let value = self.eval_expr(&stmt.value)?;

    let mut bindings = Vec::new();
    if let Some(pat) = stmt.pat {
      self.eval_pat(pat, value, &mut bindings)?;
    }

    for (k, v) in bindings {
      self.scope().define(k, v, false);
    }

    Ok(())
  }

  /// Evaluates an object literal, taking care to set up the
  /// self-stack.
  fn eval_obj(
    &mut self,
    zuper: Option<Object<'i>>,
    fields: &'i [syn::Kv<'i, syn::Expr<'i>>],
  ) -> Result<'i, Object<'i>> {
    let obj = if let Some(zuper) = zuper {
      zuper.extend()
    } else {
      Object::new()
    };

    self.current_frame().start_object(obj.clone());
    let val = self.eval_obj_inner(obj, fields);
    self.current_frame().end_object();
    val
  }

  fn eval_obj_inner(
    &mut self,
    obj: Object<'i>,
    fields: &'i [syn::Kv<'i, syn::Expr<'i>>],
  ) -> Result<'i, Object<'i>> {
    let zuper = obj.zuper();
    for field in fields {
      let key = self.eval_expr(&field.key)?;
      let key_str = match key {
        Value::String(s) => s,
        v => error!(
          self,
          field.key,
          "can only use strings as keys; got {}",
          v.ty()
        ),
      };
      let val = if field.ty != syn::KvType::Normal {
        if zuper.is_none() {
          error!(
            self,
            field.key, "cannot use super key outside of object extension"
          )
        }
        let super_val = match zuper.as_ref().unwrap().lookup(&key_str) {
          None if field.ty == syn::KvType::MaybeSuper => continue,
          Some(Value::Object(o)) => o,
          Some(t) => {
            error!(self, field.key, "expected type object; got {}", t.ty())
          }
          _ => error!(self, field.key, "key {} not present", key_str),
        };
        let extn = match &field.value {
          syn::Expr::Object(syn::Object {
            zuper: None,
            fields,
            ..
          }) => fields,
          _ => error!(
            self,
            field.value,
            "value of super field must be a non-extension object literal"
          ),
        };
        Value::Object(self.eval_obj(Some(super_val), extn)?)
      } else {
        self.eval_expr(&field.value)?
      };
      match (&val, field.nullable) {
        (Value::Null, true) => continue,
        _ => {}
      }
      obj.define(key_str, val, true);
    }
    obj.freeze();
    Ok(obj)
  }

  /// Evaluate a key-value pair.
  pub fn eval_kv(
    &mut self,
    kv: &'i syn::Kv<'i, syn::Expr<'i>>,
  ) -> Result<'i, (Value<'i>, Value<'i>, bool)> {
    let key = self.eval_expr(&kv.key)?;
    let val = self.eval_expr(&kv.value)?;
    Ok((key, val, kv.nullable))
  }

  /// Evaluates a pattern, by attempting to match `matchee` against `pat`.
  ///
  /// This function does not actually produce pattern bindings. Instead,
  /// bindings are written to a buffer passed to the function.
  ///
  /// If the caller plans to roll back bindings if the function returns an
  /// error, they can take the length of `bindings` before the call, and
  /// truncate it if the call fails.
  pub fn eval_pat(
    &mut self,
    pat: &'i syn::Pat<'i>,
    matchee: Value<'i>,
    bindings: &mut Vec<(Str<'i>, Value<'i>)>,
  ) -> Result<'i, ()> {
    let span = pat.span();

    #[inline]
    fn bind<'i>(
      this: &mut Context<'i>,
      span: Span<'i>,
      bindings: &mut Vec<(Str<'i>, Value<'i>)>,
      name: impl Into<Str<'i>>,
      val: impl Into<Value<'i>>,
    ) -> Result<'i, ()> {
      let name = name.into();
      if &*name == "_" {
        return Ok(());
      }

      if let Some(_) = bindings.iter().find(|(k, _)| *k == name) {
        error!(this, span, "cannot bind same name twice in pattern")
      }
      bindings.push((name, val.into()));
      Ok(())
    }

    match pat {
      syn::Pat::Expr(expr) => {
        let expr = self.eval_expr(expr)?;
        if !self.compare_eq(span, matchee, expr)? {
          error!(self, span, "pattern match failed")
        }
      }
      syn::Pat::Bind(id) => bind(self, span, bindings, id.name, matchee)?,
      syn::Pat::ExactList(pat) => {
        let list = match matchee {
          Value::List(list) => list,
          v => {
            error!(self, span, "expected list for list pattern; got {}", v.ty())
          }
        };

        if list.len() != pat.pats.len() {
          error!(
            self,
            span,
            "expected {} elements in list; got {}",
            pat.pats.len(),
            list.len()
          )
        }

        for (i, pat) in pat.pats.iter().enumerate() {
          let val = list[i].clone();
          self.eval_pat(pat, val, bindings)?;
        }
      }
      syn::Pat::GlobList(pat) => {
        let list = match matchee {
          Value::List(list) => list,
          v => {
            error!(self, span, "expected list for list pattern; got {}", v.ty())
          }
        };

        let minimum_len = pat.front.len() + pat.back.len();
        if list.len() < minimum_len {
          error!(
            self,
            span,
            "expected at least {} elements in list; got {}",
            minimum_len,
            list.len()
          )
        }

        for (i, pat) in pat.front.iter().enumerate() {
          let val = list[i].clone();
          self.eval_pat(pat, val, bindings)?;
        }

        let back_start = list.len() - pat.back.len();
        for (i, pat) in pat.back.iter().enumerate() {
          let val = list[back_start + i].clone();
          self.eval_pat(pat, val, bindings)?;
        }

        if let Some(id) = &pat.middle {
          let middle_list = list.slice(pat.front.len()..back_start).unwrap();
          bind(self, id.span(), bindings, id.name, middle_list)?;
        }
      }
      syn::Pat::Object(pat) => {
        let obj = match matchee {
          Value::Object(obj) => obj,
          v => error!(
            self,
            span,
            "expected object for object pattern; got {}",
            v.ty()
          ),
        };

        let mut allowed_keys = HashSet::new();
        for field in pat.fields {
          let key = match self.eval_expr(&field.key)? {
            Value::String(s) => s,
            v => error!(
              self,
              field.key,
              "can only use strings as keys; got {}",
              v.ty()
            ),
          };
          let key_str = key.as_sliced();

          let val = match (field.nullable, obj.lookup(key_str)) {
            (_, Some(v)) => v,
            (true, None) => Value::Null,
            (false, None) => error!(self, field.key, "key {} not present", key),
          };

          if let Some(pat) = &field.value {
            self.eval_pat(pat, val, bindings)?;
          } else if escaping::is_identifier(key_str) {
            bind(self, field.key.span(), bindings, key.clone(), val)?;
          }

          if pat.is_exact {
            allowed_keys.insert(key);
          }
        }

        if pat.is_exact {
          for (k, _, _) in obj.iter() {
            if !allowed_keys.contains(&*k) {
              error!(self, span, "matchee had superfluous key: {}", k)
            }
          }
        }
      }
      syn::Pat::At(pat) => {
        bind(
          self,
          pat.ident.span(),
          bindings,
          pat.ident.name,
          matchee.clone(),
        )?;
        self.eval_pat(&pat.pat, matchee, bindings)?;
      }
      syn::Pat::Or(pat) => {
        let mark = bindings.len();
        for p in pat.pats {
          match self.eval_pat(p, matchee.clone(), bindings) {
            Ok(_) => return Ok(()),
            Err(_) => bindings.truncate(mark),
          }
        }
        error!(self, pat, "could not match any subpattern")
      }
    }

    Ok(())
  }
}
