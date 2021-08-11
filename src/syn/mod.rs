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

//! Syntax tree data structures for the Alkyne language.

#![deny(missing_docs)]

use std::fmt;
use std::path::Path;

mod parser;
pub use parser::{parse, ParseError};

pub use toolshed::Arena;

/// A source span.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Span<'i> {
  file_name: &'i Path,
  input: Option<&'i str>,
  start: usize,
  end: usize,
}

impl<'i> Span<'i> {
  /// Builds a new `Span` from raw parts.
  pub(crate) fn new_from_parts(
    file_name: &'i Path,
    input: &'i str,
    span: (usize, usize),
  ) -> Self {
    Self {
      file_name,
      input: Some(input),
      start: span.0,
      end: span.1,
    }
  }

  /// Builds a new "synthetic" span, which might point to a non-Alkyne file.
  pub fn synthetic(file_name: &'i Path) -> Self {
    Self {
      file_name,
      input: None,
      start: 0,
      end: 0,
    }
  }

  /// Returns the name of the file this `Span` refers to.
  pub fn file_name(&self) -> &'i Path {
    self.file_name
  }

  /// Returns whether this `Span` is synthetic, i.e., whether it does not
  /// actually point to a real file.
  pub fn is_synthetic(&self) -> bool {
    self.input.is_none()
  }

  /// Returns the offset at which this `Span` starts.
  pub fn start_byte(&self) -> usize {
    self.start
  }

  /// Returns the offset at which this `Span` ends.
  pub fn end_byte(&self) -> usize {
    self.end
  }

  /// Returns the line and column this `Span` starts at, both one-indexed.
  pub fn start_position(&self) -> Option<(usize, usize)> {
    self.input.map(|s| {
      pest::Position::new(s, self.start_byte())
        .unwrap()
        .line_col()
    })
  }

  /// Returns the line and column this `Span` ends at, both one-indexed.
  pub fn end_position(&self) -> Option<(usize, usize)> {
    self
      .input
      .map(|s| pest::Position::new(s, self.end_byte()).unwrap().line_col())
  }

  /// Returns the input text that this `Span` refers to.
  pub fn input(&self) -> Option<&'i str> {
    self.input
  }

  /// Returns the text that this `Span` refers to.
  pub fn text(&self) -> Option<&'i str> {
    self.input.as_ref().map(|s| &s[self.start..self.end])
  }

  /// Joins two spans into a single, contiguous span.
  ///
  /// # Panics
  ///
  /// Panics if `first` and `second` are not in sequence.
  pub fn join(first: Span<'i>, second: Span<'i>) -> Span<'i> {
    assert!(first.end <= second.start);
    Span {
      end: second.end,
      ..first
    }
  }

  /// Creates a copy of this `Span`, such that it contains all the lines that
  /// this this `Span` contained a part of.
  pub fn snap_to_lines(&self) -> Self {
    if self.is_synthetic() {
      return *self;
    }

    let input = self.input.unwrap();
    let start = self.start_position().unwrap().0 - 1;
    let end = self.end_position().unwrap().0 - 1;

    let mut start_byte = 0;
    let mut end_byte = 0;
    for (i, line) in input.split('\n').enumerate() {
      if i < start {
        start_byte += line.len() + 1;
      }
      end_byte += line.len() + 1;
      if i == end {
        break;
      }
    }
    end_byte = end_byte.min(input.len());

    Self {
      file_name: self.file_name,
      input: Some(input),
      start: start_byte,
      end: end_byte,
    }
  }
}

impl fmt::Debug for Span<'_> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    if self.is_synthetic() {
      return write!(f, "<{}>[?..?]", self.file_name().display());
    }
    write!(
      f,
      "<{}>[{}..{}]",
      self.file_name().display(),
      self.start_byte(),
      self.end_byte()
    )
  }
}

impl fmt::Display for Span<'_> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    if self.is_synthetic() {
      return write!(f, "{}:?:?", self.file_name().display());
    }
    let (line, col) = self.start_position().unwrap();
    write!(f, "{}:{}:{}", self.file_name().display(), line + 1, col + 1)
  }
}

/// Represents a type with a file span.
pub trait Spanned<'i> {
  /// Returns the associated file span.
  fn span(&self) -> Span<'i>;
}

impl<'i> Spanned<'i> for Span<'i> {
  fn span(&self) -> Span<'i> {
    *self
  }
}

impl<'i, S> Spanned<'i> for &S
where
  S: Spanned<'i>,
{
  fn span(&self) -> Span<'i> {
    S::span(*self)
  }
}

/// A `Unit` represents a complete unit of evaluation, i.e., a single file.
#[derive(Copy, Clone, Debug)]
pub struct Unit<'i> {
  /// The imports this `Unit` brings in.
  pub imports: &'i [Use<'i>],
  /// The `let` statements at the top level of this file.
  pub stmts: &'i [Let<'i>],
  /// The value at the end of the file.
  pub value: Expr<'i>,
}

/// An `Ident` represents a Alkyne identifier, appearing as both an expression
/// and in binding definitions.
#[derive(Copy, Clone, Debug)]
pub struct Ident<'i> {
  /// The name of this identifier.
  pub name: &'i str,
  /// This AST node's span.
  pub span: Span<'i>,
}

impl<'i> Spanned<'i> for Ident<'i> {
  fn span(&self) -> Span<'i> {
    self.span
  }
}

/// A `Use` represents an import statement in Alkyne, with syntax
/// ```text
/// use foo = 'my/config/foo.alkyne';
/// ```
///
/// Imports can only appear at the beginning of a file.
#[derive(Copy, Clone, Debug)]
pub struct Use<'i> {
  /// The variable this import introduces into file scope.
  pub var: Ident<'i>,
  /// The text of the string literal after the '=' sign, quoted and
  /// unescaped.
  pub import: Str<'i>,
  /// This AST node's span.
  pub span: Span<'i>,
}

impl<'i> Spanned<'i> for Use<'i> {
  fn span(&self) -> Span<'i> {
    self.span
  }
}

/// A `Let` represents a variable binding, the sole permitted statement
/// in Alkyne. It computes the right hand side, and then attempts to match it
/// against the pattern.
#[derive(Copy, Clone, Debug)]
pub struct Let<'i> {
  /// The pattern to match the rhs against.
  pub pat: Option<&'i Pat<'i>>,
  /// Whether this `Let` is really a floating statement. This information is
  /// mostly just used by the parser.
  pub is_floating: bool,
  /// The value to be evaluated, and then matched against left hand side.
  pub value: Expr<'i>,
  /// This AST node's span.
  pub span: Span<'i>,
}

impl<'i> Spanned<'i> for Let<'i> {
  fn span(&self) -> Span<'i> {
    self.span
  }
}

/// A `Pat` represents a Alkyne pattern, used in e.g. `let` bindings.
#[derive(Copy, Clone, Debug)]
#[allow(missing_docs)]
pub enum Pat<'i> {
  Expr(Expr<'i>),
  Bind(Ident<'i>),
  ExactList(ExactListPat<'i>),
  GlobList(GlobListPat<'i>),
  Object(ObjectPat<'i>),
  Or(OrPat<'i>),
  At(AtPat<'i>),
}

impl<'i> Spanned<'i> for Pat<'i> {
  fn span(&self) -> Span<'i> {
    match self {
      Pat::Expr(s) => s.span(),
      Pat::Bind(s) => s.span(),
      Pat::ExactList(s) => s.span(),
      Pat::GlobList(s) => s.span(),
      Pat::Object(s) => s.span(),
      Pat::Or(s) => s.span(),
      Pat::At(s) => s.span(),
    }
  }
}

/// An `ExactListPat` represents a Alkyne pattern that matches a list of an exact
/// size.
#[derive(Copy, Clone, Debug)]
pub struct ExactListPat<'i> {
  /// The exact patterns to match, in order.
  pub pats: &'i [Pat<'i>],
  /// This AST node's span.
  pub span: Span<'i>,
}

impl<'i> Spanned<'i> for ExactListPat<'i> {
  fn span(&self) -> Span<'i> {
    self.span
  }
}

/// A `GlobListPat` represents a Alkyne pattern that matches a list of unknown
/// size, extracting elements from the front and back.
#[derive(Copy, Clone, Debug)]
pub struct GlobListPat<'i> {
  /// The patterns to match at the front end of the list.
  pub front: &'i [Pat<'i>],
  /// The name to bind the "middle" portion of the list to, if any.
  pub middle: Option<Ident<'i>>,
  /// The patterns to match at the back end of the list.
  pub back: &'i [Pat<'i>],
  /// This AST node's span.
  pub span: Span<'i>,
}

impl<'i> Spanned<'i> for GlobListPat<'i> {
  fn span(&self) -> Span<'i> {
    self.span
  }
}

/// A `ObjectPat` represents a Alkyne pattern that matches an object with various
/// keys, possibly exactly.
#[derive(Copy, Clone, Debug)]
pub struct ObjectPat<'i> {
  /// The fields to match for.
  pub fields: &'i [Kv<'i, Option<Pat<'i>>>],
  /// Whether this pattern expects the pattern to match *exactly*, i.e., there
  /// are no superfluous keys.
  pub is_exact: bool,
  /// This AST node's span.
  pub span: Span<'i>,
}

impl<'i> Spanned<'i> for ObjectPat<'i> {
  fn span(&self) -> Span<'i> {
    self.span
  }
}

/// A `AtPat` represents a Alkyne pattern that delegates to another pattern, but
/// binds the matchee to a given identifier.
#[derive(Copy, Clone, Debug)]
pub struct AtPat<'i> {
  /// The pattern to defer to.
  pub pat: &'i Pat<'i>,
  /// The identifier to bind the matchee to.
  pub ident: Ident<'i>,
  /// This AST node's span.
  pub span: Span<'i>,
}

impl<'i> Spanned<'i> for AtPat<'i> {
  fn span(&self) -> Span<'i> {
    self.span
  }
}

/// A `OrPat` represents a Alkyne pattern that tries one of several patterns until
/// one succeeds.
#[derive(Copy, Clone, Debug)]
pub struct OrPat<'i> {
  /// The patterns to try.
  pub pats: &'i [Pat<'i>],
  /// This AST node's span.
  pub span: Span<'i>,
}

impl<'i> Spanned<'i> for OrPat<'i> {
  fn span(&self) -> Span<'i> {
    self.span
  }
}

/// An `Expr` represents a Alkyne expression, as a union of all of the potential
/// Alkyne expression types.
#[derive(Copy, Clone, Debug)]
#[allow(missing_docs)]
pub enum Expr<'i> {
  Null(Null<'i>),
  Bool(Bool<'i>),
  Num(Num<'i>),
  Str(Str<'i>),
  Ref(Ident<'i>),
  Builtin(Builtin<'i>),
  List(List<'i>),
  Object(Object<'i>),
  Block(Block<'i>),
  Fn(Fn<'i>),
  If(If<'i>),
  Switch(Switch<'i>),
  For(For<'i>),
  Yield(Yield<'i>),
  YieldKv(YieldKv<'i>),
  Break(Break<'i>),
  Cont(Cont<'i>),
  Ret(Ret<'i>),
  Member(Member<'i>),
  Call(Call<'i>),
  Index(Index<'i>),
  Do(Do<'i>),
  UnOp(UnOp<'i>),
  BinOp(BinOp<'i>),
}

impl<'i> Spanned<'i> for Expr<'i> {
  fn span(&self) -> Span<'i> {
    match self {
      Expr::Null(s) => s.span(),
      Expr::Bool(s) => s.span(),
      Expr::Num(s) => s.span(),
      Expr::Str(s) => s.span(),
      Expr::Ref(s) => s.span(),
      Expr::Builtin(s) => s.span(),
      Expr::List(s) => s.span(),
      Expr::Object(s) => s.span(),
      Expr::Block(s) => s.span(),
      Expr::Fn(s) => s.span(),
      Expr::If(s) => s.span(),
      Expr::Switch(s) => s.span(),
      Expr::For(s) => s.span(),
      Expr::Yield(s) => s.span(),
      Expr::YieldKv(s) => s.span(),
      Expr::Break(s) => s.span(),
      Expr::Cont(s) => s.span(),
      Expr::Ret(s) => s.span(),
      Expr::Member(s) => s.span(),
      Expr::Call(s) => s.span(),
      Expr::Index(s) => s.span(),
      Expr::Do(s) => s.span(),
      Expr::UnOp(s) => s.span(),
      Expr::BinOp(s) => s.span(),
    }
  }
}

/// A `Null` represents a literal `null`.
#[derive(Copy, Clone, Debug)]
pub struct Null<'i> {
  /// This AST node's span.
  pub span: Span<'i>,
}

impl<'i> Spanned<'i> for Null<'i> {
  fn span(&self) -> Span<'i> {
    self.span
  }
}

/// A `Bool` represents a literal number: one of `true` or `false`.
#[derive(Copy, Clone, Debug)]
pub struct Bool<'i> {
  /// The parsed value of this literal.
  pub value: bool,
  /// This AST node's span.
  pub span: Span<'i>,
}

impl<'i> Spanned<'i> for Bool<'i> {
  fn span(&self) -> Span<'i> {
    self.span
  }
}

/// A `Num` represents a literal number.
///
/// Currently, all numbers are floating point, but this is subject to
/// change.
#[derive(Copy, Clone, Debug)]
pub struct Num<'i> {
  /// The parsed value of this literal.
  pub value: f64,
  /// This AST node's span.
  pub span: Span<'i>,
}

impl<'i> Spanned<'i> for Num<'i> {
  fn span(&self) -> Span<'i> {
    self.span
  }
}

/// A `Str` represents a literal string, which can be double or single
/// quoted, or neither. Literals with `is_quoted` set should be treated as
/// being surrounded by quotes and needing unescaping
#[derive(Copy, Clone, Debug)]
pub struct Str<'i> {
  /// The possibly quoted, escaped value of this literal.
  pub value: &'i str,
  /// Whether this is a "quoted" string literal, as opposed to a bareword.
  pub is_quoted: bool,
  /// This AST node's span.
  pub span: Span<'i>,
}

impl<'i> Spanned<'i> for Str<'i> {
  fn span(&self) -> Span<'i> {
    self.span
  }
}

/// A `BuiltinTy` is a particular type of `Builtin`.
///
/// Because both `Self` and `self` are reserved words in Rust, we spell that
/// variant as `Zelf`.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum BuiltinTy {
  /// `self`, the value of the nearest enclosing object literal, or the receiver
  /// of a method call: `foo.bar(..)`.
  Zelf,
  /// `super`, super object of `self` (or null, if it doesn't exist).
  Super,
  /// `top`, the file-level scope object.
  Top,
  /// `here`, the current scope object against which all variable lookups
  /// are made.
  Here,
  /// `std`, the special standard library object.
  Std,
  /// `it`, used in `do` expressions.
  It,
}

/// A `Builtin` represents a literal reserved name has special meaning as
/// an expression and cannot be used for variable declarations.
#[derive(Copy, Clone, Debug)]
pub struct Builtin<'i> {
  /// The type of builtin this literal represents.
  pub ty: BuiltinTy,
  /// This AST node's span.
  pub span: Span<'i>,
}

impl<'i> Spanned<'i> for Builtin<'i> {
  fn span(&self) -> Span<'i> {
    self.span
  }
}

/// A `List` represents a list literal, with the syntax
/// ```text
/// [expr1, expr2, expr3]
/// ```
#[derive(Copy, Clone, Debug)]
pub struct List<'i> {
  /// The values that this list, when evaluated, should contain.
  pub values: &'i [Expr<'i>],
  /// This AST node's span.
  pub span: Span<'i>,
}

impl<'i> Spanned<'i> for List<'i> {
  fn span(&self) -> Span<'i> {
    self.span
  }
}

/// A `KvType` is a type of key-value binding.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[allow(missing_docs)]
pub enum KvType {
  Normal,
  Super,
  MaybeSuper,
}

/// A `Kv` represents a key-value pair, for use as fields in objects; it is
/// not an expression. It has the syntaxes
/// ```text
/// ident: expr
/// "string literal": expr
/// [key_expr]: expr
/// ```
///
/// The first variant should be represented as a `Str` with `is_quoted`
/// false, rather than an identifier.
#[derive(Copy, Clone, Debug)]
pub struct Kv<'i, V> {
  /// The key associated with this pair.
  pub key: Expr<'i>,
  /// The value associated with this pair.
  pub value: V,
  /// The type of key-value: normal, `super`, or `super?`.
  pub ty: KvType,
  /// Whether this pair ignores null values.
  pub nullable: bool,
  /// This AST node's span.
  pub span: Span<'i>,
}

impl<'i, V> Spanned<'i> for Kv<'i, V> {
  fn span(&self) -> Span<'i> {
    self.span
  }
}

/// A `Object` represents an object literal, possibly with a "super" object
/// that it is extending. It has the syntaxes
/// ```text
/// { key: value, key: value }
/// expr { key: value, key: value }
/// ```
#[derive(Copy, Clone, Debug)]
pub struct Object<'i> {
  /// The super expression for this object, if it has one.
  pub zuper: Option<&'i Expr<'i>>,
  /// The fields this object is being initialized with.
  pub fields: &'i [Kv<'i, Expr<'i>>],
  /// This AST node's span.
  pub span: Span<'i>,
}

impl<'i> Spanned<'i> for Object<'i> {
  fn span(&self) -> Span<'i> {
    self.span
  }
}

/// A `Block` represents a block expression, i.e., a sequence of `Let` bindings
/// ending in an expression. It has the syntax
/// ```text
/// {
///   let var = expr;
///   let var = expr;
///   expr
/// }
/// ```
#[derive(Copy, Clone, Debug)]
pub struct Block<'i> {
  /// The bindings to execute in preparation for the final expression.
  pub lets: &'i [Let<'i>],
  /// The final expression to evaluate and return.
  pub value: &'i Expr<'i>,
  /// This AST node's span.
  pub span: Span<'i>,
}

impl<'i> Spanned<'i> for Block<'i> {
  fn span(&self) -> Span<'i> {
    self.span
  }
}

/// A `Fn` represents a function literal, which includes argument names and a
/// body. It has syntaxes
/// ```text
/// fn foo(a, b, c) { .. }
/// fn(a, b, c) expr
/// ```
///
/// The former is actually a `Let` which has a `Fn` as its value.
#[derive(Copy, Clone, Debug)]
pub struct Fn<'i> {
  /// The name of this `Fn`, if it has one.
  pub name: Option<Ident<'i>>,
  /// The declared argument names.
  pub args: &'i [Pat<'i>],
  /// The body, to be evaluated after the argument names are bound.
  pub body: &'i Expr<'i>,
  /// This AST node's span.
  pub span: Span<'i>,
}

impl<'i> Spanned<'i> for Fn<'i> {
  fn span(&self) -> Span<'i> {
    self.span
  }
}

/// An `If` represents a `if` expression, consisting of a sequence of
/// clause and expression pairs, and possibly an `else` block. In full
/// generality, it has syntax
/// ```text
/// if expr {
///   ...
/// } else if expr {
///   ...
/// } else {
///   ...
/// }
/// ```
#[derive(Copy, Clone, Debug)]
pub struct If<'i> {
  /// The conditioned `if` clauses in this expression.
  pub clauses: &'i [(&'i Expr<'i>, Block<'i>)],
  /// The ending `else` block, if there is one.
  pub else_block: Option<Block<'i>>,
  /// This AST node's span.
  pub span: Span<'i>,
}

impl<'i> Spanned<'i> for If<'i> {
  fn span(&self) -> Span<'i> {
    self.span
  }
}

/// A `Switch` represents a `switch` expression, which evaluates the first
/// branch whose value equals that of the argument. In full generality, it
/// has syntax
/// ```text
/// switch arg {
///   expr -> expr,
///   expr, expr -> expr,
///   else -> expr,
/// }
/// ```
#[derive(Copy, Clone, Debug)]
pub struct Switch<'i> {
  /// The value being switched on.
  pub arg: &'i Expr<'i>,
  /// The non-else clauses.
  pub clauses: &'i [SwitchClause<'i>],
  /// The optional `else` clause.
  pub else_clause: Option<&'i Expr<'i>>,
  /// This AST node's span.
  pub span: Span<'i>,
}

/// A `SwitchClause` is a non-`else` clause within a `Switch`, consisting
/// of a sequence of potential cases and the value it should evaluate to.
#[derive(Copy, Clone, Debug)]
pub struct SwitchClause<'i> {
  /// The values to potentially match on the lhs.
  pub cases: &'i [Expr<'i>],
  /// The value to evaluate and return, on the rhs.
  pub value: Expr<'i>,
}

impl<'i> Spanned<'i> for Switch<'i> {
  fn span(&self) -> Span<'i> {
    self.span
  }
}

/// A `For` represents a `for` expression, i.e., a comprehension. It has
/// the syntax
/// ```text
/// for x, y in iter {
///   ...
/// }
/// ```
#[derive(Copy, Clone, Debug)]
pub struct For<'i> {
  /// The patterns to bind during each iteration of the loop.
  pub pats: &'i [Pat<'i>],
  /// Whether failure of a pattern match should be interpreted as skipping that
  /// iteration step.
  pub is_match_required: bool,
  /// The value to iterate over.
  pub iter: &'i Expr<'i>,
  /// The body to execute, and potentially yield from.
  pub body: &'i Expr<'i>,
  /// This AST node's span.
  pub span: Span<'i>,
}

impl<'i> Spanned<'i> for For<'i> {
  fn span(&self) -> Span<'i> {
    self.span
  }
}

/// A `Yield` represents a normal `yield` expression, which builds up a
/// list from inside a `for` loop. It has syntax
/// ```text
/// yield expr
/// ```
#[derive(Copy, Clone, Debug)]
pub struct Yield<'i> {
  /// The value to yield.
  pub value: &'i Expr<'i>,
  /// This AST node's span.
  pub span: Span<'i>,
}

impl<'i> Spanned<'i> for Yield<'i> {
  fn span(&self) -> Span<'i> {
    self.span
  }
}

/// A `YieldKv` represents a key-value `yield` expression, which builds up an
/// object from inside a `for` loop. It has syntax
/// ```text
/// yield [key]: value
/// ```
#[derive(Copy, Clone, Debug)]
pub struct YieldKv<'i> {
  /// The key-value pair to yield.
  pub kv: &'i Kv<'i, Expr<'i>>,
  /// This AST node's span.
  pub span: Span<'i>,
}

impl<'i> Spanned<'i> for YieldKv<'i> {
  fn span(&self) -> Span<'i> {
    self.span
  }
}

/// A `Break` represents a `break` expression, which ends iteration in a loop.
/// A `break` may have a value to indicate that that value should replace
/// whatever the loop was in the process of yielding. It has syntaxes
/// ```text
/// break
/// break expr
/// ```
#[derive(Copy, Clone, Debug)]
pub struct Break<'i> {
  /// The value to break with, if it exists.
  pub value: Option<&'i Expr<'i>>,
  /// This AST node's span.
  pub span: Span<'i>,
}

impl<'i> Spanned<'i> for Break<'i> {
  fn span(&self) -> Span<'i> {
    self.span
  }
}

/// A `Cont` represents a `continue` expression, which moves on to th next
/// iteration in a loop.
/// ```text
/// continue
/// ```
#[derive(Copy, Clone, Debug)]
pub struct Cont<'i> {
  /// This AST node's span.
  pub span: Span<'i>,
}

impl<'i> Spanned<'i> for Cont<'i> {
  fn span(&self) -> Span<'i> {
    self.span
  }
}

/// A `Ret` represents a `return` expression, which returns a value early from
/// a function.
/// ```text
/// return expr
/// ```
#[derive(Copy, Clone, Debug)]
pub struct Ret<'i> {
  /// The value to return.
  pub value: &'i Expr<'i>,
  /// This AST node's span.
  pub span: Span<'i>,
}

impl<'i> Spanned<'i> for Ret<'i> {
  fn span(&self) -> Span<'i> {
    self.span
  }
}

/// A `Member` represents a member access, which has syntax
/// ```text
/// expr.ident
/// ```
#[derive(Copy, Clone, Debug)]
pub struct Member<'i> {
  /// The value to perform an access on.
  pub value: &'i Expr<'i>,
  /// The name of the member to access.
  pub member: &'i Expr<'i>,
  /// Whether this access is null-safe.
  pub nullable: bool,
  /// This AST node's span.
  pub span: Span<'i>,
}

impl<'i> Spanned<'i> for Member<'i> {
  fn span(&self) -> Span<'i> {
    self.span
  }
}

/// A `Call` represents a function call, which evaluates a function, a list
/// of arguments, and then calls the former with the latter. It has syntax
/// ```text
/// expr(expr, expr, expr)
/// ```
#[derive(Copy, Clone, Debug)]
pub struct Call<'i> {
  /// The function to call.
  pub fnc: &'i Expr<'i>,
  /// The arguments to evaluate and call the function with.
  pub args: &'i [Expr<'i>],
  /// This AST node's span.
  pub span: Span<'i>,
}

impl<'i> Spanned<'i> for Call<'i> {
  fn span(&self) -> Span<'i> {
    self.span
  }
}

/// An `Index` represents an indexing operation, which is syntactically
/// identical to a function call. It has syntax
/// ```text
/// expr[expr, expr, expr]
/// ```
#[derive(Copy, Clone, Debug)]
pub struct Index<'i> {
  /// The value to be indexed.
  pub value: &'i Expr<'i>,
  /// The values to index it with.
  pub args: &'i [Expr<'i>],
  /// Whether this indexing is null-safe.
  pub nullable: bool,
  /// This AST node's span.
  pub span: Span<'i>,
}

impl<'i> Spanned<'i> for Index<'i> {
  fn span(&self) -> Span<'i> {
    self.span
  }
}

/// A `Do` represents a do expression. It has syntax
/// ```text
/// expr do { foo(it) }
/// expr do? switch it { .. }
/// ```
#[derive(Copy, Clone, Debug)]
pub struct Do<'i> {
  /// The value of `it` in this block.
  pub it: &'i Expr<'i>,
  /// The calculation to perform on `it`.
  pub body: &'i Expr<'i>,
  /// Whether this `do`-expression should short-circuit on `null`.
  pub nullable: bool,
  /// This AST node's span.
  pub span: Span<'i>,
}

impl<'i> Spanned<'i> for Do<'i> {
  fn span(&self) -> Span<'i> {
    self.span
  }
}

/// An `UnOpTy` is a type of unary operation.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[allow(missing_docs)]
pub enum UnOpTy {
  Neg,
  Not,
}

impl UnOpTy {
  /// Returns the symbol corresponding to this operator.
  pub fn name(&self) -> &'static str {
    match self {
      UnOpTy::Neg => "-",
      UnOpTy::Not => "!",
    }
  }

  /// Returns whether this operator is overloadable by user code.
  pub fn overloadable(&self) -> bool {
    true
  }
}

impl fmt::Display for UnOpTy {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{}", self.name())
  }
}

/// An `UnOp` represents an unary operation, with the usual syntax.
#[derive(Copy, Clone, Debug)]
pub struct UnOp<'i> {
  /// The argument to the operation.
  pub arg: &'i Expr<'i>,
  /// The operation type.
  pub ty: UnOpTy,
  /// This AST node's span.
  pub span: Span<'i>,
}

impl<'i> Spanned<'i> for UnOp<'i> {
  fn span(&self) -> Span<'i> {
    self.span
  }
}

/// An `UnOpTy` is a type of unary operation.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[allow(missing_docs)]
pub enum BinOpTy {
  Add,
  Sub,
  Mul,
  Div,
  Rem,
  Eq,
  Ne,
  Ge,
  Le,
  Gt,
  Lt,
  AndAnd,
  OrOr,
  Elvis,
}

impl BinOpTy {
  /// Returns the symbol corresponding to this operator.
  pub fn name(&self) -> &'static str {
    match self {
      BinOpTy::Add => "+",
      BinOpTy::Sub => "-",
      BinOpTy::Mul => "*",
      BinOpTy::Div => "/",
      BinOpTy::Rem => "%",
      BinOpTy::Eq => "==",
      BinOpTy::Ne => "!=",
      BinOpTy::Ge => ">=",
      BinOpTy::Le => "<=",
      BinOpTy::Gt => ">",
      BinOpTy::Lt => "<",
      BinOpTy::AndAnd => "&&",
      BinOpTy::OrOr => "||",
      BinOpTy::Elvis => "??",
    }
  }

  /// Returns whether this operator is overloadable by user code.
  pub fn overloadable(&self) -> bool {
    matches!(
      self,
      BinOpTy::Add
        | BinOpTy::Sub
        | BinOpTy::Mul
        | BinOpTy::Div
        | BinOpTy::Rem
        | BinOpTy::Eq
    )
  }
}

impl fmt::Display for BinOpTy {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{}", self.name())
  }
}

/// An `BinOp` represents an unary operation, with the usual syntax.
#[derive(Copy, Clone, Debug)]
pub struct BinOp<'i> {
  /// The left-hand-side of the operation.
  pub lhs: &'i Expr<'i>,
  /// The right-hand-side of the operation.
  pub rhs: &'i Expr<'i>,
  /// The operation type.
  pub ty: BinOpTy,
  /// This AST node's span.
  pub span: Span<'i>,
}

impl<'i> Spanned<'i> for BinOp<'i> {
  fn span(&self) -> Span<'i> {
    self.span
  }
}
