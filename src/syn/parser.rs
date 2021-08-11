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

//! The nuts and bolts of the Alkyne parser.

#![allow(clippy::upper_case_acronyms)]

use std::fmt;
use std::mem;
use std::path::Path;

use pest::error::ErrorVariant;
use pest::error::InputLocation;
use pest::iterators::Pair;
use pest::Position;

use pest_derive::Parser;

use crate::syn;
use crate::syn::Span;
use crate::syn::Spanned as _;

/// A `ParseError` represents a parse failure at some `Span`.
#[derive(Clone, Debug)]
pub struct ParseError<'i> {
  /// The `Span` at which the error occured.
  pub span: Span<'i>,
  /// An error message.
  pub message: String,
}

impl fmt::Display for ParseError<'_> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    writeln!(f, "error: {}", self.message)
  }
}

/// Parse `src` into a `Unit`, returning an error on failure.
pub fn parse<'i>(
  file_name: &'i Path,
  input: &'i str,
  arena: &'i syn::Arena,
) -> Result<&'i syn::Unit<'i>, ParseError<'i>> {
  use pest::Parser as _;
  let ctx = Context {
    file_name,
    input,
    arena,
  };

  let mut pairs = match PegParser::parse(Rule::Unit, input) {
    Ok(pair) => pair,
    Err(err) => {
      let span = match err.location {
        InputLocation::Pos(pos) => {
          let pos = Position::new(input, pos).unwrap();
          pos.span(&pos)
        }
        InputLocation::Span((start, end)) => {
          let start = Position::new(input, start).unwrap();
          let end = Position::new(input, end).unwrap();
          start.span(&end)
        }
      };

      let message = match err.variant {
        ErrorVariant::ParsingError {
          positives,
          negatives,
        } => format!("positives: {:?}, negatives: {:?}", positives, negatives),
        _ => "parse error".to_string(),
      };

      return Err(syn::ParseError {
        span: ctx.span(span),
        message,
      });
    }
  };

  Ok(ctx.arena.alloc(ctx.parse_unit(pairs.next().unwrap())))
}

#[derive(Parser)]
#[grammar = "syn/alkyne.pest"]
struct PegParser;

struct Context<'i> {
  file_name: &'i Path,
  input: &'i str,
  arena: &'i toolshed::Arena,
}

impl<'i> Context<'i> {
  fn span(&self, span: pest::Span<'i>) -> Span<'i> {
    syn::Span::new_from_parts(
      self.file_name,
      self.input,
      (span.start(), span.end()),
    )
  }

  fn zero_span(&self) -> Span<'i> {
    syn::Span::new_from_parts(self.file_name, self.input, (0, 0))
  }

  fn parse_unit(&self, pair: Pair<'i, Rule>) -> syn::Unit<'i> {
    let mut imports = Vec::new();
    let mut stmts = Vec::new();

    let mut value = None;
    for pair in pair.into_inner() {
      let span = self.span(pair.as_span());
      match pair.as_rule() {
        Rule::Import => {
          let mut pairs = pair.into_inner();
          let _use = pairs.next();
          let name_pair = pairs.next().unwrap();
          let name = syn::Ident {
            name: name_pair.as_str(),
            span: self.span(name_pair.as_span()),
          };
          let _eq = pairs.next();
          let str = match self.parse_expr(pairs.next().unwrap()) {
            syn::Expr::Str(s) => s,
            _ => unreachable!(),
          };

          imports.push(syn::Use {
            var: name,
            import: str,
            span,
          })
        }
        Rule::Stmt => {
          if let Some(stmt) = self.parse_stmt(pair) {
            stmts.push(stmt)
          }
        }
        Rule::Expr => {
          value = Some(self.parse_expr(pair));
          break;
        }
        Rule::EOI => break,
        r => panic!("unexpected rule: {:?}", r),
      }
    }
    // We never got a final expression, so we make one up, either from a floating
    // statement or just a null.
    let value = match value {
      Some(value) => value,
      None => {
        if let Some(syn::Let {
          is_floating: true, ..
        }) = stmts.last()
        {
          stmts.pop().unwrap().value
        } else {
          syn::Expr::Null(syn::Null {
            // TODO(mcyoung): pick a better span.
            span: self.zero_span(),
          })
        }
      }
    };
    syn::Unit {
      imports: self.arena.alloc_vec(imports),
      stmts: self.arena.alloc_vec(stmts),
      value,
    }
  }

  fn parse_expr(&self, pair: Pair<'i, Rule>) -> syn::Expr<'i> {
    let span = self.span(pair.as_span());
    match pair.as_rule() {
      Rule::Null => syn::Expr::Null(syn::Null { span }),
      Rule::True => syn::Expr::Bool(syn::Bool { value: true, span }),
      Rule::False => syn::Expr::Bool(syn::Bool { value: false, span }),
      Rule::Number => syn::Expr::Num(syn::Num {
        // TODO: don't just unwrap!
        value: pair.as_str().parse::<f64>().unwrap(),
        span,
      }),
      Rule::String => syn::Expr::Str(syn::Str {
        value: pair.as_str(),
        is_quoted: true,
        span,
      }),
      Rule::Ident => syn::Expr::Ref(syn::Ident {
        name: pair.as_str(),
        span,
      }),
      Rule::Zelf => syn::Expr::Builtin(syn::Builtin {
        ty: syn::BuiltinTy::Zelf,
        span,
      }),
      Rule::Super => syn::Expr::Builtin(syn::Builtin {
        ty: syn::BuiltinTy::Super,
        span,
      }),
      Rule::Top => syn::Expr::Builtin(syn::Builtin {
        ty: syn::BuiltinTy::Top,
        span,
      }),
      Rule::Here => syn::Expr::Builtin(syn::Builtin {
        ty: syn::BuiltinTy::Here,
        span,
      }),
      Rule::Std => syn::Expr::Builtin(syn::Builtin {
        ty: syn::BuiltinTy::Std,
        span,
      }),
      Rule::It => syn::Expr::Builtin(syn::Builtin {
        ty: syn::BuiltinTy::It,
        span,
      }),
      Rule::List => syn::Expr::List(syn::List {
        values: self
          .arena
          .alloc_vec(pair.into_inner().map(|p| self.parse_expr(p)).collect()),
        span,
      }),
      Rule::Object => syn::Expr::Object(syn::Object {
        zuper: None,
        fields: self
          .arena
          .alloc_vec(pair.into_inner().map(|p| self.parse_kv(p)).collect()),
        span,
      }),
      Rule::Block => {
        let mut stmts = Vec::new();
        let mut value = None;
        for pair in pair.into_inner() {
          match pair.as_rule() {
            Rule::Stmt => {
              if let Some(stmt) = self.parse_stmt(pair) {
                stmts.push(stmt)
              }
            }
            Rule::Expr => {
              value = Some(self.parse_expr(pair));
              break;
            }
            r => panic!("unexpected rule: {:?}", r),
          }
        }
        let value = match value {
          Some(value) => value,
          None => {
            if let Some(syn::Let {
              is_floating: true, ..
            }) = stmts.last()
            {
              stmts.pop().unwrap().value
            } else {
              syn::Expr::Null(syn::Null {
                // TODO(mcyoung): pick a better span.
                span,
              })
            }
          }
        };
        syn::Expr::Block(syn::Block {
          lets: self.arena.alloc_vec(stmts),
          value: self.arena.alloc(value),
          span,
        })
      }
      Rule::FnLit => {
        let mut args = Vec::new();
        for pair in pair.into_inner() {
          match pair.as_rule() {
            Rule::Fn => {}
            Rule::Pat => args.push(self.parse_pat(pair)),
            Rule::Expr => {
              return syn::Expr::Fn(syn::Fn {
                name: None,
                args: self.arena.alloc_vec(args),
                body: self.arena.alloc(self.parse_expr(pair)),
                span,
              })
            }
            r => panic!("unexpected rule: {:?}", r),
          }
        }
        unreachable!()
      }
      Rule::IfExpr => {
        let mut clauses = Vec::new();
        let mut else_block = None;
        let mut pairs = pair.into_inner();
        while let Some(mut kw) = pairs.next() {
          if kw.as_rule() == Rule::Else {
            kw = pairs.next().unwrap();
          }
          match kw.as_rule() {
            Rule::If => {
              let cond = self.parse_expr(pairs.next().unwrap());
              let block = match self.parse_expr(pairs.next().unwrap()) {
                syn::Expr::Block(b) => b,
                _ => unreachable!(),
              };
              clauses.push((&*self.arena.alloc(cond), block))
            }
            Rule::Block => {
              let block = match self.parse_expr(kw) {
                syn::Expr::Block(b) => b,
                _ => unreachable!(),
              };
              else_block = Some(block)
            }
            r => panic!("unexpected rule: {:?}", r),
          }
        }
        syn::Expr::If(syn::If {
          clauses: self.arena.alloc_vec(clauses),
          else_block,
          span,
        })
      }
      Rule::SwitchExpr => {
        let mut clauses = Vec::new();
        let mut else_clause = None;
        let mut cases = Vec::new();

        let mut pairs = pair.into_inner();
        let _switch = pairs.next();
        let arg = self.parse_expr(pairs.next().unwrap());
        while let Some(pair) = pairs.next() {
          match pair.as_rule() {
            Rule::Expr => cases.push(self.parse_expr(pair)),
            Rule::Arrow => {
              let clause = pairs.next().unwrap();
              let value = self.parse_expr(clause);
              clauses.push(syn::SwitchClause {
                cases: self.arena.alloc_vec(mem::take(&mut cases)),
                value,
              });
            }
            Rule::Else => {
              let _arrow = pairs.next();
              else_clause = Some(
                &*self.arena.alloc(self.parse_expr(pairs.next().unwrap())),
              );
            }
            r => panic!("unexpected rule: {:?}", r),
          }
        }
        syn::Expr::Switch(syn::Switch {
          arg: self.arena.alloc(arg),
          clauses: self.arena.alloc_vec(clauses),
          else_clause,
          span,
        })
      }
      Rule::ForYield | Rule::ForExpr => {
        let mut pats = Vec::new();
        let mut pairs = pair.into_inner();
        let _for = pairs.next();
        while let Some(pair) = pairs.next() {
          match pair.as_rule() {
            Rule::Pat => pats.push(self.parse_pat(pair)),
            Rule::In => break,
            r => panic!("unexpected rule: {:?}", r),
          }
        }
        let is_match_required =
          pairs.peek().unwrap().as_rule() != Rule::Question;
        if !is_match_required {
          let _ = pairs.next();
        }
        let iter = self.parse_expr(pairs.next().unwrap());
        let body = self.parse_expr(pairs.next().unwrap());

        syn::Expr::For(syn::For {
          pats: self.arena.alloc_vec(pats),
          is_match_required,
          iter: self.arena.alloc(iter),
          body: self.arena.alloc(body),
          span,
        })
      }
      Rule::YieldVal => {
        let mut pairs = pair.into_inner();
        let _yield = pairs.next();
        let value = self.parse_expr(pairs.next().unwrap());

        syn::Expr::Yield(syn::Yield {
          value: self.arena.alloc(value),
          span,
        })
      }
      Rule::YieldKv => {
        let mut pairs = pair.into_inner();
        let _yield = pairs.next();
        let kv = self.parse_kv(pairs.next().unwrap());

        syn::Expr::YieldKv(syn::YieldKv {
          kv: self.arena.alloc(kv),
          span,
        })
      }
      Rule::BreakExpr => {
        let mut pairs = pair.into_inner();
        let _break = pairs.next();
        let value =
          pairs.next().map(|p| &*self.arena.alloc(self.parse_expr(p)));

        syn::Expr::Break(syn::Break { value, span })
      }
      Rule::Cont => syn::Expr::Cont(syn::Cont { span }),
      Rule::RetExpr => {
        let mut pairs = pair.into_inner();
        let _return = pairs.next();
        let value = self.parse_expr(pairs.next().unwrap());

        syn::Expr::Ret(syn::Ret {
          value: self.arena.alloc(value),
          span,
        })
      }
      Rule::SufExpr => {
        let mut pairs = pair.into_inner();
        let mut expr = self.parse_expr(pairs.next().unwrap());
        for suf in pairs {
          let span = Span::join(expr.span(), self.span(suf.as_span()));
          match suf.as_rule() {
            Rule::Member => {
              let mut suf = suf.into_inner();
              let nullable = match suf.peek().map(|p| p.as_rule()) {
                Some(Rule::Question) => {
                  let _ = suf.next();
                  true
                }
                _ => false,
              };
              let field = suf.next().unwrap();
              let field_expr = match field.as_rule() {
                Rule::Ident => syn::Str {
                  value: field.as_str(),
                  is_quoted: false,
                  span: self.span(field.as_span()),
                },
                Rule::String => syn::Str {
                  value: field.as_str(),
                  is_quoted: true,
                  span: self.span(field.as_span()),
                },
                r => panic!("unexpected rule: {:?}", r),
              };
              expr = syn::Expr::Member(syn::Member {
                value: self.arena.alloc(expr),
                member: self.arena.alloc(syn::Expr::Str(field_expr)),
                nullable,
                span,
              })
            }
            Rule::Call => {
              let args = suf.into_inner().map(|p| self.parse_expr(p)).collect();
              expr = syn::Expr::Call(syn::Call {
                fnc: self.arena.alloc(expr),
                args: self.arena.alloc_vec(args),
                span,
              })
            }
            Rule::Index => {
              let mut suf = suf.into_inner();
              let nullable = match suf.peek().map(|p| p.as_rule()) {
                Some(Rule::Question) => {
                  let _ = suf.next();
                  true
                }
                _ => false,
              };
              let args = suf.map(|p| self.parse_expr(p)).collect();
              expr = syn::Expr::Index(syn::Index {
                value: self.arena.alloc(expr),
                args: self.arena.alloc_vec(args),
                nullable,
                span,
              })
            }
            Rule::DoExpr => {
              let mut suf = suf.into_inner();
              let _do = suf.next();
              let nullable = match suf.peek().map(|p| p.as_rule()) {
                Some(Rule::Question) => {
                  let _ = suf.next();
                  true
                }
                _ => false,
              };
              let body = self.parse_expr(suf.next().unwrap());
              expr = syn::Expr::Do(syn::Do {
                it: self.arena.alloc(expr),
                body: self.arena.alloc(body),
                nullable,
                span,
              })
            }
            Rule::Object => {
              let fields = suf.into_inner().map(|p| self.parse_kv(p)).collect();
              expr = syn::Expr::Object(syn::Object {
                zuper: Some(self.arena.alloc(expr)),
                fields: self.arena.alloc_vec(fields),
                span,
              })
            }
            r => panic!("unexpected rule: {:?}", r),
          }
        }
        expr
      }
      Rule::UnaryExpr => {
        let mut pairs = pair.into_inner().rev();
        let mut expr = self.parse_expr(pairs.next().unwrap());
        for op in pairs {
          let op_ty = match op.as_rule() {
            Rule::Dash => syn::UnOpTy::Neg,
            Rule::Bang => syn::UnOpTy::Not,
            r => panic!("unexpected rule: {:?}", r),
          };
          let op_span = self.span(op.as_span());
          let span = Span::join(op_span, expr.span());
          expr = syn::Expr::UnOp(syn::UnOp {
            arg: self.arena.alloc(expr),
            ty: op_ty,
            span,
          });
        }
        expr
      }
      Rule::ElvisExpr
      | Rule::AndExpr
      | Rule::OrExpr
      | Rule::EqExpr
      | Rule::OrdExpr
      | Rule::SumExpr
      | Rule::ProdExpr => {
        let mut pairs = pair.into_inner();
        let mut expr = self.parse_expr(pairs.next().unwrap());
        while let Some(op) = pairs.next() {
          let op_ty = match op.as_rule() {
            Rule::Plus => syn::BinOpTy::Add,
            Rule::Dash => syn::BinOpTy::Sub,
            Rule::Star => syn::BinOpTy::Mul,
            Rule::Slash => syn::BinOpTy::Div,
            Rule::Pct => syn::BinOpTy::Rem,
            Rule::AndAnd => syn::BinOpTy::AndAnd,
            Rule::OrOr => syn::BinOpTy::OrOr,
            Rule::EqEq => syn::BinOpTy::Eq,
            Rule::NeEq => syn::BinOpTy::Ne,
            Rule::Gt => syn::BinOpTy::Gt,
            Rule::Lt => syn::BinOpTy::Lt,
            Rule::GtEq => syn::BinOpTy::Ge,
            Rule::LtEq => syn::BinOpTy::Le,
            Rule::Elvis => syn::BinOpTy::Elvis,
            r => panic!("unknown rule: {:?}", r),
          };
          let rhs = self.parse_expr(pairs.next().unwrap());
          let span = Span::join(expr.span(), rhs.span());
          expr = syn::Expr::BinOp(syn::BinOp {
            lhs: self.arena.alloc(expr),
            rhs: self.arena.alloc(rhs),
            ty: op_ty,
            span,
          })
        }
        expr
      }
      Rule::Parens | Rule::Expr => {
        self.parse_expr(pair.into_inner().next().unwrap())
      }
      r => panic!("unknown rule: {:?}", r),
    }
  }

  fn parse_stmt(&self, pair: Pair<'i, Rule>) -> Option<syn::Let<'i>> {
    let span = self.span(pair.as_span());
    let stmt = match pair.as_rule() {
      Rule::LetStmt => {
        let mut pairs = pair.into_inner();
        let _let = pairs.next();
        let pat = self.parse_pat(pairs.next().unwrap());
        let _eq = pairs.next();
        let value = self.parse_expr(pairs.next().unwrap());
        syn::Let {
          pat: Some(&*self.arena.alloc(pat)),
          is_floating: false,
          value,
          span,
        }
      }
      Rule::FnStmt => {
        let mut args = Vec::new();
        let mut pairs = pair.into_inner();
        let _fn = pairs.next();
        let name_pair = pairs.next().unwrap();
        let name = syn::Ident {
          name: name_pair.as_str(),
          span: self.span(name_pair.as_span()),
        };
        for pair in pairs {
          match pair.as_rule() {
            Rule::Pat => args.push(self.parse_pat(pair)),
            Rule::Eq => {}
            _ => {
              let body = self.parse_expr(pair);
              let fnc = syn::Expr::Fn(syn::Fn {
                name: Some(name),
                args: self.arena.alloc_vec(args),
                body: self.arena.alloc(body),
                span,
              });
              return Some(syn::Let {
                pat: Some(&*self.arena.alloc(syn::Pat::Bind(name))),
                is_floating: false,
                value: fnc,
                span,
              });
            }
          }
        }
        unreachable!()
      }
      Rule::ExprStmt => syn::Let {
        pat: None,
        is_floating: false,
        value: self.parse_expr(pair.into_inner().next().unwrap()),
        span,
      },
      Rule::Stmt => {
        if let Some(pair) = pair.into_inner().next() {
          return self.parse_stmt(pair);
        } else {
          return None;
        }
      }
      _ => syn::Let {
        pat: None,
        is_floating: true,
        value: self.parse_expr(pair),
        span,
      },
    };
    Some(stmt)
  }

  fn parse_pat(&self, pair: Pair<'i, Rule>) -> syn::Pat<'i> {
    let span = self.span(pair.as_span());
    match pair.as_rule() {
      Rule::LiteralPat => {
        syn::Pat::Expr(self.parse_expr(pair.into_inner().next().unwrap()))
      }
      Rule::BindPat => {
        let mut pairs = pair.into_inner();
        let name_pair = pairs.next().unwrap();
        let name = syn::Ident {
          name: name_pair.as_str(),
          span,
        };
        syn::Pat::Bind(name)
      }
      Rule::ExactListPat => syn::Pat::ExactList(syn::ExactListPat {
        pats: self
          .arena
          .alloc_vec(pair.into_inner().map(|p| self.parse_pat(p)).collect()),
        span,
      }),
      Rule::GlobListPat => {
        let mut front = Vec::new();
        let mut back = Vec::new();
        let mut middle = None;

        let mut has_seen_dotdot = false;
        let mut pairs = pair.into_inner();
        while let Some(pair) = pairs.next() {
          if let Rule::DotDot = pair.as_rule() {
            has_seen_dotdot = true;
            if let Some(Rule::Ident) = pairs.peek().map(|p| p.as_rule()) {
              let name_pair = pairs.next().unwrap();
              middle = Some(syn::Ident {
                name: name_pair.as_str(),
                span,
              });
            }
            continue;
          }

          let pat = self.parse_pat(pair);
          if !has_seen_dotdot {
            front.push(pat);
          } else {
            back.push(pat);
          }
        }

        syn::Pat::GlobList(syn::GlobListPat {
          front: self.arena.alloc_vec(front),
          middle,
          back: self.arena.alloc_vec(back),
          span,
        })
      }
      Rule::ObjectPat => {
        let mut fields = Vec::new();
        let mut is_exact = true;
        for pair in pair.into_inner() {
          match pair.as_rule() {
            Rule::DotDot => is_exact = false,
            Rule::KvPat => {
              let span = self.span(pair.as_span());

              let mut inner = pair.into_inner();
              let key = inner.next().unwrap();
              let nullable = match inner.peek().map(|p| p.as_rule()) {
                Some(Rule::Question) => {
                  let _ = inner.next();
                  true
                }
                _ => false,
              };
              let val = inner.next();

              let key_expr = match key.as_rule() {
                Rule::Ident => syn::Expr::Str(syn::Str {
                  value: key.as_str(),
                  is_quoted: false,
                  span: self.span(key.as_span()),
                }),
                Rule::String => syn::Expr::Str(syn::Str {
                  value: key.as_str(),
                  is_quoted: true,
                  span: self.span(key.as_span()),
                }),
                r => panic!("unexpected rule: {:?}", r),
              };

              let val_pat = val.map(|v| self.parse_pat(v));

              fields.push(syn::Kv {
                key: key_expr,
                value: val_pat,
                ty: syn::KvType::Normal,
                nullable,
                span,
              })
            }
            r => panic!("unexpected rule: {:?}", r),
          }
        }

        syn::Pat::Object(syn::ObjectPat {
          fields: self.arena.alloc_vec(fields),
          is_exact,
          span,
        })
      }
      Rule::OrPat => {
        let pairs = pair.into_inner();
        let mut pats = Vec::new();

        for pair in pairs {
          if let Rule::Or = pair.as_rule() {
            continue;
          }

          pats.push(self.parse_pat(pair));
        }
        if pats.len() == 1 {
          return pats.pop().unwrap();
        }
        syn::Pat::Or(syn::OrPat {
          pats: self.arena.alloc_vec(pats),
          span,
        })
      }
      Rule::AtPat => {
        let mut idents = Vec::new();
        for pair in pair.into_inner() {
          match pair.as_rule() {
            Rule::Ident => {
              let name = syn::Ident {
                name: pair.as_str(),
                span,
              };
              idents.push(name);
            }
            _ => {
              let mut pat = self.parse_pat(pair);
              for ident in idents.into_iter().rev() {
                let span = Span::join(ident.span(), pat.span());
                pat = syn::Pat::At(syn::AtPat {
                  pat: self.arena.alloc(pat),
                  ident,
                  span,
                })
              }
              return pat;
            }
          }
        }
        unreachable!()
      }
      Rule::ParenPat | Rule::Pat => {
        self.parse_pat(pair.into_inner().next().unwrap())
      }
      r => panic!("unexpected rule: {:?}", r),
    }
  }

  fn parse_kv(&self, pair: Pair<'i, Rule>) -> syn::Kv<'i, syn::Expr<'i>> {
    let span = self.span(pair.as_span());

    let mut inner = pair.into_inner();
    let key = inner.next().unwrap();
    let nullable = match inner.peek().map(|p| p.as_rule()) {
      Some(Rule::Question) => {
        let _ = inner.next();
        true
      }
      _ => false,
    };
    let val = inner.next().unwrap();

    let mut key_inner = key.into_inner();
    let mut ty = syn::KvType::Normal;
    if let Some(Rule::Super) = key_inner.peek().map(|p| p.as_rule()) {
      ty = syn::KvType::Super;
      let _ = key_inner.next();
      if let Some(Rule::Question) = key_inner.peek().map(|p| p.as_rule()) {
        ty = syn::KvType::MaybeSuper;
        let _ = key_inner.next();
      }
    }

    let key_pair = key_inner.next().unwrap();
    let key_expr = match key_pair.as_rule() {
      Rule::Ident => syn::Expr::Str(syn::Str {
        value: key_pair.as_str(),
        is_quoted: false,
        span: self.span(key_pair.as_span()),
      }),
      Rule::String => syn::Expr::Str(syn::Str {
        value: key_pair.as_str(),
        is_quoted: true,
        span: self.span(key_pair.as_span()),
      }),
      Rule::Expr => self.parse_expr(key_pair),
      _ => panic!("unexpected rule: {:?}", key_pair.as_rule()),
    };

    let val_expr = self.parse_expr(val);

    syn::Kv {
      key: key_expr,
      value: val_expr,
      ty,
      nullable,
      span,
    }
  }
}
