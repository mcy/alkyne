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

//! Alkyne-like encoding for Alkyne values.

use std::collections::HashSet;

use crate::eval::encode::Context;
use crate::eval::encode::Encode;
use crate::eval::encode::EncodeError;
use crate::eval::encode::PathComponent;
use crate::eval::escaping;
use crate::eval::value::DebugInfo;
use crate::eval::value::Value;

#[derive(Default)]
pub struct UclEncoding(());

impl<'i> Encode<'i> for UclEncoding {
  fn encode(
    mut ctx: Context<Self>,
    val: &Value<'i>,
  ) -> Result<(), EncodeError<'i>> {
    use std::fmt::Write;
    match val {
      Value::Null => {
        let _ = write!(ctx.buf(), "null");
      }
      Value::Bool(b) => {
        let _ = write!(ctx.buf(), "{}", b);
      }
      Value::Number(n) => {
        let _ = write!(ctx.buf(), "{}", n);
      }
      Value::String(s) => {
        escaping::escape_alkyne_string(s.as_ref(), false, ctx.buf());
      }
      Value::List(val) => {
        let _ = write!(ctx.buf(), "[");
        for (i, v) in val.iter().enumerate() {
          if i != 0 {
            let _ = write!(ctx.buf(), ", ");
          }
          match ctx.recurse(PathComponent::Index(i), v) {
            Ok(()) => {}
            Err(EncodeError::Cycle { .. }) => {
              let _ = write!(ctx.buf(), "<cycle>");
            }
            e @ Err(_) => return e,
          }
        }
        let _ = write!(ctx.buf(), "]");
      }
      Value::Object(val) => {
        let mut first = true;
        let _ = write!(ctx.buf(), "{{");
        // Ensure that we only encode the *latest* version of a particular
        // key.
        let mut encoded_keys = HashSet::new();
        for (k, v, _) in val.iter() {
          if encoded_keys.contains(&*k) {
            continue;
          }
          encoded_keys.insert(&*k);

          if !first {
            let _ = write!(ctx.buf(), ", ");
          } else {
            let _ = write!(ctx.buf(), " ");
          }
          first = false;

          escaping::escape_alkyne_string(k, true, ctx.buf());
          let _ = write!(ctx.buf(), ": ");
          match ctx.recurse(PathComponent::Ident(k.to_string()), v) {
            Ok(()) => {}
            Err(EncodeError::Cycle { .. }) => {
              let _ = write!(ctx.buf(), "<cycle>");
            }
            e @ Err(_) => return e,
          }
        }
        if !first {
          let _ = write!(ctx.buf(), " ");
        }
        let _ = write!(ctx.buf(), "}}");
      }
      Value::Fn(fnc) => {
        let _ = write!(ctx.buf(), "{}", fnc);
      }
      Value::NativeFn(fnc) => {
        let _ = write!(ctx.buf(), "{}", fnc);
      }
      Value::Std => {
        let _ = write!(ctx.buf(), "<std>");
      }
      _ => {
        let _ = write!(ctx.buf(), "<opaque>");
      }
    }
    Ok(())
  }
}

#[derive(Default)]
pub struct VerboseEncoding {
  indent: usize,
}

impl<'i> Encode<'i> for VerboseEncoding {
  fn encode(
    mut ctx: Context<Self>,
    val: &Value<'i>,
  ) -> Result<(), EncodeError<'i>> {
    use std::fmt::Write;
    match val {
      Value::Null => {
        let _ = write!(ctx.buf(), "{}null", ().debug_info());
      }
      Value::Bool(b) => {
        let _ = write!(ctx.buf(), "{}{}", b.debug_info(), b);
      }
      Value::Number(n) => {
        let _ = write!(ctx.buf(), "{}{}", n.debug_info(), n);
      }
      Value::String(s) => {
        let _ = write!(ctx.buf(), "{}", s.debug_info());
        escaping::escape_alkyne_string(s.as_ref(), false, ctx.buf());
      }
      Value::List(val) => {
        let _ = write!(ctx.buf(), "{}", val.debug_info());
        let _ = write!(ctx.buf(), "[");

        let indent = "  ".repeat(ctx.indent);
        ctx.indent += 1;

        for (i, v) in val.iter().enumerate() {
          if i == 0 {
            let _ = writeln!(ctx.buf());
          }
          let _ = write!(ctx.buf(), "{}  [{}]: ", indent, i);
          match ctx.recurse(PathComponent::Index(i), v) {
            Ok(()) => {}
            Err(EncodeError::Cycle { .. }) => {
              let _ = write!(ctx.buf(), "<cycle>");
            }
            e @ Err(_) => return e,
          }

          let _ = writeln!(ctx.buf(), ",");
        }

        if !val.is_empty() {
          let _ = write!(ctx.buf(), "{}", indent);
        }

        ctx.indent -= 1;
        let _ = write!(ctx.buf(), "]");
      }
      Value::Object(val) => {
        let _ = write!(ctx.buf(), "{}", val.debug_info());
        let _ = write!(ctx.buf(), "{{");
        let indent = "  ".repeat(ctx.indent);
        ctx.indent += 1;

        let mut looped = false;
        for (k, v, o) in val.iter() {
          looped = true;
          let _ = writeln!(ctx.buf());

          let _ = write!(ctx.buf(), "{}  key: {}", indent, k.debug_info());
          escaping::escape_alkyne_string(k, false, ctx.buf());
          let _ = writeln!(ctx.buf(), ",");

          let _ = write!(ctx.buf(), "{}  val: ", indent);
          match ctx.recurse(PathComponent::Ident(k.to_string()), v) {
            Ok(()) => {}
            Err(EncodeError::Cycle { .. }) => {
              let _ = write!(ctx.buf(), "<cycle>");
            }
            e @ Err(_) => return e,
          }
          let _ = writeln!(ctx.buf(), ",");

          let _ =
            writeln!(ctx.buf(), "{}  own: {}{{..}},", indent, o.debug_info());
        }

        ctx.indent -= 1;
        if looped {
          let _ = write!(ctx.buf(), "{}", indent);
        }
        let _ = write!(ctx.buf(), "}}");
      }
      Value::Fn(fnc) => {
        let indent = "  ".repeat(ctx.indent);
        let _ = writeln!(ctx.buf(), "<{}>{{", fnc);
        ctx.indent += 1;

        let _ = writeln!(ctx.buf(), "{}  src: {:p},", indent, fnc.src());

        let _ = write!(ctx.buf(), "{}  name: ", indent);
        match ctx.recurse(
          PathComponent::Ident("name".to_string()),
          &fnc.name().map(Value::String).unwrap_or(Value::Null),
        ) {
          Ok(()) => {}
          Err(EncodeError::Cycle { .. }) => {
            let _ = write!(ctx.buf(), "<cycle>");
          }
          e @ Err(_) => return e,
        }
        let _ = writeln!(ctx.buf(), ",");

        let _ = write!(ctx.buf(), "{}  self: ", indent);
        match ctx.recurse(
          PathComponent::Ident("self".to_string()),
          &fnc.referent().map(Value::Object).unwrap_or(Value::Null),
        ) {
          Ok(()) => {}
          Err(EncodeError::Cycle { .. }) => {
            let _ = write!(ctx.buf(), "<cycle>");
          }
          e @ Err(_) => return e,
        }
        let _ = writeln!(ctx.buf(), ",");

        let _ = write!(ctx.buf(), "{}  here: ", indent);
        match ctx.recurse(
          PathComponent::Ident("here".to_string()),
          &Value::Object(fnc.captures()),
        ) {
          Ok(()) => {}
          Err(EncodeError::Cycle { .. }) => {
            let _ = write!(ctx.buf(), "<cycle>");
          }
          e @ Err(_) => return e,
        }
        let _ = writeln!(ctx.buf(), ",");

        ctx.indent -= 1;
        let _ = write!(ctx.buf(), "{}}}", indent);
      }
      Value::NativeFn(fnc) => {
        let indent = "  ".repeat(ctx.indent);
        let _ = writeln!(ctx.buf(), "<{}>{{", fnc);
        ctx.indent += 1;

        let _ = writeln!(ctx.buf(), "{}  src: {:#x},", indent, fnc.ptr_value());

        let _ = write!(ctx.buf(), "{}  name: ", indent);
        match ctx.recurse(
          PathComponent::Ident("name".to_string()),
          &fnc.name().map(Value::String).unwrap_or(Value::Null),
        ) {
          Ok(()) => {}
          Err(EncodeError::Cycle { .. }) => {
            let _ = write!(ctx.buf(), "<cycle>");
          }
          e @ Err(_) => return e,
        }
        let _ = writeln!(ctx.buf(), ",");

        ctx.indent -= 1;
        let _ = write!(ctx.buf(), "{}}}", indent);
      }
      Value::Std => {
        let _ = write!(ctx.buf(), "<std>");
      }
      _ => {
        let _ = write!(ctx.buf(), "<opaque>");
      }
    }
    Ok(())
  }
}
