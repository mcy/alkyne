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

//! Json encoding for Alkyne values.

use std::collections::HashSet;

use crate::eval::encode::Context;
use crate::eval::encode::Encode;
use crate::eval::encode::EncodeError;
use crate::eval::encode::PathComponent;
use crate::eval::escaping;
use crate::eval::value::Value;

#[derive(Default)]
pub struct JsonEncoding(());

impl<'i> Encode<'i> for JsonEncoding {
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
        escaping::escape_json_string(s.as_ref(), ctx.buf());
      }
      Value::List(val) => {
        let _ = write!(ctx.buf(), "[");
        for (i, v) in val.iter().enumerate() {
          if i != 0 {
            let _ = write!(ctx.buf(), ",");
          }
          ctx.recurse(PathComponent::Index(i), v)?
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
            let _ = write!(ctx.buf(), ",");
          }
          first = false;

          escaping::escape_json_string(k, &mut ctx.buf());
          let _ = write!(ctx.buf(), ":");
          ctx.recurse(PathComponent::Ident(k.to_string()), v)?
        }
        let _ = write!(ctx.buf(), "}}");
      }
      v => {
        return Err(EncodeError::BadType {
          bad_type: v.ty(),
          path: ctx.path().to_vec(),
        })
      }
    }
    Ok(())
  }
}
