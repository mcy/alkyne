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

//! Alkyne Objects.

use std::collections::hash_map::Iter as MapIter;
use std::collections::HashMap;
use std::fmt;
use std::sync::atomic::AtomicBool;
use std::sync::atomic::Ordering;
use std::sync::Arc;
use std::sync::RwLock;
use std::sync::RwLockReadGuard;

use crate::eval::value::seq::Str;
use crate::eval::value::DebugInfo;
use crate::eval::value::Value;

/// An `Object` is a Alkyne object, consisting of a set of fields, and a potential
/// super object, wrapped up in an `Arc` pointer.
///
/// `Object`s are also used as the value representation of variable scopes.
#[derive(Clone, Debug)]
pub struct Object<'i>(Arc<Inner<'i>>);

#[derive(Debug)]
struct Inner<'i> {
  root: Option<Object<'i>>,
  zuper: Option<Object<'i>>,
  fields: RwLock<HashMap<Str<'i>, Value<'i>>>,
  frozen: AtomicBool,
}

impl<'i> Object<'i> {
  /// Creates a new `Object` with no super object.
  pub fn new() -> Self {
    Object(Arc::new(Inner {
      root: None,
      zuper: None,
      fields: RwLock::new(HashMap::new()),
      frozen: AtomicBool::new(false),
    }))
  }

  /// Creates a new `Object` with `self` as the super object.
  pub fn extend(self) -> Self {
    Object(Arc::new(Inner {
      zuper: Some(self.clone()),
      root: Some(self.root()),
      fields: RwLock::new(HashMap::new()),
      frozen: AtomicBool::new(false),
    }))
  }

  /// Returns the root `Object` of this object, i.e., the top of the
  /// super-object chain.
  pub fn root(&self) -> Self {
    match &self.0.root {
      Some(root) => root.clone(),
      None => self.clone(),
    }
  }

  /// Looks up `key` in this object and all of its parents.
  pub fn lookup(&self, key: &str) -> Option<Value<'i>> {
    let mut current = self;
    loop {
      if let Some(v) = current.0.fields.read().unwrap().get(key) {
        return Some(v.clone());
      }

      if let Some(zuper) = &current.0.zuper {
        current = zuper
      } else {
        return None;
      }
    }
  }

  /// Defines `key` in this object. This function will panic if this object
  /// has been frozen.
  pub fn define(
    &self,
    key: impl Into<Str<'i>>,
    val: impl Into<Value<'i>>,
    allow_underscore: bool,
  ) {
    if self.0.frozen.load(Ordering::SeqCst) {
      panic!("tried to mutate frozen object; this is a bug")
    }

    let key = key.into();
    let mut val = val.into();

    if key.as_sliced() == "_" && !allow_underscore {
      return;
    }

    if let Value::Fn(fnc) = &mut val {
      fnc.rename(key.clone())
    }

    if let Value::NativeFn(fnc) = &mut val {
      fnc.rename(key.clone())
    }

    self.0.fields.write().unwrap().insert(key, val);
  }

  /// Freezes this `Object`; should be called one all fields have been evaluated,
  /// to catch any future attempts to define more fields.
  pub fn freeze(&self) {
    self.0.frozen.store(true, Ordering::SeqCst)
  }

  /// Checks whether this `Object` has been frozen.
  pub fn frozen(&self) -> bool {
    self.0.frozen.load(Ordering::SeqCst)
  }

  /// Returns the super object of this `Object`, if it has one.
  pub fn zuper(&self) -> Option<Object<'i>> {
    self.0.zuper.clone()
  }

  /// Returns an iterator over the fields of this `Object`.
  pub fn fields<'a>(
    &'a self,
  ) -> impl Iterator<Item = (&'a Str<'i>, &'a Value<'i>)> {
    let mut fields = Fields {
      lock: self.0.fields.read().unwrap(),
      iter: None,
    };
    unsafe {
      // This is safe, because `lock` gets moved into the same struct as the
      // iterator, and it will never be moved from, so they have equal
      // lifetimes.
      use std::mem::transmute;
      fields.iter = Some(transmute(fields.lock.iter()));
    }
    fields
  }

  /// Returns an iterator over all the recursive fields of this `Object`.
  pub fn iter<'a>(
    &'a self,
  ) -> impl Iterator<Item = (&'a Str<'i>, &'a Value<'i>, &'a Object<'i>)> {
    Iter {
      obj: Some(self),
      field_lock: None,
      field_iter: None,
    }
  }

  pub fn ptr_value(&self) -> usize {
    self.0.as_ref() as *const _ as usize
  }
}

/// A `DebugInfoObj` provides debug information for a Alkyne `Object`.
#[derive(Copy, Clone, Debug)]
pub struct DebugInfoObj {
  /// The address of this object.
  pub addr: usize,
  /// The number of ref-counts for this object.
  pub refs: usize,
  /// Whether this object has been frozen.
  pub frozen: bool,
  /// The address of the super-object, if any.
  pub zuper_addr: Option<usize>,
  /// The address of the root object, if any.
  pub root_addr: Option<usize>,
}

impl fmt::Display for DebugInfoObj {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "<{:#x}", self.addr)?;
    if let Some(zuper_addr) = self.zuper_addr {
      write!(f, " -> {:#x}", zuper_addr)?;
      match self.root_addr {
        Some(root_addr) if root_addr != zuper_addr => {
          write!(f, "..{:#x}", root_addr)?
        }
        _ => {}
      }
    }

    let mutability = if self.frozen { "fzn" } else { "mut" };
    write!(f, ", arc = {}, {}>", self.refs, mutability)
  }
}

impl DebugInfo for Object<'_> {
  type Info = DebugInfoObj;

  fn debug_info(&self) -> Self::Info {
    DebugInfoObj {
      addr: self.ptr_value(),
      refs: Arc::strong_count(&self.0),
      frozen: self.frozen(),
      zuper_addr: self.0.zuper.as_ref().map(Object::ptr_value),
      root_addr: self.0.root.as_ref().map(Object::ptr_value),
    }
  }
}

struct Fields<'i, 'a> {
  lock: RwLockReadGuard<'a, HashMap<Str<'i>, Value<'i>>>,
  iter: Option<MapIter<'a, Str<'i>, Value<'i>>>,
}

impl<'i, 'a> Iterator for Fields<'i, 'a> {
  type Item = (&'a Str<'i>, &'a Value<'i>);

  fn next(&mut self) -> Option<Self::Item> {
    self.iter.as_mut().unwrap().next()
  }
}

struct Iter<'i, 'a> {
  obj: Option<&'a Object<'i>>,
  field_lock: Option<RwLockReadGuard<'a, HashMap<Str<'i>, Value<'i>>>>,
  field_iter: Option<MapIter<'a, Str<'i>, Value<'i>>>,
}

impl<'i, 'a> Iterator for Iter<'i, 'a> {
  type Item = (&'a Str<'i>, &'a Value<'i>, &'a Object<'i>);

  fn next(&mut self) -> Option<Self::Item> {
    loop {
      if self.obj.is_none() {
        return None;
      }
      let obj = self.obj.as_mut().unwrap();

      if self.field_iter.is_none() {
        if self.field_lock.is_none() {
          self.field_lock = Some(obj.0.fields.read().unwrap());
        }
        let field_lock = self.field_lock.as_ref().unwrap();

        unsafe {
          // Extend the lifetime of `iter()` to last until the lifetime
          // of `field_lock`. This is safe, because because the extended
          // references all point into `field_lock`, which is semantically
          // a shared reference of lifetime 'a.
          use std::mem::transmute;
          self.field_iter = Some(transmute(field_lock.iter()));
        }
      }
      let iter = self.field_iter.as_mut().unwrap();
      let item = match iter.next() {
        Some((k, v)) => Some((k, v, *obj)),
        None => None,
      };

      if item.is_none() {
        self.obj = obj.0.zuper.as_ref();
        self.field_lock = None;
        self.field_iter = None;
      } else {
        break item;
      }
    }
  }
}

impl fmt::Display for Object<'_> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{{")?;
    let mut first = false;
    for (k, v) in self.fields() {
      if first {
        write!(f, "{}: {}", k, v)?;
        first = false;
      } else {
        write!(f, ", {}: {}", k, v)?;
      }
    }
    write!(f, "}}")
  }
}
