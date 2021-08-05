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

//! Execution environment for evaluating many Alkyne files at once.

#![allow(warnings)]

use std::collections::HashMap;
use std::io;
use std::path::Path;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering;
use std::sync::mpsc;
use std::sync::Mutex;

use chashmap::CHashMap;

use thread_local::ThreadLocal;

use crate::eval::value::Value;
use crate::eval::Context;
use crate::exec::fs::FileSys;
use crate::syn;

/// A parallel executor, which can execute a large set of Alkyne files
/// simulataneously.
pub struct Executor<'i, Fs> {
  evaluated_files: CHashMap<&'i Path, EvalState<'i>>,
  fs: &'i Fs,
  arenas: &'i ThreadLocal<syn::Arena>,
  log_output: Mutex<Box<dyn io::Write + Send + 'i>>,
  errors: AtomicUsize,
}

enum EvalState<'i> {
  Complete(Option<Value<'i>>),
  Waiting(Vec<mpsc::SyncSender<Option<Value<'i>>>>),
}

impl<'i, Fs> Executor<'i, Fs>
where
  Fs: FileSys,
{
  /// Constructs a new `Executor`, using the given file system, arena source,
  /// and log sink.
  pub fn new(
    fs: &'i Fs,
    arenas: &'i ThreadLocal<syn::Arena>,
    log_output: impl io::Write + Send + 'i,
  ) -> Self {
    Executor {
      evaluated_files: CHashMap::new(),
      fs,
      arenas,
      log_output: Mutex::new(Box::new(log_output)),
      errors: AtomicUsize::new(0),
    }
  }

  /// Executes the given set of files with the given level of parallism.
  pub fn exec_files(
    &self,
    file_names: impl IntoIterator<Item = &'i Path>,
    parallelism: usize,
  ) -> Result<HashMap<&'i Path, Value<'i>>, usize> {
    let file_names = file_names.into_iter().collect::<Vec<_>>();
    let next_work_item = AtomicUsize::new(0);
    crossbeam::scope(|s| {
      for i in 0..parallelism {
        s.builder()
          .name(format!("alkyne-evaluator-{}", i))
          .stack_size(1024 * 1024 * 8) // 8 MB.
          .spawn(|_| loop {
            let idx = next_work_item.fetch_add(1, Ordering::SeqCst);
            if idx >= file_names.len() {
              return;
            }
            let file_name = file_names[idx];
            match self.lookup_or_exec(file_name) {
              Ok(v) => v,
              Err(chan) => chan.recv().unwrap(),
            };
          })
          .unwrap();
      }
    })
    .unwrap();

    let errors = self.errors.load(Ordering::SeqCst);
    if errors > 0 {
      return Err(errors);
    }

    let mut values = HashMap::new();
    for file_name in file_names.iter() {
      let val = match &*self.evaluated_files.get(file_name).unwrap() {
        EvalState::Complete(Some(v)) => v.clone(),
        _ => unreachable!(),
      };
      values.insert(*file_name, val);
    }

    Ok(values)
  }

  /// Attempts to look up `file_name`'s computed result, or, if unavailable, it
  /// computes it itself.
  fn lookup_or_exec(
    &self,
    file_name: &'i Path,
  ) -> Result<Option<Value<'i>>, mpsc::Receiver<Option<Value<'i>>>> {
    let mut ret = None;
    self.evaluated_files.upsert(
      file_name,
      || EvalState::Waiting(Vec::new()),
      |v| match v {
        EvalState::Complete(v) => ret = Some(Ok(v.clone())),
        EvalState::Waiting(chans) => {
          let (tx, rx) = mpsc::sync_channel(1);
          chans.push(tx);
          ret = Some(Err(rx));
        }
      },
    );

    if let Some(ret) = ret {
      return ret;
    }

    let result = self.exec(file_name);
    self.evaluated_files.alter(file_name, |v| match v {
      Some(EvalState::Waiting(chans)) => {
        for chan in chans {
          chan.send(result.clone()).unwrap();
        }
        Some(EvalState::Complete(result.clone()))
      }
      Some(v) => Some(v),
      None => None,
    });

    Ok(result)
  }

  /// Actually executes some Alkyne.
  fn exec(&self, file_name: &'i Path) -> Option<Value<'i>> {
    writeln!(
      self.log_output.lock().unwrap(),
      "info: queueing {}...",
      file_name.display()
    )
    .unwrap();

    let text = match self.fs.read_file(file_name) {
      Ok(s) => s,
      Err(e) => {
        self.errors.fetch_add(1, Ordering::SeqCst);
        writeln!(
          self.log_output.lock().unwrap(),
          "error: cannot read file {}: {}",
          file_name.display(),
          e
        )
        .unwrap();
        return None;
      }
    };

    let arena = self.arenas.get_or(|| syn::Arena::new());
    let ast = match syn::parse(file_name.as_ref(), text, arena) {
      Ok(a) => a,
      Err(e) => {
        self.errors.fetch_add(1, Ordering::SeqCst);
        write!(self.log_output.lock().unwrap(), "{}", e).unwrap();
        return None;
      }
    };

    let mut ctx = Context::new();
    let val = match ctx.eval(ast, |file_name| {
      match self.lookup_or_exec(file_name.as_ref()) {
        Ok(v) => v,
        Err(chan) => chan.recv().unwrap(),
      }
    }) {
      Ok(v) => v,
      Err(e) => {
        self.errors.fetch_add(1, Ordering::SeqCst);
        write!(self.log_output.lock().unwrap(), "{}", e).unwrap();
        return None;
      }
    };

    writeln!(
      self.log_output.lock().unwrap(),
      "info: finished {}",
      file_name.display()
    )
    .unwrap();
    Some(val)
  }
}
