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

//! Virtual file systems for executor file lookups.

use std::cell::RefCell;
use std::collections::HashMap;
use std::env;
use std::fs;
use std::io;
use std::path::Path;
use std::path::PathBuf;
use std::sync::Mutex;

use toolshed::Arena;

/// A virtual file system, allowing for access to access to files for execution.
///
/// For example, this could be a collection of in-memory files, or it could
/// be a thin wrapper around the local file system (or a subset of it).
pub trait FileSys: Send + Sync {
  /// Looks up the file with the given name,
  fn read_file(&self, file_name: &Path) -> io::Result<&str>;
}

/// The local file system.
///
/// A `Local` can specify a custom "working directory" (relative to which
/// relative paths are resolved) and a "required prefix", such that
/// canonicalized paths cannot escape a certain subset of the local file system.
pub struct Local {
  inner: Mutex<LocalInner>,
}

struct LocalInner {
  arena: Arena,
  // NOTE: the pointers in `files` live for as long as `arena` does.
  files: RefCell<HashMap<PathBuf, *const str>>,

  cwd: PathBuf,
  prefix: Option<PathBuf>,
}

// It's actually Send, but we need to force the implementation because it has
// raw self-pointers inside it.
unsafe impl Send for LocalInner {}

impl Local {
  /// Creates a new `Local` with the current process's working directory as both
  /// the working directory and the prefix.
  pub fn new() -> Self {
    let cwd =
      env::current_dir().expect("cannot read current working directory");
    let cwd_clone = cwd.clone();
    Self::with_options(Some(cwd_clone), Some(cwd))
  }

  /// Creates a new `Local` with the given working directory and prefix.
  pub fn with_options(cwd: Option<PathBuf>, prefix: Option<PathBuf>) -> Self {
    Self {
      inner: Mutex::new(LocalInner {
        arena: Arena::new(),
        files: RefCell::new(HashMap::new()),

        cwd: cwd.unwrap_or_else(|| {
          env::current_dir().expect("cannot read current working directory")
        }),
        prefix,
      }),
    }
  }
}

impl FileSys for Local {
  fn read_file(&self, file_name: &Path) -> io::Result<&str> {
    let inner = self.inner.lock().unwrap();

    let mut files = inner.files.borrow_mut();
    if let Some(ptr) = files.get(file_name) {
      // SAFETY: This is safe because we only put arena pointers into the map.
      // Those pointers are always alive and valid when this function is called.
      unsafe { return Ok(&**ptr) }
    }

    let mut full_path = inner.cwd.clone();
    full_path.push(file_name);
    if let Some(prefix) = &inner.prefix {
      full_path = fs::canonicalize(&full_path)?;
      if !full_path.starts_with(prefix) {
        return Err(io::Error::new(
          io::ErrorKind::PermissionDenied,
          "attempted to escape local filesystem prefix",
        ));
      }
    }

    let text = inner
      .arena
      .alloc_string(std::fs::read_to_string(full_path)?)
      as *const str;
    files.insert(file_name.to_path_buf(), text);
    // SAFETY: This is necessary to convince the compiler that the returned
    // reference can outlive the mutex lock.
    Ok(unsafe { &*text })
  }
}
