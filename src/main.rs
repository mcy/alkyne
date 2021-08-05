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

#![deny(unused)]
#![deny(warnings)]

use crate::eval::encode::json::JsonEncoding;
use crate::eval::encode::Encoder;
use crate::exec::fs::Local;
use crate::exec::parallel::Executor;

pub mod eval;
pub mod exec;
pub mod syn;

fn main() {
  if std::env::args().len() <= 1 {
    let arena = syn::Arena::new();
    exec::repl::Executor::new(&arena).execute_loop().unwrap();
  }

  let fs = Local::new();
  let arenas = thread_local::ThreadLocal::new();

  let file_names = std::env::args_os().skip(1).collect::<Vec<_>>();
  let file_names = file_names.iter().map(AsRef::as_ref).collect::<Vec<_>>();
  let exec = Executor::new(&fs, &arenas, std::io::stderr());
  let vals = match exec.exec_files(file_names, 8) {
    Ok(v) => v,
    Err(n) => {
      eprintln!("error: got {} errors", n);
      std::process::exit(1)
    }
  };

  for (file, value) in vals {
    match Encoder::<JsonEncoding>::new().encode(&value) {
      Ok(j) => println!("# {}\n{}", file.display(), j),
      Err(e) => eprintln!("# {}\n{}", file.display(), e),
    }
  }
}
