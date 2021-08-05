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

//! Execution environment for the Alkyne Read-Eval-Print Loop.

use std::convert::Infallible;
use std::io;
use std::time::Duration;
use std::time::Instant;

use rustyline::error::ReadlineError;
use rustyline::Editor;

use crate::eval::encode::alkyne::UclEncoding;
use crate::eval::encode::alkyne::VerboseEncoding;
use crate::eval::encode::json::JsonEncoding;
use crate::eval::encode::EncodeError;
use crate::eval::encode::Encoder;
use crate::eval::value::Value;
use crate::eval::Context;
use crate::syn;

const DOUBLE_CTRL_C_THRESHOLD: Duration = Duration::from_millis(300);

/// All state for the REPL.
pub struct Executor<'i> {
  arena: &'i syn::Arena,
  context: Context<'i>,
  editor: Editor<()>,
  last_ctrl_c: Instant,
  print_function: Box<dyn Fn(&Value<'i>) -> Result<String, EncodeError<'i>>>,
}

impl<'i> Executor<'i> {
  /// Creates a new REPL; call `execute_loop()` to run it.
  pub fn new(arena: &'i syn::Arena) -> Self {
    Executor {
      arena,
      context: Context::new(),
      editor: Editor::new(),
      last_ctrl_c: Instant::now(),
      print_function: Box::new(|v| Encoder::<UclEncoding>::new().encode(v)),
    }
  }

  /// Execs into the REPL; does not return except in the case of errors.
  pub fn execute_loop(&mut self) -> io::Result<Infallible> {
    eprintln!(
      "Welcome to Alkyne v{version} (rustc v{rustc}, {arch} {os})",
      version = env!("CARGO_PKG_VERSION"),
      os = std::env::consts::OS,
      arch = std::env::consts::ARCH,
      rustc = rustc_version::version().unwrap_or((0, 0, 0).into()),
    );
    eprintln!("Enter expressions to below and have them evaluated");
    eprintln!("Run :quit, or double-press ^C, to escape.");
    eprintln!("Run :help for more information.");
    eprintln!();
    loop {
      let buf = self.read_line()?;
      if buf.is_empty() {
        continue;
      }

      if buf.starts_with(":") {
        self.execute_command(&buf)?;
        continue;
      }

      let text = self.arena.alloc_string(buf);
      let unit = match syn::parse("<stdin>".as_ref(), text, self.arena) {
        Ok(unit) => unit,
        Err(e) => {
          eprintln!("{}", e);
          continue;
        }
      };

      match self.context.eval(unit, |_| None) {
        Ok(Value::Null) => continue,
        Ok(val) => {
          let text = match (self.print_function)(&val) {
            Ok(text) => text,
            Err(e) => {
              eprintln!("{}", e);
              continue;
            }
          };
          println!("{}", text);
        }
        Err(e) => {
          eprintln!("{}", e);
        }
      }
    }
  }

  fn read_line(&mut self) -> io::Result<String> {
    let mut buf = String::new();
    let mut indent = 0;
    loop {
      let prompt = if buf.is_empty() { "alkyne> " } else { "   | " };
      let indent_whitespace = "  ".repeat(indent);
      match self
        .editor
        .readline_with_initial(prompt, (&indent_whitespace, ""))
      {
        Ok(s) => {
          buf.push_str(s.as_str());
          buf.push('\n');
        }
        Err(ReadlineError::Io(e)) => return Err(e),
        Err(ReadlineError::Interrupted) => {
          if self.last_ctrl_c.elapsed() < DOUBLE_CTRL_C_THRESHOLD {
            std::process::exit(0)
          }
          self.last_ctrl_c = Instant::now();

          return Ok(String::new());
        }
        Err(e) => panic!("{}", e),
      }

      let (matches, i) = check_brackets_match(&buf);
      if matches || i < 0 {
        buf.pop();
        self.editor.add_history_entry(&buf);
        return Ok(buf);
      }
      indent = i as usize;
    }
  }

  fn execute_command(&mut self, command: &str) -> io::Result<()> {
    let args = command.split_ascii_whitespace().collect::<Vec<_>>();
    match args[0] {
      ":help" | ":h" => println!(
        "\
available commands:
:clear - clears the terminal
:emit  - set print mode: one of alkyne, debug, or json
:help  - shows this message
:quit  - exits the REPL\
"
      ),
      ":emit" | ":e" => match args.get(1).map(|s| *s) {
        Some("alkyne") | Some("u") => {
          self.print_function =
            Box::new(|v| Encoder::<UclEncoding>::new().encode(v))
        }
        Some("json") | Some("j") => {
          self.print_function =
            Box::new(|v| Encoder::<JsonEncoding>::new().encode(v))
        }
        Some("debug") | Some("d") => {
          self.print_function =
            Box::new(|v| Encoder::<VerboseEncoding>::new().encode(v))
        }
        _ => eprintln!("expected 'alkyne', 'debug' or 'json'"),
      },
      ":clear" | ":c" => {
        print!("{}{}", termion::clear::All, termion::cursor::Goto(1, 1))
      }
      ":quit" | ":q" => std::process::exit(0),
      command => eprintln!("unknown command: {}", command),
    }
    Ok(())
  }
}

/// Returns true if `s` has balanced brackets, strings, and comments;
/// it also returns the expected indentation level.
fn check_brackets_match(s: &str) -> (bool, i32) {
  let mut bracket_count: i32 = 0;
  let mut comment_count: i32 = 0;

  let mut chars = s.chars().peekable();
  'char_loop: while let Some(c) = chars.next() {
    match (c, chars.peek()) {
      ('/', Some('/')) if comment_count == 0 => loop {
        match chars.next() {
          Some('\n') | None => continue 'char_loop,
          _ => {}
        }
      },

      ('/', Some('*')) => comment_count += 1,
      ('*', Some('/')) => comment_count -= 1,

      ('(', _) | ('[', _) | ('{', _) if comment_count == 0 => {
        bracket_count += 1
      }
      (')', _) | (']', _) | ('}', _) if comment_count == 0 => {
        bracket_count -= 1
      }

      ('"', _) | ('\'', _) if comment_count == 0 => loop {
        let next = chars.next();
        let peek = chars.peek();
        match (next, peek) {
          (Some('\\'), Some('\\')) => {
            let _ = chars.next();
          }
          (Some('\\'), Some(q)) if *q == c => {
            let _ = chars.next();
          }
          (Some(q), _) if q == c => continue 'char_loop,
          (None, _) => return (false, 0),
          _ => {}
        }
      },
      _ => {}
    }
  }

  (bracket_count == 0 && comment_count == 0, bracket_count)
}
