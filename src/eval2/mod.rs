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

//! The "new" compiled-bytecode runtime, intended to replace the existing AST
//! interpreter.
//!
//! `eval2` is stack machine. All instructions interact with this stack by
//! popping operands and pushing their results.
//!
//! Stack elements are 64-bit words representing one of the eight Alkyne types:
//! `null`, `boolean`, `number`, `string`, `list`, `object`, `function`, and
//! `opaque`. Although Alkyne does not treat integers as their own type, the
//! instruction set does. Their encoding is currently unspecified.
//!
//! An `eval2` module consists of *functions* and *constants*. Functions do not
//! have unique names, but can be distinguished via unique identifier. Constants
//! are values of `number` or `string` type, and are identified via unique
//! identifiers. Constants and function identifiers share the same namespace,
//! and can all be pushed by the `lc` instruction.
//!
//! Each function has its own stack, a random-access array of
//! *local variables*, and a *loop stack* used by the `loop` instruction and
//! related instructions. The size of each of these must be specified by the
//! function.
//! The calling convention places a function's arguments into its stack (last
//! argument at the top), and the `ret` instruction returns whatever is at the
//! top of the stack.
//!
//! Functions, constants, and variables are identified by 24-bit integers.
//!
//! # The ISA
//!  
//! Instructions are 16 bit integers, with the following encoding:
//! ```text
//! struct Instruction {
//!   opcode: u4,
//!   union {
//!     // "12" type.
//!     imm12: u12,
//!     // "8" type.
//!     struct {
//!       opcode2: u4,
//!       imm8: u8,
//!     }
//!   }
//! }
//! ```
//! 
//! To describe the encoding of an instruction, we use the syntax `[op]` for
//! a 12-bit immediate instruction, and `[op, op2]` for an 8-bit immediate
//! instruction. Opcodes are given in single-digit hex.
//!
//! | Mnemonic               | Encoding | Name                 | Description                                                                                |
//! |------------------------|----------|----------------------|--------------------------------------------------------------------------------------------|
//! | **Stack Manipulation** |          |                      |                                                                                            |
//! | `ldi.n`                | `[1, 1]` | Load Null            | Pushes a `null`.                                                                           |
//! | `ldi.b <t/f>`          | `[1, 2]` | Load Bool            | Pushes an immediate `bool`.                                                                |
//! | `ldi.i <i12>`          | `[a]`    | Load Int             | Pushes an immediate 12-bit integer `number`.                                               |
//! | `ldc.s <sym>`          | `[b]`    | Load String          | Pushes a string constant.                                                                  |
//! | `ldc.fl <sym>`         | `[c]`    | Load Float           | Pushes a floating-point constant.                                                          |
//! | `ldc.fn <sym>`         | `[d]`    | Load Function        | Pushes a function constant.                                                                |
//! | `pop <i8>`             | `[2, 0]` | Pop                  | Discard top `n` values on the stack.                                                       |
//! | `dup <i8>`             | `[2, 1]` | Duplicate            | Push duplicate of `n`th value on the stack.                                                |
//! | `swap <i8>`            | `[2, 2]` | Swap                 | Swap the top of the stack with the `n`th value.                                            |
//! | **Arithmetic**         |          |                      |                                                                                            |
//! | `add`                  | `[3, 0]` | Add                  | Pop `a0`, `a1`; push `a1 + a0`.                                                            |
//! | `sub`                  | `[3, 1]` | Subtract             | Pop `a0`, `a1`; push `a1 - a0`.                                                            |
//! | `mul`                  | `[3, 2]` | Multiply             | Pop `a0`, `a1`; push `a1 * a0`.                                                            |
//! | `div`                  | `[3, 3]` | Divide               | Pop `a0`, `a1`; push `a1 / a0`.                                                            |
//! | `rem`                  | `[3, 4]` | Remainder            | Pop `a0`, `a1`; push `a1 % a0`.                                                            |
//! | `neg`                  | `[3, 5]` | Negate               | Pop `a0`; push `-a0`.                                                                      |
//! | `not`                  | `[3, 6]` | Not                  | Pop `a0`; push `!a0`.                                                                      |
//! | `round`                | `[3, 7]` | Round To Int         | Pop `a0`; push `a0` rounded to an integer value, towards zero.                             |
//! | **Aggregates**         |          |                      |                                                                                            |
//! | `new.list <imm>`       | `[4, 0]` | New List             | Pop `n` values on the stack; push a `list` containing them.                                |
//! | `new.obj`              | `[4, 1]` | New Object           | Pop `a0`; push new `object` that extends `a0`.                                             |
//! | `ld.len`               | `[4, 2]` | Load Length          | Pop `a0`; push its length (`string` or `list`).                                            |
//! | `ld.idx`               | `[4, 3]` | Load Field           | Pop `a0`, `a1`; push `a1[a0]`, or `poison` if missing.                                     |
//! | `ld.idx2`              | `[4, 3]` | Load Field           | Pop `a0`, `a1`, `a2`; push `a2[a1, a0]`, or `poison` if missing.                           |
//! | **Selectors**          |          |                      |                                                                                            |
//! | `seq`                  | `[5, 0]` | Select If Equal      | Pop `a0`, `a1`, `a2`, `a3`; if `a0 == a1`, push `a2`; else push `a3`.                      |
//! | `sne`                  | `[5, 1]` | Select If Not Equal  | Pop `a0`, `a1`, `a2`, `a3`; if `a0 != a1`, push `a2`; else push `a3`.                      |
//! | `slt`                  | `[5, 2]` | Select If Less       | Pop `a0`, `a1`, `a2`, `a3`; if `a0 < a1`, push `a2`; else push `a3`.                       |
//! | `sle`                  | `[5, 3]` | Select If Leq        | Pop `a0`, `a1`, `a2`, `a3`; if `a0 =< a1`, push `a2`; else push `a3`.                      |
//! | `s.psn`                | `[5, 4]` | Select If Poison     | Pop `a0`, `a1`; if `a0` is `poison`, push `a1`; else push `a0`.                            |
//! | `s.null`               | `[5, 5]` | Select If Null       | Pop `a0`, `a1`; if `a0` is `null`, push `a1`; else push `a0`.                              |
//! | `s.true`               | `[5, 6]` | Select If True       | Pop `a0`, `a1`, `a2`; if `a0 == true`, push `a1`; else push `a2`.                          |
//! | **Control Flow**       |          |                      |                                                                                            |
//! | `b <i8>`               | `[6, 0]` | Branch               | Skip `n` instructions.                                                                     |
//! | `bt <i8>`              | `[6, 1]` | Branch If True       | Pop `a0`; if `a0 == true`, skip `n` instructions.                                          |
//! | `beq <i8>`             | `[6, 2]` | Branch If Equal      | Pop `a0`, `a1`; if `a0 == a1`, skip `n` instructions.                                      |
//! | `bne <i8>`             | `[6, 3]` | Branch If Not Equal  | Pop `a0`, `a1`; if `a0 == a1`, skip `n` instructions.                                      |
//! | `blt <i8>`             | `[6, 4]` | Branch If Less       | Pop `a0`, `a1`; if `a0 == a1`, skip `n` instructions.                                      |
//! | `ble <i8>`             | `[6, 5]` | Branch If Leq        | Pop `a0`, `a1`; if `a0 == a1`, skip `n` instructions.                                      |
//! | `rep <i8>`             | `[7, 0]` | Repeat               | Pop `a0` (must be an integer). Push a loop to run `a0` times.                              |
//! | `iter <i8>`            | `[7, 1]` | Iterate              | Pop `a0`. Push a loop to iterate over `a0.`                                                |
//! | `break` <i8>           | `[7, 2]` | Break Loop           | Break out of the `n`th loop in the loop stack.                                             |
//! | `cont` <i8>            | `[7, 3]` | Continue Loop        | Skip to the start of the next iteration of the `n`th loop in the loop stack.               |
//! | `call <i12>`           | `[8]`    | Call Static          | Call static subroutine.                                                                    |
//! | `callv`                | `[9, 0]` | Call Virtual         | Pop `a0`; call `a0` as a virtual subroutine.                                               |
//! | `bind <i8>`            | `[9, 1]` | Bind Function        | Pop `a0` (must be function) and `n` stack values; push `a0` with those values as captures. |
//! | `ret`                  | `[9, 2]` | Return From Function | Return from current function.                                                              |
//! | **Misc**               |          |                      |                                                                                            |
//! | `nop`                  | `[0, 0]` | No-op                | Does nothing.                                                                              |
//! | `halt`                 | `[0, 1]` | Halt Execution       | Halt execution unconditionally.                                                            |
//! | `halt.psn`             | `[0, 2]` | Halt if Poisoned     | Halt execution if the top of the stack is `poison`.                                        |
//! | `wni <i12>`            | `[f]`    | Widen Next Immediate | See below.                                                                                 |
//!
//! ## Arithmetic
//! Note that the following instructions only apply when the operands are
//! integers, *except* for `add`, which operates on strings and lists by
//! concatenation. <!-- Maybe add a concat operator...? -->
//!
//! - `add` Add. Pops `a` and `b` from the stack and pushes `a + b`.
//! - `sub` Subtract. Pops `a` and `b` from the stack and pushes `a - b`.
//! - `mul` Multiply. Pops `a` and `b` from the stack and pushes `a * b`.
//! - `div` Divide. Pops `a` and `b` from the stack and pushes `a / b`.
//! - `rem` Remainder. Pops `a` and `b` from the stack and pushes `a % b`.
//! - `neg` Negate. Pops `a` from the stack and pushes `-a`.
//!
//! - `addi <imm>` Add immediate. Pops `a` from the stack and pushes `a + imm`.
//! - `muli <imm>` Multiply immediate. Pops `a` from the stack and pushes `a * imm`.
//!
//! ## Aggregate operations
//!
//! - `list.new` Pushes an empty, mutable list onto the top of the stack.
//! - `list.new <imm>` Pops the top `imm` values on the stack into a new list,
//!    pushing the resulting list. Values popped are inserted into the list in
//!    last-out-first-in order.
//! - `obj.new` Pushes a empty, mutable `object` onto the stack.
//! - `obj.ext` Pops an `object` `a` from the top of the stack and pushes a new,
//!   mutable `object` with `a` as its parent onto the stack.
//! - `obj.super` Pops an `object` and pushes its parent onto the stack.
//!
//! - `freeze`. Freeze aggregate. Freezes a mutable `list` or `object` at the
//!   top of the stack.
//! - `len` Length. Pushes the length of a `list` or `string`.
//! - `idx` Index. Pops `a` and `b` from the stack and pushes `b[a]`.
//! - `idx2` Slice. Pops `a`, `b`, and `c` from the stack and pushes `c[b, a]`.
//! - `idx.or` Index or. Pops `a` and `b` from the stack; if `b[a]` succeeds,
//!    pop an additional value and push `b[a]`.
//! - `idx2.or` Slice or. Pops `a`, `b`, and `c` from the stack; if `c[b, a]`
//!   succeeds, pop and additional value and push `c[b, a]`.
//!
//! ## Control Flow
//! All branch instructions perform some kind of test and then skip the next
//! `n` instructions.
//!
//! - `beq <imm>` Branch if equal. If the top two values on the stack are
//!   equal, branch.
//! - `bz <imm>` Branch if zero. If the top value on the stack is zero-like
//!   (`null`, `false`, positive `0`, `""`, or `[]`), branch.
//! - `bn <imm>` Branch if not zero. Opposite of `bz`.
//!   instructions.
//! - `blt <imm>` Branch if less than. If the top value on the stack is less
//!   than the value below it, branch.
//! - `ble <imm>` Branch if less than or equal . If the top value on the stack
//!   is less than or equal to the value below it, branch.
//!
//! - `loop <imm>` Iterate. Pop an *iterable* value (as defined by Alkyne) from
//!   the stack, and push a *loop frame* onto the stack. As long the iterator
//!   is non-empty:
//!   - Push the iteration values onto the stack (e.g., if iterating a list,
//!     push the index, then the value).
//!   - Upon the program counter being exactly `imm` instructions away from
//!     the `loop` instruction, jump back to it and push new arguments.
//!   
//!   Being inside of a loop frame has a few effects:
//!   - Branch instructions cannot put the program counter beyond the last
//!     instruction of a `loop`.
//!   - The stack cannot be popped below the height it was at when the `loop`
//!     instruction was executed; the stack is popped down to this height
//!     at the beginning of each iteration.
//!
//! - `loop.cont <imm>` Re-start iteration. Pop `imm` loop frames off of the
//!   loop stack, then jump to the first instruction after the `loop` at the top
//!   of the stack (popping the value stack as would happen at the beginning of
//!   a loop iteration). Faults if the loop stack is emptied by the popping
//!   operation.
//! - `loop.break <imm>` End iteration. Pop `imm` loop frames off of the loop
//!   stack, then jump to the first instruction after the last loop popped's
//!   last instruction.
//!
//! - `call <imm>` Call subroutine. Calls the function identified by the
//!   immediate.
//! - `call` Call dynamic subroutine. Pops a function value, and
//!   however many arguments it requests, off of the stack, and calls it. Pushes
//!   the function's return value.
//! - `bind <imm>` Bind function. Pops a function value and `imm` further values
//!   from the stack, and pushes a new function value with those values bound
//!   as its first `n` arguments.
//! - `ret` Pops a value from the stack and returns it from the current
//!   function. The last instruction in a function must be a `ret`.
//!
//! ## Miscellaneous
//! - `nop` No-op. Does nothing.
//! - `halt` Explicitly-unimplemented instruction. Immediately halts execution
//!   with an error.
//!

#![allow(unused)]

use std::mem::MaybeUninit;
use std::rc::Rc;
use std::marker::PhantomData;

use crate::syn;
use crate::eval2::value::StackVal;

pub mod gc;
pub mod value;

///
pub struct Fn {
  arg_count: usize,
  var_count: usize,
  loop_depth: usize,
  stack_depth: usize,
  code: Rc<[u32]>,
}

pub struct Module {
  fns: Vec<Fn>,
  strings: Vec<String>,
}

pub struct Context {
  modules: Vec<Module>,
  op_stack: OpStack,
  call_stack: CallStack,

  pc: usize,
  icache: Option<Rc<[u32]>>,
}

pub struct OpStack {
  ty_stack: Vec<u8>,
  val_stack: Vec<MaybeUninit<u64>>,
  lower_bound: usize,
}

impl OpStack {
  pub fn height(&self) -> usize {
    debug_assert!(self.ty_stack.len() == self.val_stack.len());
    self.val_stack.len()
  }

  pub fn push(&mut self, val: StackVal) {
    let (ty, val) = val.into_raw_parts();
    self.ty_stack.push(ty);
    self.val_stack.push(val);
  }

  pub fn peek(&mut self, idx: usize) -> Option<StackVal> {
    if idx >= self.height() {
      return None
    }
    
    let idx = self.height() - 1 - idx;
    unsafe {
      let &ty = self.ty_stack.get_unchecked(idx);
      let &val = self.val_stack.get_unchecked(idx);
      Some(StackVal::from_raw_parts(ty, val))
    }
  }

  pub fn dup(&mut self, idx: usize) {
    // TODO: Error!
    let top = self.peek(idx).unwrap();
    self.push(top)
  }

  pub fn pop(&mut self, count: usize) {
    // TODO: Error!
    let new_len = self.height().saturating_sub(count);
    self.ty_stack.truncate(new_len);
    self.val_stack.truncate(new_len);
  }
}

pub struct CallStack {

}

pub struct CallFrame {
  fnc: u32, // ConstPtr?
  code: Rc<[u32]>,
  stack_height: usize,
}