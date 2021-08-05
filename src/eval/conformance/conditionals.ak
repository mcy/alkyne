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

// Check that conditional expressions and scopes work correctly.

use t = "test_lib.ak";

let x = if true { 42 };
t.expect(x == 42);

let y = if false { 42 };
t.expect(y == null);

let z = if false { 42 } else { 55 };
t.expect(z == 55);

if true { null } else {
  t.fail()
}

if true {
  null
} else if t.fail() {
  null
}

let foo = switch "foo" {
  "bar" -> 0,
  "foo", "baz" -> 1,
};
t.expect(foo == 1);

let bar = switch "bar" {
  "baz" -> 5,
  else -> 7,
};
t.expect(bar == 7);

let baz = switch "baz" {
    "baz" -> 5,
    "baz" -> 6,
    "baz" -> t.fail(),
};

t.expect_death(fn() switch "foo" { 0 -> 0, });
