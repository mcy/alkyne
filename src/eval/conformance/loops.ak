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

// Check that loops and comprehensions work as expected.

use t = "test_lib.ak";

let xs = for i in std.range(0, 5) yield i * 2;
t.expect(xs[2] == 4);
t.expect(xs[4] == 8);

let xs_map = for i, v in xs yield [std.fmt('%d', [i])]: v;
t.expect(xs_map."3" == 6);

let obj = { abc: 0, xyz: 5 };
let obj2 = for k, v, _ in obj {
  let key = k + k[0];
  yield [key]: k;
};
t.expect(obj2.xyzx == "xyz");

let keys = for k, _, _ in obj { z: 4 } yield k;
t.expect(std.len(keys) == 3);

let chopped = for i, c in "hello!" {
  if c == "l" { continue }
  yield std.fmt('%d%s', [i, c]);
};
t.expect(std.concat(chopped) == "0h1e4o5!");

let early = for _, v in ["a", "b"] {
  if v == "b" {
    break
  }
  yield [v]: v;
};
t.expect(early?.a == "a");
t.expect(early?.b == null);

let no_yield = for _ in std.range(0, 5) { 42 };
t.expect(no_yield == null);

for _ in std.range(0, 0) {
  t.fail()
}

fn return_in_loop(xs) for _, x in xs {
  if x == 10 {
    return 42
  }
  yield 0;
}

t.expect(return_in_loop([1, 2, 4, 10, 6]) == 42);
t.expect(return_in_loop([1, 2, 3])[1] == 0);