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

// Check that all valid list operations work as expected.

use t = "test_lib.ak";

fn one() = 1;
t.expect(one() == 1);

fn plus_5() = one() + 5;
t.expect(plus_5() == 6);

fn make_scope(n) {
  let x = n;
  here
}
let scope1 = make_scope(4);
let scope2 = make_scope(2);
t.expect(scope1.x == 4);
t.expect(scope2.x == 2);

let x = 0;
fn get_x() = x;
t.expect(get_x() == 0);
let x = 1;
t.expect(get_x() == 1);


fn forever() = forever;
forever()()()()()()()()()()();

fn recurse() = recurse();
t.expect_death(fn() recurse());

fn clever_recurse(f) = f(f);
t.expect_death(fn() clever_recurse(clever_recurse));

fn sum(a, b, c) = a + b + c;

t.expect(sum(1, 2, 3) == 6);
t.expect_death(fn() sum(1));

fn maybe(cond) if cond {
  5
} else {
  t.fail()
}
t.expect(maybe(true) == 5);

fn early_ret(cond) {
  if !cond { return 20 }
  t.fail()
}
early_ret(false);

fn break_out() = break;
fn cont_out() = continue;

t.expect_death(fn() break_out());
t.expect_death(fn() cont_out());

let len = "foo" do { std.len(it) };
t.expect(len == 3);

fn do_ret() {
    42 do { return it + 5 }
}
t.expect(do_ret() == 47);

let x = 5 do? if it == 5 { "foo" } else { "bar" };
t.expect(x == "foo");

null do? { t.fail() };

let obj = {
  bound: fn(x) self.member + x,
  member: 24,
};

t.expect(obj.bound(5) == 29);
let bound = obj.bound;
t.expect(obj.bound(7) == 31);

fn unbound(x) = self.member - x;
t.expect(std.bind(unbound, obj)(4) == 20);
