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

// Check that block expressions and scopes work correctly.

use t = "test_lib.ak";

let x = {5};
t.expect(x == 5);

let x = {
    let y = x;
    { let y = 11; }
    y * 2
};
t.expect(x == 10);
t.expect_death(fn() y);

let z = {
    let foo = 5;
    here
};
t.expect(z.foo == 5);

let baz = {
    let z = 7;
    top.z.foo
};
t.expect(baz == 5);

let none = {
    let x = 0;
};
t.expect(none == null);

let obj = {{}};
t.expect(obj != null);