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

// Check that variable references and pattern matching work correctly.

use t = "test_lib.ak";

let x = 0;
t.expect(x == 0);

let y = 1;
t.expect(x == 0);
t.expect(y == 1);

let x = 2;
t.expect(x == 2);
t.expect(y == 1);

t.expect_death(fn() z);
t.expect_death(fn() { let x = z; });

let _ = 0;
t.expect_death(fn() _);

let null = null;
let "let" = "let";
t.expect_death(fn() { let "let" = "lett"; });

let [] = [];

let [a, b, _] = [1, 2, 3];
t.expect(a == 1);

let [x, y, ..] = [1, 2];
t.expect(x == 1);

let [x, y, ..] = [3, 4, 5];
t.expect(x == 3);

let [x, y, ..zs] = [6, 7, 8, 9];
t.expect(x == 6);
t.expect(zs[1] == 9);

let [x, .., y] = ["10", "11", "12", "13"];
t.expect(y == "13");

let [c] = [0];
t.expect(c == 0);

t.expect_death(fn() { let [x, y] = 0; });
t.expect_death(fn() { let [x, y] = [0]; });
t.expect_death(fn() { let [x, x] = [0, 0]; });

let {} = {};
let {..} = {};

let { x } = { x: 5 };
t.expect(x == 5);

let { no_match: _ } = { no_match: 20 };
t.expect_death(fn() no_match);

t.expect_death(fn() { let { x } = { x: 4, y: 5 }; });

let { list: [first, ..] } = { list: [5, 4, 3] };
t.expect(first == 5);
t.expect_death(fn() list);

let { maybe? } = { maybe: 5 };
t.expect(maybe == 5);

let { maybe? } = {};
t.expect(maybe == null);

let { x0, .. } = { x0: 7, x1: 77, x2: 777 };
t.expect(x0 == 7);
t.expect_death(fn() x2);

let { "quoted key" } = { "quoted key": "q" };
t.expect_death(fn() here."quoted key" );

let { "quoted key": q } = { "quoted key": "q" };
t.expect(q == "q");

let { "quoted_id" } = { quoted_id: "qq" };
t.expect(quoted_id == "qq");