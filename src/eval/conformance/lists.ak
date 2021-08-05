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

t.expect([1, 2, 3][0] == 1);
t.expect([1, 2, 3][1, 3][0] == 2);

t.expect_death(fn() [1, 2, 3][-1]);
t.expect_death(fn() [1, 2, 3][5]);
t.expect_death(fn() [1, 2, 3][0.9]);
t.expect_death(fn() [1, 2, 3][0, 1.3]);
t.expect_death(fn() [1, 2, 3][0, 0, 0]);
t.expect_death(fn() [1, 2, 3][]);
t.expect_death(fn() [][]);

t.expect(std.len([1, 2, 3]) == 3);
t.expect(std.len([]) == 0);
t.expect(std.len([[[[[]]]]][0]) == 1);

t.expect_death(fn() [] == []);
