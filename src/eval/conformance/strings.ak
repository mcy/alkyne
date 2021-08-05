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

// Check that string operations work correctly.

use t = "test_lib.ak";

t.expect("abc" == "abc");
t.expect("abc" != "abd");
t.expect("\n" == "
");
t.expect('"' == "\"");
t.expect("'" == '\'');
t.expect("\x20" == " ");
t.expect("\u6587" == "文");
t.expect("\U0001F914" == "🤔");

t.expect("" == "");
t.expect("abc" + "" == "abc");
t.expect("ab" + "abc" == "ababc");

t.expect("abcdef"[3] == "d");
t.expect("abcdef"[2, 4] == "cd");
t.expect("abcdef"[5, 5] == "");
t.expect("abcdef"[0] == "a");

t.expect_death(fn() "abc"[-1]);
t.expect_death(fn() "abc"[5]);
t.expect_death(fn() "abc"[0.9]);
t.expect_death(fn() "abc"[0, 1.3]);
t.expect_death(fn() "abc"[0, 0, 0]);
t.expect_death(fn() "abc"[]);

t.expect(std.len("") == 0);
t.expect(std.len("abc") == 3);