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

// Check that number operations work correctly.
// We don't go too deeply into float testing, though.

use t = "test_lib.ak";

t.expect(0 == 0.0);
t.expect(1 != 0);

t.expect(1 + 1 == 2);
t.expect(1 - 3 == -2);
t.expect(5 * 3 == 15);
t.expect(4 / 2 == 2);
t.expect(5 / 2 == 2.5);

t.expect(6 % 4 == 2);
t.expect(-1 % 4 == 3);

t.expect(1/0 == 2/0);
t.expect(1/0 != (-2)/0);

let nan = 0/0;
t.expect(nan != nan);

t.expect(0 < 1);
t.expect(-1 > -3);
t.expect(-4 <= -4);
t.expect(!(-4 < -4));
