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

// Check that all valid bool operations work as expected.

use t = "test_lib.ak";

t.expect(true == true);
t.expect(false == false);
t.expect(true != false);
t.expect(false != true);

t.expect(true == !false);
t.expect(false == !true);

t.expect((true || false) == true);
t.expect((true && true) == true);
t.expect((true && false) == false);
t.expect((false || false) == false);

t.expect((false && null) == false);
t.expect((true || t.check(false)) == true);
t.expect_death(fn() null && false);
