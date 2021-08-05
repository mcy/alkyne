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

// Check that all valid objct operations work as expected.

use t = "test_lib.ak";

let obj = {
  foo: 0,
  "bar": "abc",
  'baz': [1, 2],
  ['fu' + 'nc']: fn() self['baz'],
  "self": fn() self,
};

t.expect(obj.foo == 0);
t.expect(obj["bar"] == "abc");
t.expect(obj.'baz'[1] == 2);
t.expect(obj.func()[0] == 1);
t.expect(obj.'self'()."self"()['foo'] == 0);

t.expect_death(fn() obj.missing);
t.expect_death(fn() obj['nope']);


let proto = { a: 1, b: 2, c: 3 };
let sub = proto { a: 2, d: 4 };

t.expect(proto.a == 1);
t.expect(sub.a == 2);
t.expect(proto.c == 3);
t.expect(sub.c == 3);
t.expect_death(fn() proto.d);
t.expect(sub.d == 4);


let proto = { foo: { a: 1, b: 'c' } };
let sub = proto { super.foo: { a: 'z' } };

t.expect(proto.foo.a == 1);
t.expect(sub.foo.a == 'z');
t.expect(proto.foo.b == 'c');
t.expect(sub.foo.b == 'c');


let obj = { a: 'a', e: 5 };
t.expect(obj?.a == 'a');
t.expect(obj?.b == null);
t.expect(obj?['a'] == 'a');
t.expect(obj?['b'] == null);
t.expect(obj?.a?.b == null);

let sub = obj {
    a?: super?.b,
    b: super?.c,
    c?: 0,
    d?: null,
    e: null,
};

t.expect(sub?.a == 'a');
t.expect(sub.a == 'a');

t.expect(sub?.b == null);
t.expect(sub.b == null);

t.expect(sub?.c == 0);
t.expect(sub.c == 0);

t.expect(sub?.d == null);
t.expect_death(fn() sub.d);

t.expect(obj?.e == 5);
t.expect(sub?.e == null);
t.expect(sub.e == null);

let obj = { a: {} };

let sub = obj {
    super?.a: { x: 5 },
    super?.b: { x: 5 },
};
t.expect(sub?.a?.x == 5);
t.expect(sub?.b?.x == null);

let add = {
  val: 1,
  oper+: fn(that) self { val: self.val + that.val },
};

t.expect((add + add + add).val == 3);

t.expect_death(fn() {} == {});
