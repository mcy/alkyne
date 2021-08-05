# The Alkyne Reference

The purpose of this document is to provide a complete description of Alkyne,
a scripting language aimed at generating configuration and embedability. That
said, it is not standardsese intended to completely specify the language.

<!-- MarkdownTOC autolink="true" -->

- [Design Goals](#design-goals)
- [Execution Model](#execution-model)
- [Overall syntactic notes](#overall-syntactic-notes)
- [Values](#values)
  - [Null](#null)
  - [Booleans](#booleans)
  - [Numbers](#numbers)
  - [Strings](#strings)
  - [Lists](#lists)
  - [Objects](#objects)
  - [Functions](#functions)
  - [Opaque values](#opaque-values)
- [Scopes and bindings](#scopes-and-bindings)
- [Expressions](#expressions)
  - [Scalar literals](#scalar-literals)
  - [List literals](#list-literals)
  - [Object literals](#object-literals)
  - [Function literals](#function-literals)
  - [Identifiers, references and builtin names](#identifiers-references-and-builtin-names)
  - [Block expressions](#block-expressions)
  - [`if` expressions](#if-expressions)
  - [`switch` expressions](#switch-expressions)
  - [`for` and `yield` expressions](#for-and-yield-expressions)
  - [`break`, `continue`, and `return` expressions](#break-continue-and-return-expressions)
  - [Indexing expressions](#indexing-expressions)
  - [Function call expressions](#function-call-expressions)
  - [`do` expressions](#do-expressions)
- [Patterns](#patterns)
  - [Binding patterns](#binding-patterns)
  - [Expression patterns](#expression-patterns)
  - [List patterns](#list-patterns)
  - [Object patterns](#object-patterns)
  - [Disjunction patterns](#disjunction-patterns)
- [Operator precedence and overloading](#operator-precedence-and-overloading)
- [Imports](#imports)
- [`std`, the Alkyne Standard Library](#std-the-alkyne-standard-library)

<!-- /MarkdownTOC -->

## Design Goals

Alkyne is a non-Turing-complete language, intended,
more than anything else, for generating blobs of JSON-like data. It is 
comparable to Jsonnet, Starlark, and Coil in this regard. It also takes after
JavaScript and Lua somewhat for its execution environment. The syntax is 
mostly inspired by Rust, and as such, belongs to the curly-brace family of 
languages.

The design of Alkyne attempts to satisfy the following competing priorities:

> Non-Turing-completeness: every Alkyne program should terminate, similar to 
> Starlark, or at least, it should be really hard to do.

> Abstractability: user-defined functions and configuration schemata should 
> be easy to use.

> Embeddability: it should be possible to use Alkyne as a limited
> scripting/configuration language inside another application.

> Readability: the language should have minimal gotchas, and configuration 
> should look like an imperative program. This implies a strong dynamic type 
> system.

> Generality: the language should aim to be useable for generating any kind of
> tree-like blob, not just e.g. Kubernetes configurations.

> Compatibilty: All JSON parses as Alkyne, no questions asked, except in manners of
> encoding, since Alkyne does not believe in UTF-16.

## Execution Model

Alkyne is intended to be embeddable as a configuration language within other 
applications, or as a stand-alone interpreter. The execution of Alkyne files, other
than at the file scope, is mostly implementation-defined.

A Alkyne file is executed in the following manner:
- Imports are resolved in an implementation-defined manner; each import 
  introduces a new binding to file scope.
- Statements are evaluated, introducing further bindings to file scope.
- A final expression is optionally evaluated.
- As artifacts of this computation, the implementation receives the top-level
  bindings of the file scope, as well as the final expression, as outputs.

Any of the above steps can also fail with an error. Alkyne does not provide any
mechanism for recovering from an error within the language; these must be 
handled by the enclosing implementation.

Moreover, Alkyne is strictly evaluated and dynamically typed. The interpreter will 
evaluate as little as code as possible, so type errors (and anything else called
out as an error in this document) will only be raised at runtime if the 
interpreter is required to pass through the offending code.

The rest of this document is dedicated to defining all of the above steps, 
except for those which are implementation-defined.

## Overall syntactic notes

While BNF snippets are provided along with descriptions of syntax we also 
provide some informal notes regarding the syntax of Alkyne:
- Alkyne supports C-style comments: `//` introduces a line comment, 
  while `/* ... */` is a block comment. Block comments may be nested. Comments
  have no semantic meaning whatsoever.
- Whitespace is irrelevant, except to separate tokens. Space, newline, carriage
  return, and tabs are recognized as whitespace.
- Semicolons are required, and moreover, are syntactically significant, like in 
  ML.
- All comma-delimited lists may have trailing commas; this is not reflected by
  BNF snippets, for brevity.
- Alkyne files use the extension `.ak`, and are always UTF-8 encoded.

## Values

A Alkyne value can have one of seven types:
- `null`, which acts as a dummy value.
- Booleans, which can be used in conditionals.
- Numbers, which have floating-point arithmetic.
- Strings, which are UTF-8-encoded byte arrays.
- Lists, which are fixed arrays of values.
- Objects, hashtable-like data structures which form the core of Alkyne.
- Functions, which can be called.

All of these, except for functions, correspond to the six JSON types. In 
addition, some values may be "opaque", effectively having no type.

### Null

There is exactly one null value, given by the reserved constant `null`. `null`
compares equal to itself, and, unlike all other values, can be compared for 
equality with all other values, though those comparisons will always yield 
false. 

`null` acts as the "missing" value, which a lot of operations return in 
exceptional circumstances. For this reason, the collapse operator (known in 
some  languages as the "Elvis operator") is provided for turning `null`s into
more interesting values:
```alkyne
alkyne> null ?? 42  // Replaces null with the rhs.
42

alkyne> 25 ?? 42    // Lhs is already non-null, so the rhs is not evaluated.
25
```
In particular, the right hand side of `??` is only evaluated when the left hand
side is null, similar to a short-circuiting logic operator. See
[Operator precendence](#operator-precedence-and-overloading) for precedence
information.

A number of other language features (also involving question marks) are
available for dealing with or producing nulls instead of errors, such as in 
[object definitions](#object-literals) or
[indexing operations](#indexing-expressions).

`null` also acts as a dummy function: it can be safely called with any number of
arguments, which will be ignored, and return `null` once more. See
[Function call expressions](#function-call-expressions) for details.

### Booleans

There are exactly two boolean values, given by the reserved constants `true` and
`false`. They may be compared for equality with each other, but comparing them
with any other type of values is an error. They may also be composed with the 
short-circuiting logic operators `&&` and `||`, which have the standard
evaluation behavior as in other languages. The usual `!` prefix operation is 
available, as well.

The main purpose of booleans is to act as the conditions in
[`if`-expressions](#if-expressions).

### Numbers

Numbers are floating-point numbers of implementation-defined precision
(64-bit IEEE floats can be expected, since every processor has them). They can
be compared with each other (as well as floats *can* be compared) for both 
equality and order, though not with any other types.

Numbers support only decimal literals: `0`, `-1`, `0.5`, `42`, and so on. The
decimal point may only be present when followed by another digit.

Numbers support schoolbook arithmetic, through the usual addition, subtraction,
multiplication, and division operators (`+`, `-`, `*`, and `/`). They also 
support Ealkyneidean remainder through `%`, that is, for all finite numbers `a` 
and `d`, `0 <= a % d < d` holds. See 
[Operator precendence](#operator-precedence-and-overloading) for precedence
information.

Some operations (mostly indexing) require integers; providing a number with a
nonzero fractional part to any expression expecting an integer is an error.

### Strings

Strings are immutable byte arrays encoded as UTF-8 (the one true encoding).
String literals can be either double-quoted (`"Hello, world!"`) or single-quoted
(`'hello world'`), and may contain any UTF-8 encoded Unicode text (including 
line breaks and other control characters, though zero-width characters are
kind-of rude), modulo escape sequences:
- `\"`, `\'`, and `\\` all produce the literal codepoint following.
- `\n`, `\t`, `\r`, `\b`, and `\f` all have their usual meanings.
- `\0` produces a NUL terminator, though Alkyne does not use NUL-terminated 
  strings.
- `\xNN` produces a ASCII character, given in hex.
- `\uNNNN` produces a Unicode codepoint on the Basic Multilingual Plane, given
  in hex (aka, `U+NNNN`).
- `\UNNNNNNNN` produces any Unicode codepoint (e.g., on the Astral Plane), given
  in hex.
- All other escape sequences, as well as creating a codepoint which does not 
  encode some Unicode character, is an error.

Strings can be compared to each other for equality or lexicographic order,
though comparisons to any other types are errors. They may also be 
concatenated with the `+` operator.

Strings may be indexed and sliced by byte index:
```alkyne
alkyne> "hello"[2]  // Shorthand for "hello"[2, 3]
"l"

alkyne> "hello"[1, 3]
"el"
```
Indexing out of range of the string, or slicing through a UTF-8 encoded
code-point boundary, is an error.

Strings can be iterated over: see
[`for` expressions](#for-and-yield-expressions) for details.

### Lists

Lists are identical to strings in every way, except that they are immutable 
arrays of other Alkyne values, rather than Unicode codepoints. A list literal 
consists of a list of values between square brackets, such as `[]`, `[42]`, and
`[0, "foo", false]`. Notably, lists are heterogenous.

Lists cannot be compared to each other at all (since general Alkyne values are
incomparable), but may be concatenated with the `+` operator.

Lists may be indexed and sliced the same way as strings, though a single index
produces the element at that index, rather than a single-character string.
```alkyne
alkyne> [1, 2, 3, 4][1]
2

alkyne> [1, 2, 3, 4][0, 2]
[1, 2, 3]
```
Out-of-bounds indexing is an error.

Lists may be iterated over, and constructed using `yield` expressions: see 
[`for` expressions](#for-and-yield-expressions) for details.

### Objects

Objects are immutable associative arrays, similar to JavaScript objects. An
object consists of a mapping from strings to values, and an optional 
"superobject" or "prototype", which is used for a simple inheritance system.

Object initialization syntax is complex, and will be elaborated on later on, but
the basic form is similar to JavaScript's:
```alkyne
{ a: 2, b: 3, my_long_key: "my long string", "": "" }
```
An object literal can also "extend" another object, which will set that object
as its superobject:
```alkyne
my_obj { overriden_key: "..." }
```
See [Object literals](#object-literals) for the complete syntax.

Objects can be indexed by string:
```alkyne
alkyne> { x: 3, y: 4 }["x"]
3
```
If the key is not present, then the chain of superobjects is searched until it
is found; failing that, an error is raised. As a shorthand, when looking up a
literal as the key, the syntaxes `obj.foo` and `obj."non trivial string"` are
available.

Like lists, objects are usually incomparable; however, they support a limited
form of [operator overloading](#operator-precedence-and-overloading).

Objects may be iterated over, and constructed using `yield` expressions; see 
[`for` expressions](#for-and-yield-expressions) for details.

### Functions

Functions are callable values, which can be created using the `fn` keyword:
```alkyne
fn(x) x + 5  // A function that adds 5 to its argument.
```
Functions capture their whole environment. When a function is called, a new 
stack frame is pushed down, which is popped off when the function ends. For 
the duration of this frame, the scope in which the function was defined 
replaces the current scope.

A function may also have a "referent", which is a value that will be produced by
the reserved name `self` within that function's body. Such bound functions can
only be created when accessing a member through dot notation: `foo.bar`, which
enables a sort of method notation: `foo.bar()` will be able to access the 
value of `foo`. It is also possible to synthetically bind a function using
`std.bind()`. A single function may have multiple copies bound to different
values.

Functions are incomparable and support no other operations. They also cannot be
recursive: it is an error to re-entrantly call any function, including different
bound copies of the same function.

### Opaque values

Some values cannot be manipulated except in a limited number of ways, such as
the values produced by `std.range`. The operations which an opaque value
supports should be documented by the function which produces it.

Implementations may define their own opaque values.

## Scopes and bindings

Alkyne programs also operate on scopes. A scope is an ambient object which contains
local variable bindings. A number of scopes are present in a Alkyne program:
- The top-level file scope.
- A function's scope, corresponding to its freshly created stack frame.
- A scope introduced by a block expression: `{ ... }`. Unlike the above scope,
  the scope within a block has the parent scope as its superobject, so that all
  names in the parent scope are also visible in the new block scope. See
  [block expressions](#block-expressions).

A binding can be introduced with a `let` statement, which is the only kind of
statement Alkyne has, though it has a number of variants.
```alkyne
let discombomulee = discombobulate(); // Bind `discombomulee` to the rhs.
```
This statement introduces a new binding into the current scope, accessible as
`x`. Binding names are the usual identifiers: an alphanumeric string, including
underscores, not starting with a digit. Conventionally, these names should be in
`snake_case`. There are also `oper` identifiers, which are used for
[operator overloading](#operator-precedence-and-overloading).

An existing statement may be rebound repeatedly:
```alkyne
let x = 0; let x = 1; let x = 2;
```
Note that this is distinct from mutation: it is not possible for a `let`
statement to affect bindings in any scope other than the current one.

The left hand side of a `let` binding isn't a mere identifier; it can be any
[pattern](#patterns). For example, when binding a value of list type, it can be 
destructured:
```alkyne
alkyne> let xs = ["foo", "bar", "bonk"];
alkyne> let [a, b, c] = xs;
alkyne> b
"bar"
```
It is an error if the pattern fails to match.

Additionally, there is syntax sugar for defining a function:
```alkyne
fn my_cool_function(x, y, z) = x + y + z;
// Equivalent to:
let my_cool_function = fn(x, y, z) = ...;
```
When the left hand side is a "floating" expression (i.e., any of the block,
`if`, `for`, or `switch` expressions), the equals sign and semicolon may be 
omitted:
```alkyne
fn my_cool_function(x, y, z) = {
  x + y + z
}
// Equivalent to:
let my_cool_function = fn(x, y, z) { x + y + z };
```

In all of the above forms, `_` is a valid variable name, but the assignment will
silently fail; this is useful for discarding elements in a list destructuring.
Furthermore, an expression followed by a semicolon will be treated as a
statement:
```alkyne
whatever_man();
// Equivalent to:
let _ = whatever_man();
```

Finally, scopes are Alkyne values, too: they're objects, which can be extended
and iterated like normal objects. The reserved name `here` 
refers to the current scope (which is allowed to be returned to a higher scope,
i.e., scopes may escape themselves). In particular, a variable reference `x` is
implicitly the lookup `here.x`. A function literal implicitly captures `here` 
and uses it as its scope when called later on.

The reserved name `top` refers to the file scope of the file in which `top`
was referenced. In particular, `top` in a function always refers to the file in
which that function was syntactically defined.

Unlike most Alkyne objects, scopes are mutable: `let` bindings introduce new keys.
However, this mutability is limited: a scope cannot be mutated mid-way through 
an expression that can reference it directly: the right-hand-side of a `let` 
binding must fully execute before bindings are updated and execution proceeds.

```bnf
let-binding     ::= "let" pat "=" expr ";"

floating-expr   ::= block | if | for | switch
fn-binding      ::= "fn" ident "(" (pat ",")* ")" 
                     ("=" expr ";") | floating-expr

trivial-binding ::= (expr ";") | floating-expr

binding         ::= let-binding | fn-binding | trivial-binding
```

## Expressions

Alkyne is an expression-oriented language: absolutely everything that can be an
expression is an expression: the only syntactic constructs that are not
expressions are `let` bindings and import statements.

### Scalar literals

The "scalar" types, null, bool, number, and string, have the usual literals:
- `null` is the sole null constant, and is a reserved word.
- `true` and `false` are the two boolean constants, which are reserved words.
- Numbers are given by decimal constants, like `1`, `25`, `-100.5`, `0.7`. They
  must start and end with a digit, and may include a minus sign.
- Strings can be delimited with either single or double quotes. See
  [Strings](#strings) for a list of restrictions.

```bnf
null   ::= "null"
bool   ::= "true" | "false"
number ::= "-"? digit+ ("." digit+)?
string ::= <see section on strings>
```

### List literals

Lists literals consist of a list of comma-separated expressions, enclosed in
square brackets: `[0, 1, 2]`, `[]`, `["foo", "bar"]`.

```bnf
list ::= "[" (expr ",")* "]"
```

### Object literals

Objects are the most versatile types in Alkyne, and, as such, have complex
initialization syntax. In its simplest form an object literal is a
comma-delimited list of key-value pairs enclosed in curly braces:
`{ a: 5, b: "foo" }`. An empty pair of braces, `{}`, always parses as an 
object, and never as a block.

The curly braces of an object literal do not introduce a new scope (they don't
need to, since `let` bindings are not allowed inside them). 

This list may be suffixed to another expression. That expression must be of
object type, and the resulting new object will have that object as its 
superobject:
```alkyne
new_template() {
  job_name: 'www_webserver',
}
```
This syntax is an *object extension*.

The reserved word `self` can be used to refer to the literal from inside of 
itself, to access other keys. Only keys prior to the key-value pair containing
a `self` reference will be visible, with similar semantics to the keys 
observable in a `here` reference. If the literal is an extension, the reserved
word `super` will be available, referring to the object being extended. 
Referring to `self` and `super` in any other context, unless otherwise 
specified, is an error.

The key of a key-value pair can be either an identifier, a string literal, or a
square-bracketed expression. In the first case, the key is the name of the
identifier; in the second case, the value of the string. In the third case, the
expression will be evaluated, and, if its value is a string, it will be used as
the key; non-string values are an error.
```alkyne
{
  foo: 4,
  "bar": 5,
  [baz()]: 6,
}
```

The key of a key-value pair may be suffixed with a question mark; this will
cause the assignment to be silently ignored if the value is null.
```alkyne
alkyne> let obj = { foo: null, bar?: null };
alkyne> std.has(obj, "foo")
true
alkyne> std.has(obj, "bar")
false
```

The key may also be prefixed with `super.`. In this case, the value must be a
non-extension object literal, and the following desugaring will take place:
```alkyne
{ super.a: { ... } }
// Becomes:
{ a: super.a { ... } }
```
If, instead, the key is prefixed with `super?.`, the assignment will be silently
ignored if `super` does not have the necessary key; in particular, the
right-hand-side will not be evaluated.

```bnf
key-value ::= ("super" "?"? ".")? 
              (ident | string | "[" expr "]") "?"? ":" expr
object    ::= expr? "{" (key-value ",")* "}"
```

### Function literals

Function literals consist of the following syntax: `fn(a, b, ...) expr`. 
The expression following the parentheses will not be executed in any way
until the function is called.

The arguments of a function don't have to be plain identifiers; like with `let`
bindings, they can be any [pattern](#patterns):
```alkyne
fn([a, b, ..rest]) [a + b] + rest
```
When the function is called, the arguments are matched against the patterns and 
bound. It is an error if any pattern fails to match.

The body of the function may reference anything defined in the containing scope,
and, when called, will see the latest version of that scope. The body of the
function itself creates a new scope, containing the function arguments
pre-defined. See [Function call expressions](#function-call-expressions) for 
further details.

Functions can also be defined using the syntax described in
[Scopes and bindings](#scopes-and-bindings)

```bnf
function ::= "fn" "(" (pat ",")* ")" expr
```

### Identifiers, references and builtin names

Like in many languages, Alkyne identifiers include all alphanumeric sequences not
beginning with a digit, but also includes  `oper+`, `oper-`, `oper*`, `oper/`,
`oper%`, `oper==`, and `oper!`, which are used for
[operator overloading](#operator-precedence-and-overloading).

Variables defined with `let` bindings can be accessed by naming their
identifier:
```alkyne
alkyne> let k = 42;
alkyne> k
42
```
This lookup is functionally equivalent to `here["k"]`. See
[Scopes and bindings](#scopes-and-bindings) for more information on bindings.
Note that this type of access does *not* trigger a bind of `self` in a function;
the syntax `here.k` should be used for that, instead.

A variable reference is an identifier. 

A number of variables are reserved and pre-defined by the language. These are:
- `self` and `super`, both of which are used by 
  [object literals](#object-literals); `self` is also used by 
  [bound functions](#functions).
- `here` and `top`, which provide access to scopes-as-objects, see
  [Scopes and bindings](#scopes-and-bindings).
- `std`, which provides an opaque object that can be indexed by strings to
  obtain various built-in functions, acting as Alkyne's standard library. See
  [`std`, the Alkyne Standard Library](#std-the-alkyne-standard-library).
- `it`, which is used by [`do` expressions](#do-expressions).

```bnf
identifier ::= [a-zA-Z_][0-9a-zA-Z]* | 
               "oper" ("+" | "-" | "*" | "/" | "%" | "==" | "!")
reference  ::= identifier
builtin    ::= "self" | "super" | "here" | "top" | "std" | "it"
```

### Block expressions

Blocks in Alkyne are expressions, providing a limited scope for creating
temporaries and returning a result:
```alkyne
let a = {
  let b = foo(...);
  b * 5
};
// `b` is not accessible here.
```

A block consists of a list of bindings, potentially ending in an expression.
When a block is executed, a new scope is created, each binding is executed in
that scope, and, if there is an ending expression, that expression is executed
and returned. If no final expression is present, the block returns `null`.

The top level scope of a file behaves exactly like a block expression: it may
end in an expression, or, if one is missing, return null.

If the final syntactic element in a block could be parsed as either a binding
(e.g., a floating `if` or `for`) or an expression, it is parsed as an 
expression. Also, empty blocks are forbidden: `{}` always parses as an object
literal. Neither of these syntactic ambiguity rules are noted in the BNF below.

Except for the case of `{}`, distinguishing an object literal (or object
extension) from a block is unambiguous, since blocks cannot contain key-value
pairs, though this necessarily incurs infinite lookahead.

```bnf
block ::= "{" binding* expr? "}"
```

### `if` expressions

`if` expressions are one of Alkyne's two forms of branching control flow, the other
one being [`switch` expressions](#switch-expressions). The syntax does not use
parentheses for conditions, and requires bodies be block expressions. For 
example:
```alkyne
if my_condition {
  ...
} else if my_predicate() {
  ...
} else {
  ...
}
```

Evaluation proceeds as follows: Each condition is successively evaluated. If it
evaluates to `true`, the corresponding block is evaluated, and its value 
returned. If it evaluates to `false`, execution continues to the next condition.
Any other value is an error. If we run out of conditions to evaluate, we either
evaluate the `else` block and return its contents, or return `null`.

```bnf
if-clause ::= `if` expr block
if-expr   ::= if-clause ("else" if-clause)* ("else" block)?
```

### `switch` expressions

`switch` expressions are, evaluation-wise, syntax sugar over
[`if` expressions](#if-expressions).

A `switch` consists of a number of cases, each of which consist of a list of
comma-separated expressions, followed by an expression to be evaluated. For 
example:
```alkyne
switch foo {
  "foo", discombobulate() -> foo.bar(),
  0, 1, 2 -> froob(),
  else -> false,
}
```
For each case, each expression is serially evaluated and compared for equality
against the "switchee". If the comparision for equality produces `true`, the
right hand side of the case is immediately executed and returned. If no
expression matches, then the `else` case is taken. It is an error if no 
expression matches and no `else` case is present (unlike in an `if` 
expression, where `null` is implicitly produced).

The above example is sugar for the following `if-else` chain, noting that `foo`
is evaluated exactly once.
```alkyne
if foo == "foo" {
  foo.bar()
} else if foo == discombobulate() {
  foo.bar()
} else if foo == 0 {
  froob()
} else if foo == 1 {
  froob()
} else if foo == 2 {
  froob()
} else {
  false
}
```

An empty switch block is forbidden (since that is ambiguous with the empty
object extension). This is not reflected in the BNF below.

```bnf
switch-case ::= (expr ",")+ "->" expr ","
else-case   ::= "else" "->" "expr" ","
switch-expr ::= "switch" expr "{" switch-case* else-case? "}"
```

### `for` and `yield` expressions

`for` expressions provide a limited looping mechanism for Alkyne. They are not true
loops, since they can only iterate over pre-existing, finite values.

A `for` expression has the following syntax:
```alkyne
for a, ... in iterable {
   ...
}
```
The following Alkyne values can be iterated over:
- Strings. There are two iteration variables, corresponding to the byte index of
  each codepoint, and a string containing just that codepoint, respectively.
- Lists. There are two iteration variables: the index, and the element at that
  index.
- Objects. There are three iteration variables: the key of a member, the 
  associated value, and the object value holding that key-value binding (among
  the super-objects of that object). The same key may appear multiple times,
  though belonging to different objects. The keys defined in a particular object
  are returned in an unspecified order, but all of the keys of a particular
  object are returned before proceeding onto the keys of the parent.
- Values produced by `std.range()` and `std.range_step()`. These have one
  iteration variable.
  
The number of iteration variables must exactly match the number of variables
required by the value being iterated; failing to do so is an error. Attempting
to iterate any other kind of value is also an error. The return value of the 
actual block is ignored.

The iteration variables themselves are actually [patterns](#patterns). If an
iteration produces iteration variables that, in turn, fail to match the given
patterns, an error is raised. However, if the `in` keyword is followed by a `?`
token, a match failure will instead cause the iteration to be skipped 
altogether.

```alkyne
let xs = for _, [x, y] in [[2, 3], [4, 5], [6, 7]] {
  yield x + y;
};

// Second iteration will raise an error.
for _, [x, y] in [[2, 3], "foo"] { ... }

// Second iteration will be skipped.
for _, [x, y] in? [[2, 3], "foo"] { ... }
```

Since the bodies of `for` loops are blocks, they cannot affect the scope outside
of themselves. `yield` expressions provide a way to return elements from a `for`
loop. There are two kinds of `yield` expressions:
- List-like `yield`s take one expression, evaluate it, and push it onto a list,
  which becomes the return value of the `for` expression.
- Object-like `yield`s take a key-value, evaluate it as per the rules in
  [Object literals](#object-literals), and add it to an object, which becomes
  the return value of the `for` expression. Note that `super` and `self` are
  *not* available inside the loop body.
  
There may be multiple `yield`s per iteration of the loop, but mixing different
kinds of `yield`s in the same loop evaluation is an error. If no `yield` is ever
executed, the `for` loop returns `null`.

`yield`, as an expression, always returns `null`.

For convenience, if the only expression in a `for`-loop is a `yield`, it may
instead be written as
```alkyne
alkyne> for i, x in [10, 20, 30] yield i + x;
[10, 21, 32]
```

Note that only the block form of a `for` expression is considered syntactically
"free-floating".

```bnf
yield-list ::= "yield" expr
yield-kv   ::= "yield" key-value
yield-expr ::= yield-list | yield-expr

for-expr   ::= "for" (pat ",")+ "in" "?"? expr (yield-expr | block)
```

### `break`, `continue`, and `return` expressions

`break` can be used to end a [`for` expression](#for-and-yield-expressions)
prematurely. It can either take no argument, in which case it immediately
returns the value that would have been returned normally (i.e, the collective
result of the `yield`s). It can also take a single argument, in which case it
overrides the normal return value with that argument.

`continue` simply jumps to the end of the current loop iteration.

It is an error to use `break` and `continue` inside of a loop (e.g., they cannot
cause functions to return).

`return` ends the current function, and returns its sole argument as that
function's value. `return` must always have exactly one argument.

All three may be used as expressions, though they return no values since they
immediately yank control flow.

```bnf
break-expr    ::= "break" expr?
continue-expr ::= "continue"
return-expr   ::= "return" expr
```

### Indexing expressions

Aggregate Alkyne objects can be decomposed using indexing expressions, like
`foo[bar, baz]`. The following types of indexings are legal:
- Given a string, `s[a, b]` will slice it along the interval `[a, b)`, assuming
  `a` and `b` are integers. It is an error to slice out of bounds or to slice
  through UTF-8 surrogates. The syntax `s[a]` is equivalent to `s[a, a + 1]`.
- Given a list, `xs[n]` produces the `n`th element of the list, assuming
  `n` is an integer. `xs[n, m]` produces the sublist corresponding to the
  interval `[a, b)`. Indexing out of bounds is an error.
- Given an object, `obj[k]` produces the value bound at the key `k`. If no such
  key exists, then the parents of the object are searched recursively. It is an
  error for this procedure to not produce a value, or for `k` to not be a
  string.
- The `std` opaque value may be indexed by strings for a specified or
  implementation-defined standard library definition. It an error to look up a
  non-existent definition.

Any other kind of indexing is an error. However, if the syntax `foo?[bar, baz]`
is used, all indexings above, which would be considered errors, instead produce
`null`. This can be used to roughly guess for the presence of keys, though, for
objects, `std.has()` should be used in situations where `null` may be present
as a value.

If the desired key is a string known a-priori, the syntax `foo["bar"]` may be
replaced with either `foo.bar` or `foo."bar"` (the former is reserved for the
case when the string is a valid identifier). The equivalent of `foo?["bar"]` is
`foo?.bar` or `foo?."bar"`. 

The above dot syntax also has the additional property that, if the returned 
value is a function, then the indexed value will be bound as the referent. 
See [Functions](#functions) for more information on bound functions.

```bnf
index-expr  ::= expr "?"? "[" expr "]"
member-expr ::= expr "?"? (ident | string)
```

### Function call expressions

Functions are called with the usual syntax: `f(...)`. The following function
calls are valid:
- If `f` is a function, then the number of arguments must match exactly; this is
  otherwise an error.
- If `f` is a "native" function defined by the implementation, the checking of
  arguments is left to the implementation.
- if `f` is `null`, the number of arguments is irrelevant, and the value
  returned is always `null`.
  
In all three cases, all arguments are evaluated before calling the function.

The requirement that `null` be a function is required merely so that the syntax
`foo?.bar()` works correctly, without requiring method call and function call
syntax to be separate.

Actually calling a function will, of course, transfer control to the called
function until it returns a value; the function call expression will return that
value.

```bnf
call-expr ::= expr "(" expr ")"
```

### `do` expressions

The `do` expression provides a "pipeline operator". The expression
```alkyne
foo_bar() do {
  baz(it)
}
```
is equivalent to `baz(foo_bar())`. Within the body of a `do` expression, the
built-in name `it` takes on the value of the left-hand side. `do` expressions
can be nested; `it` will always refer to the innermost expression.

The body of a `do` expression may be any "floating" expression, as defined in
[Scopes and bindings](#scopes-and-bindings).

```bnf
do-expr ::= expr "do" floating-expr
```

## Patterns

Patterns, or "coexpressions", are a syntactic construct common in many 
functional programming languages. Patterns feature anywhere where a value is
bound to a scope, most prominently in `let` expressions:
```alkyne
let [x, y, z, ..] = ...;
```

A pattern can be "matched" against a value and optionally produce bindings; in
this way, it is the dual of an expression (which reads bindings from scope
and produces a value). A match may be said to succeed or fail; usually, but
not always, failure results in an error. When a match succeeds, the set of of
bindings produced is the union of the bindings produced by all the successful
subpatterns.

The value being matched is sometimes called a "matchee" or "scrutinee".

### Binding patterns

A binding pattern is the dual of a
[variable reference](#identifiers-references-and-builtin-names). It consists of
a single identifier. The match always succeeds, and produces a single 
binding, namely, the matchee is bound to the pattern's identifier.

This is the pattern that drives basic `let` bindings, and really all other
kinds of patterns:
```alkyne
alkyne> let x = 5;
alkyne> x
5
```

Of note, the pattern `_` will never produce a binding.

A binding pattern may require that another pattern succeeds, but still bind the
entire matchee of the pattern. Namely, the syntax `id @ p` will bind the matchee
of `p` to `id`, if `p` succeeds. "Normal" binding patterns are, essentially,
syntax sugar for `id @ _`.

```bnf
binding-pat ::= ident ("@" pat)?
```

### Expression patterns

A limited subset of the expression grammar is also in the pattern grammar. An
expression pattern computes an expression, and compares its value to the matchee
for equality. The pattern match succeeds if equality is true. For example:
```alkyne
let null = null; // Matches.
let "foo" = 5;   // Fails.
```

This expression does not bind anything. It's not too useful on its own, and its
main value is to be embedded in compound patterns.

Currently, only [scalar literals](#scalar-literals) may be used as expression
patterns.

```bnf
expr-pat ::= null | bool | number | string
```

### List patterns

A list pattern is the dual of a [list literal](#list-literals). The most basic
form is just a square-bracket-delimited list of patterns:
```alkyne
alkyne> let [a, b, c] = [1, 2, 3];
alkyne> a
1
alkyne> c
3
```

List patterns are a useful way for functions to return multiple values, similar
to tuples in other languages like Python and Rust.
```alkyne
let [froog, ok] = maybe_frump();
```

However, a list pattern, unlike a list expression, does not need to know all of
the elements of the list, or even the length of the list. In a list pattern,
at most one of the constituent subpatterns may be replaced with `..`, possibly 
followed by an identifier. This will match "everything else" that is not 
matched by the patterns near the start and end of the list. For example:
```alkyne
alkyne> let [a, ..middle, b] = [1, 2, 3, 4];
alkyne> middle
[2, 3]
```
The `..` glob can match anything, including an empty list. Of course, this 
variant will still fail if there are not enough elements in the list to make up
for the other subpatterns.

```alkyne
exact-list-pat ::= "[" (pat ",")* "]"
glob-list-pat  ::= "[" (pat ",")* ".." ident?, (pat ",")* "]"
```

### Object patterns

Similar to list patterns, object patterns are the dual of 
[object literals](#object-literals). An object literal looks a lot like a
non-extension object, with some differences:
- The "values" must be a patterns, which are optional in this case.
- The keywords `super` and `self` are inaccessible.
- The key must be a string or an identifier (this restriction may be lifted in
  the future).
- The final item in the list of key-value pairs may be token `..`.

For example:
```alkyne
let { x: [x0, ..], y, "quoted key"?: quoted } = ...;
```
For each key-value pair, the key is looked up in the right-hand side. If it
exists, it is matched against the "value" part of the pair; if it does not, an
error is raised. An error is also raised if any keys not specified in the 
pattern are present in the matchee.

If the key is followed by a question mark, rather than raising an error, the
"value" part is matched against `null`.

If there is no value, and the key evaluates to a valid Alkyne identifier, then 
looked-up value is bound to a variable with the name of that key. In particular,
this means that the following are equivalent:
```alkyne
let { my_key } = ...;
let { my_key: my_key } = ...;
```

This pattern is useful for creating functions that take keyword arguments:
```alkyne
alkyne> fn kwargs({ are_cool }) if are_cool { "Cool!" } else { "..." }
alkyne> kwargs({ are_cool: true })
"Cool!"
```

If the last element of the list of key-value pairs is the token `..`, then the
match is no longer exact: the matchee may have any keys, so long as some subset
of them satisfies the pattern.

```bnf
kv-pat     ::= (ident | str) ("?"? ":" pat)?
object-pat ::= "{" (kv-pat ",")* ".."? "}"
```

### Disjunction patterns

Given two patterns `p1` and `p2`, the pattern `p1 | p2` will attempt to match
`p1`, followed by `p2` if that match did not succeed; it succeeds if either
matches. It binds only the bindings of the first successful pattern.

For example:
```alkyne
let [x] | x = ...;  // Flatten a one-element list.
```

There is no requirement that the bindings in both patterns be the same, though
care should be taken to use `here` for accessing maybe-missing bindings:
```alkyne
alkyne> let [x, ..] | [] = [];
alkyne> here?.x
null
```

```bnf
or-pat ::= pat "|" pat
```

## Operator precedence and overloading

Compound expressions, i.e., expressions consisting of operators, have the
following precedence, in order of weaker binding:

| Name | Symbol |
| ---:| --- |
| Postfix operators | `.` `[]` `()` `do` |
| Prefix operators  | `-` `!` |
| Multiplicative operators | `*` `/` `%` |
| Additive operators | `+` `-` |
| Collapse operator | `??` |
| Order comparisons | `<` `>` `<=` `>=` |
| Equality comparisons | `==` `!=` |
| Conjunction | `&&` |
| Disjunction | <code>&#124;&#124;</code> |

All operators are left-associative (i.e, they bind left-to-right).

The five arithmetic operators, the unary operators, and the equality comparison,
may be overloaded by objects:

- Given `a ^ b`, where `^` is an arithmetic operation, then:
  - If `a` is an object and `a.oper^` is well-defined, the expression is
    re-written to `a.oper^(b)`.
  - If instead `b` is an object and `b.oper^` is well-defined, the expression is
    re-written to `b.oper^(a)`.
- Given `a == b`, the above rules apply, except `oper==` is the name that gets
  looked up, and the resulting function call *must* return a boolean. `a != b`
  is always defined as `!(a == b)`, so overloading `==` also overloads `!=`.
- Given `^a`, where `^` is an unary operation, then:
  - If `a` is an object and `a.oper^` is well-defined, the expression is
    re-written to `a.oper^(null)`.

The last, unusual desugaring is so that implementations can distinguish binary
`oper-` and unary `oper-`. Overloaded operators cannot distinguish between
`a ^ b` and `b ^ a`, so operations must be commutative.

## Imports

Imports use the syntax `use foo = "...";`. The (unescaped) value of the string
is passed to the implementation, which must produce a Alkyne value in response;
this value is bound to `foo`. All imports must appear at the top of the file,
before any bindings or expressions.

While, conventionally, other Alkyne files might be imported with
`use foo = "my/file.alkyne";`, this behavior is not required by the implementation,
and imports may instead (or also) be used as an annotation system, or some other
implementation-relevant mechanism.

```bnf
import ::= "use" ident "=" string ";"
```

## `std`, the Alkyne Standard Library

Alkyne provides a number of built-in functions, which provide operations that the
base language does not provide.

`TODO(mcyoung): decide what to specify here.`
