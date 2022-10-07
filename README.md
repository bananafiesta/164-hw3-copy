# Homework 3: mul, div, and, or, let, case

_**Note:** This is a 2-week assignment (due 2 week after release)._

🚩 This is a particularly difficult homework; we encourage you to start early!

## Introduction

In this homework, you'll build upon an interpreter and compiler to add support
for the following language constructs:

- Multiplication and division
- Short-circuiting `and` and `or`
- `let` expressions that bind multiple variables
- `case` expressions

At the end of this homework assignment, your interpreter and compiler should
support the following grammar (we've highlighted what you'll be adding):

```diff
<expr> ::= <num>
         | <id>
         | true
         | false
         | (<unary_prim> <expr>)
         | (<binary_prim> <expr> <expr>)
         | (if <expr> <expr> <expr>)
+        | (and <expr> <expr>)
+        | (or <expr> <expr>)
+        | (let ((<id> <expr>) ...) <expr>)
+        | (case <expr> (<num> <expr>) (<num> <expr>) ...)


<unary_prim> ::= add1
               | sub1
               | zero?
               | num?
               | not


<binary_prim> ::= +
                | -
                | =
                | <
+               | *
+               | /
```

## Important information about testing

### Tests will not be graded

_We will **NOT** be grading your tests for this homework._

However, it will still be that case that when you submit your implementation to
Gradescope (to the assignment `hw3`), your suite of examples in the `examples/`
directory will be run against the reference interpreter and compiler. If the
reference implementation fails on any of your examples, Gradescope will show you
how its output differed from the expected output of your example (if you wrote a
`.out` file for it).

You can do this as many times as you want. We encourage you to use this option
to develop a good set of examples *before* you start working on your interpreter
and compiler!

### Updated testing framework

Our testing framework now additionally supports expecting an error in the
`examples/examples.csv` file. If you want to indicate that the expected output
is an error, you can now write `error` or `ERROR` in the second column.

Here is an example `examples/examples.csv` file:

```
(+ 1 2), 3
(add1 4), 5
(/ 1 0), error
```

## Some tips

### Running tests

You can use `dune runtest -f` to run all your tests in the `examples/`
directory, as described above.

### Running the compiler and the interpreter manually

In addition to using `dune runtest -f`, you can manually run the interpreter
and compiler on input files.

To run the interpreter on a file, execute the following command:

```
dune exec bin/interp.exe -- <file.lisp>
```

To run the compiler on a file, execute the following command:

```
dune exec bin/compile.exe -- <file.lisp> output
```

The resulting `.s` file (containing assembly code) and `.exe` file (an
executable) will be in the `output/` directory. You can then run the executable
with:

```
./output/<file.lisp>.exe
```

You can also tell the compiler to run the executable immediately after compiling
by adding `-r`, e.g.:

```
dune exec bin/compile.exe -- <file.lisp> output -r
```

### Inspecting and debugging assembly

If you run the compiler on a `.lisp` file (as described above), you can take a
look at the emitted assembly by looking in the `.s` file in the `output`
directory. This is a really useful way to understand how your compiler is
working as a whole and to debug any issues you may be facing.

For a more interactive way to debug assembly, check out
[Section 4](https://classroom.github.com/a/2vgY35Yw)!

### Manually assembling `.s` files

If it ever happens that the assembly emitted by your compiler is invalid and
you're not sure why, you can try manually compiling a test file (see above),
then manually running `nasm` on the `.s` file in the `output` directory:

```bash
nasm -o <input-filename>.s -o <output-filename>.o <format>
```

where `<format>` is `macho64` on macOS and `elf64` on Linux. This may give you
more helpful error messages than the automated testing infrastructure.

## 1. Multiplication and division (3 subtasks)

In this task, you will extend the interpreter and compiler to support the `*`
and `/` operations, which perform multiplication and division respectively.

**Task 1.1 (not graded):** Write tests for the multiplication and division
operators in the `examples/` directory.

**Task 1.2:** Extend the interpreter to support the multiplication and division
operators.

_Hint:_ In the interpreter, `*` and `/` should be implemented very similarly
to `+` and `-`.

**Task 1.3:** Extend the compiler to support the multiplication and division
operators.

_Hint:_ In the compiler, `*` and `/` are a bit trickier than `+` and `-`:

- In x86-64 assembly, we can multiply signed integers using the `imul`
  instruction. This instruction takes in _one_ argument and multiplies the
  register `rax` by it. Because the multiplication of two 64-bit integers may
  result in an integer that takes 128 bits to store, the output of `imul` is
  stored across two registers: the high 64 bits are stored in `rdx`, and the low
  64 bits are stored in `rax`. This is usually notated `rdx:rax`.
- In x84-64 assembly, we can divide signed integers using the `idiv` operation.
  Like `imul`, this instruction takes in _one_ argument and divides the register
  `rax` by it, then, unlike `imul`, simply stores the result in `rax`. One
  caveat is that `idiv` looks to `rdx` for sign information, so every time we
  call `idiv`, _we first need to sign-extend `rax` into `rdx` by calling `cqo`._
- With `add` and `sub`, we were able to ignore our encoding of integers because
  multiplication distributes over addition and our choice of tag for integers
  (`0b00`) corresponds to multiplying by `4`. For `imul` and `idiv`, you may
  need to shift integers left or right to preserve the proper tag.

  As an example: If we encode `2 + 3 = 5` as `8 + 12 = 20`, we can recover `5`
  by computing `20/4`. But if we encode `2 * 3 = 6` as `8 * 12 = 96`, dividing
  `96` by `4` doesn't give us the right answer.

  To shift an integer left, use `shl`. To shift an integer right, use `sar`
  (arithmetic right shift) instead of `shr` (logical right shift) to keep the
  sign consistent.

_Note:_ You will essentially be using `sar` and `shl` to cast our 62-bit Lisp
integers to and from `int64`s, and `cqo` for casts from `int64` to `int128`.
Casting from a larger integer set to a smaller one may fail (e.g. from `2^63` to
a Lisp integer); however, you are __not__ required to handle these cases in this
assignment, and may treat it as undefined behavior. (Your interpreter and
compiler can return anything and you need not perform any safety checks.)
Also recall from our discussion in class that OCaml uses 63-bit integers on
64-bit platforms.

## 2. Short-circuiting `and` and `or` (3 subtasks)

In this task, you will extend the interpreter and compiler to support the
short-circuiting `and` and `or` operations.

Short-circuiting `and` is defined as follows. Let `X` and `Y` be any expressions
in the grammar (including of non-`bool` type).

- If `X` evaluates to `false`, then `(and X Y)` evaluates to `false`.
- If `X` evaluates to anything other than `false`, then `(and X Y)` evaluates to
  the evaluation of `Y`.

Short-circuiting `or` is defined as follows. Again let `X` and `Y` be any
expressions in the grammar (including of non-`bool` type).

- If `X` evaluates to `false`, then `(or X Y)` evaluates to the evaluation of
  `Y`.
- If `X` evlauates to anything other than `false`, then `(or X Y)` evaluates to
  the evaluation of `X`.

Both `and` and `or` should _short-circuit_: if they are returning their first
argument, they should **not** evaluate their second argument. For this reason,
they must **not** be implemented as binary primitives, since the arguments of
binary primitives are eagerly evaluated before `compile_primitive` or
`interp_binary_primitive` are called.

**Task 2.1 (not graded):** Write tests for the short-circuiting `and` and `or`
operators in the `examples/` directory.

_Hint:_ It might be useful to write a test case that will fail if they do not
short-circuit, perhaps using your new `/` operator with a `0` argument.

_Hint:_ Make sure you test your implementation with arguments of `num` type.

**Task 2.2:** Extend the interpreter to support the short-circuiting `and` and
`or` operators.

**Task 2.3:** Extend the compiler to support the short-circuiting `and` and `or`
operators.

## 3. `let` expressions that bind multiple variables (3 subtasks)

The `let` form we implement in class binds exactly one variable. The generalized
form binds multiple variables; for example,

```
(let ((x 2)
      (y 3))
  (+ x y))
```

should evaluate to `5`.

These variables should be bound *simultaneously*: none of the definitions should
see any of the other bindings. This means that you cannot implement this
generalized form as multiple nested single let bindings.

_Hint:_ It might be useful to think of a test case that will have different
behavior if `let` is implemented in this way!

_Hint:_ We've provided a `get_bindings` helper function in `lib/util.ml` that
may be useful for the following subtasks. You can import that module with
`open Util`.

If a given `let` expression contains multiple bindings for the same name `n`, the program behavior should be the same as if only the last binding of `n` is included.  E.g., `(let ((x 1) (x 2)) x)` should evaluate to `2`.

**Task 3.1 (not graded):** Write tests for `let` expressions with multiple
bindings in the `examples/` directory.

**Task 3.2:** Extend the interpreter to support `let` expressions with multiple
bindings.

**Task 3.3:** Extend the compiler to support `let` expressions with multiple
bindings.

## 4. Case expressions (3 subtasks)

Common Lisp's `case` expression, like C's `switch` and OCaml's pattern-matching,
compares a single expression (called a "scrutinee") against a number of values;
for example,

```
(case 4
  (1 1)
  (2 4)
  (3 9)
  (4 16)
  (5 25))
```

should evaluate to `16`.

You'll implement a limited form of this expression in which:

- The scrutinee must be an expression that evaluates to an integer.
- The left-hand side of each case must be a *literal* integer.
- There must be at least one case.
- The last case in the expression is the default case, which will be used if
  none of the other cases match.
- If multiple cases match, then the right-hand side of the first match (from
  left-to-right) is returned.

**Task 4.1 (not graded):** Write tests for `case` expressions in the `examples/`
directory.

_Hint_: As you go through the next sections, you may want to keep the following
functions in mind, which you may find useful for implementing `case` in your
interpreter and/or compiler:

- `List.assoc_opt` for using `('a * 'b) list`s like maps. See the
  [OCaml documentation for association lists](https://ocaml.org/api/List.html#1_Associationlists)
  for more information.
- `List.nth` and `List.length` may be helpful for accessing the last case in a
  `case` expression.
- `get_cases` for parsing a list of expressions into a list of
  `(number, expression)` pairs. This function is defined in `lib/util.ml`,
  which can be opened with `open Util`.
- `List.range lo hi` for producing a list of numbers from `lo` to `hi`,
   inclusive. This function is added to the `List` module in `lib/util.ml`.
   which can be opened with `open Util`.

**Task 4.2:** Extend the interpreter to support `case` expressions.

In your interpreter, you can implement support for case expressions however
you'd like. However, for your compiler, we require that you use something called
a _branch table_, which we explain below.

### Branch tables

#### Why do we want branch tables?

The idea behind a branch table is to avoid the need for many comparisons and
jumps as compared to nested `if` expressions. For instance, imagine converting
the case expression above to `if` expressions:

```
(if (= 4 1)
  1
  (if (= 4 2)
    4
    (if (= 4 3)
      9
      (if (= 4 4)
        16
        25))))
```

If we compiled this code and ran it, the processor would end up needing to
execute 4 `cmp` instructions and 4 `jmp` instructions. If we added more cases,
the worst case scenario gets worse; execution time will be linear in the number
of cases.

For four or five cases, this usually isn't too terrible. But for some
applications, it's really important to be able to do this kind of switching in
constant time in the number of cases. Branch tables let us do that.

#### What is a branch table?

A [_branch table_](https://en.wikipedia.org/wiki/Branch_table)
is a chunk of assembly directives that, rather than specifying instructions,
contains just the addresses of labels. It looks like this:

```
branch_table_label:
   dq some_label
   dq another_label
   dq yet_another_label
   ...
   dq the_last_label
```

(The `dq` instruction injects static data into the executable---in this case,
the name of the label we will jump to.)

#### Using branch tables to compile `case` expressions

Suppose we want to compile a `case` expression whose scrutinee is an integer,
whose minimum case is `min`, and whose maximum case is `max`.

We can use a branch table with `max - min + 1` entries, each corresponding to an
integer between `min` and `max` (inclusive) in order, with no gaps in between,
as follows:

- Compare the argument to the minimum and maximum cases. If it's outside those
  bounds (i.e., less than the minimum case or greater than the maximum case),
  jump to the default label. _Warning:_ the default case will only correspond to
  the last entry in the branch table if the default case also happens to be the
  largest case!
- Compute the offset of the label for your argument. For a scrutinee that
  evaluates to `k`, the offset is `(k - min) * 8`. (We multiply by `8` because
  label addresses take up eight bytes on a 64-bit architecture.)
- Load the label for the branch table into a register. You should use `LeaLabel`
  for this.
- Jump to the computed label. You should use `ComputedJmp` with a `MemOffset`
  argument for this.

After the branch table, you should emit code for each case's expression labeled
with the correct label. Just as for the `then` branch of an `if`, each case
should jump to the same "continue" label at the end.

_Hints:_

- The first label in the branch table should be the label of the smallest (and
  not necessarily first) case.
- The last label should be the label of the largest (not necessarily last!)
  case.
- There should be a label for every value in between the minimum and the
  maximum; this means you might have more labels than cases. For the "gaps"
  between cases, you should use the label of the last (not necessarily largest!)
  case, since this is the default.
- We will test on branch tables with fewer than 1000 branches.

**Task 4.3:** Extend the compiler to support `case` expressions using a branch
table, as described above.
