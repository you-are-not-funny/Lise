# Lise reference semantics

`lise_semantics.py` is the normative, executable definition of what a Lise program means.
It is a small, slow, definitional interpreter that runs the real parsed AST and shares no code
with the verifier, the backend or the fuzzer's own evaluators. Run it with
`python lise.py interpret FILE`. This document describes the same rules in prose; if the two ever
disagree, that is a bug to be fixed in one of them.

## What it is used for

| Claim | How it is tested |
|---|---|
| A program the verifier accepts never reaches a STUCK state | `fuzz_lise.py` runs every accepted program on the reference semantics |
| The compiled program does exactly what the semantics says (result and output) | tests compare native binaries with the interpreter on all examples; the fuzzer compares three evaluators (its own reference, the reference semantics, the compiled code) |
| The static ownership rules are sound | `fuzz_own.py`: accepted programs must never violate ownership on the reference semantics, which checks it by storage identity |
| The interpreter itself is right | unit tests for each rule below; seven planted interpreter bugs must be caught (`mutation_test.py`) |

## Values and types

* `Integer`: mathematical integer. In program code every result must lie in [-2^63, 2^63-1].
* `Bool`; `enum`: a tag; `Outcome[V, E]`: success/failure (payload unobservable); `Void`.
* `Array[T, N]`: exactly `N` elements, always initialised (`fill(x)`); `record`: named fields,
  always fully initialised by its constructor. Records and arrays are never copied: they are moved
  (`consume`, `return`) or borrowed (`in`, `mutable`). A `mutable` parameter aliases the caller's storage
  (including a single record field or array element for scalar `mutable` parameters).
* A refinement `T where p` (inline, or via `type` aliases with generic parameters) is a predicate over
  the variable `value`; a record may carry an invariant over its field names. Generic parameters are
  types or integer constants; constants are variables inside bodies and contracts.

## Arithmetic and expressions

* `+ - *` and unary `-`: exact; the result outside 64 bits is **STUCK (overflow)** in program code.
* `/` and `%` are Euclidean: `a = b*q + r` with `0 <= r < |b|`. `b = 0` is **STUCK (div_zero)**;
  `INT64_MIN / -1` is **STUCK (overflow)**.
* `and`, `or`, `implies` short-circuit; comparisons and `==`/`!=` on integers, booleans, enums.
* `a[i]` and `a[i] := v`: `0 <= i < N` else **STUCK (index)**.
* **Spec mode** (contracts, asserts, invariants, measures, refinement predicates) uses unbounded
  integers (they are never executed by the compiled program); division by zero is still STUCK.
* `old(e)` is `e` evaluated on the parameters' values at entry; `result` is the returned value.

## Statements

* `let`/`var` bind a fresh name (no shadowing); a declared type must hold for the initial value
  (**STUCK (refinement)** otherwise). Arrays are initialised with `fill(x)`, records with `R(f1, f2, ...)`,
  and a record/array may be initialised by a call to a function returning one.
* Assignment: the new value must satisfy the target's declared type (field/element/variable);
  record-level invariants are checked at construction, at calls and at return, not between assignments.
* `if`/`while`; `assert e` must hold (**STUCK (assert)**).
* `while c invariant I decreases m`: each invariant holds before every evaluation of `c` (entry and after each
  iteration; **STUCK (invariant)**); the measure is `>= 0` and strictly smaller each iteration (**STUCK (measure)**).
* `print("literal")`, `print_int(e)`: append text to the output.

## Ownership (enforced dynamically by the reference semantics)

* A value of a non-Copy type (record, array, or a function's own generic type parameter) is **moved** when a
  variable is used by value in an owning position: declaration, assignment, `return`, a `consume`
  argument, a record constructor or `fill` argument. Reading a moved variable is
  **STUCK (ownership)**; assigning to the whole variable re-initialises it.
* Moving a borrowed (`in`/`mutable`) parameter, or moving a non-Copy field or array element, is STUCK.
* Assigning to a `let` variable, an `in` parameter, or through one, is STUCK; a `mutable` argument must be
  a mutable variable.
* A `mutable` argument must not overlap any other argument of the same call. Overlap is decided on actual
  storage (the same variable, the same record or array object, the same field/element), not on names, so
  `f(r.a, r.b)` does not overlap while `f(r, r)` and `f(r, r.a)` do. The verifier's rule is deliberately
  stricter (it refuses `f(r.a, r.b)`): conservative, never unsound.

## Functions

* Arguments must satisfy the parameter types (**STUCK (refinement)**), then `requires` must hold
  (**STUCK (precondition)**). On return the result satisfies the return type, borrowed/moved record
  parameters satisfy their type and invariants again, and every `ensures` holds (**STUCK (postcondition)**).
* A non-`Void` function must return on every path (**STUCK (fell_off)**).
* `decreases m max B`: on entry `0 <= m <= B`; a call to a function in the same recursion cycle has
  a strictly smaller measure than the caller had on entry (**STUCK (measure)**). Hence recursion
  depth is at most `B + 1`.
* Interpreter budgets (steps, call depth) report **STUCK (nontermination)**; they exist only so the
  interpreter itself always halts.

## What the semantics does NOT cover (yet)

* **Ownership of values not represented at run time**: the interpreter tracks moves per variable and
  aliasing per call; it does not model borrows that outlive a call (the language has no references that
  can be stored, so none exist).
* **Stack size and I/O failure**: the interpreter has no stack limit and never loses output; the
  compiled program has a static stack bound (checked by tests against a real OS stack limit) and drops
  output if `write(2)` fails.
* **Concurrency**: none exists yet.
