# Lise

A systems language where **no proof means no binary**.
Contracts (`requires`, `ensures`, loop `invariant`/`decreases`) and refinement
types (`Integer where value > 0`) are part of the grammar and are discharged by
Z3 at compile time. An SMT answer of `unknown` or a timeout is a compile
error, never a pass.

## Status: Phase 1 reference compiler (frontend + verifier)

Working and tested (137 tests):

- Lexer, parser, AST
- Refinement types, generics (type params and value params like `N: PositiveSize`)
- Records with field refinements and record-level invariants
- Enums (nominal), `Outcome[V, E]` (tags only, payload erased for now)
- Functions with `requires` / `ensures` / `old(...)` / `result`
- Modular verification: callers see callee contracts, never bodies
- `while` with mandatory `invariant`s and `decreases` (termination proven)
- Proofs of: array bounds, division by zero, 64-bit overflow on every
  arithmetic op, refinement preservation on every assignment, postconditions
- Counterexamples on failure
- Ownership (affine) checking: `consume` moves non-copyable values (records,
  arrays, generic `T`); use-after-move, double move, moving out of a borrowed
  parameter, moving inside a loop, and moving out of arrays/fields are errors.
  Integers, Bool, enums, Outcome are Copy. Exclusive `mutable` borrows are
  checked for aliasing at call sites.
- LLVM IR backend (`python lise.py build FILE`): runs only after verification
  passes; proven checks are erased (zero runtime cost). Supports Integer/Bool,
  enums, Outcome (tag only), records, fixed-size arrays, `mutable`/`consume`
  params, and generics by monomorphization (type args must be scalar).
- Functions can return records and arrays: `fn make() -> RingBuffer[Integer, 4]`
  returns a local variable (moving it out); callers write
  `var q: RingBuffer[Integer, 4] := make()`; contracts talk about `result.field`
  / `result[i]`. In the backend the result is written through a hidden pointer.
- Output: string literals (printable ASCII, escapes `\n \t \\ \"`) and two builtins,
  `print("literal")` and `print_int(n)`. Implemented by a tiny runtime in LLVM IR over
  write(2); a failed write stops that output and the program continues.
- Recursion (direct and mutual): every recursive function declares
  `decreases <measure> max <bound>`. The measure is proven `0 <= m <= bound` on entry and strictly
  smaller at every call inside the recursion cycle, so termination is proven and the recursion is at
  most `bound+1` frames deep; the compiler folds that into the static stack bound and rejects the
  build if it is too big.
- Frame rule: a call to a function with `mutable` params forgets only what the
  callee can modify (computed from its body, transitively), so facts about
  untouched fields and arrays survive calls.
- Local records and arrays: `var a: Array[Integer, 8] := fill(0)` and
  `var q: RingBuffer[Integer, 4] := RingBuffer(fill(0), 0, 0, 0)` (constructor
  args must satisfy the field types and record invariants, proven at the
  declaration).
- Ahead-of-time native build, no JIT (`lise.py build FILE --exe`, `lise.py run FILE`):
  verified IR -> LLVM O2 -> object file -> system linker -> ELF/Mach-O executable.
  Entry point is `fn main() -> Integer`; its value is the exit status.
- Proof cache (`.lise-cache/`), keyed on function tokens + callee contracts +
  type decls + Lise/Z3 version. Only successes are cached.

NOT built yet (rejected with a clear error or simply absent):

- Whole-array assignment, nested record construction, Outcome payloads (payloads are erased; they cannot be read yet)
- Region blocks / arenas (`region r { }`), actors and deadlock
  analysis, independent proof-certificate checking
- Quantifiers, refined array element types, modules/imports,
  dynamic strings, input, files (output is literals and integers only)

Semantics worth knowing: `Integer` is 64-bit signed; `/` and `%` are
Euclidean; contracts use unbounded math; type arguments must be generic
parameters or constants.

## Safety (priority #1)

There is exactly one Lise: no unchecked mode, no suppress pragma, no unsafe
escape. Everything is checked at compile time: every proof must be confirmed by
two independent solvers (Z3 and cvc5) plus a small solver-free checker (`lise_fmcheck.py`), builds never trust the proof cache, the
worst-case stack is bounded statically, and the verifier is fuzzed against a
reference interpreter (`python fuzz_lise.py 200`) whose own sensitivity is
mutation-tested (`python mutation_test.py`, 30 planted bugs). The proven obligations remain in the
binary only as a trap backstop that never fires in correct code. See
[SAFETY.md](SAFETY.md) for guarantees, the trusted base, and honest gaps.

[SEMANTICS.md](SEMANTICS.md) defines what a program means; `python lise.py interpret FILE` runs it
under that executable reference semantics (`lise_semantics.py`).

## Run it

    pip install -r requirements.txt   # z3-solver, cvc5, llvmlite
    python lise.py check example_ok_ring_buffer.lise example_ok_loops.lise
    python lise.py check example_fail_ring_buffer.lise   # shows a counterexample
    python lise.py build example_ok_math.lise     # writes example_ok_math.ll
    python lise.py build example_ok_main.lise --exe -o prog && ./prog   # native binary
    python lise.py run example_ok_main.lise       # build + run, exit status = main()
    python lise.py run example_ok_hello.lise      # prints text and numbers
    python lise.py run example_ok_recursion.lise  # recursion with proven termination
    python lise.py run example_ok_queue_main.lise # verified generic ring buffer, native (exit 42)
    python -m unittest -v      # backend tests need: pip install llvmlite

Options: `--independent` (strict: every proof must also be re-derived by the solver-free checker), `--timeout-ms N`, `--no-cache`, `-O0..-O3`, `-o OUT`, `--stack-limit N`.
Native builds need `llvmlite` and `gcc`/`cc`/`clang` on PATH.

## Files

| File | Role |
|---|---|
| `lise_lexer.py` | tokens, `LiseError` |
| `lise_ast.py` | AST + pretty printer |
| `lise_parser.py` | recursive-descent parser |
| `lise_verify.py` | type/sort checks + VC generation + Z3 + cache |
| `lise_codegen.py` | LLVM IR backend (scalar subset) |
| `lise_aot.py` | AOT: IR -> object -> linked executable |
| `lise.py` | CLI (`check`, `build`) |
| `test_lise.py` | tests |
| `fuzz_lise.py` | differential soundness fuzzer (verifier + backend vs reference) |
| `mutation_test.py` | plants known bugs; the fuzzer must catch every one |
| `lise_semantics.py` | executable reference semantics: the normative meaning of a program |
| `SEMANTICS.md` | the semantics in prose: stuck states, what is and is not covered |
| `lise_xcheck.py` | second-solver (cvc5) confirmation of every proof |
| `lise_fmcheck.py` | solver-free checker (exact integer arithmetic) that re-derives the linear core of proofs |
| `SAFETY.md` | safety case: guarantees, trusted base, gaps, roadmap |
| `example_*.lise` | `ok` must verify, `fail` must be rejected |

## Next phases

1. Regions/arenas with inferred lifetimes (no `'a`) on top of the ownership checker
2. Independent proof-certificate checker (shrinks trusted base)
3. Returning records/arrays, strings, I/O, recursion with `decreases`
4. Actors + deadlock-freedom proofs, verified stdlib, self-hosting
