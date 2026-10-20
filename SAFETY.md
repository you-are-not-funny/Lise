# Lise safety case (honest version)

Goal: be at least as safe as Ada, ideally safer. This file says what is
actually guaranteed today, what is *not*, and what would be needed to justify
the claim "safer than Ada". Read the gaps section before trusting anything.

## What a successful build guarantees (if the verifier and backend are correct)

| Hazard | How Lise handles it |
|---|---|
| Integer overflow | proven absent on every arithmetic op (64-bit), else compile error |
| Division by zero, `MIN / -1`, `MIN % -1` | proven absent |
| Array out of bounds | proven absent on every read and write |
| Uninitialised memory | impossible: every variable/array/record needs an initialiser |
| Use after move / double move | rejected (affine ownership checking) |
| Aliasing of `mutable` arguments | rejected at call sites |
| Dangling pointers, heap errors | no pointers, no heap |
| Non-terminating loops | `decreases` measure required and proven |
| Non-terminating recursion / stack overflow | recursion needs a proven `decreases m max B` (measure >= 0, <= B on entry, strictly decreasing at each call in the cycle), so depth <= B+1; a **static worst-case stack bound** includes it and the build fails if over the limit (default 1 MiB). Tested against a real OS stack limit. |
| Unproven obligations | an SMT `unknown`/timeout is a compile error, never a pass |
| Violated contracts | `requires`/`ensures`/invariants/refinements proven |

## Defence in depth (beyond what Ada gives you by default)

1. **There is exactly one Lise.** No `unchecked` mode, no `pragma Suppress`, no
   `unsafe` escape hatch, no flag that skips a proof. Every program that gets a
   binary has passed every check below.
2. **Proofs are mandatory.** In Ada/SPARK you can compile code whose proofs
   failed or were never run. In Lise "no proof, no binary".
3. **Two independent solvers must agree.** Every obligation Z3 proves is
   re-checked by cvc5. cvc5 `sat` is a hard "SOLVER DISAGREEMENT" error; cvc5
   `unknown`/timeout means the proof is *not accepted*. Dead-path pruning (which
   skips obligations) also needs both solvers to agree the path is dead.
4. **A solver-free checker is a gate, not a bystander** (`lise_fmcheck.py`, shares no code with
   Z3/cvc5). For every obligation both solvers call proved it must reach a verdict itself:
   *re-derived* (accepted), *counterexample* (it found an assignment and verified it by evaluating the
   original formula with its own evaluator: **the build stops, even though both solvers said yes**),
   or *unknown* (**rejected: fail closed**). Dead-path pruning needs the same three-way agreement.
   **Every re-derivation is a certificate**: the search (untrusted, ~600 lines) writes its refutation
   as data (case splits, then a list of exact steps: tighten, combine, product facts) and a separate
   validator, `lise_certcheck.py` (~200 lines, standard library only: no solver, no Lise imports),
   re-checks each step with exact integer arithmetic. A bug in the search can therefore not get a
   bad proof accepted (tested by breaking the search on purpose). `lise.py check FILE --certificates DIR`
   writes one JSON certificate per obligation; `python lise_certcheck.py DIR` validates them anywhere.
   Techniques: case splitting; exact Fourier-Motzkin over the integers with gcd tightening and exact
   (+-1) elimination; polynomial normal form with interval and McCormick bounds for products;
   Euclid facts for `/` and `%` (by literals exactly, by variables via |x/n| <= |x|, 0 <= r < |n|);
   read-over-write, constant arrays and Ackermann consistency for arrays; enums as bounded integers.
   On the bundled examples and on fuzz-verified programs it re-derives 100% of the obligations. What it
   still cannot do is rejected rather than trusted: e.g. `x*x*x*x >= 0` or `x*x + y*y >= 2*x*y` over
   unbounded integers pass both solvers and are refused. The checker is property-tested against Z3 in
   both directions on random formulas (never "unsat" for a satisfiable formula; every counterexample
   it reports really satisfies the formula) and mutation-tested; the gate itself is tested by making
   both solvers lie.
4b. **Developer-mistake guards are errors**: unused variables/parameters (`_name` opts out, which also
   catches ignored results), contradictory preconditions (every proof would be vacuous), code no path
   reaches, branches that are always/never taken, self-assignment. Unreachability is only reported when
   all three engines agree the path is dead.
5. **Trap backstop.** The proven obligations (overflow, bounds, division) are
   also compiled in as trap-on-violation (`llvm.trap`). They never fire in a
   correctly verified program; if the verifier or backend ever has a bug, the
   program stops instead of corrupting memory. Arithmetic never uses
   `nsw`/`nuw`, so it cannot produce LLVM poison/UB.
6. **Builds never trust the proof cache.** `build`/`run` re-prove everything;
   a tampered `.lise-cache/` cannot produce a binary.
7. **Static stack bound** instead of a runtime `Storage_Error`: no heap, and recursion only
   with a proven depth bound, so worst-case stack is computed at build time and enforced.
8. **Differential fuzzing** (`python fuzz_lise.py N`): random programs with
   arithmetic, arrays, branches, loops, records, helper functions taking a record
   `mutable` (with their own contracts, nested calls and array fields), random recursive functions with a termination measure (a verified program that does not
   terminate or breaks its postcondition is a BUG), functions that
   return a record whose postconditions the caller then relies on, and `print_int`
   output (the text actually written must equal the reference's) and random
   `assert` / `requires` / `ensures` / loop `invariant` clauses are verified; every accepted program is
   run on many inputs against a Python reference interpreter. A false assertion,
   postcondition or invariant, an overflow / div-by-zero / out-of-bounds in
   verified code, a result mismatch, or a trap is reported as a BUG.
9. **An executable reference semantics** (`SEMANTICS.md`, `lise_semantics.py`) defines what a
   program means, with every undefined behaviour as an explicit STUCK state. Every program the
   verifier accepts is also run on it: it must never get stuck, and its result and output must
   equal both the fuzzer's independent reference and the compiled code (three evaluators). Native
   binaries are compared with it on all examples.
10. **Ownership is fuzzed** (`python fuzz_own.py N`): random programs move, borrow, alias and mutate
    records; every program the verifier accepts must be free of ownership violations when run on the
    reference semantics, which decides aliasing by actual storage rather than by names. Seven
    planted ownership bugs (moves not recorded, aliasing allowed, immutables assignable, borrowed
    parameters movable, loop moves, moved-argument reads) are all caught.
11. **The fuzzers, the checker and the semantics are mutation-tested** (`python mutation_test.py`): sixty-one
   deliberately planted bugs (missing/weakened overflow, division, bounds,
   assert, postcondition and invariant proofs; three frame-rule mistakes; wrong
   backend instructions) must all be caught. The ones added in the last two rounds (checker, gate, developer guards, certificate validator, runtime hardening) were re-run and are all caught; the older ones were last confirmed before the gate and guards were added, so re-run `python mutation_test.py` before relying on this claim (twenty-nine backend/recursion/checker/semantics ones by named unit tests, since random
   programs cannot observe a stack-depth error), but
   the two array-bounds mutants are hit only ~1-2 times per 150 seeds: thin margin. Getting there
   needed template-based "one risky construct" programs: a purely random
   generator missed three of them. Random programs verify only ~20% of the time,
   so coverage of rarer constructs depends on such targeted templates.

## Semantics decisions that matter for safety

- Program arithmetic is **64-bit signed and every operation is proven not to
  overflow**. Division and `%` are Euclidean; `x / 0`, `MIN / -1`, `MIN % -1` are
  proven absent.
- Contracts, `assert`s and invariants use **mathematical (unbounded) integers**,
  because they are never executed (erased). A division by zero inside a contract
  is still an error. Programs cannot observe the difference.

## Runtime robustness: what "it cannot crash" can and cannot mean

No language can promise that a process is never killed. What Lise promises is narrower and checkable:
**nothing you can write in Lise makes a compiled program crash**, and the environment-caused failures
that remain are turned into early, explained, controlled exits.

| Way a program can die | Status |
|---|---|
| Overflow, bad index, division by zero, uninitialised or dangling data, data races (no threads yet) | impossible by proof (and re-checked by the backstop below) |
| Infinite loop / infinite recursion | proven absent (`decreases`; recursion needs a bound) |
| Stack overflow | worst-case stack is bounded at build time; **at start-up the program checks the OS stack limit and exits with status 70 and a message if it is too small**, before running any code |
| Heap exhaustion | there is no heap |
| Closed output pipe (SIGPIPE) | ignored: output is dropped, the program keeps running |
| A proven check fails anyway (a verifier/backend bug) | the backstop stops it with a message and **exit status 71**, never an illegal-instruction crash or memory corruption |
| Killed from outside (OOM-killer, `kill`, power loss), hardware faults, kernel bugs | cannot be prevented by a language |
| Bugs in LLVM, the linker, libc, or in Lise's own verifier/checkers | reduced by the layers above, not eliminated (see below) |

## Trusted computing base (what you must still trust)

- **Z3 and cvc5** (a false proof is accepted only if BOTH have a soundness bug on the
  same query; cvc5 runs with `arrays-exp`, an experimental option needed for constant arrays)
- **The certificate validator** (`lise_certcheck.py`, ~200 lines, standard library only) and the
  translation of obligations into the checker's input; the search that produces certificates is NOT trusted.
- **The verifier** (`lise_verify.py`, ~1,200 lines of Python): its encoding of
  Lise semantics into SMT. No independent proof checker exists yet.
- **The backend** (`lise_codegen.py`) and **LLVM** (optimiser + code generator),
  the system linker, the OS, the CPU.
- **The specification itself.** Lise proves the code meets its contracts; a
  wrong or too-weak contract is not caught.
- **The stack bound** is a conservative estimate (alloca sizes + 256 B per frame),
  not a measured value.

## Honest comparison with Ada / SPARK

Ada + SPARK is the benchmark: ~40 years of use, DO-178C / EN 50128 qualified
toolchains (GNAT Pro, GNATprove), multiple provers behind Why3, proof
replay, formal semantics, large industrial corpora.

Lise today is a ~3,000-line research compiler. On *design* it enforces more by
default (mandatory proofs, mandatory termination, checks on by default, static
stack bound, ownership). On *assurance evidence* it is far behind. **The claim
"safer than Ada" is not established and must not be made yet.**

## What would justify the claim (roadmap, in priority order)

1. *(mostly done)* Independent checking, now with checkable certificates for the arithmetic core: a solver-free checker is now a fail-closed gate with its own
   counterexample search (100% of obligations on the examples and fuzz-verified programs). Still
   missing: checking the SOLVERS' own proof objects (Z3/cvc5 emit them; the validator would need to
   understand them), formally verifying the validator in a proof assistant, and deeper nonlinear reasoning.
2. *(done)* Cross-check every obligation with a second solver (cvc5).
3. *(partly done)* Written semantics: `SEMANTICS.md` + an executable interpreter, tested against the
   verifier and the backend. Still missing: a *mechanised* semantics (a proof assistant), and an
   oracle for the static ownership/aliasing rules.
4. Translation validation of the backend (IR vs. source semantics).
5. Much larger fuzz corpus incl. records/arrays/calls/loops with contracts;
   coverage-guided; run in CI on every change.
6. *(done)* Frame rule on `mutable` parameters: a call forgets only what the callee can
   modify (computed from the callee body, transitively); the proof cache key includes it.
7. Qualification evidence (requirements traceability, tests, reviews).

## Known limitations that affect safety

- Output is fire-and-forget: if `write(2)` fails (closed pipe, full disk) that output is
  dropped and the program continues. Memory safety is unaffected, but a program cannot
  currently detect lost output. The tiny output runtime (hand-written LLVM IR) and libc's
  `write` are part of the trusted base; the integer-to-text routine is tested against
  Python on ~300 edge/random values and fuzzed.

- Outcome payloads are erased (unobservable today, matters once they can be read).
- Verifier precision: arrays are modelled as one value, so a call that writes any
  element of an array forgets all of its elements (safe but incomplete). The frame
  rule is a *soundness-relevant* analysis (a wrong modification set would let a
  caller assume false facts); it is covered by unit tests and fuzzer mutants.
- No concurrency yet (so no data-race story yet).
- `Integer` is 64-bit signed only; no wrap-around or saturating types yet.
