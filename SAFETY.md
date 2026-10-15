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
| Unbounded recursion / stack overflow | recursion rejected; **static worst-case stack bound** computed, build fails if over the limit (default 1 MiB) |
| Unproven obligations | an SMT `unknown`/timeout is a compile error, never a pass |
| Violated contracts | `requires`/`ensures`/invariants/refinements proven |

## Defence in depth (beyond what Ada gives you by default)

1. **Proofs are mandatory.** In Ada/SPARK you can compile code whose proofs
   failed or were never run. In Lise "no proof, no binary".
2. **Checked builds are the default.** The proven checks are *also* compiled in
   (overflow-trapping arithmetic, bounds checks, division checks) and trap
   (`llvm.trap`) if they ever fire. A verifier or backend bug then stops the
   program instead of silently corrupting memory. `--unchecked` erases them
   (zero cost) and is an explicit opt-in. Arithmetic never uses `nsw`/`nuw`, so
   even unchecked code cannot hit LLVM poison/UB from arithmetic.
3. **Builds never trust the proof cache.** `build`/`run` re-prove everything;
   a tampered `.lise-cache/` cannot produce a binary.
4. **Differential fuzzing of the verifier** (`python fuzz_lise.py N`): random
   programs are verified; every accepted program is run on many inputs against a
   Python reference interpreter (unbounded integers, Euclidean division). Any
   overflow / div-by-zero / out-of-bounds in the reference, any result mismatch,
   any trap in checked code is reported as a BUG. The fuzzer itself was
   mutation-tested: six deliberately injected bugs (missing div-zero proof,
   weakened overflow proof, wrong Euclidean remainder, two off-by-one bounds
   proofs, broken array fill) were all detected.
5. **Static stack bound** instead of a runtime `Storage_Error`.

## Trusted computing base (what you must still trust)

- **Z3** (a single SMT solver; a Z3 soundness bug could accept a false proof)
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

1. Independent proof-certificate checker (shrink the TCB below Z3 + verifier).
2. Cross-check every obligation with a second solver (e.g. cvc5); disagreement = error.
3. Written formal semantics of Lise; verifier and backend both checked against it.
4. Translation validation of the backend (IR vs. source semantics).
5. Much larger fuzz corpus incl. records/arrays/calls/loops with contracts;
   coverage-guided; run in CI on every change.
6. Frame rules on `mutable` parameters (precision, not soundness).
7. Qualification evidence (requirements traceability, tests, reviews).

## Known limitations that affect safety

- Outcome payloads are erased (unobservable today, matters once they can be read).
- Verifier precision: a call to a `mutable` function forgets array contents it
  did not promise to preserve (safe but incomplete; may reject valid programs).
- No concurrency yet (so no data-race story yet).
- `Integer` is 64-bit signed only; no wrap-around or saturating types yet.
