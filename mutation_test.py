#!/usr/bin/env python3
"""Mutation test of the safety net: plant known bugs and check that the fuzzer finds each one.

usage: python mutation_test.py [SEEDS_PER_MUTANT=400] [--only 0,3,5]
For every mutant a temporary copy of the project gets ONE deliberate bug (a removed or
weakened proof obligation, or a wrong backend instruction) and `fuzz_lise.py` must report
BUGS > 0.  A mutant that survives means the fuzzer is too weak to catch that class of bug.
"""
import concurrent.futures
import os
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
MUTANTS = [
    ("verify: no division-by-zero proof", "lise_verify.py",
     'self.oblige(st, r != 0, f"division by zero in \'{fmt_expr(e)}\'", e.loc)', "pass"),
    ("verify: overflow proof only checks lower bound", "lise_verify.py",
     '''self.oblige(st, z3.And(res >= I64_MIN, res <= I64_MAX),
                            f"integer overflow in '{fmt_expr(e)}'", e.loc)
            return res''',
     '''self.oblige(st, res >= I64_MIN,
                            f"integer overflow in '{fmt_expr(e)}'", e.loc)
            return res'''),
    ("verify: array read bound off by one", "lise_verify.py",
     'self.oblige(st, z3.And(i >= 0, i < st.ltypes[p].length),',
     'self.oblige(st, z3.And(i >= 0, i <= st.ltypes[p].length),'),
    ("verify: array write allows index -1", "lise_verify.py",
     'self.prove(st, z3.And(i >= 0, i < lt.length),', 'self.prove(st, z3.And(i >= -1, i < lt.length),'),
    ("verify: asserts are not proven", "lise_verify.py",
     'self.prove(st, g, f"assertion may not hold: {fmt_expr(s.expr)}", s.loc)', "pass"),
    ("verify: postconditions are not proven", "lise_verify.py",
     'self.prove(es, g, f"postcondition may not hold: {fmt_expr(clause)} (at return, line {loc[0]})", clause.loc)',
     "pass"),
    ("verify: loop invariant not proven on entry", "lise_verify.py",
     'self.prove(st, g, f"loop invariant may not hold on entry: {fmt_expr(inv)}", inv.loc)', "pass"),
    ("verify: loop invariant not proven preserved", "lise_verify.py",
     'self.prove(e, g, f"loop invariant may not be preserved by the loop body: {fmt_expr(inv)}", inv.loc)', "pass"),
    ("backend: Euclidean remainder fix-up removed", "lise_codegen.py",
     'self.o(f"{res} = select i1 {neg}, i64 {fix}, i64 {rem}")', 'self.o(f"{res} = add i64 {rem}, 0")'),
    ("frame rule: transitive modifications ignored", "lise_verify.py",
     "sub = self.callee_mods(sub_fn)", "sub = set()"),
    ("frame rule: array element writes ignored", "lise_verify.py",
     '''                if path.split(".")[0] in mp:
                    mods.add(path)''',
     '''                if path.split(".")[0] in mp and not isinstance(n.target, Index):
                    mods.add(path)'''),
    ("frame rule: nothing is ever havoced at calls", "lise_verify.py",
     "if mods is not None and not any(cpath == q or cpath.startswith(q + \".\") for q in mods):",
     "if True:"),
    ("returns: postconditions of aggregate-returning functions not proven", "lise_verify.py",
     'self.prove(es, g, f"postcondition may not hold: {fmt_expr(clause)} (at return, line {loc[0]})", clause.loc)',
     'None if agg is not None else self.prove(es, g, f"postcondition may not hold: {fmt_expr(clause)} (at return, line {loc[0]})", clause.loc)'),
    ("output: print_int digit offset wrong", "lise_codegen.py", "%c = add i8 %d, 48", "%c = add i8 %d, 49"),
    ("output: print_int drops the minus sign", "lise_codegen.py", "store i8 45, ptr %gm", "store i8 43, ptr %gm"),
    ("recursion: measure may stay equal at a recursive call", "lise_verify.py",
     "self.prove(cs, mg < self.entry_measure,", "self.prove(cs, mg <= self.entry_measure,"),
    ("recursion: declared maximum not enforced on entry", "lise_verify.py",
     "self.prove(st, m <= fn.dec_max,", "self.prove(st, m <= fn.dec_max + 1000,",
     ["test_lise.Recursion.test_measure_must_be_non_negative_and_bounded_on_entry"]),
    ("recursion: stack bound ignores the recursion depth", "lise_codegen.py",
     "depth = max(bounds) + 1", "depth = 1",
     ["test_lise.AotRecursion.test_bound_holds_on_a_real_small_stack",
      "test_lise.AotRecursion.test_stack_bound_covers_depth_times_frame"]),
    ("fm checker: integer tightening over-rounds", "lise_fmcheck.py",
     "return ({v: a // g for v, a in co.items()}, -((-k) // g))",
     "return ({v: a // g for v, a in co.items()}, -((-k) // g) + 1)", ["test_lise.IndependentChecker"]),
    ("fm checker: negated <= is too strong", "lise_fmcheck.py",
     "return (\"lit\", lin_add(lin_scale(d, -1), lin_const(1)))",
     "return (\"lit\", lin_add(lin_scale(d, -1), lin_const(2)))", ["test_lise.IndependentChecker"]),
    ("fm checker: remainder range off by one", "lise_fmcheck.py",
     "lin_add(rl, lin_const(-(abs(c) - 1)))", "lin_add(rl, lin_const(-(abs(c) - 2)))", ["test_lise.IndependentChecker"]),
    ("fm checker: if-then-else branches swapped", "lise_fmcheck.py",
     "self.defs.append((\"or\", [self.nnf(c, True), self.eq(vl, tb, True)]))",
     "self.defs.append((\"or\", [self.nnf(c, True), self.eq(vl, ta, True)]))", ["test_lise.IndependentChecker"]),
    ("semantics: division rounds toward floor instead of Euclid", "lise_semantics.py",
     "return (a - r) // b, r", "return a // b, r", ["test_lise.ReferenceSemantics"]),
    ("semantics: remainder uses Python's sign convention", "lise_semantics.py",
     "r = a % abs(b)\n        return", "r = a % b\n        return"),
    ("semantics: array bound check off by one", "lise_semantics.py",
     "if not isinstance(a, Arr) or not 0 <= i < len(a.items):\n                raise Stuck(\"index\", f\"index {i} out of bounds for length",
     "if not isinstance(a, Arr) or not 0 <= i <= len(a.items):\n                raise Stuck(\"index\", f\"index {i} out of bounds for length", ["test_lise.ReferenceSemantics"]),
    ("semantics: 64-bit overflow is not detected", "lise_semantics.py",
     "if not spec and not I64_MIN <= res <= I64_MAX:", "if False:", ["test_lise.ReferenceSemantics"]),
    ("semantics: `and` does not short-circuit", "lise_semantics.py",
     "return self.ev(e.left, fr, spec) and self.ev(e.right, fr, spec)",
     "l = self.ev(e.left, fr, spec)\n            r = self.ev(e.right, fr, spec)\n            return l and r", ["test_lise.ReferenceSemantics"]),
    ("semantics: assignments skip the refinement check", "lise_semantics.py",
     "self.check(slot.desc, v, f\"assignment to {fmt_expr(s.target)}\", s.loc, record_invariants=False)\n            if isinstance(slot, RefSlot):",
     "if isinstance(slot, RefSlot):", ["test_lise.ReferenceSemantics"]),
    ("semantics: old() reads the current state", "lise_semantics.py",
     "return self.ev(e.expr, fr.old, True)", "return self.ev(e.expr, fr, True)", ["test_lise.ReferenceSemantics"]),
    ("ownership: moves are not recorded", "lise_verify.py", "st.moved.add(root)", "pass", "fuzz_own.py"),
    ("ownership: aliasing of mutable arguments allowed", "lise_verify.py",
     "if any(isinstance(n, Name) and n.ident == root for n in walk(other)):", "if False:", "fuzz_own.py"),
    ("ownership: assignment to immutable variables allowed", "lise_verify.py",
     "        if not st.vars[root][1]:\n            raise LiseError(f\"cannot assign to '{root}': it is not mutable \"",
     "        if False:\n            raise LiseError(f\"cannot assign to '{root}': it is not mutable \"", "fuzz_own.py"),
    ("ownership: mutable argument need not be a mutable variable", "lise_verify.py",
     "if root not in st.vars or not st.vars[root][1]:", "if root not in st.vars:", "fuzz_own.py"),
    ("ownership: borrowed parameters can be moved", "lise_verify.py",
     "        if root in st.borrowed:\n            raise LiseError(f\"cannot move '{root}': it is a borrowed",
     "        if False:\n            raise LiseError(f\"cannot move '{root}': it is a borrowed", "fuzz_own.py"),
    ("ownership: moving inside a loop body is not detected", "lise_verify.py",
     "bad = sorted(n for n in (e.moved - st.moved) if n in st.vars)", "bad = []", "fuzz_own.py"),
    ("ownership: use of a moved variable in a call argument not detected", "lise_verify.py",
     "                if p.split(\".\")[0] in st.moved:\n                    raise LiseError(f\"use of moved value '{p.split('.')[0]}'\", arg.loc)",
     "                if False:\n                    raise LiseError(f\"use of moved value '{p.split('.')[0]}'\", arg.loc)", "fuzz_own.py"),
    ("fm checker: McCormick envelope has the wrong sign", "lise_fmcheck.py",
     "add(\"mc1\", refs, _mk({m: -1, b: la, a: lb}, -la * lb))", "add(\"mc1\", refs, _mk({m: 1, b: -la, a: -lb}, la * lb))",
     ["test_lise.IndependentChecker.test_known_cases"]),
    ("fm checker: reads of equal indices are not tied together (Ackermann)", "lise_fmcheck.py",
     "        ctx.ackermann()\n", "", ["test_lise.IndependentChecker.test_known_cases"]),
    ("fm checker: read-over-write branches swapped", "lise_fmcheck.py",
     "self.defs.append((\"or\", [diff, self.eq(rl, self.lin(v), True)]))\n            self.defs.append((\"or\", [same, self.eq(rl, self.lin(rest), True)]))",
     "self.defs.append((\"or\", [diff, self.eq(rl, self.lin(rest), True)]))\n            self.defs.append((\"or\", [same, self.eq(rl, self.lin(v), True)]))",
     ["test_lise.IndependentChecker.test_known_cases"]),
    ("fm checker: quotient magnitude bound is wrong", "lise_fmcheck.py",
     "(\"and\", [self.le(nx, ql, True), self.le(ql, xl, True)])", "(\"and\", [self.le(nx, ql, True), self.le(ql, nx, True)])",
     ["test_lise.IndependentChecker.test_known_cases"]),
    ("fm checker: exact elimination heuristic removed", "lise_fmcheck.py",
     "pool = [x for x in occ if x not in inexact] or list(occ)", "pool = list(occ)",
     ["test_lise.IndependentChecker.test_known_cases"]),
    ("fm checker: counterexamples are not verified before being reported", "lise_fmcheck.py",
     "if all(_ev(a, env) is True for a in assertions):", "if True:", ["test_lise.IndependentChecker.test_known_cases"]),
    ("gate: a verified counterexample no longer stops the build", "lise_verify.py",
     "                elif fm_status == lise_fmcheck.SAT:", "                elif False:", ["test_lise.IndependentGate.test_checker_stops_the_build_when_both_solvers_wrongly_accept"]),
    ("gate: unconfirmed proofs are accepted (fail open)", "lise_verify.py",
     "                elif self.independent == \"require\":", "                elif False:", ["test_lise.IndependentGate.test_what_the_checker_cannot_rederive_is_rejected"]),
    ("gate: dead-path pruning trusts the solvers alone", "lise_verify.py",
     "        return lise_fmcheck.check(s)[0] != lise_fmcheck.UNSAT", "        return False", ["test_lise.IndependentGate.test_gate_also_guards_dead_path_pruning"]),
    ("guard: contradictory preconditions are not detected", "lise_verify.py",
     "if self.lints and not self.feasible(st):", "if False:", ["test_lise.DeveloperGuards"]),
    ("guard: branches no path reaches are not reported", "lise_verify.py",
     "            if key not in self.branch_live:", "            if False:", ["test_lise.DeveloperGuards"]),
    ("guard: unused variables are not reported", "lise_verify.py",
     "if isinstance(n, Let) and not n.name.startswith(\"_\") and n.name not in reads:", "if False:", ["test_lise.DeveloperGuards"]),
    ("guard: code after a return is not reported", "lise_verify.py",
     "                if rest:\n                    self.lint(", "                if False:\n                    self.lint(", ["test_lise.DeveloperGuards"]),
    ("guard: unused parameters are not reported", "lise_verify.py",
     "if not p.name.startswith(\"_\") and p.name not in reads and p.name not in assigned \\", "if False and p.name not in assigned \\", ["test_lise.DeveloperGuards"]),
    ("certificate validator: integer tightening over-rounds", "lise_certcheck.py",
     "return ({v: a // g for v, a in co.items()}, -((-k) // g))", "return ({v: a // g for v, a in co.items()}, -((-k) // g) + 1)",
     ["test_lise.CertificateValidator"]),
    ("certificate validator: combines constraints with equal-sign coefficients", "lise_certcheck.py",
     "            if not (a > 0 and nb < 0):", "            if False:", ["test_lise.CertificateValidator"]),
    ("certificate validator: accepts `0 <= 0` as a contradiction", "lise_certcheck.py",
     "            if co or k <= 0:", "            if co or k < 0:", ["test_lise.CertificateValidator"]),
    ("certificate validator: incomplete case splits are accepted", "lise_certcheck.py",
     "if proof[0] != \"split\" or len(proof[1]) != len(f[1]):", "if proof[0] != \"split\":", ["test_lise.CertificateValidator"]),
    ("certificate validator: bound references are not checked for direction", "lise_certcheck.py",
     "    if kind != want:\n        raise Invalid(", "    if False:\n        raise Invalid(", ["test_lise.CertificateValidator"]),
    ("certificate validator: a branch can finish without any derivation", "lise_certcheck.py",
     "    if proof[0] != \"derive\":\n        raise Invalid(\"a finished branch needs a derivation\")", "    if False:\n        raise Invalid(\"a finished branch needs a derivation\")",
     ["test_lise.CertificateValidator"]),
    ("runtime: the start-up stack check never fails", "lise_aot.py",
     "            f\"  %enough = icmp uge i64 %cur, {need}\",", "            \"  %enough = icmp uge i64 %cur, 0\",", ["test_lise.RuntimeHardening"]),
    ("runtime: SIGPIPE is not ignored", "lise_aot.py",
     "f\"  %sig = call ptr @signal(i32 {SIGPIPE}, ptr inttoptr (i64 1 to ptr))\",", "f\"  %sig = call ptr @signal(i32 {SIGPIPE}, ptr null)\",", ["test_lise.RuntimeHardening"]),
    ("runtime: a failed backstop exits with the wrong status", "lise_codegen.py",
     "call void @_exit(i32 71)", "call void @_exit(i32 0)", ["test_lise.Safety.test_backstop_traps_when_a_proof_would_be_wrong"]),
    ("runtime: missing stack exits with success", "lise_aot.py",
     "f\"  ret i32 {EXIT_STACK}\",", "\"  ret i32 0\",", ["test_lise.RuntimeHardening"]),
    ("backend: array fill loop stops one short", "lise_codegen.py",
     'self.o(f"{c} = icmp slt i64 {i}, {n}")', 'self.o(f"{c} = icmp slt i64 {i}, {n - 1}")'),
]


def run(m, seeds):
    name, fname, old, new = m[:4]
    tests = m[4] if len(m) > 4 else None
    with tempfile.TemporaryDirectory() as d:
        dst = os.path.join(d, "p")
        shutil.copytree(HERE, dst, ignore=shutil.ignore_patterns("__pycache__", ".lise-cache", ".git"))
        path = os.path.join(dst, fname)
        src = open(path, encoding="utf-8").read()
        if old not in src:
            return name, "STALE", "mutation target not found (update mutation_test.py)"
        open(path, "w", encoding="utf-8").write(src.replace(old, new, 1))
        if isinstance(tests, str):      # mutants of the ownership rules are hunted by the ownership fuzzer
            r = subprocess.run([sys.executable, tests, str(seeds), "0"], cwd=dst, capture_output=True, text=True)
            last = (r.stdout.strip().splitlines() or ["(no output)"])[0]
            return name, ("CAUGHT" if r.returncode == 1 and "BUGS=" in last else "SURVIVED"), last
        if tests:       # mutants the fuzzer cannot observe are checked by named unit tests instead
            r = subprocess.run([sys.executable, "-m", "unittest"] + tests, cwd=dst, capture_output=True, text=True)
            return name, ("CAUGHT" if r.returncode != 0 else "SURVIVED"), "unit tests: " + (
                "failed as required" if r.returncode != 0 else "all passed")
        r = subprocess.run([sys.executable, "fuzz_lise.py", str(seeds), "0"], cwd=dst,
                           capture_output=True, text=True)
        last = (r.stdout.strip().splitlines() or ["(no output)"])[0]
        return name, ("CAUGHT" if r.returncode == 1 and "BUGS=" in last else "SURVIVED"), last


def main():
    args = sys.argv[1:]
    only = None
    if "--only" in args:
        k = args.index("--only")
        only = {int(x) for x in args[k + 1].split(",")}
        del args[k:k + 2]
    seeds = int(args[0]) if args else 400
    mutants = [m for i, m in enumerate(MUTANTS) if only is None or i in only]
    bad = 0
    with concurrent.futures.ThreadPoolExecutor(max_workers=min(4, os.cpu_count() or 1)) as ex:
        for name, status, detail in ex.map(lambda m: run(m, seeds), mutants):
            print(f"{status:9} {name}   [{detail}]")
            bad += status != "CAUGHT"
    print(f"{len(mutants) - bad}/{len(mutants)} mutants caught")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
