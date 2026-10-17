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
     "lin_add(r, lin_const(-(abs(c) - 1)))", "lin_add(r, lin_const(-(abs(c) - 2)))", ["test_lise.IndependentChecker"]),
    ("fm checker: if-then-else branches swapped", "lise_fmcheck.py",
     "self.defs.append((\"or\", [self.nnf(c, True), self.eq(v, tb, True)]))",
     "self.defs.append((\"or\", [self.nnf(c, True), self.eq(v, ta, True)]))", ["test_lise.IndependentChecker"]),
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
