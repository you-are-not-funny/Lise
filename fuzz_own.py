#!/usr/bin/env python3
"""Fuzzer for the static ownership rules (moves, borrowing, aliasing, mutability).

Random programs move, borrow, alias and mutate records in many orders.  Most statements follow a
simple model of the rules (so many programs are valid), the rest break the rules on purpose.
Every program the verifier ACCEPTS is run on the reference semantics, which enforces ownership
dynamically by storage identity (lise_semantics.py): it must never get STUCK on any input.
A STUCK on an accepted program means a static rule is unsound.

usage: python fuzz_own.py [COUNT=300] [START_SEED=0]
"""
import random
import sys

HEADER = """record R
    a: Integer where value >= 0 and value <= 9
    b: Integer where value >= 0 and value <= 9
end
fn take(r: consume R) -> Integer
is
    return r.a
end
fn peek(r: R) -> Integer
is
    return r.a
end
fn bump(r: mutable R)
is
    r.a := 1
end
fn both(x: mutable R, y: R) -> Integer
is
    x.a := 2
    return y.b
end
fn both2(x: mutable R, y: mutable R)
is
    x.a := 3
    y.b := 4
end
fn mix(x: mutable R, k: Integer where value >= 0 and value <= 9)
is
    x.a := k
end
"""

BAD_HELPERS = [   # each breaks one rule inside a helper (never called): the verifier must reject the program
    "fn bad_move_borrowed(r: R) -> Integer\nis\n    return take(r)\nend\n",
    "fn bad_assign_in(r: R)\nis\n    r.a := 1\nend\n",
    "fn bad_double_take(r: consume R) -> Integer\nis\n    let x = take(r)\n    return take(r)\nend\n",
    "fn bad_alias(x: mutable R) -> Integer\nis\n    both(x, x)\n    return 0\nend\n",
    "fn bad_mutable_of_in(r: R)\nis\n    bump(r)\nend\n",
    "fn bad_use_after_move(r: consume R) -> Integer\nis\n    let x = take(r)\n    return r.a\nend\n",
]


class Gen:
    def __init__(self, rng):
        self.rng, self.n = rng, 0
        self.vars = {}          # name -> {"mut": bool, "moved": bool}
        self.lines = []

    def live(self, mut=False):
        return [v for v, s in self.vars.items() if not s["moved"] and (s["mut"] or not mut)]

    def temp(self):
        self.n += 1
        return f"t{self.n}"

    def action(self, sp, valid, in_loop=False):
        rng, V = self.rng, list(self.vars)
        kinds = ["peek", "take", "bump", "both", "both2", "mix", "set", "alias_mix"]
        k = rng.choice(kinds)

        def pick(pool):
            return rng.choice(pool) if pool else rng.choice(V)

        if valid:
            outer_ok = not in_loop
            if k == "take":
                pool = self.live() if outer_ok else []
                if not pool:
                    k = "peek"
            if k in ("bump", "mix", "set") and not self.live(True):
                k = "peek"
            if k in ("both", "both2", "alias_mix") and len(self.live()) < 2 and k != "alias_mix":
                k = "peek"
            if k == "alias_mix":
                k = "peek"
            if k == "peek" and not self.live():
                return
        out = []
        if k == "peek":
            v = pick(self.live() if valid else V)
            out.append(f"let {self.temp()} = peek({v})")
        elif k == "take":
            v = pick(self.live() if valid else V)
            out.append(f"let {self.temp()} = take({v})")
            self.vars[v]["moved"] = True
        elif k == "bump":
            v = pick(self.live(True) if valid else V)
            out.append(f"bump({v})")
        elif k == "both":
            i = pick(self.live(True) if valid else V)
            j = pick([x for x in self.live() if x != i] if valid else V)
            out.append(f"let {self.temp()} = both({i}, {j})")
        elif k == "both2":
            i = pick(self.live(True) if valid else V)
            j = pick([x for x in self.live(True) if x != i] if valid else V)
            out.append(f"both2({i}, {j})")
        elif k == "mix":
            v = pick(self.live(True) if valid else V)
            out.append(f"mix({v}, p0)")
        elif k == "set":
            v = pick(self.live(True) if valid else V)
            out.append(f"{v}.a := {rng.randint(0, 9)}")
        else:                                              # alias_mix (invalid): mutable arg also read in the same call
            v = pick(V)
            out.append(f"mix({v}, {v}.a)")
        self.lines.extend(sp + o for o in out)

    def block(self, sp, depth, count, valid_p, in_loop=False):
        rng = self.rng
        for _ in range(count):
            r = rng.random()
            valid = rng.random() < valid_p
            if depth > 0 and r < .2:
                c = rng.randint(2, 6)
                self.lines.append(f"{sp}if p0 > {c} then")
                before = {v: dict(s) for v, s in self.vars.items()}
                self.block(sp + "    ", depth - 1, rng.randint(1, 2), valid_p, in_loop)
                for v in self.vars:                         # a variable moved on one path is unusable afterwards
                    self.vars[v]["moved"] = self.vars[v]["moved"] or before[v]["moved"]
                self.lines.append(f"{sp}end")
            elif depth > 0 and r < .32:
                self.n += 1
                i = f"i{self.n}"
                self.lines += [f"{sp}var {i}: Integer := 0", f"{sp}while {i} < p0",
                               f"{sp}invariant 0 <= {i} and {i} <= p0", f"{sp}decreases p0 - {i}", f"{sp}do"]
                self.block(sp + "    ", depth - 1, rng.randint(1, 2), valid_p, True)
                self.lines += [f"{sp}    {i} := {i} + 1", f"{sp}end"]
            else:
                self.action(sp, valid, in_loop)


def gen_program(seed):
    rng = random.Random(seed)
    g = Gen(rng)
    nvars = rng.randint(2, 4)
    decl = []
    for i in range(nvars):
        mut = rng.random() < .75
        g.vars[f"v{i}"] = {"mut": mut, "moved": False}
        decl.append(f"    {'var' if mut else 'let'} v{i}: R := R({rng.randint(0, 9)}, {rng.randint(0, 9)})")
    g.block("    ", 2, rng.randint(3, 8), rng.choice([.6, .85, .95]))
    helpers = rng.choice(BAD_HELPERS) if rng.random() < .2 else ""
    src = HEADER + helpers + "fn f(p0: Integer where value >= 0 and value <= 9) -> Integer\nis\n" + \
          "\n".join(decl) + "\n" + "\n".join(g.lines) + "\n    return 0\nend\n"
    return src, bool(helpers)


def run_seed(seed):
    from lise_lexer import lex
    from lise_parser import Parser
    from lise_semantics import Machine, Stuck
    from lise_verify import check_source
    src, has_bad_helper = gen_program(seed)
    rep = check_source(src, f"own{seed}.lise", timeout_ms=3000, independent="report", lints=False)
    if not rep.ok:
        return "rejected", src
    if has_bad_helper:
        return "BUG(verifier accepted a program containing a rule-breaking helper)", src
    prog = Parser(lex(src)).parse_program()
    for p0 in range(0, 10):
        try:
            Machine(prog).run_function("f", (p0,))
        except Stuck as st:
            return f"BUG(accepted program is STUCK for p0={p0}: {st})", src
    return "verified", src


def main():
    sys.setrecursionlimit(20000)
    count = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    start = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    stats, bugs = {"verified": 0, "rejected": 0}, []
    for seed in range(start, start + count):
        status, src = run_seed(seed)
        if status.startswith("BUG"):
            bugs.append((seed, status, src))
        else:
            stats[status] += 1
    print(f"seeds {start}..{start + count - 1}: verified={stats['verified']} rejected={stats['rejected']} "
          f"BUGS={len(bugs)}")
    for seed, status, src in bugs[:5]:
        print(f"  seed {seed}: {status}")
    if bugs:
        print("PROGRAM-BEGIN\n" + bugs[0][2] + "PROGRAM-END")
    return 1 if bugs else 0


if __name__ == "__main__":
    sys.exit(main())
