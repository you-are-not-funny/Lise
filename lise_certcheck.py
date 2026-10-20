#!/usr/bin/env python3
"""Standalone validator for Lise proof certificates.  Standard library only: no z3, no cvc5, no
imports from the rest of Lise.  This is the small trusted core for the arithmetic proofs: the
(complicated, untrusted) prover in lise_fmcheck.py searches for a refutation and writes it down;
this file merely CHECKS it, step by step, with exact integer arithmetic.

A certificate is JSON:
  {"version": 1,
   "formulas": [F, ...],       # the formula to refute, in negation normal form (conjunction of F's)
   "rels":     [[a, b, m]],    # monomial variable m stands for the product a*b
   "proof":    P}

  F := ["true"] | ["false"] | ["and", [F..]] | ["or", [F..]]
     | ["lit", C]               # the linear constraint C holds
     | ["bvar", id, positive]   # an opaque propositional atom
  C := [[[var, coeff], ...], const]          meaning  sum(coeff*var) + const <= 0   (over the integers)

  P := ["derive", [step, ...]]   # the constraints collected on this branch are contradictory
     | ["split",  [P, ...]]      # the next pending "or" is split; one proof per alternative
     | ["closed"]                # the branch closed by itself (`false`, or an atom needed both ways)

Branch handling is deterministic (see walk()): formulas are processed in the order given (children of
"and" in order, `lit`s are collected in that order as facts 0, 1, 2, ...); the first `or` met is the one
that is split, with the remaining formulas still pending.  A derivation starts from the branch's facts and
every step must be a valid integer consequence of earlier facts:
  ["tighten", i]            divide fact i by the gcd of its coefficients, rounding the constant up
  ["comb", i, j, v]         b*fact_i + a*fact_j, eliminating v (a = coeff of v in i > 0, -b = coeff in j < 0)
  ["pf", kind, rel, refs..] a product fact about m = a*b from bounds that earlier facts state
  ["contra", i]             fact i is `0 <= -k` with k > 0: the contradiction (must be the last step)

usage: python lise_certcheck.py FILE.json | DIRECTORY
"""
import json
import math
import os
import sys


class Invalid(Exception):
    pass


def tighten(c):
    co, k = c
    if not co:
        return c
    g = 0
    for a in co.values():
        g = math.gcd(g, abs(a))
    if g > 1:
        return ({v: a // g for v, a in co.items()}, -((-k) // g))
    return c


def con(c):
    return ({v: a for v, a in c[0]}, c[1])


def unit_bound(c, var):
    """A unit constraint a*var + k <= 0 as ('lo'|'hi', integer bound)."""
    co, k = c
    if set(co) != {var}:
        raise Invalid(f"not a unit constraint on {var}")
    a = co[var]
    return ("hi", (-k) // a) if a > 0 else ("lo", -((-k) // (-a)))


def bound(F, idx, var, want):
    if not (isinstance(idx, int) and 0 <= idx < len(F)):
        raise Invalid("bad bound reference")
    kind, val = unit_bound(F[idx], var)
    if kind != want:
        raise Invalid(f"fact {idx} is not a {want}er bound of {var}")
    return val


def mk(co, k):
    return ({v: a for v, a in co.items() if a}, k)


def product_fact(F, rels, kind, ri, refs):
    a, b, m = rels[ri]
    if kind in ("sqmax", "sqmin"):
        if a != b:
            raise Invalid("square fact on a non-square")
        lo, hi = bound(F, refs[0], a, "lo"), bound(F, refs[1], a, "hi")
        if kind == "sqmax":
            return mk({m: 1}, -max(lo * lo, hi * hi))
        if not (lo > 0 or hi < 0):
            raise Invalid("sqmin needs a bound excluding 0")
        return mk({m: -1}, min(lo * lo, hi * hi))
    if kind == "sqnn":
        if a != b:
            raise Invalid("square fact on a non-square")
        return mk({m: -1}, 0)
    if a == b:
        raise Invalid("product fact on a square")
    if kind in ("ssnn", "osnp"):
        def side(idx, var):
            kd, val = unit_bound(F[idx], var)
            return kd, val
        ka, va = side(refs[0], a)
        kb, vb = side(refs[1], b)
        if kind == "ssnn":
            if not ((ka == "lo" and va >= 0 and kb == "lo" and vb >= 0) or (ka == "hi" and va <= 0 and kb == "hi" and vb <= 0)):
                raise Invalid("signs do not justify m >= 0")
            return mk({m: -1}, 0)
        if not ((ka == "lo" and va >= 0 and kb == "hi" and vb <= 0) or (ka == "hi" and va <= 0 and kb == "lo" and vb >= 0)):
            raise Invalid("signs do not justify m <= 0")
        return mk({m: 1}, 0)
    la, ua = bound(F, refs[0], a, "lo"), bound(F, refs[1], a, "hi")
    lb, ub = bound(F, refs[2], b, "lo"), bound(F, refs[3], b, "hi")
    corners = [la * lb, la * ub, ua * lb, ua * ub]
    if kind == "clo":
        return mk({m: -1}, min(corners))
    if kind == "chi":
        return mk({m: 1}, -max(corners))
    if kind == "mc1":
        return mk({m: -1, b: la, a: lb}, -la * lb)
    if kind == "mc2":
        return mk({m: -1, b: ua, a: ub}, -ua * ub)
    if kind == "mc3":
        return mk({m: 1, b: -ua, a: -lb}, ua * lb)
    if kind == "mc4":
        return mk({m: 1, b: -la, a: -ub}, la * ub)
    raise Invalid(f"unknown product fact {kind}")


def verify_derivation(cons, steps, rels):
    F = list(cons)
    if not steps or steps[-1][0] != "contra":
        raise Invalid("a derivation must end with a contradiction")
    for n, st in enumerate(steps):
        op = st[0]
        if op == "tighten":
            F.append(tighten(F[st[1]]))
        elif op == "comb":
            _, i, j, v = st
            p, q = F[i], F[j]
            a, nb = p[0].get(v, 0), q[0].get(v, 0)
            if not (a > 0 and nb < 0):
                raise Invalid("comb needs a positive and a negative coefficient")
            b = -nb
            co = dict()
            for var, c in p[0].items():
                co[var] = co.get(var, 0) + b * c
            for var, c in q[0].items():
                co[var] = co.get(var, 0) + a * c
            F.append(({var: c for var, c in co.items() if c}, b * p[1] + a * q[1]))
        elif op == "pf":
            F.append(product_fact(F, rels, st[1], st[2], st[3:]))
        elif op == "contra":
            if n != len(steps) - 1:
                raise Invalid("contradiction must be last")
            co, k = F[st[1]]
            if co or k <= 0:
                raise Invalid("not a contradiction")
            return True
        else:
            raise Invalid(f"unknown step {op}")
    raise Invalid("no contradiction")


def walk(cons, bools, pending, proof, rels):
    pending, cons, bools = list(pending), list(cons), dict(bools)
    while pending:
        f = pending.pop()
        k = f[0]
        if k == "true":
            continue
        if k == "false":
            return                                     # branch closed
        if k == "and":
            pending.extend(reversed(f[1]))
        elif k == "lit":
            cons.append(con(f[1]))
        elif k == "bvar":
            if bools.get(f[1], f[2]) != f[2]:
                return                                 # an atom needed both ways: closed
            bools[f[1]] = f[2]
        else:                                          # "or"
            if proof[0] == "derive":
                verify_derivation(cons, proof[1], rels)
                return
            if proof[0] != "split" or len(proof[1]) != len(f[1]):
                raise Invalid("an `or` needs a split with one proof per alternative")
            for alt, sub in zip(f[1], proof[1]):
                walk(cons, bools, pending + [alt], sub, rels)
            return
    if proof[0] != "derive":
        raise Invalid("a finished branch needs a derivation")
    verify_derivation(cons, proof[1], rels)


def verify(cert):
    """Returns (True, '') or (False, reason)."""
    try:
        if cert.get("version") != 1:
            raise Invalid("unknown certificate version")
        rels = [tuple(r) for r in cert["rels"]]
        walk([], {}, list(reversed(cert["formulas"])), cert["proof"], rels)
        return True, ""
    except Invalid as ex:
        return False, str(ex)
    except (KeyError, IndexError, TypeError, ValueError, RecursionError) as ex:
        return False, f"malformed certificate ({type(ex).__name__}: {ex})"


def main(argv):
    paths = []
    for a in argv[1:]:
        if os.path.isdir(a):
            paths += [os.path.join(a, f) for f in sorted(os.listdir(a)) if f.endswith(".json")]
        else:
            paths.append(a)
    if not paths:
        print(__doc__)
        return 2
    bad = 0
    for p in paths:
        with open(p, encoding="utf-8") as fh:
            ok, why = verify(json.load(fh))
        print(f"{'VALID  ' if ok else 'INVALID'} {p}" + ("" if ok else f": {why}"))
        bad += not ok
    print(f"{len(paths) - bad}/{len(paths)} certificates valid")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
