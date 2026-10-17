"""A small, solver-free proof checker for the linear-integer-arithmetic core of every obligation.

Z3 and cvc5 are big programs.  This module is ~250 lines of exact integer arithmetic and shares no
code with either of them.  Given the assertions of an obligation whose negation the solvers called
UNSAT, it independently re-derives the contradiction using
  * case splitting on the boolean structure (and / or / not / implies / iff / if-then-else),
  * exact linear arithmetic over the integers: Fourier-Motzkin elimination with integer tightening
    (divide by the gcd and round), every step a valid consequence over the integers,
  * linearisation of `/` and `%` by a literal (x = c*q + r, 0 <= r < |c|, Euclidean),
  * abstraction of everything else (nonlinear products, array reads, enums, ...) by a fresh
    variable per distinct term -- sound for UNSAT: if the abstraction is contradictory, so is the
    original.
It answers only "unsat" (independently confirmed) or "unknown" (outside its fragment or over budget).
It never claims SAT, so it cannot reject anything; it can only add confidence.
"""
import math

import z3

UNSAT, UNKNOWN = "unsat", "unknown"
NODE_BUDGET = 4000        # case-split nodes
FM_CAP = 250              # constraints kept during elimination


class _Budget(Exception):
    pass


# ----------------------------------------------------------------------------- linear forms
# A linear form is (coeffs: dict var -> int, const: int) meaning  sum(coeff*var) + const.
def lin_const(c):
    return ({}, c)


def lin_var(v):
    return ({v: 1}, 0)


def lin_add(a, b, k=1):
    co = dict(a[0])
    for v, c in b[0].items():
        co[v] = co.get(v, 0) + k * c
        if co[v] == 0:
            del co[v]
    return (co, a[1] + k * b[1])


def lin_scale(a, k):
    return ({v: c * k for v, c in a[0].items()} if k else {}, a[1] * k)


def is_const(a):
    return not a[0]


# ----------------------------------------------------------------------------- Fourier-Motzkin
def tighten(c):
    """sum(a_i x_i) + const <= 0 over the integers: divide by gcd(a_i), rounding the constant up."""
    co, k = c
    if not co:
        return c
    g = 0
    for a in co.values():
        g = math.gcd(g, abs(a))
    if g > 1:
        return ({v: a // g for v, a in co.items()}, -((-k) // g))
    return c


def fm_infeasible(cons):
    """True if the conjunction `lin <= 0` is infeasible over the integers (proved); False if not proved."""
    work, seen = [], set()
    for c in cons:
        c = tighten(c)
        if not c[0]:
            if c[1] > 0:
                return True
            continue
        key = (tuple(sorted(c[0].items())), c[1])
        if key not in seen:
            seen.add(key)
            work.append(c)
    while work:
        occurrences = {}
        for co, _ in work:
            for v, a in co.items():
                p, n = occurrences.get(v, (0, 0))
                occurrences[v] = (p + (a > 0), n + (a < 0))
        v = min(occurrences, key=lambda x: occurrences[x][0] * occurrences[x][1])
        pos = [c for c in work if c[0].get(v, 0) > 0]
        neg = [c for c in work if c[0].get(v, 0) < 0]
        rest = [c for c in work if v not in c[0]]
        new, seen = [], set()
        for c in rest + [lin_add(lin_scale(p, -n[0][v]), lin_scale(n, p[0][v])) for p in pos for n in neg]:
            c = tighten(c)
            if not c[0]:
                if c[1] > 0:
                    return True
                continue
            key = (tuple(sorted(c[0].items())), c[1])
            if key not in seen:
                seen.add(key)
                new.append(c)
        if len(new) > FM_CAP:
            return False
        work = new
    return False


# ----------------------------------------------------------------------------- z3 AST -> NNF
class _Ctx:
    def __init__(self):
        self.defs, self.divs, self.fresh_n = [], {}, 0

    def fresh(self, hint):
        self.fresh_n += 1
        return f"{hint}#{self.fresh_n}"

    # ---- integer terms
    def term(self, e):
        k = e.decl().kind() if z3.is_app(e) else None
        if z3.is_int_value(e):
            return lin_const(e.as_long())
        if k == z3.Z3_OP_ADD:
            r = lin_const(0)
            for a in e.children():
                r = lin_add(r, self.term(a))
            return r
        if k == z3.Z3_OP_SUB:
            ch = e.children()
            r = self.term(ch[0])
            for a in ch[1:]:
                r = lin_add(r, self.term(a), -1)
            return r
        if k == z3.Z3_OP_UMINUS:
            return lin_scale(self.term(e.arg(0)), -1)
        if k == z3.Z3_OP_MUL:
            parts = [self.term(a) for a in e.children()]
            consts = [p for p in parts if is_const(p)]
            if len(consts) >= len(parts) - 1:
                r = lin_const(1)
                nonconst = [p for p in parts if not is_const(p)]
                for c in consts:
                    r = lin_scale(r, c[1])
                return lin_scale(nonconst[0], r[1]) if nonconst else r
            return self.opaque(e)
        if k in (z3.Z3_OP_IDIV, z3.Z3_OP_MOD):
            num, den = self.term(e.arg(0)), self.term(e.arg(1))
            if is_const(den) and den[1] != 0:
                c = den[1]
                key = (tuple(sorted(num[0].items())), num[1], c)
                if key not in self.divs:
                    q, r = lin_var(self.fresh("q")), lin_var(self.fresh("r"))
                    self.divs[key] = (q, r)
                    # num = c*q + r,  0 <= r <= |c|-1
                    eq = lin_add(num, lin_add(lin_scale(q, c), r), -1)
                    self.defs.append(("and", [("lit", eq), ("lit", lin_scale(eq, -1)),
                                              ("lit", lin_scale(r, -1)), ("lit", lin_add(r, lin_const(-(abs(c) - 1))))]))
                q, r = self.divs[key]
                return q if k == z3.Z3_OP_IDIV else r
            return self.opaque(e)
        if k == z3.Z3_OP_ITE and z3.is_int(e):
            v = lin_var(self.fresh("ite"))
            c = e.arg(0)
            ta, tb = self.term(e.arg(1)), self.term(e.arg(2))
            self.defs.append(("or", [self.nnf(c, False), self.eq(v, ta, True)]))
            self.defs.append(("or", [self.nnf(c, True), self.eq(v, tb, True)]))
            return v
        return self.opaque(e)

    def opaque(self, e):
        return lin_var(f"t{e.get_id()}")

    # ---- atoms
    def le(self, a, b, positive=True):          # a <= b   /  not (a <= b)  ==  a >= b+1
        d = lin_add(a, b, -1)
        if positive:
            return ("lit", d)
        return ("lit", lin_add(lin_scale(d, -1), lin_const(1)))

    def eq(self, a, b, positive):
        d = lin_add(a, b, -1)
        if positive:
            return ("and", [("lit", d), ("lit", lin_scale(d, -1))])
        return ("or", [("lit", lin_add(d, lin_const(1))), ("lit", lin_add(lin_scale(d, -1), lin_const(1)))])

    # ---- boolean structure, negation pushed to the leaves
    def nnf(self, e, pos):
        if z3.is_true(e):
            return ("true",) if pos else ("false",)
        if z3.is_false(e):
            return ("false",) if pos else ("true",)
        k = e.decl().kind() if z3.is_app(e) else None
        ch = e.children() if z3.is_app(e) else []
        if k == z3.Z3_OP_NOT:
            return self.nnf(ch[0], not pos)
        if k == z3.Z3_OP_AND:
            return ("and" if pos else "or", [self.nnf(c, pos) for c in ch])
        if k == z3.Z3_OP_OR:
            return ("or" if pos else "and", [self.nnf(c, pos) for c in ch])
        if k == z3.Z3_OP_IMPLIES:
            return ("or", [self.nnf(ch[0], not pos), self.nnf(ch[1], pos)]) if pos else \
                   ("and", [self.nnf(ch[0], True), self.nnf(ch[1], False)])
        if k == z3.Z3_OP_XOR and len(ch) == 2:
            return self.nnf(z3.Not(ch[0] == ch[1]), pos)
        if k == z3.Z3_OP_ITE and z3.is_bool(e):
            c, a, b = ch
            return ("or", [("and", [self.nnf(c, True), self.nnf(a, pos)]),
                           ("and", [self.nnf(c, False), self.nnf(b, pos)])])
        if k == z3.Z3_OP_EQ and len(ch) == 2:
            a, b = ch
            if z3.is_bool(a):
                same = ("or", [("and", [self.nnf(a, True), self.nnf(b, True)]),
                               ("and", [self.nnf(a, False), self.nnf(b, False)])])
                diff = ("or", [("and", [self.nnf(a, True), self.nnf(b, False)]),
                               ("and", [self.nnf(a, False), self.nnf(b, True)])])
                return same if pos else diff
            if z3.is_int(a):
                return self.eq(self.term(a), self.term(b), pos)
        if k == z3.Z3_OP_DISTINCT and len(ch) == 2 and z3.is_int(ch[0]):
            return self.eq(self.term(ch[0]), self.term(ch[1]), not pos)
        if k in (z3.Z3_OP_LE, z3.Z3_OP_LT, z3.Z3_OP_GE, z3.Z3_OP_GT) and z3.is_int(ch[0]):
            a, b = self.term(ch[0]), self.term(ch[1])
            if k == z3.Z3_OP_LT:       # a < b  ==  a + 1 <= b
                return self.le(lin_add(a, lin_const(1)), b, pos)
            if k == z3.Z3_OP_GE:
                return self.le(b, a, pos)
            if k == z3.Z3_OP_GT:       # a > b  ==  b + 1 <= a
                return self.le(lin_add(b, lin_const(1)), a, pos)
            return self.le(a, b, pos)
        return ("bvar", e.get_id(), pos)             # any other boolean term: an opaque propositional atom


# ----------------------------------------------------------------------------- search
def _refute(cons, bools, pending, counter):
    """True if every branch of the case split is contradictory."""
    pending = list(pending)
    cons, bools = list(cons), dict(bools)
    while pending:
        f = pending.pop()
        k = f[0]
        if k == "true":
            continue
        if k == "false":
            return True
        if k == "and":
            pending.extend(f[1])
        elif k == "lit":
            cons.append(f[1])
        elif k == "bvar":
            if bools.get(f[1], f[2]) != f[2]:
                return True
            bools[f[1]] = f[2]
        else:                                       # "or": every alternative must be refuted
            counter[0] += 1
            if counter[0] > NODE_BUDGET:
                raise _Budget()
            if fm_infeasible(cons):
                return True
            return all(_refute(cons, bools, pending + [alt], counter) for alt in f[1])
    return fm_infeasible(cons)


def check_assertions(assertions):
    """Independently confirm that the conjunction of z3 `assertions` is unsatisfiable."""
    try:
        ctx = _Ctx()
        formulas = [ctx.nnf(a, True) for a in assertions]
        formulas.extend(ctx.defs)
        counter = [0]
        return (UNSAT, "") if _refute([], {}, formulas, counter) else (UNKNOWN, "not refuted within the linear fragment")
    except _Budget:
        return UNKNOWN, "case-split budget exceeded"
    except RecursionError:
        return UNKNOWN, "formula too deep"


def check(z3_solver):
    return check_assertions(list(z3_solver.assertions()))
