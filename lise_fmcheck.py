"""Independent, solver-free checker for the arithmetic core of every proof obligation  (v2).

Z3 and cvc5 are huge programs.  This module is a small, separate implementation (no solver inside)
that is given the assertions of an obligation whose NEGATION the solvers called UNSAT, and tries to
reach one of two verdicts on its own:

  "unsat"    it re-derived the contradiction itself  (independent confirmation)
  "sat"      it found a concrete counterexample and VERIFIED it by evaluating the original assertions
             with its own evaluator.  This means both solvers (or the verifier's encoding) are wrong:
             a hard error that stops the build.
  "unknown"  neither.  The verifier treats this as "not confirmed" and rejects (fail closed).

Techniques (all sound for UNSAT, i.e. only valid consequences are used):
  * case splitting on boolean structure; exact Fourier-Motzkin elimination over the integers with
    gcd tightening;
  * polynomial normal form: products of variables become monomial variables, with interval and
    McCormick bounds added from the bounds known in each case;
  * division / remainder by a literal: exact; by a variable: Euclid facts (0 <= r < |n|, x = n*q + r);
  * arrays: read-over-write and constant arrays by rewriting, plus functional consistency of reads
    (Ackermann); enum values as bounded integers; uninterpreted sorts as unbounded integers;
  * everything else is abstracted by one fresh variable per distinct term.
"""
import json
import math
import random

import z3

import lise_certcheck

UNSAT, SAT, UNKNOWN, INVALID = "unsat", "sat", "unknown", "invalid"
NODE_BUDGET = 6000
FM_CAP = 300
ACKERMANN_LIMIT = 10
MODEL_TRIES = 1500


class _Budget(Exception):
    pass


class _Unsupported(Exception):
    pass


# ----------------------------------------------------------------------------- polynomials
# poly: dict  monomial (sorted tuple of variable names, () = constant)  ->  int coefficient
def p_const(c):
    return {(): c} if c else {}


def p_var(v):
    return {(v,): 1}


def p_add(a, b, k=1):
    r = dict(a)
    for m, c in b.items():
        r[m] = r.get(m, 0) + k * c
        if r[m] == 0:
            del r[m]
    return r


def p_scale(a, k):
    return {m: c * k for m, c in a.items()} if k else {}


def p_mul(a, b):
    r = {}
    for m1, c1 in a.items():
        for m2, c2 in b.items():
            m = tuple(sorted(m1 + m2))
            r[m] = r.get(m, 0) + c1 * c2
            if r[m] == 0:
                del r[m]
    return r


def p_is_const(a):
    return all(m == () for m in a)


def p_const_value(a):
    return a.get((), 0)


# linear form (after monomials are named): (coeffs: var -> int, const)
def lin_add(a, b, k=1):
    co = dict(a[0])
    for v, c in b[0].items():
        co[v] = co.get(v, 0) + k * c
        if co[v] == 0:
            del co[v]
    return (co, a[1] + k * b[1])


def lin_scale(a, k):
    return ({v: c * k for v, c in a[0].items()} if k else {}, a[1] * k)


def lin_const(c):
    return ({}, c)


# ----------------------------------------------------------------------------- Fourier-Motzkin
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


def var_bounds(cons):
    """Interval of every variable that has unit constraints: {var: [lo|None, hi|None]}."""
    b = {}
    for co, k in cons:
        if len(co) == 1:
            (v, a), = co.items()
            lo_hi = b.setdefault(v, [None, None])
            if a > 0:            # a*v + k <= 0  ->  v <= floor(-k / a)
                hi = (-k) // a
                lo_hi[1] = hi if lo_hi[1] is None else min(lo_hi[1], hi)
            else:                # -|a|*v + k <= 0  ->  v >= ceil(k / |a|)
                lo = -((-k) // (-a))
                lo_hi[0] = lo if lo_hi[0] is None else max(lo_hi[0], lo)
    return b


def bound_index(F):
    """Tightest unit bounds known: {var: {"lo": (value, fact index), "hi": (value, fact index)}}."""
    out = {}
    for i, (co, k) in enumerate(F):
        if len(co) == 1:
            (v, a), = co.items()
            d = out.setdefault(v, {})
            if a > 0:
                val = (-k) // a
                if "hi" not in d or val < d["hi"][0]:
                    d["hi"] = (val, i)
            else:
                val = -((-k) // (-a))
                if "lo" not in d or val > d["lo"][0]:
                    d["lo"] = (val, i)
    return out


def _mk(co, k):
    return ({v: a for v, a in co.items() if a}, k)


def derive(cons, rels):
    """Try to refute the conjunction of `cons` (each `lin <= 0`).  Returns a derivation (a list of steps
    that lise_certcheck can verify) or None.  The search below is UNTRUSTED: only the steps matter."""
    F, steps, deps = list(cons), {}, {}
    n0 = len(F)

    def push(c, step, dep):
        F.append(c)
        steps[len(F) - 1], deps[len(F) - 1] = step, dep
        return len(F) - 1

    # ---- facts about product (monomial) variables, from the bounds the facts already state
    emitted = set()
    for _ in range(3):
        B = bound_index(F)
        grew = False
        for ri, (a, b, m) in enumerate(rels):
            ba, bb = B.get(a, {}), B.get(b, {})

            def add(kind, refs, c):
                nonlocal grew
                key = (ri, kind, tuple(refs))
                if key not in emitted:
                    emitted.add(key)
                    push(c, ["pf", kind, ri] + list(refs), list(refs))
                    grew = True

            if a == b:
                add("sqnn", [], _mk({m: -1}, 0))                                   # x*x >= 0
                if "lo" in ba and "hi" in ba:
                    lo, hi = ba["lo"][0], ba["hi"][0]
                    refs = [ba["lo"][1], ba["hi"][1]]
                    add("sqmax", refs, _mk({m: 1}, -max(lo * lo, hi * hi)))
                    if lo > 0 or hi < 0:
                        add("sqmin", refs, _mk({m: -1}, min(lo * lo, hi * hi)))
                continue
            if "lo" in ba and "lo" in bb and ba["lo"][0] >= 0 and bb["lo"][0] >= 0:
                add("ssnn", [ba["lo"][1], bb["lo"][1]], _mk({m: -1}, 0))
            if "hi" in ba and "hi" in bb and ba["hi"][0] <= 0 and bb["hi"][0] <= 0:
                add("ssnn", [ba["hi"][1], bb["hi"][1]], _mk({m: -1}, 0))
            if "lo" in ba and "hi" in bb and ba["lo"][0] >= 0 and bb["hi"][0] <= 0:
                add("osnp", [ba["lo"][1], bb["hi"][1]], _mk({m: 1}, 0))
            if "hi" in ba and "lo" in bb and ba["hi"][0] <= 0 and bb["lo"][0] >= 0:
                add("osnp", [ba["hi"][1], bb["lo"][1]], _mk({m: 1}, 0))
            if all(x in ba for x in ("lo", "hi")) and all(x in bb for x in ("lo", "hi")):
                la, ua, lb, ub = ba["lo"][0], ba["hi"][0], bb["lo"][0], bb["hi"][0]
                refs = [ba["lo"][1], ba["hi"][1], bb["lo"][1], bb["hi"][1]]
                corners = [la * lb, la * ub, ua * lb, ua * ub]
                add("clo", refs, _mk({m: -1}, min(corners)))
                add("chi", refs, _mk({m: 1}, -max(corners)))
                add("mc1", refs, _mk({m: -1, b: la, a: lb}, -la * lb))
                add("mc2", refs, _mk({m: -1, b: ua, a: ub}, -ua * ub))
                add("mc3", refs, _mk({m: 1, b: -ua, a: -lb}, ua * lb))
                add("mc4", refs, _mk({m: 1, b: -la, a: -ub}, la * ub))
        if not grew:
            break

    # ---- Fourier-Motzkin with integer tightening
    def consider(i, work, seen):
        t = tighten(F[i])
        if t != F[i]:
            i = push(t, ["tighten", i], [i])
        c = F[i]
        if not c[0]:
            return i if c[1] > 0 else None, None
        key = (tuple(sorted(c[0].items())), c[1])
        if key not in seen:
            seen[key] = i
            work.append(i)
        return None, None

    work, seen = [], {}
    for i in range(len(F)):
        contra, _ = consider(i, work, seen)
        if contra is not None:
            return _finish(F, steps, deps, n0, contra)
    while work:
        occ, inexact = {}, set()
        for i in work:
            for v, a in F[i][0].items():
                p, n = occ.get(v, (0, 0))
                occ[v] = (p + (a > 0), n + (a < 0))
                if abs(a) != 1:
                    inexact.add(v)
        # Prefer variables whose coefficients are all +-1: eliminating those keeps INTEGER feasibility
        # exactly, so parity-style contradictions survive.
        pool = [x for x in occ if x not in inexact] or list(occ)
        v = min(pool, key=lambda x: occ[x][0] * occ[x][1])
        pos = [i for i in work if F[i][0].get(v, 0) > 0]
        neg = [i for i in work if F[i][0].get(v, 0) < 0]
        rest = [i for i in work if v not in F[i][0]]
        new, seen2 = list(rest), {}
        for i in rest:
            c = F[i]
            seen2[(tuple(sorted(c[0].items())), c[1])] = i
        for p in pos:
            for n in neg:
                c = lin_add(lin_scale(F[p], -F[n][0][v]), lin_scale(F[n], F[p][0][v]))
                ci = push(c, ["comb", p, n, v], [p, n])
                contra, _ = consider(ci, new, seen2)
                if contra is not None:
                    return _finish(F, steps, deps, n0, contra)
        if len(new) > FM_CAP:
            return None
        work = new
    return None


def _finish(F, steps, deps, n0, contra):
    """Keep only the steps the contradiction depends on, renumbered; axioms (index < n0) keep their index."""
    needed, stack = set(), [contra]
    while stack:
        i = stack.pop()
        if i >= n0 and i not in needed:
            needed.add(i)
            stack.extend(deps[i])
    order = sorted(needed)
    newidx = {old: n0 + k for k, old in enumerate(order)}
    ref = lambda i: newidx.get(i, i)
    out = []
    for old in order:
        st = steps[old]
        if st[0] == "tighten":
            out.append(["tighten", ref(st[1])])
        elif st[0] == "comb":
            out.append(["comb", ref(st[1]), ref(st[2]), st[3]])
        else:
            out.append(st[:3] + [ref(r) for r in st[3:]])
    out.append(["contra", ref(contra)])
    return out


# ----------------------------------------------------------------------------- z3 AST -> NNF over polynomials
class _Ctx:
    def __init__(self):
        self.defs, self.divs, self.n = [], {}, 0
        self.monos = {}              # monomial variable name -> key tuple
        self.rels = []               # (a, b, m): m = a * b
        self.selects = {}            # base array key -> [(index linear form, value variable)]
        self.consts = {}             # original z3 constants: name -> sort kind ("int", "bool", "enum", "array", "uninterp")
        self.enum_domains = {}

    def fresh(self, hint):
        self.n += 1
        return f"{hint}#{self.n}"

    # ---- polynomials <-> linear forms
    def mono_var(self, key):
        name = "m:" + "*".join(key)
        if name not in self.monos:
            self.monos[name] = key
            first, rest = key[0], key[1:]
            restname = rest[0] if len(rest) == 1 else self.mono_var(rest)
            self.rels.append((first, restname, name))
            if all(key.count(v) % 2 == 0 for v in set(key)):
                self.defs.append(("lit", ({name: -1}, 0)))          # a monomial with only even exponents is >= 0
        return name

    def lin(self, poly):
        co, const = {}, 0
        for m, c in poly.items():
            if m == ():
                const += c
            elif len(m) == 1:
                co[m[0]] = co.get(m[0], 0) + c
            else:
                v = self.mono_var(m)
                co[v] = co.get(v, 0) + c
        return ({v: c for v, c in co.items() if c}, const)

    # ---- terms of integer-like sorts
    def term(self, e):
        """Return a polynomial for an Int-sorted (or uninterpreted / enum sorted) term."""
        k = e.decl().kind() if z3.is_app(e) else None
        if z3.is_int_value(e):
            return p_const(e.as_long())
        if k == z3.Z3_OP_ADD:
            r = {}
            for a in e.children():
                r = p_add(r, self.term(a))
            return r
        if k == z3.Z3_OP_SUB:
            ch = e.children()
            r = self.term(ch[0])
            for a in ch[1:]:
                r = p_add(r, self.term(a), -1)
            return r
        if k == z3.Z3_OP_UMINUS:
            return p_scale(self.term(e.arg(0)), -1)
        if k == z3.Z3_OP_MUL:
            r = p_const(1)
            for a in e.children():
                r = p_mul(r, self.term(a))
            return r
        if k in (z3.Z3_OP_IDIV, z3.Z3_OP_MOD):
            return self.divmod_term(e, k)
        if k == z3.Z3_OP_ITE and not z3.is_bool(e):
            v = p_var(self.fresh("ite"))
            vl = self.lin(v)
            c = e.arg(0)
            ta, tb = self.lin(self.term(e.arg(1))), self.lin(self.term(e.arg(2)))
            self.defs.append(("or", [self.nnf(c, False), self.eq(vl, ta, True)]))
            self.defs.append(("or", [self.nnf(c, True), self.eq(vl, tb, True)]))
            return v
        if k == z3.Z3_OP_SELECT:
            return self.select(e.arg(0), self.lin(self.term(e.arg(1))), e)
        if k == z3.Z3_OP_DT_CONSTRUCTOR and e.num_args() == 0 and isinstance(e.sort(), z3.DatatypeSortRef):
            s = e.sort()
            for i in range(s.num_constructors()):
                if s.constructor(i).name() == e.decl().name():
                    return p_const(i)
        if z3.is_const(e) and k == z3.Z3_OP_UNINTERPRETED:
            return self.atom(e)
        return p_var(f"t{e.get_id()}")

    def atom(self, e):
        name = e.decl().name()
        s = e.sort()
        if z3.is_int(e):
            self.consts[name] = "int"
        elif isinstance(s, z3.DatatypeSortRef):
            self.consts[name] = "enum"
            self.enum_domains[name] = s.num_constructors()
            self.defs.append(("and", [("lit", ({name: -1}, 0)), ("lit", ({name: 1}, -(s.num_constructors() - 1)))]))
        else:
            self.consts[name] = "uninterp"
        return p_var(name)

    def select(self, arr, idx_lin, whole):
        k = arr.decl().kind() if z3.is_app(arr) else None
        if k == z3.Z3_OP_STORE:
            a, i, v = arr.arg(0), self.lin(self.term(arr.arg(1))), self.term(arr.arg(2))
            res = p_var(self.fresh("rw"))
            rl = self.lin(res)
            rest = self.select(a, idx_lin, None)
            same = self.eq(idx_lin, i, True)
            diff = self.eq(idx_lin, i, False)
            self.defs.append(("or", [diff, self.eq(rl, self.lin(v), True)]))
            self.defs.append(("or", [same, self.eq(rl, self.lin(rest), True)]))
            return res
        if k == z3.Z3_OP_CONST_ARRAY:
            return self.term(arr.arg(0))
        if k == z3.Z3_OP_ITE:
            res = p_var(self.fresh("ra"))
            rl = self.lin(res)
            ta, tb = self.lin(self.select(arr.arg(1), idx_lin, None)), self.lin(self.select(arr.arg(2), idx_lin, None))
            self.defs.append(("or", [self.nnf(arr.arg(0), False), self.eq(rl, ta, True)]))
            self.defs.append(("or", [self.nnf(arr.arg(0), True), self.eq(rl, tb, True)]))
            return res
        base = arr.get_id()
        if z3.is_const(arr) and k == z3.Z3_OP_UNINTERPRETED:
            self.consts.setdefault(arr.decl().name(), "array")
        v = f"sel{base}[{tuple(sorted(idx_lin[0].items()))},{idx_lin[1]}]"
        lst = self.selects.setdefault(base, [])
        if not any(name == v for _, name in lst):
            lst.append((idx_lin, v))
        return p_var(v)

    def divmod_term(self, e, k):
        num, den = self.term(e.arg(0)), self.term(e.arg(1))
        key = (tuple(sorted(num.items())), tuple(sorted(den.items())))
        if key not in self.divs:
            q, r = p_var(self.fresh("q")), p_var(self.fresh("r"))
            self.divs[key] = (q, r)
            ql, rl, nl, xl = self.lin(q), self.lin(r), self.lin(den), self.lin(num)
            if p_is_const(den) and p_const_value(den) != 0:
                c = p_const_value(den)               # x = c*q + r,  0 <= r <= |c|-1  (exact)
                eq = lin_add(xl, lin_add(lin_scale(ql, c), rl), -1)
                self.defs.append(("and", [("lit", eq), ("lit", lin_scale(eq, -1)), ("lit", lin_scale(rl, -1)),
                                          ("lit", lin_add(rl, lin_const(-(abs(c) - 1))))]))
            elif not p_is_const(den):
                prod = self.lin(p_mul(den, q))       # n*q is a monomial variable (McCormick'd in each case)
                eq = lin_add(xl, lin_add(prod, rl), -1)
                pos = ("and", [self.le(lin_const(1), nl, True), ("lit", lin_scale(rl, -1)),
                               ("lit", lin_add(lin_add(rl, nl, -1), lin_const(1))),            # r <= n - 1
                               ("lit", eq), ("lit", lin_scale(eq, -1))])
                neg = ("and", [self.le(nl, lin_const(-1), True), ("lit", lin_scale(rl, -1)),
                               ("lit", lin_add(lin_add(rl, nl), lin_const(1))),                # r <= -n - 1
                               ("lit", eq), ("lit", lin_scale(eq, -1))])
                self.defs.append(("or", [pos, neg, self.eq(nl, lin_const(0), True)]))
                # |x / n| <= |x| for every n != 0 (Euclid), the fact behind "a / b cannot overflow"
                nx = lin_scale(xl, -1)
                self.defs.append(("or", [self.eq(nl, lin_const(0), True),
                                         ("and", [("or", [self.le(xl, lin_const(-1), True),
                                                          ("and", [self.le(nx, ql, True), self.le(ql, xl, True)])]),
                                                  ("or", [self.le(lin_const(0), xl, True),
                                                          ("and", [self.le(xl, ql, True), self.le(ql, nx, True)])])])]))
                # sharper facts used by the typical `i % n`, `i / n` patterns
                self.defs.append(("or", [self.le(nl, lin_const(0), True), self.le(xl, lin_const(-1), True),
                                         ("and", [self.le(lin_const(0), ql, True), self.le(ql, xl, True),
                                                  self.le(rl, xl, True)])]))
        q, r = self.divs[key]
        return q if k == z3.Z3_OP_IDIV else r

    # ---- atoms and boolean structure
    def le(self, a, b, positive=True):          # a <= b
        d = lin_add(a, b, -1)
        if positive:
            return ("lit", d)
        return ("lit", lin_add(lin_scale(d, -1), lin_const(1)))

    def eq(self, a, b, positive):
        d = lin_add(a, b, -1)
        if positive:
            return ("and", [("lit", d), ("lit", lin_scale(d, -1))])
        return ("or", [("lit", lin_add(d, lin_const(1))), ("lit", lin_add(lin_scale(d, -1), lin_const(1)))])

    def is_intlike(self, e):
        s = e.sort()
        return z3.is_int(e) or isinstance(s, z3.DatatypeSortRef) or (
            s.kind() == z3.Z3_UNINTERPRETED_SORT)

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
            if self.is_intlike(a):
                return self.eq(self.lin(self.term(a)), self.lin(self.term(b)), pos)
        if k == z3.Z3_OP_DISTINCT and self.is_intlike(ch[0]):
            terms = [self.lin(self.term(c)) for c in ch]
            pairs = [self.eq(terms[i], terms[j], False) for i in range(len(terms)) for j in range(i + 1, len(terms))]
            return ("and", pairs) if pos else ("or", [self.eq(terms[i], terms[j], True)
                                                     for i in range(len(terms)) for j in range(i + 1, len(terms))])
        if k == z3.Z3_OP_DT_IS and len(ch) == 1 and isinstance(ch[0].sort(), z3.DatatypeSortRef):
            s = ch[0].sort()                                  # `is(C, t)`  ==  t is the C-th constructor
            cname = e.decl().params()[0].name()
            for i in range(s.num_constructors()):
                if s.constructor(i).name() == cname:
                    return self.eq(self.lin(self.term(ch[0])), lin_const(i), pos)
        if k in (z3.Z3_OP_LE, z3.Z3_OP_LT, z3.Z3_OP_GE, z3.Z3_OP_GT) and z3.is_int(ch[0]):
            a, b = self.lin(self.term(ch[0])), self.lin(self.term(ch[1]))
            if k == z3.Z3_OP_LT:
                return self.le(lin_add(a, lin_const(1)), b, pos)
            if k == z3.Z3_OP_GE:
                return self.le(b, a, pos)
            if k == z3.Z3_OP_GT:
                return self.le(lin_add(b, lin_const(1)), a, pos)
            return self.le(a, b, pos)
        if z3.is_const(e) and k == z3.Z3_OP_UNINTERPRETED and z3.is_bool(e):
            self.consts[e.decl().name()] = "bool"
        if k == z3.Z3_OP_SELECT and z3.is_bool(e):
            pass
        return ("bvar", e.get_id(), pos, e.decl().name() if (z3.is_const(e) and z3.is_bool(e)) else None)

    def square_cuts(self):
        """(a - b)^2 >= 0 and (a + b)^2 >= 0 for every product a*b that occurs: a*a + b*b -+ 2*a*b >= 0."""
        for name, key in list(self.monos.items()):
            if len(key) == 2 and key[0] != key[1]:
                a, b = key
                aa, bb = self.mono_var((a, a)), self.mono_var((b, b))
                self.defs.append(("lit", ({aa: -1, bb: -1, name: 2}, 0)))
                self.defs.append(("lit", ({aa: -1, bb: -1, name: -2}, 0)))

    def ackermann(self):
        """Reads of the same array at equal indices return equal values."""
        for lst in self.selects.values():
            lst = lst[:ACKERMANN_LIMIT]
            for i in range(len(lst)):
                for j in range(i + 1, len(lst)):
                    (ia, va), (ib, vb) = lst[i], lst[j]
                    self.defs.append(("or", [self.eq(ia, ib, False),
                                             self.eq(lin_var(va), lin_var(vb), True)]))


def lin_var(v):
    return ({v: 1}, 0)


# ----------------------------------------------------------------------------- search
def _refute(cons, bools, pending, counter, rels, leaf):
    """Returns a proof tree (see lise_certcheck) or None.  Branch handling here and in lise_certcheck.walk
    is deliberately identical, so the validator can follow the proof without searching."""
    pending = list(pending)
    cons, bools = list(cons), dict(bools)
    while pending:
        f = pending.pop()
        k = f[0]
        if k == "true":
            continue
        if k == "false":
            return ["closed"]
        if k == "and":
            pending.extend(reversed(f[1]))
        elif k == "lit":
            cons.append(f[1])
        elif k == "bvar":
            if bools.get(f[1], f[2]) != f[2]:
                return ["closed"]
            bools[f[1]] = f[2]
            if f[3] is not None:
                bools[("name", f[3])] = f[2]
        else:
            counter[0] += 1
            if counter[0] > NODE_BUDGET:
                raise _Budget()
            d = derive(cons, rels)
            if d is not None:
                return ["derive", d]
            subs = []
            for alt in f[1]:
                p = _refute(cons, bools, pending + [alt], counter, rels, leaf)
                if p is None:
                    return None
                subs.append(p)
            return ["split", subs]
    d = derive(cons, rels)
    if d is not None:
        return ["derive", d]
    if leaf[0] is None:
        leaf[0] = (list(cons), dict(bools))
    return None


def serialize(f):
    k = f[0]
    if k in ("true", "false"):
        return [k]
    if k in ("and", "or"):
        return [k, [serialize(g) for g in f[1]]]
    if k == "lit":
        co, c = f[1]
        return ["lit", [sorted([v, a] for v, a in co.items()), c]]
    return ["bvar", f[1], f[2]]


# ----------------------------------------------------------------------------- evaluator + model finder
class _Arr:
    def __init__(self, default, over=None):
        self.default, self.over = default, dict(over or {})

    def get(self, i):
        return self.over.get(i, self.default)

    def put(self, i, v):
        o = dict(self.over)
        o[i] = v
        return _Arr(self.default, o)


def _ev(e, env):
    """Evaluate a z3 term/formula under `env` with Python semantics (the checker's own evaluator)."""
    if z3.is_true(e):
        return True
    if z3.is_false(e):
        return False
    if z3.is_int_value(e):
        return e.as_long()
    k = e.decl().kind()
    ch = e.children()
    if k == z3.Z3_OP_UNINTERPRETED and not ch:
        if e.decl().name() not in env:
            raise _Unsupported(e.decl().name())
        return env[e.decl().name()]
    if k == z3.Z3_OP_DT_CONSTRUCTOR and not ch:
        return ("enum", e.decl().name())
    if k == z3.Z3_OP_ADD:
        return sum(_ev(c, env) for c in ch)
    if k == z3.Z3_OP_SUB:
        r = _ev(ch[0], env)
        for c in ch[1:]:
            r -= _ev(c, env)
        return r
    if k == z3.Z3_OP_UMINUS:
        return -_ev(ch[0], env)
    if k == z3.Z3_OP_MUL:
        r = 1
        for c in ch:
            r *= _ev(c, env)
        return r
    if k in (z3.Z3_OP_IDIV, z3.Z3_OP_MOD):
        a, b = _ev(ch[0], env), _ev(ch[1], env)
        if b == 0:
            raise _Unsupported("division by zero is unconstrained in z3")
        r = a % abs(b)
        return (a - r) // b if k == z3.Z3_OP_IDIV else r
    if k == z3.Z3_OP_ITE:
        return _ev(ch[1], env) if _ev(ch[0], env) else _ev(ch[2], env)
    if k == z3.Z3_OP_DT_IS:
        return _ev(ch[0], env) == ("enum", e.decl().params()[0].name())
    if k == z3.Z3_OP_NOT:
        return not _ev(ch[0], env)
    if k == z3.Z3_OP_AND:
        return all(_ev(c, env) for c in ch)
    if k == z3.Z3_OP_OR:
        return any(_ev(c, env) for c in ch)
    if k == z3.Z3_OP_IMPLIES:
        return (not _ev(ch[0], env)) or _ev(ch[1], env)
    if k == z3.Z3_OP_XOR:
        return _ev(ch[0], env) != _ev(ch[1], env)
    if k in (z3.Z3_OP_EQ, z3.Z3_OP_DISTINCT):
        vals = [_ev(c, env) for c in ch]
        if any(isinstance(v, _Arr) for v in vals):
            raise _Unsupported("array equality")
        if k == z3.Z3_OP_EQ:
            return all(vals[0] == v for v in vals[1:])
        return len(set(vals)) == len(vals)
    if k in (z3.Z3_OP_LE, z3.Z3_OP_LT, z3.Z3_OP_GE, z3.Z3_OP_GT):
        a, b = _ev(ch[0], env), _ev(ch[1], env)
        return {z3.Z3_OP_LE: a <= b, z3.Z3_OP_LT: a < b, z3.Z3_OP_GE: a >= b, z3.Z3_OP_GT: a > b}[k]
    if k == z3.Z3_OP_SELECT:
        return _ev(ch[0], env).get(_ev(ch[1], env))
    if k == z3.Z3_OP_STORE:
        return _ev(ch[0], env).put(_ev(ch[1], env), _ev(ch[2], env))
    if k == z3.Z3_OP_CONST_ARRAY:
        return _Arr(_ev(ch[0], env))
    raise _Unsupported(str(e.decl().name()))


def _collect_consts(e, out, seen):
    if e.get_id() in seen:
        return
    seen.add(e.get_id())
    if z3.is_app(e):
        if e.decl().kind() == z3.Z3_OP_UNINTERPRETED and e.num_args() == 0:
            out[e.decl().name()] = e.sort()
        for c in e.children():
            _collect_consts(c, out, seen)


def _literals(e, out, seen):
    if e.get_id() in seen:
        return
    seen.add(e.get_id())
    if z3.is_int_value(e):
        out.add(e.as_long())
    elif z3.is_app(e):
        for c in e.children():
            _literals(c, out, seen)


def find_counterexample(assertions, leaf, ctx, tries=MODEL_TRIES, seed=7):
    """Search for an assignment satisfying ALL assertions; return (description, env) or None."""
    consts, seen = {}, set()
    for a in assertions:
        _collect_consts(a, consts, seen)
    cons, bools = leaf
    bnds = var_bounds(cons)
    rng = random.Random(seed)
    special = [0, 1, -1, 2, -2, 3, 5, 10, 100, 2 ** 31, -(2 ** 31), 2 ** 62, -(2 ** 62), 2 ** 63 - 1, -(2 ** 63)]
    lits, seen_l = set(), set()
    for a in assertions:
        _literals(a, lits, seen_l)
    lits = sorted(lits, key=abs)[:14]
    derived = set(special)
    for a in lits:
        derived.update({a, a - 1, a + 1, -a})
        for b in lits:
            derived.update({a * b, a + b, a - b, a * b + 1, a * b - 1})
    special = sorted(derived, key=abs)[:160]

    def candidates(name, sort):
        if sort.kind() == z3.Z3_BOOL_SORT:
            if ("name", name) in bools:
                return [bools[("name", name)]]
            return [False, True]
        if isinstance(sort, z3.DatatypeSortRef):
            return [("enum", sort.constructor(i).name()) for i in range(sort.num_constructors())]
        if sort.kind() == z3.Z3_ARRAY_SORT:
            return ["array"]
        lo, hi = bnds.get(name, [None, None])
        vals = set()
        for v in (lo, hi):
            if v is not None:
                vals.update({v, v - 1, v + 1})
        if lo is not None and hi is not None and hi >= lo:
            vals.update({(lo + hi) // 2, lo, hi})
            vals.update(rng.randint(lo, hi) for _ in range(6))
        else:
            vals.update(special)
        out = [v for v in vals if (lo is None or v >= lo) and (hi is None or v <= hi)]
        return out or [lo if lo is not None else hi]

    domains = {n: candidates(n, s) for n, s in consts.items()}
    names = sorted(domains)
    for _ in range(tries):
        env = {}
        for n in names:
            v = rng.choice(domains[n])
            if v == "array":
                v = _Arr(rng.choice(special), {i: rng.choice(special) for i in range(-1, 4) if rng.random() < .5})
            env[n] = v
        try:
            if all(_ev(a, env) is True for a in assertions):
                shown = {n: (v if not isinstance(v, _Arr) else f"array(default={v.default}, {v.over})")
                         for n, v in env.items()}
                return ", ".join(f"{n} = {v}" for n, v in sorted(shown.items(), key=lambda x: x[0]))[:300], env
        except _Unsupported:
            continue
        except (RecursionError, OverflowError):
            continue
    return None


def check_assertions(assertions):
    """Verdict on the conjunction of z3 `assertions`: UNSAT (re-derived), SAT (verified counterexample) or UNKNOWN."""
    st, detail, _ = check_assertions_env(assertions)
    return st, detail


last_cert = None   # the most recent validated certificate (read by the verifier for --certificates)


def check_assertions_env(assertions):
    global last_cert
    try:
        ctx = _Ctx()
        formulas = [ctx.nnf(a, True) for a in assertions]
        ctx.ackermann()
        ctx.square_cuts()
        formulas.extend(ctx.defs)
        counter, leaf = [0], [None]
        proof = _refute([], {}, list(reversed(formulas)), counter, ctx.rels, leaf)
        if proof is not None:
            cert = json.loads(json.dumps({"version": 1, "formulas": [serialize(f) for f in formulas],
                                          "rels": [list(r) for r in ctx.rels], "proof": proof}))
            ok, why = lise_certcheck.verify(cert)          # the small standalone validator decides
            if not ok:
                return INVALID, "certificate rejected by the validator: " + why, None
            last_cert = cert
            return UNSAT, "", None
        if leaf[0] is not None:
            found = find_counterexample(assertions, leaf[0], ctx)
            if found is not None:
                return SAT, found[0], found[1]
        return UNKNOWN, "not refuted by the independent checker", None
    except _Budget:
        return UNKNOWN, "case-split budget exceeded", None
    except RecursionError:
        return UNKNOWN, "formula too deep", None


def check(z3_solver):
    return check_assertions(list(z3_solver.assertions()))
