#!/usr/bin/env python3
"""Differential soundness fuzzer for Lise.

Generates random integer/array programs, runs the verifier, and for every program
the verifier ACCEPTS it checks, on many inputs:
  0. (contracts) random `assert`, `requires`, `ensures` and loop `invariant` clauses are
     evaluated by the reference: a verified program whose assert/ensures/invariant is
     FALSE on some input is a BUG (the verifier proved something false)
  1. a Python reference interpreter (unbounded ints, Euclidean / and %) never hits
     overflow, division by zero, MIN/-1 or an out-of-bounds index   (verifier soundness)
  2. the compiled code returns the reference result and never traps  (backend correctness)
Any failure is a BUG: it means a proof was wrong or the backend disagrees with the spec.

  4. (calls) programs with a record, helper functions taking it `mutable`, their own
     requires/ensures, and call sites: frame/havoc handling, precondition checks at
     calls and use of callee postconditions are all checked against the reference

  5. (output) random print_int statements: the text the compiled code writes to stdout must
     equal what the reference interpreter prints

  6. (recursion) random recursive functions with `decreases ... max` and postconditions; a
     verified program that recurses without end (reference depth limit), exceeds its declared
     bound, or whose postcondition is false is a BUG

  7. (semantics) every accepted program is ALSO run by the executable reference semantics
     (lise_semantics.py) on the real AST: it must never get STUCK, and its result and output must
     equal both the fuzzer's own reference and the compiled code (three independent evaluators)

usage: python fuzz_lise.py [COUNT=200] [START_SEED=0]
Each chunk runs in a child process so a trap in "proven" code is caught and reported.
Uses llvmlite's JIT as a test-only executor (the product build is AOT).
"""
import ctypes
import random
import subprocess
import sys

I64_MIN, I64_MAX = -(2 ** 63), 2 ** 63 - 1


class Violation(Exception):
    pass


# ------------------------------------------------------------------ generator
DIV_OK = True   # calls-mode programs avoid division so that more of them verify
LITS = [0, 1, 2, 3, 7, 10, -1, -2, -5, 100, 1000, 2 ** 31, 2 ** 40, 2 ** 62, I64_MAX]


def lit(rng):
    v = rng.choice(LITS)
    return v if v == I64_MAX or rng.random() < .5 else rng.choice([v, -v]) if abs(v) < I64_MAX else v


def gidx(rng, vars_, arr, d):
    """Index expression: often a small raw offset of a variable, to probe -1 / length / length+1."""
    if vars_ and rng.random() < .5:
        v = ("var", rng.choice(vars_))
        k = rng.choice([-1, 0, 1, 2, 3, 4, -2])
        return v if k == 0 else ("bin", "+", v, ("num", k))
    return gexpr(rng, vars_, arr, d)


def gexpr(rng, vars_, arr, d):
    r = rng.random()
    if d == 0 or r < .25:
        if vars_ and rng.random() < .65:
            return ("var", rng.choice(vars_))
        return ("num", lit(rng))
    if r < .33:
        return ("neg", gexpr(rng, vars_, arr, d - 1))
    if r < .43 and arr:
        m = rng.choice([4, 4, 5, 3, None, None])
        return ("idx", gidx(rng, vars_, arr, d - 1) if m is None else gexpr(rng, vars_, arr, d - 1), m)
    op = rng.choice(["+", "+", "-", "-", "*", "/", "%"] if DIV_OK else ["+", "+", "-", "-", "*"])
    l = gexpr(rng, vars_, arr, d - 1)
    if op in "/%":
        q = rng.random()
        if q < .3:
            rr = ("num", rng.choice([2, 3, 7, -3, -1, 10]))
        elif q < .65 and vars_:
            rr = ("var", rng.choice(vars_))      # raw variable divisor: usually unprovable, sometimes guarded
        else:
            rr = gexpr(rng, vars_, arr, d - 1)
    else:
        rr = gexpr(rng, vars_, arr, d - 1)
    return ("bin", op, l, rr)


RANGES = {}   # parameter name -> (lo, hi) of the program being generated


def gcond(rng, vars_, arr, d):
    r = rng.random()
    if RANGES and rng.random() < .35:      # boundary-probing comparison: true / just-false at the ends
        v = rng.choice([x for x in vars_ if x in RANGES] or list(RANGES))
        lo, hi = RANGES[v]
        return ("cmp", rng.choice(["<", "<=", ">", ">="]), ("var", v),
                ("num", max(I64_MIN + 1, min(I64_MAX, rng.choice([lo, hi]) + rng.choice([-1, 0, 1])))))
    if d == 0 or r < .6:
        return ("cmp", rng.choice(["<", "<=", ">", ">=", "==", "!="]), gexpr(rng, vars_, arr, 1), gexpr(rng, vars_, arr, 1))
    if r < .75:
        return ("not", gcond(rng, vars_, arr, d - 1))
    return (rng.choice(["and", "or"]), gcond(rng, vars_, arr, d - 1), gcond(rng, vars_, arr, d - 1))


FIELDS = ["a", "b", "c"]
DELEMS = [f"rec.d[{i}]" for i in range(3)]   # elements of the array field `d` (fill(dfill) initially)


class Gen:
    def __init__(self, rng, calls=None):
        self.rng, self.n, self.calls = rng, 0, calls

    def block(self, vars_, arr, depth, count):
        rng, out, vars_ = self.rng, [], list(vars_)
        for _ in range(count):
            if rng.random() < .08:
                out.append(("print", gexpr(rng, vars_, arr, 1)))
            r = rng.random()
            if self.calls and r < .42:
                c = self.calls
                q = rng.random()
                if q < .45:            # call a helper that takes `rec` mutably
                    h = rng.choice(c["names"])
                    klo, khi = c["krange"][h]
                    z = rng.random()
                    arg = (("num", rng.randint(klo, khi)) if z < .5 else
                           ("var", rng.choice([v for v in vars_ if v.startswith("p")] or ["p0"])) if z < .75 else
                           gexpr(rng, vars_, False, 1))
                    self.n += 1
                    name = f"t{self.n}"
                    out.append(("call", h, arg, name))
                    vars_.append(name)
                elif q < .7:           # assertion about a record field (frame-rule probe)
                    f = rng.choice(FIELDS)
                    lo, hi = c["franges"][f]
                    lit = rng.choice([c["inits"][f], c["inits"][f], lo, hi, c["inits"][f] + 1, c["inits"][f] - 1])
                    out.append(("assert", ("cmp", rng.choice(["==", "==", "<=", ">=", "!=", "<", ">"]),
                                           ("var", f"rec.{f}"), ("num", lit))))
                elif q < .82:          # array-element write / assert (whole-array frame)
                    el = rng.choice(DELEMS)
                    if rng.random() < .5:
                        out.append(("assign", el, gexpr(rng, vars_, False, 1)))
                    else:
                        out.append(("assert", ("cmp", rng.choice(["==", "==", "!=", "<=", ">="]), ("var", el),
                                               ("num", rng.choice([c["dfill"], c["dfill"], c["dfill"] + 1, 0])))))
                else:                  # guarded field assignment
                    f = rng.choice(FIELDS)
                    lo, hi = c["franges"][f]
                    e = gexpr(rng, vars_, False, 1)
                    out.append(("if", ("and", ("cmp", ">=", e, ("num", lo)), ("cmp", "<=", e, ("num", hi))),
                                [("assign", f"rec.{f}", e)], []))
            elif r < .30:
                out.append(("assign", "r", gexpr(rng, vars_, arr, 2)))
            elif r < .50:
                self.n += 1
                name = f"t{self.n}"
                out.append(("let", name, gexpr(rng, vars_, arr, 2)))
                vars_.append(name)
            elif r < .65 and arr:
                m = rng.choice([4, 4, 5, 3, None, None])
                out.append(("aset", gidx(rng, vars_, arr, 1) if m is None else gexpr(rng, vars_, arr, 1), m,
                            gexpr(rng, vars_, arr, 2)))
            elif r < .60 and vars_:
                v = rng.choice(vars_)
                out.append(("if", ("cmp", "!=", ("var", v), ("num", 0)),
                            [("assign", "r", ("bin", rng.choice(["/", "%"]), gexpr(rng, vars_, arr, 1), ("var", v)))],
                            [("assign", "r", ("num", 0))]))
            elif r < .72:
                out.append(("assert", gcond(rng, vars_, arr, 1)))
            elif r < .85 and depth > 0:
                out.append(("if", gcond(rng, vars_, arr, 1), self.block(vars_, arr, depth - 1, rng.randint(1, 2)),
                            self.block(vars_, arr, depth - 1, rng.randint(0, 2))))
            elif depth > 0:
                self.n += 1
                k = rng.randint(0, 4)
                body_vars = [v for v in vars_ if v != "r"]
                q = rng.random()
                if q < .35:
                    inv = gcond(rng, vars_, arr, 1)
                elif q < .8:   # invariant about r that the body may or may not preserve
                    inv = ("cmp", rng.choice(["<=", ">=", "<", ">", "=="]), ("var", "r"),
                           ("num", rng.choice([0, 1, 5, 10, 100, -1])))
                else:
                    inv = None
                out.append(("while", f"i{self.n}", k, gexpr(rng, body_vars, arr, 1), inv))
            else:
                out.append(("assign", "r", gexpr(rng, vars_, arr, 1)))
        return out


def gen_small(rng):
    """Tiny template programs with exactly one risky construct and everything else provable,
    so a weakened proof rule is much more likely to produce an accepted-but-wrong program."""
    lo, hi = rng.randint(-3, 0), rng.randint(1, 6)
    params = [("p0", lo, hi)]
    RANGES.clear()
    RANGES["p0"] = (lo, hi)
    p0, k = ("var", "p0"), rng.choice([-2, -1, 0, 1, 2, 3, 4])
    t = rng.choice(["aset", "aset", "aget", "aget", "loop_preserve", "loop_entry", "div", "fill_read"])
    prog = dict(params=params, arr=False, arrfill=0, init=("num", 0), body=[], req=None, ens=[])
    if t in ("aset", "aget"):
        prog["arr"] = True
        edge = rng.choice(["upper_ok", "upper_bad", "lower_ok", "lower_bad", "random"])
        k = {"upper_ok": 3 - hi, "upper_bad": 4 - hi, "lower_ok": -lo, "lower_bad": -1 - lo}.get(edge, k)
        idx = p0 if k == 0 else ("bin", "+", p0, ("num", k))
        prog["body"] = ([("aset", idx, None, ("num", 5))] if t == "aset"
                        else [("assign", "r", ("idx", idx, None))])
    elif t == "fill_read":          # every element of a non-zero fill must really be initialised
        prog["params"] = [("p0", 0, 3)]
        RANGES["p0"] = (0, 3)
        prog["arr"], prog["arrfill"] = True, rng.choice([1, 9])
        prog["body"] = [("assign", "r", ("idx", p0, None))]
    elif t == "loop_preserve":
        c = rng.choice([-1, 0, 1, 5])
        e = ("bin", "+", p0, ("num", c))
        inv = ("cmp", rng.choice(["<=", ">=", "<", ">", "=="]), ("var", "r"), ("num", rng.choice([0, 1, 5, 6])))
        prog["body"] = [("while", "i1", rng.randint(1, 3), e, inv)]
    elif t == "loop_entry":
        prog["init"] = ("num", rng.choice([0, 1, 5]))
        inv = ("cmp", rng.choice(["<=", ">=", "<", ">", "=="]), ("var", "r"), ("num", rng.choice([0, 1, 5])))
        prog["body"] = [("while", "i1", rng.randint(0, 3), ("num", rng.choice([0, 1, 5])), inv)]
    else:
        den = p0 if k == 0 else ("bin", "+", p0, ("num", k))
        prog["body"] = [("assign", "r", ("bin", rng.choice(["/", "%"]), ("num", 100), den))]
    return prog


HELPERS_SO_FAR = {}


def gen_helper(rng, name, franges, krange, earlier=()):
    """fn name(rec: mutable R, k: Integer in krange) -> Integer, with random contracts."""
    kv = ["k"] + [f"rec.{f}" for f in FIELDS]
    RANGES.clear()
    RANGES.update({f"rec.{f}": franges[f] for f in FIELDS})
    RANGES["k"] = krange
    body, temps = [], []
    for i in range(rng.randint(1, 3)):
        q = rng.random()
        if q < .15:                                   # write one element of the array field
            body.append(("assign", rng.choice(DELEMS), gexpr(rng, kv + temps, False, 1)))
        elif q < .3 and earlier:                      # transitive modification through another helper
            h0, hk = rng.choice(earlier)
            t = f"u{i}"
            body.append(("call", h0, ("num", rng.randint(*hk)), t))
            temps.append(t)
        elif q < .6:
            f = rng.choice(["a", "b", "c"] if rng.random() < .2 else ["a", "b"])
            lo, hi = franges[f]
            e = gexpr(rng, kv + temps, False, 1)
            body.append(("if", ("and", ("cmp", ">=", e, ("num", lo)), ("cmp", "<=", e, ("num", hi))),
                         [("assign", f"rec.{f}", e)], []))
        else:
            t = f"u{i}"
            body.append(("let", t, gexpr(rng, kv + temps, False, 1)))
            temps.append(t)
    olds = [f"old(rec.{f})" for f in FIELDS]
    RANGES.update({o: franges[f] for o, f in zip(olds, FIELDS)})
    h = dict(name=name, krange=krange, body=body, ret=gexpr(rng, kv + temps, False, 1),
             req=gcond(rng, kv, False, 1) if rng.random() < .25 else None, ens=[])
    # candidate postconditions: frame facts + random ones; keep those true on every sampled run
    cands = [("cmp", "==", ("var", f"rec.{f}"), ("var", f"old(rec.{f})")) for f in FIELDS]
    cands += [("cmp", rng.choice([">=", "<="]), ("var", f"rec.{f}"), ("var", f"old(rec.{f})")) for f in FIELDS]
    dold = [e.replace("rec.", "old(rec.") + ")" for e in DELEMS]
    cands += [("cmp", "==", ("var", e), ("var", o)) for e, o in zip(DELEMS, dold)]   # d frame facts
    cands += [gcond(rng, kv + ["result"] + olds, False, 1) for _ in range(8)]
    samples = []
    for k in range(krange[0], krange[1] + 1):
        for combo in range(8):
            samples.append((k, {f: franges[f][(combo >> i) & 1] for i, f in enumerate(FIELDS)}))
    dsample = [0, 7, 7]
    good = list(cands)
    for k, fv in samples:
        env = {f"rec.{f}": v for f, v in fv.items()}
        try:
            local = {"k": k}
            for f in FIELDS:
                local[f"rec.{f}"] = fv[f]
                local[f"old(rec.{f})"] = fv[f]
            for e, o, v in zip(DELEMS, dold, dsample):
                local[e], local[o] = v, v
            if h["req"] is not None and not spec_cond(h["req"], local, []):
                continue
            global CALLS
            CALLS = {"helpers": HELPERS_SO_FAR, "franges": franges, "inits": {}}
            rexec(h["body"], local, [])
            local["result"] = rev(h["ret"], local, [])
            good = [c for c in good if spec_cond(c, local, [])]
        except Violation:
            continue
    rng.shuffle(good)
    h["ens"] = good[:rng.choice([1, 2, 2, 3])] if good else []
    return h


def mk_values(mk, k):
    a = mk["y"] if mk["y"] is not None and k >= mk["t"] else mk["base"]["a"]
    return {"a": a, "b": mk["base"]["b"], "c": mk["base"]["c"], "d": mk["dfill"]}


def mk_env(mk, k):
    v = mk_values(mk, k)
    env = {"k": k, "result.a": v["a"], "result.b": v["b"], "result.c": v["c"]}
    env.update({f"result.d[{i}]": v["d"] for i in range(3)})
    return env


def gen_mk(rng, franges):
    """fn mk(k) -> R : builds a record and returns it; random true-on-samples postconditions
    plus (sometimes) an unfiltered one that may be false and must then be rejected."""
    klo = rng.randint(-3, 0)
    mk = dict(krange=(klo, klo + rng.randint(1, 5)), base={f: rng.randint(*franges[f]) for f in FIELDS},
              dfill=rng.choice([0, 1, 5]), t=None, y=None, ens=[])
    if rng.random() < .5:
        mk["t"] = rng.randint(*mk["krange"])
        mk["y"] = rng.randint(*franges["a"])
    saved = dict(RANGES)
    RANGES.clear()
    RANGES.update({f"result.{f}": franges[f] for f in FIELDS})
    RANGES["k"] = mk["krange"]
    vars_ = ["k"] + [f"result.{f}" for f in FIELDS] + [f"result.d[{i}]" for i in range(3)]
    cands = [("cmp", "==", ("var", f"result.{f}"), ("num", mk["base"][f])) for f in FIELDS]
    cands += [("cmp", "==", ("var", f"result.d[{i}]"), ("num", mk["dfill"])) for i in range(3)]
    cands += [gcond(rng, vars_, False, 1) for _ in range(8)]
    def holds(c):
        try:
            return all(spec_cond(c, mk_env(mk, k), []) for k in range(mk["krange"][0], mk["krange"][1] + 1))
        except Violation:
            return False
    good = [c for c in cands if holds(c)]
    rng.shuffle(good)
    mk["ens"] = good[:rng.choice([1, 2, 3])]
    if rng.random() < .3:
        mk["ens"].append(rng.choice(cands))          # negative control: may well be false
    RANGES.clear()
    RANGES.update(saved)
    return mk


def gen_calls_program(rng):
    global DIV_OK
    DIV_OK = False
    try:
        return _gen_calls_program(rng)
    finally:
        DIV_OK = True


def _gen_calls_program(rng):
    franges = {}
    for f in FIELDS:
        lo = rng.randint(-5, 0)
        franges[f] = (lo, lo + rng.randint(1, 10))
    inits = {f: rng.randint(*franges[f]) for f in FIELDS}
    dfill = rng.choice([0, 1, 5])
    mk, mkarg = None, None
    if rng.random() < .5:                      # the initial record comes from a function returning R
        mk = gen_mk(rng, franges)
        mkarg = rng.randint(*mk["krange"])
        vals = mk_values(mk, mkarg)
        inits, dfill = {f: vals[f] for f in FIELDS}, vals["d"]
    helpers = {}
    global HELPERS_SO_FAR
    HELPERS_SO_FAR = helpers
    for i in range(rng.randint(1, 3)):
        n = f"h{i}"
        klo = rng.randint(-5, 0)
        helpers[n] = gen_helper(rng, n, franges, (klo, klo + rng.randint(1, 8)),
                                [(m, helpers[m]["krange"]) for m in helpers])
    wide = rng.random() < .3
    params = [(f"p{i}", -(2 ** 20) if wide else -5, 2 ** 20 if wide else 8) for i in range(rng.randint(1, 2))]
    pv = [p[0] for p in params]
    RANGES.clear()
    RANGES.update({n: (lo, hi) for n, lo, hi in params})
    RANGES.update({f"rec.{f}": franges[f] for f in FIELDS})
    calls = dict(names=list(helpers), krange={n: h["krange"] for n, h in helpers.items()},
                 franges=franges, inits=inits, helpers=helpers, dfill=dfill, mk=mk, mkarg=mkarg)
    g = Gen(rng, calls)
    vars_ = pv + ["r"] + [f"rec.{f}" for f in FIELDS]
    body = g.block(vars_, False, 1, rng.randint(3, 6))
    prog = dict(params=params, arr=False, arrfill=0, init=("num", 0), body=body, req=None, ens=[], calls=calls)
    # bias towards provable programs: drop asserts that are false on sampled inputs (keep 20% as controls)
    global SOFT
    SOFT = set()
    try:
        for args in inputs(random.Random(rng.random()), prog)[:12]:
            try:
                reference(prog, args)
            except Violation:
                pass
        bad = SOFT
    finally:
        SOFT = None
    keep_bad = rng.random() < .2
    if bad and not keep_bad:
        prog["body"] = drop_asserts(prog["body"], bad)
    return prog


def drop_asserts(stmts, ids):
    out = []
    for s in stmts:
        if s[0] == "assert" and id(s) in ids:
            continue
        if s[0] == "if":
            s = ("if", s[1], drop_asserts(s[2], ids), drop_asserts(s[3], ids))
        out.append(s)
    return out


def gen_frame_template(rng):
    """Frame-rule probe: h0 really modifies rec.a and rec.d[1]; h1 modifies them only by calling h0.
    The caller then asserts facts about untouched (true) and modified (false) locations."""
    franges = {f: (0, 10) for f in FIELDS}
    inits = {"a": rng.randint(0, 5), "b": rng.randint(0, 10), "c": rng.randint(0, 10)}
    new_a = inits["a"] + rng.randint(1, 4)
    dfill = rng.choice([0, 1, 5])
    kv = ("var", "k")
    h0 = dict(name="h0", krange=(0, 3), req=None, ens=[("cmp", "==", ("var", "rec.b"), ("var", "old(rec.b)"))],
              body=[("assign", "rec.a", ("num", new_a)), ("assign", "rec.d[1]", ("num", dfill + 4))], ret=kv)
    h1 = dict(name="h1", krange=(0, 3), req=None, ens=[], body=[("call", "h0", ("num", 0), "u0")], ret=kv)
    calls = dict(names=["h0", "h1"], krange={"h0": (0, 3), "h1": (0, 3)}, franges=franges, inits=inits,
                 helpers={"h0": h0, "h1": h1}, dfill=dfill)
    body = [("call", rng.choice(["h0", "h1"]), ("num", 0), "t1")]
    true_facts = [("rec.b", inits["b"]), ("rec.c", inits["c"])]          # provable only with the frame rule
    risky = [("rec.a", inits["a"]), ("rec.d[1]", dfill)]                 # FALSE: the callee changed them
    picks = rng.sample(true_facts, rng.randint(0, 2))
    if rng.random() < .85:
        picks.append(rng.choice(risky))
    for name, val in picks:
        body.append(("assert", ("cmp", "==", ("var", name), ("num", val))))
    body.append(("assign", "r", ("var", "rec.a")))
    return dict(params=[("p0", 0, 1)], arr=False, arrfill=0, init=("num", 0), body=body, req=None, ens=[],
                calls=calls)


def gen_mk_template(rng):
    global DIV_OK
    DIV_OK = False
    try:
        return _gen_mk_template(rng)
    finally:
        DIV_OK = True


def _gen_mk_template(rng):
    """A function returning a record: the caller asserts true-and-pinned, true-but-unpinned and
    false facts about the result.  Only facts entailed by mk's postconditions may be accepted."""
    franges = {f: (rng.randint(-5, 0), 0) for f in FIELDS}
    franges = {f: (lo, lo + rng.randint(1, 10)) for f, (lo, _) in franges.items()}
    mk = gen_mk(rng, franges)
    arg = rng.randint(*mk["krange"])
    vals = mk_values(mk, arg)
    inits = {f: vals[f] for f in FIELDS}
    calls = dict(names=[], krange={}, franges=franges, inits=inits, helpers={}, dfill=vals["d"], mk=mk, mkarg=arg)
    places = [(f"rec.{f}", vals[f], franges[f]) for f in FIELDS] + [(f"rec.d[{i}]", vals["d"], None) for i in range(3)]
    body = []
    for name, v, rg in rng.sample(places, rng.randint(1, 4)):
        kind = rng.choice(["eq", "eq", "ne_wrong", "ge", "le", "off"])
        if kind == "eq":
            c = ("cmp", "==", ("var", name), ("num", v))
        elif kind == "off":
            c = ("cmp", "==", ("var", name), ("num", v + 1))          # false
        elif kind == "ne_wrong":
            c = ("cmp", "!=", ("var", name), ("num", v))              # false
        elif kind == "ge":
            c = ("cmp", ">=", ("var", name), ("num", rg[0] if rg else v))   # true (needs the field range)
        else:
            c = ("cmp", "<=", ("var", name), ("num", rg[1] if rg else v))
        body.append(("assert", c))
    body.append(("assign", "r", ("var", "rec.a")))
    return dict(params=[("p0", 0, 1)], arr=False, arrfill=0, init=("num", 0), body=body, req=None, ens=[],
                calls=calls)


def rrec(R, n, depth=0):
    """Reference semantics of the generated recursive function g."""
    if depth > 120:
        raise Violation("recursion does not terminate")
    if not 0 <= n <= R["K"]:
        raise Violation("argument violates parameter type of g")
    env = {"n": n}
    if rcond(R["base"], env, []):
        res = rev(R["base_expr"], env, [])
    else:
        env["t"] = rrec(R, rev(R["step"], env, []), depth + 1)
        res = rev(R["comb"], env, [])
    if R.get("check", True):
        env["result"] = res
        for c in R["ens"]:
            if not spec_cond(c, env, []):
                raise Violation("recursive postcondition false")
    return res


def gen_rec_template(rng):
    """g(n) with a base case, a recursive step and a combination; random provable-or-not contracts."""
    K = rng.choice([3, 6, 12, 20])
    nv, tv = ("var", "n"), ("var", "t")
    kind = rng.choice(["dec1", "dec1", "dec2", "half", "bad0", "bad_up", "bad_big"])
    step = {"dec1": ("bin", "-", nv, ("num", 1)), "dec2": ("bin", "-", nv, ("num", 2)),
            "half": ("bin", "/", nv, ("num", 2)), "bad0": nv, "bad_up": ("bin", "+", nv, ("num", 1)),
            "bad_big": ("num", K)}[kind]
    base = {"dec1": ("cmp", "==", nv, ("num", 0)), "dec2": ("cmp", "<=", nv, ("num", 1)),
            "half": ("cmp", "==", nv, ("num", 0))}.get(kind, ("cmp", "==", nv, ("num", 0)))
    comb = ("bin", rng.choice(["+", "+", "-"]), tv, rng.choice([nv, ("num", rng.randint(0, 5)),
                                                                 ("bin", "*", nv, ("num", 2))]))
    R = dict(K=K, step=step, base=base, base_expr=("num", rng.randint(0, 5)), comb=comb, ens=[], check=False,
             kind=kind)
    vals = None
    try:
        vals = [rrec(R, n) for n in range(K + 1)]
    except Violation:
        pass
    cands = []
    if vals is not None:
        for A in (0, 1, 10, 100):
            B = max(v - A * n for n, v in enumerate(vals))
            cands.append(("cmp", "<=", ("var", "result"), ("bin", "+", ("bin", "*", ("num", A), nv),
                                                            ("num", B + rng.randint(0, 120)))))
        lo = min(vals)
        cands.append(("cmp", ">=", ("var", "result"), ("num", lo - rng.randint(0, 150))))
        cands.append(("cmp", "<=", ("var", "result"), ("num", max(vals))))        # tight: rarely inductive
        cands.append(("cmp", ">=", ("var", "result"), ("num", lo)))
    cands.append(("cmp", ">=", ("var", "result"), ("num", rng.randint(-3, 6))))   # may be false
    robust = []
    if vals is not None:      # generous, usually inductive bounds, so that more programs get verified
        B = max(v - 1000 * n for n, v in enumerate(vals))
        robust = [("cmp", "<=", ("var", "result"), ("bin", "+", ("bin", "*", ("num", 1000), nv), ("num", B + 1000))),
                  ("cmp", ">=", ("var", "result"), ("num", min(vals) - 1000))]
    rng.shuffle(cands)
    R["ens"] = (robust + cands[:rng.choice([0, 0, 1])]) if (robust and rng.random() < .65) else cands[:rng.choice([1, 2, 2])]
    if kind.startswith("bad") and rng.random() < .7:
        # "provable if one ignores termination": result >= 0 follows from itself by induction, so only the
        # termination check stands between this program and acceptance
        R["comb"] = ("bin", rng.choice(["+", "-"]), tv, ("num", 0))      # no overflow possible
        R["base_expr"] = ("num", rng.randint(0, 5))
        R["ens"] = [("cmp", ">=", ("var", "result"), ("num", 0))]
    R["check"] = True
    arg = rng.randint(0, K)
    return dict(params=[("p0", 0, K)], arr=False, arrfill=0, init=("num", 0), req=None, ens=[], rec=R,
                body=[("gcall", ("var", "p0") if rng.random() < .5 else ("num", arg), "t1"),
                      ("assign", "r", ("var", "t1"))])


def gen_program(seed):
    rng = random.Random(seed)
    q = rng.random()
    if q < .1:
        return gen_mk_template(rng)
    if rng.random() < .14:
        return gen_rec_template(rng)
    if q < .22:
        return gen_frame_template(rng)
    if rng.random() < .3:
        return gen_calls_program(rng)
    if rng.random() < .4:
        return gen_small(rng)
    wide = rng.random() < .35
    params = []
    for i in range(rng.randint(1, 3)):
        if wide:
            lo, hi = rng.choice([(-(2 ** 62), 2 ** 62), (-(I64_MAX), I64_MAX), (-(2 ** 31), 2 ** 31), (0, I64_MAX)])
        else:
            lo = -rng.choice([0, 5, 100, 1000])
            hi = rng.choice([1, 5, 100, 1000])
        params.append((f"p{i}", lo, hi))
    RANGES.clear()
    RANGES.update({n: (lo, hi) for n, lo, hi in params})
    arr = rng.random() < .5
    g = Gen(rng)
    body = g.block([p[0] for p in params] + ["r"], arr, 2, rng.randint(2, 5))
    init = gexpr(rng, [p[0] for p in params], arr, 1) if False else ("num", rng.choice([0, 1, 5]))
    pv = [p[0] for p in params]
    req = gcond(rng, pv, False, 1) if rng.random() < .35 else None
    ens = [gcond(rng, pv + ["result"], False, 1) for _ in range(rng.choice([0, 0, 1, 2]))]
    return dict(params=params, arr=arr, arrfill=rng.choice([0, 1, 9]), init=init, body=body, req=req, ens=ens)


# ------------------------------------------------------------------ printer
def pidx(e, m):
    return f"({pe(e)}) % {m}" if m else pe(e)


def pe(e):
    k = e[0]
    if k == "num":
        return str(e[1]) if e[1] >= 0 else f"(-{-e[1]})"
    if k == "var":
        return e[1]
    if k == "neg":
        return f"(-{pe(e[1])})"
    if k == "idx":
        return f"arr[{pidx(e[1], e[2])}]"
    return f"({pe(e[2])} {e[1]} {pe(e[3])})"


def pc(c):
    k = c[0]
    if k == "cmp":
        return f"({pe(c[2])} {c[1]} {pe(c[3])})"
    if k == "not":
        return f"(not {pc(c[1])})"
    return f"({pc(c[1])} {k} {pc(c[2])})"


def pb(stmts, ind):
    sp, out = "    " * ind, []
    for s in stmts:
        k = s[0]
        if k == "assign":
            out.append(f"{sp}{s[1]} := {pe(s[2])}")
        elif k == "let":
            out.append(f"{sp}let {s[1]} = {pe(s[2])}")
        elif k == "aset":
            out.append(f"{sp}arr[{pidx(s[1], s[2])}] := {pe(s[3])}")
        elif k == "print":
            out += [f"{sp}print_int({pe(s[1])})", f'{sp}print("\\n")']
        elif k == "gcall":
            out.append(f"{sp}let {s[2]} = g({pe(s[1])})")
        elif k == "call":
            out.append(f"{sp}let {s[3]} = {s[1]}(rec, {pe(s[2])})")
        elif k == "assert":
            out.append(f"{sp}assert {pc(s[1])}")
        elif k == "if":
            out.append(f"{sp}if {pc(s[1])} then")
            out.extend(pb(s[2], ind + 1))
            if s[3]:
                out.append(f"{sp}else")
                out.extend(pb(s[3], ind + 1))
            out.append(f"{sp}end")
        else:
            _, i, kk, e, inv = s
            out += [f"{sp}var {i}: Integer := 0", f"{sp}while {i} < {kk}",
                    f"{sp}invariant 0 <= {i} and {i} <= {kk}"]
            if inv is not None:
                out.append(f"{sp}invariant {pc(inv)}")
            out += [f"{sp}decreases {kk} - {i}", f"{sp}do",
                    f"{sp}    r := {pe(e)}", f"{sp}    {i} := {i} + 1", f"{sp}end"]
    return out


def render(p):
    ps = ", ".join(f"{n}: Integer where value >= {'(-%d)' % -lo if lo < 0 else lo} and value <= {hi}"
                   for n, lo, hi in p["params"])
    lines = []
    c = p.get("calls")
    if c:
        lines.append("record R")
        for f in FIELDS:
            lo, hi = c["franges"][f]
            lines.append(f"    {f}: Integer where value >= {'(-%d)' % -lo if lo < 0 else lo} and value <= {hi}")
        lines += ["    d: Array[Integer, 3]", "end", ""]
        mk = c.get("mk")
        if mk:
            n = lambda x: str(x) if x >= 0 else f"(-{-x})"
            klo, khi = mk["krange"]
            lines.append(f"fn mk(k: Integer where value >= {n(klo)} and value <= {khi}) -> R")
            lines += [f"ensures {pc(e)}" for e in mk["ens"]]
            lines += ["is", "    var out: R := R(" + ", ".join(n(mk["base"][f]) for f in FIELDS)
                      + f", fill({mk['dfill']}))"]
            if mk["y"] is not None:
                lines += [f"    if k >= {n(mk['t'])} then", f"        out.a := {n(mk['y'])}", "    end"]
            lines += ["    return out", "end", ""]
        for h in c["helpers"].values():
            klo, khi = h["krange"]
            lines.append(f"fn {h['name']}(rec: mutable R, k: Integer where value >= "
                         f"{'(-%d)' % -klo if klo < 0 else klo} and value <= {khi}) -> Integer")
            if h["req"] is not None:
                lines.append(f"requires {pc(h['req'])}")
            lines += [f"ensures {pc(e)}" for e in h["ens"]]
            lines.append("is")
            lines += pb(h["body"], 1)
            lines += [f"    return {pe(h['ret'])}", "end", ""]
    R = p.get("rec")
    if R:
        lines += [f"fn g(n: Integer where value >= 0 and value <= {R['K']}) -> Integer", f"decreases n max {R['K']}"]
        lines += [f"ensures {pc(e)}" for e in R["ens"]]
        lines += ["is", f"    if {pc(R['base'])} then", f"        return {pe(R['base_expr'])}", "    end",
                  f"    let t = g({pe(R['step'])})", f"    return {pe(R['comb'])}", "end", ""]
    lines.append(f"fn f({ps}) -> Integer")
    if p["req"] is not None:
        lines.append(f"requires {pc(p['req'])}")
    lines += [f"ensures {pc(c)}" for c in p["ens"]]
    lines += ["is", f"    var r: Integer := {pe(p['init'])}"]
    if c and c.get("mk"):
        lines.append(f"    var rec: R := mk({c['mkarg'] if c['mkarg'] >= 0 else '(-%d)' % -c['mkarg']})")
    elif c:
        lines.append("    var rec: R := R(" + ", ".join(str(c["inits"][f]) if c["inits"][f] >= 0 else f"(-{-c['inits'][f]})"
                                                     for f in FIELDS) + f", fill({c['dfill']}))")
    if p["arr"]:
        lines.append(f"    var arr: Array[Integer, 4] := fill({p['arrfill']})")
    lines += pb(p["body"], 1)
    lines += ["    return r", "end", ""]
    return "\n".join(lines)


# ------------------------------------------------------------------ reference interpreter
SPEC = False   # inside assert / requires / ensures / invariant: mathematical (unbounded) integers


def chk(v):
    if not SPEC and not (I64_MIN <= v <= I64_MAX):
        raise Violation(f"overflow {v}")
    return v


def ridx(e, m, env, arr):
    i = rev(e, env, arr)
    if m:
        i = i % m
    if not 0 <= i < 4:
        raise Violation(f"index {i} out of bounds")
    return i


def rev(e, env, arr):
    k = e[0]
    if k == "num":
        return e[1]
    if k == "var":
        return env[e[1]]
    if k == "neg":
        return chk(-rev(e[1], env, arr))
    if k == "idx":
        return arr[ridx(e[1], e[2], env, arr)]
    op, a, b = e[1], rev(e[2], env, arr), rev(e[3], env, arr)
    if op == "+":
        return chk(a + b)
    if op == "-":
        return chk(a - b)
    if op == "*":
        return chk(a * b)
    if b == 0:
        raise Violation("division by zero")
    if a == I64_MIN and b == -1 and not SPEC:
        raise Violation("MIN / -1")
    rem = a % abs(b)
    return chk((a - rem) // b) if op == "/" else rem


def spec_cond(c, env, arr):
    """Evaluate a contract/assert condition with spec (unbounded) arithmetic."""
    global SPEC
    old, SPEC = SPEC, True
    try:
        return rcond(c, env, arr)
    finally:
        SPEC = old


def rcond(c, env, arr):
    k = c[0]
    if k == "cmp":
        a, b = rev(c[2], env, arr), rev(c[3], env, arr)
        return {"<": a < b, "<=": a <= b, ">": a > b, ">=": a >= b, "==": a == b, "!=": a != b}[c[1]]
    if k == "not":
        return not rcond(c[1], env, arr)
    if k == "and":
        return rcond(c[1], env, arr) and rcond(c[2], env, arr)
    return rcond(c[1], env, arr) or rcond(c[2], env, arr)


CALLS = None   # calls-mode program info for the reference interpreter
SOFT = None    # when a set: false asserts are recorded instead of raising (used to bias generation)


def rcall(h, argv, env):
    klo, khi = h["krange"]
    if not klo <= argv <= khi:
        raise Violation("argument violates parameter type")
    local = {"k": argv}
    for f in FIELDS:
        local[f"rec.{f}"] = env[f"rec.{f}"]
        local[f"old(rec.{f})"] = env[f"rec.{f}"]
    for e in DELEMS:
        local[e] = env[e]
        local[e.replace("rec.", "old(rec.") + ")"] = env[e]
    if h["req"] is not None and not spec_cond(h["req"], local, []):
        raise Violation("precondition false at call")
    rexec(h["body"], local, [])
    local["result"] = rev(h["ret"], local, [])
    for c in h["ens"]:
        if not spec_cond(c, local, []):
            raise Violation("callee postcondition false")
    for f in FIELDS:
        env[f"rec.{f}"] = local[f"rec.{f}"]
    for e in DELEMS:
        env[e] = local[e]
    return local["result"]


OUT = []   # lines printed by the reference run
REC = None  # recursion-template info for the reference interpreter


def rexec(stmts, env, arr):
    for s in stmts:
        k = s[0]
        if k == "gcall":
            env[s[2]] = rrec(REC, rev(s[1], env, arr))
        elif k == "print":
            OUT.append(str(rev(s[1], env, arr)))
        elif k == "call":
            env[s[3]] = rcall(CALLS["helpers"][s[1]], rev(s[2], env, arr), env)
        elif k in ("assign", "let"):
            v = rev(s[2], env, arr)
            if CALLS and s[1][4:] in CALLS["franges"] and s[1].startswith("rec.") \
                    and not CALLS["franges"][s[1][4:]][0] <= v <= CALLS["franges"][s[1][4:]][1]:
                raise Violation("field out of declared range")
            env[s[1]] = v
        elif k == "aset":
            i = ridx(s[1], s[2], env, arr)
            arr[i] = rev(s[3], env, arr)
        elif k == "assert":
            if not spec_cond(s[1], env, arr):
                if SOFT is None:
                    raise Violation("assertion false")
                SOFT.add(id(s))
        elif k == "if":
            rexec(s[2] if rcond(s[1], env, arr) else s[3], env, arr)
        else:
            _, i, kk, e, inv = s
            env[i] = 0
            if inv is not None and not spec_cond(inv, env, arr):
                raise Violation("loop invariant false on entry")
            while env[i] < kk:
                env["r"] = rev(e, env, arr)
                env[i] += 1
                if inv is not None and not spec_cond(inv, env, arr):
                    raise Violation("loop invariant false after iteration")


def reference(p, args):
    global CALLS, REC
    CALLS = p.get("calls")
    REC = p.get("rec")
    OUT.clear()
    env = {n: a for (n, _, _), a in zip(p["params"], args)}
    if CALLS and CALLS.get("mk"):
        mk = CALLS["mk"]
        for e in mk["ens"]:
            if not spec_cond(e, mk_env(mk, CALLS["mkarg"]), []):
                raise Violation("mk postcondition false")
    if CALLS:
        env.update({f"rec.{f}": CALLS["inits"][f] for f in FIELDS})
        env.update({e: CALLS["dfill"] for e in DELEMS})
    env["r"] = rev(p["init"], env, [])
    arr = [p["arrfill"]] * 4
    rexec(p["body"], env, arr)
    env["result"] = env["r"]
    for c in p["ens"]:
        if not spec_cond(c, env, arr):
            raise Violation("postcondition false")
    return env["r"]


# ------------------------------------------------------------------ driver
def inputs(rng, p):
    out = []
    for _ in range(120):
        if len(out) >= 24:
            break
        a = []
        for _, lo, hi in p["params"]:
            c = rng.choice([lo, hi, 0, 1, -1, (lo + hi) // 2, rng.randint(lo, hi), rng.randint(lo, hi)])
            a.append(min(max(c, lo), hi))
        if p["req"] is not None:
            try:
                if not spec_cond(p["req"], {n: v for (n, _, _), v in zip(p["params"], a)}, []):
                    continue
            except Violation:
                continue
        out.append(a)
    return out


def jit_fns(ir, nparams):
    import llvmlite.binding as llvm
    llvm.initialize_native_target()
    llvm.initialize_native_asmprinter()
    fns = []
    for ir in (ir,):
        m = llvm.parse_assembly(ir)
        m.verify()
        tm = llvm.Target.from_default_triple().create_target_machine(opt=2)
        eng = llvm.create_mcjit_compiler(m, tm)
        eng.finalize_object()
        proto = ctypes.CFUNCTYPE(ctypes.c_int64, *([ctypes.c_int64] * nparams))
        fns.append((proto(eng.get_function_address("lise_f")), eng, m))
    return fns


def call_captured(fn, args):
    """Call a JIT function, capturing what it writes to file descriptor 1."""
    import os
    import tempfile
    sys.stdout.flush()
    tmp = tempfile.TemporaryFile()
    saved = os.dup(1)
    os.dup2(tmp.fileno(), 1)
    try:
        got = fn(*args)
    finally:
        os.dup2(saved, 1)
        os.close(saved)
    tmp.seek(0)
    data = tmp.read().decode()
    tmp.close()
    return got, data


def run_seed(seed):
    from lise_codegen import generate
    from lise_lexer import lex
    from lise_parser import Parser
    from lise_verify import check_source
    p = gen_program(seed)
    src = render(p)
    rep = check_source(src, f"fuzz{seed}.lise", timeout_ms=3000, independent="report", lints=False)
    if not rep.ok:
        return "rejected", src
    prog = Parser(lex(src)).parse_program()
    fns = jit_fns(generate(prog, "f"), len(p["params"]))
    rng = random.Random(seed ^ 0xABCDEF)
    for args in inputs(rng, p):
        try:
            want = reference(p, args)
        except Violation as v:
            return f"BUG(verifier unsound: {v}) args={args}", src
        expected_out = "".join(line + "\n" for line in OUT)
        for (fn, _, _), name in zip(fns, ("native",)):
            got, text = call_captured(fn, args)
            if got != want:
                return f"BUG(backend mismatch {name}: got {got}, want {want}) args={args}", src
            if text != expected_out:
                return f"BUG(output mismatch {name}: got {text!r}, want {expected_out!r}) args={args}", src
        try:
            from lise_semantics import Machine, Stuck
            ival, itext = Machine(prog).run_function("f", args)
        except Stuck as st:
            return f"BUG(verified program is STUCK in the reference semantics: {st}) args={args}", src
        if ival != want or itext != expected_out:
            return (f"BUG(reference semantics disagree: got {ival!r}/{itext!r}, fuzzer reference/native "
                    f"{want!r}/{expected_out!r}) args={args}"), src
    return "verified", src


def child(seeds):
    sys.setrecursionlimit(50000)
    for s in seeds:
        print(f"START {s}", flush=True)
        status, src = run_seed(s)
        print(f"RES {s} {status.splitlines()[0]}", flush=True)
        if status.startswith("BUG"):
            print("PROGRAM-BEGIN\n" + src + "PROGRAM-END", flush=True)


def main():
    if len(sys.argv) >= 2 and sys.argv[1] == "--child":
        child([int(x) for x in sys.argv[2:]])
        return 0
    count = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    start = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    seeds, stats, bugs = list(range(start, start + count)), {"verified": 0, "rejected": 0}, []
    while seeds:
        chunk = seeds[:25]
        r = subprocess.run([sys.executable, __file__, "--child"] + [str(s) for s in chunk],
                           capture_output=True, text=True)
        done, last_start, cur = set(), None, None
        for line in r.stdout.splitlines():
            if line.startswith("START "):
                last_start = int(line.split()[1])
            elif line.startswith("RES "):
                _, s, st = line.split(" ", 2)
                done.add(int(s))
                if st.startswith("BUG"):
                    bugs.append((int(s), st))
                else:
                    stats[st] = stats.get(st, 0) + 1
        if r.returncode != 0 and last_start is not None and last_start not in done:
            if r.returncode < 0 or r.returncode == 71:   # a signal, or the safety backstop (exit 71) in accepted code
                what = f"signal {-r.returncode}" if r.returncode < 0 else "the safety backstop (exit 71)"
                bugs.append((last_start, f"BUG(stopped by {what}: a proven check failed in verified code)"))
                done.add(last_start)
            else:                     # a Python exception in the harness itself: not a finding, fix the fuzzer
                print(f"HARNESS ERROR at seed {last_start}:\n{r.stderr[-1200:]}")
                return 2
        remaining = [s for s in chunk if s not in done]
        seeds = remaining + seeds[25:] if len(remaining) < len(chunk) else seeds[25:]
        if r.returncode != 0 and last_start is None:
            print(r.stderr[-800:])
            return 2
    print(f"seeds {start}..{start + count - 1}: verified={stats.get('verified', 0)} "
          f"rejected={stats.get('rejected', 0)} BUGS={len(bugs)}")
    for s, st in bugs:
        print(f"  seed {s}: {st}")
    return 1 if bugs else 0


if __name__ == "__main__":
    sys.exit(main())
