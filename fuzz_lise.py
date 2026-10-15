#!/usr/bin/env python3
"""Differential soundness fuzzer for Lise.

Generates random integer/array programs, runs the verifier, and for every program
the verifier ACCEPTS it checks, on many inputs:
  1. a Python reference interpreter (unbounded ints, Euclidean / and %) never hits
     overflow, division by zero, MIN/-1 or an out-of-bounds index   (verifier soundness)
  2. the compiled code (checked AND unchecked) returns the reference result and the
     checked build never traps                                       (backend correctness)
Any failure is a BUG: it means a proof was wrong or the backend disagrees with the spec.

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
LITS = [0, 1, 2, 3, 7, 10, -1, -2, -5, 100, 1000, 2 ** 31, 2 ** 40, 2 ** 62, I64_MAX]


def lit(rng):
    v = rng.choice(LITS)
    return v if v == I64_MAX or rng.random() < .5 else rng.choice([v, -v]) if abs(v) < I64_MAX else v


def gexpr(rng, vars_, arr, d):
    r = rng.random()
    if d == 0 or r < .25:
        if vars_ and rng.random() < .65:
            return ("var", rng.choice(vars_))
        return ("num", lit(rng))
    if r < .33:
        return ("neg", gexpr(rng, vars_, arr, d - 1))
    if r < .43 and arr:
        return ("idx", gexpr(rng, vars_, arr, d - 1), rng.choice([4, 4, 4, 5, 3, None]))
    op = rng.choice(["+", "+", "-", "-", "*", "/", "%"])
    l = gexpr(rng, vars_, arr, d - 1)
    if op in "/%":
        rr = ("num", rng.choice([2, 3, 7, -3, -1, 10])) if rng.random() < .7 else gexpr(rng, vars_, arr, d - 1)
    else:
        rr = gexpr(rng, vars_, arr, d - 1)
    return ("bin", op, l, rr)


def gcond(rng, vars_, arr, d):
    r = rng.random()
    if d == 0 or r < .6:
        return ("cmp", rng.choice(["<", "<=", ">", ">=", "==", "!="]), gexpr(rng, vars_, arr, 1), gexpr(rng, vars_, arr, 1))
    if r < .75:
        return ("not", gcond(rng, vars_, arr, d - 1))
    return (rng.choice(["and", "or"]), gcond(rng, vars_, arr, d - 1), gcond(rng, vars_, arr, d - 1))


class Gen:
    def __init__(self, rng):
        self.rng, self.n = rng, 0

    def block(self, vars_, arr, depth, count):
        rng, out, vars_ = self.rng, [], list(vars_)
        for _ in range(count):
            r = rng.random()
            if r < .30:
                out.append(("assign", "r", gexpr(rng, vars_, arr, 2)))
            elif r < .50:
                self.n += 1
                name = f"t{self.n}"
                out.append(("let", name, gexpr(rng, vars_, arr, 2)))
                vars_.append(name)
            elif r < .65 and arr:
                out.append(("aset", gexpr(rng, vars_, arr, 1), rng.choice([4, 4, 5, 3, None]),
                            gexpr(rng, vars_, arr, 2)))
            elif r < .85 and depth > 0:
                out.append(("if", gcond(rng, vars_, arr, 1), self.block(vars_, arr, depth - 1, rng.randint(1, 2)),
                            self.block(vars_, arr, depth - 1, rng.randint(0, 2))))
            elif depth > 0:
                self.n += 1
                k = rng.randint(0, 4)
                body_vars = [v for v in vars_ if v != "r"]
                out.append(("while", f"i{self.n}", k, gexpr(rng, body_vars, arr, 1)))
            else:
                out.append(("assign", "r", gexpr(rng, vars_, arr, 1)))
        return out


def gen_program(seed):
    rng = random.Random(seed)
    wide = rng.random() < .35
    params = []
    for i in range(rng.randint(1, 3)):
        if wide:
            lo, hi = rng.choice([(-(2 ** 62), 2 ** 62), (-(I64_MAX), I64_MAX), (-(2 ** 31), 2 ** 31), (0, I64_MAX)])
        else:
            lo = -rng.choice([0, 5, 100, 1000])
            hi = rng.choice([1, 5, 100, 1000])
        params.append((f"p{i}", lo, hi))
    arr = rng.random() < .5
    g = Gen(rng)
    body = g.block([p[0] for p in params] + ["r"], arr, 2, rng.randint(2, 5))
    init = gexpr(rng, [p[0] for p in params], arr, 1) if False else ("num", rng.choice([0, 1, 5]))
    return dict(params=params, arr=arr, arrfill=rng.choice([0, 1, 9]), init=init, body=body)


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
        elif k == "if":
            out.append(f"{sp}if {pc(s[1])} then")
            out.extend(pb(s[2], ind + 1))
            if s[3]:
                out.append(f"{sp}else")
                out.extend(pb(s[3], ind + 1))
            out.append(f"{sp}end")
        else:
            _, i, kk, e = s
            out += [f"{sp}var {i}: Integer := 0", f"{sp}while {i} < {kk}",
                    f"{sp}invariant 0 <= {i} and {i} <= {kk}", f"{sp}decreases {kk} - {i}", f"{sp}do",
                    f"{sp}    r := {pe(e)}", f"{sp}    {i} := {i} + 1", f"{sp}end"]
    return out


def render(p):
    ps = ", ".join(f"{n}: Integer where value >= {'(-%d)' % -lo if lo < 0 else lo} and value <= {hi}"
                   for n, lo, hi in p["params"])
    lines = [f"fn f({ps}) -> Integer", "is", f"    var r: Integer := {pe(p['init'])}"]
    if p["arr"]:
        lines.append(f"    var arr: Array[Integer, 4] := fill({p['arrfill']})")
    lines += pb(p["body"], 1)
    lines += ["    return r", "end", ""]
    return "\n".join(lines)


# ------------------------------------------------------------------ reference interpreter
def chk(v):
    if not (I64_MIN <= v <= I64_MAX):
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
    if a == I64_MIN and b == -1:
        raise Violation("MIN / -1")
    rem = a % abs(b)
    return chk((a - rem) // b) if op == "/" else rem


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


def rexec(stmts, env, arr):
    for s in stmts:
        k = s[0]
        if k in ("assign", "let"):
            env[s[1]] = rev(s[2], env, arr)
        elif k == "aset":
            i = ridx(s[1], s[2], env, arr)
            arr[i] = rev(s[3], env, arr)
        elif k == "if":
            rexec(s[2] if rcond(s[1], env, arr) else s[3], env, arr)
        else:
            _, i, kk, e = s
            env[i] = 0
            while env[i] < kk:
                env["r"] = rev(e, env, arr)
                env[i] += 1


def reference(p, args):
    env = {n: a for (n, _, _), a in zip(p["params"], args)}
    env["r"] = rev(p["init"], env, [])
    arr = [p["arrfill"]] * 4
    rexec(p["body"], env, arr)
    return env["r"]


# ------------------------------------------------------------------ driver
def inputs(rng, p):
    out = []
    for _ in range(24):
        a = []
        for _, lo, hi in p["params"]:
            c = rng.choice([lo, hi, 0, 1, -1, (lo + hi) // 2, rng.randint(lo, hi), rng.randint(lo, hi)])
            a.append(min(max(c, lo), hi))
        out.append(a)
    return out


def jit_fns(ir_checked, ir_unchecked, nparams):
    import llvmlite.binding as llvm
    llvm.initialize_native_target()
    llvm.initialize_native_asmprinter()
    fns = []
    for ir in (ir_checked, ir_unchecked):
        m = llvm.parse_assembly(ir)
        m.verify()
        tm = llvm.Target.from_default_triple().create_target_machine(opt=2)
        eng = llvm.create_mcjit_compiler(m, tm)
        eng.finalize_object()
        proto = ctypes.CFUNCTYPE(ctypes.c_int64, *([ctypes.c_int64] * nparams))
        fns.append((proto(eng.get_function_address("lise_f")), eng, m))
    return fns


def run_seed(seed):
    from lise_codegen import generate
    from lise_lexer import lex
    from lise_parser import Parser
    from lise_verify import check_source
    p = gen_program(seed)
    src = render(p)
    rep = check_source(src, f"fuzz{seed}.lise", timeout_ms=3000)
    if not rep.ok:
        return "rejected", src
    prog = Parser(lex(src)).parse_program()
    fns = jit_fns(generate(prog, "f", True), generate(prog, "f", False), len(p["params"]))
    rng = random.Random(seed ^ 0xABCDEF)
    for args in inputs(rng, p):
        try:
            want = reference(p, args)
        except Violation as v:
            return f"BUG(verifier unsound: {v}) args={args}", src
        for (fn, _, _), name in zip(fns, ("checked", "unchecked")):
            got = fn(*args)
            if got != want:
                return f"BUG(backend mismatch {name}: got {got}, want {want}) args={args}", src
    return "verified", src


def child(seeds):
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
            bugs.append((last_start, f"BUG(process died with code {r.returncode}: trap/crash in verified code)"))
            done.add(last_start)
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
