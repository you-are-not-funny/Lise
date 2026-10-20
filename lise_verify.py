"""Lise verifier: sort/type checking fused with verification-condition
generation (symbolic execution) discharged by Z3.

Policy: an SMT result of `unknown` (timeout etc.) is a compile ERROR,
never a pass.  Only `unsat` (negated goal unsatisfiable) counts as proved.
"""
import hashlib
import json
import os

import z3

import lise_fmcheck
import lise_xcheck

from lise_ast import *
from lise_ast import walk, fmt_expr, fmt_type
from lise_lexer import LiseError, lex
from lise_parser import Parser

VERSION = "0.3.0"
I64_MIN = -(2 ** 63)
I64_MAX = 2 ** 63 - 1
BUILTIN_TYPES = {"Integer", "Bool", "Void", "Array", "Outcome"}
BUILTIN_FNS = {"Success", "Failure", "succeeded", "failed", "fill", "print", "print_int"}
RESERVED_VARS = {"value", "result"}
_ENUM_SERIAL = {}


# ---------------------------------------------------------------- reports
class Diag:
    def __init__(self, filename, loc, msg, notes=None):
        self.filename, self.loc, self.msg, self.notes = filename, loc, msg, notes or []

    def __str__(self):
        s = f"{self.filename}:{self.loc[0]}:{self.loc[1]}: error: {self.msg}"
        for n in self.notes:
            s += f"\n    {n}"
        return s


class Report:
    def __init__(self, filename):
        self.filename = filename
        self.diags = []
        self.functions = 0
        self.verified = 0
        self.cached = 0
        self.obligations = 0
        self.confirmed = 0     # obligations re-confirmed by the second solver (cvc5)
        self.fm_confirmed = 0  # ... and independently re-derived by the solver-free FM checker

    @property
    def ok(self):
        return not self.diags


class ProofCache:
    """Content-addressed cache of *proved* functions (key -> 'proved')."""

    def __init__(self, directory=".lise-cache"):
        self.path = os.path.join(directory, "proofs.json")
        self.data = {}
        try:
            with open(self.path) as f:
                self.data = json.load(f)
        except (OSError, ValueError):
            self.data = {}
        self.dirty = False

    def has(self, key):
        return self.data.get(key) == "proved"

    def add(self, key):
        self.data[key] = "proved"
        self.dirty = True

    def save(self):
        if not self.dirty:
            return
        os.makedirs(os.path.dirname(self.path), exist_ok=True)
        with open(self.path, "w") as f:
            json.dump(self.data, f, indent=0, sort_keys=True)


# ---------------------------------------------------------------- types
class RType:
    def __init__(self, kind, name, sort=None, preds=None, elem=None,
                 length=None, decl=None, tenv=None, label=None):
        self.kind = kind      # int bool void opaque outcome enum array record
        self.name = name
        self.sort = sort
        self.preds = list(preds or [])   # [(pred_expr, bind_dict)]
        self.elem = elem
        self.length = length
        self.decl = decl
        self.tenv = tenv
        self.label = label or name

    def derive(self, extra_preds, label=None):
        r = RType(self.kind, self.name, self.sort, self.preds + list(extra_preds),
                  self.elem, self.length, self.decl, self.tenv, label or self.label)
        return r


class State:
    def __init__(self):
        self.env = {}        # leaf path -> z3 term
        self.ltypes = {}     # leaf path -> RType
        self.vars = {}       # name -> (RType, mutable)
        self.pc = []         # path condition / assumptions
        self.old_env = None
        self.in_branch = False
        self.trust = False   # skip well-formedness obligations inside ev()
        self.moved = set()   # root variables whose value has been moved away
        self.borrowed = set()  # 'in'/'mutable' parameters (cannot be moved out of)

    def fork(self, extra=None):
        s = State()
        s.env, s.ltypes, s.vars = dict(self.env), dict(self.ltypes), dict(self.vars)
        s.pc = list(self.pc)
        s.old_env, s.in_branch, s.trust = self.old_env, self.in_branch, self.trust
        s.moved, s.borrowed = set(self.moved), self.borrowed
        if extra is not None:
            s.pc.append(extra)
        return s

    def branch(self, guard):
        """Read-only evaluation context under an extra guard (short-circuit)."""
        s = State()
        s.env, s.ltypes, s.vars = self.env, self.ltypes, self.vars
        s.pc = self.pc + [guard]
        s.old_env, s.trust = self.old_env, self.trust
        s.moved, s.borrowed = self.moved, self.borrowed
        s.in_branch = True
        return s


def conj(xs):
    xs = list(xs)
    if not xs:
        return z3.BoolVal(True)
    return xs[0] if len(xs) == 1 else z3.And(*xs)


# ---------------------------------------------------------------- verifier
class Verifier:
    def __init__(self, prog, toks, filename, timeout_ms, cache, report):
        self.prog, self.toks, self.filename = prog, toks, filename
        self.timeout, self.cache, self.rep = timeout_ms, cache, report
        self.types, self.records, self.fns = {}, {}, {}
        self.enums = {}      # name -> (sort, {variant: const})
        self.counters = {}
        self._mods = {}
        self.independent = "require"
        self.cert_dir = None                 # write every validated certificate here (lise.py --certificates DIR)
        self.lints = True                    # developer-mistake guards (errors); only test harnesses switch them off
        self.lint_seen, self.branch_msg, self.branch_live = set(), {}, set()
        self.agg_call_ok = False   # set only while a typed declaration evaluates its initialiser
        self.entry_consts = []
        self.tenv = {}
        void_sort = z3.DeclareSort("Void")
        self.void_sort = void_sort
        self.void_val = z3.Const("void", void_sort)
        dt = z3.Datatype("Outcome")
        dt.declare("Success")
        dt.declare("Failure")
        self.outcome_sort = dt.create()
        self.outcome_ctor = {"Success": self.outcome_sort.Success,
                             "Failure": self.outcome_sort.Failure}
        self.void_rt = RType("void", "Void", sort=void_sort, label="Void")
        self.int_rt = RType("int", "Integer", sort=z3.IntSort(), label="Integer")

    # ---------------- diagnostics / proving
    def diag(self, loc, msg, notes=None):
        self.rep.diags.append(Diag(self.filename, loc, msg, notes))

    def fresh(self, name, sort):
        n = self.counters.get(name, 0)
        self.counters[name] = n + 1
        return z3.Const(f"{name}@{n}", sort)

    def prove(self, st, goal, msg, loc):
        """Prove `goal` under st.pc.  Only unsat of the negation counts."""
        self.rep.obligations += 1
        s = z3.Solver()
        s.set("timeout", self.timeout)
        for p in st.pc:
            s.add(p)
        s.add(z3.Not(goal))
        r = s.check()
        ok = r == z3.unsat
        if ok:
            # Independent second opinion: both solvers must agree the negation is UNSAT.
            status, detail = lise_xcheck.check(s, self.timeout * 2)
            if status == lise_xcheck.UNSAT:
                self.rep.confirmed += 1
                fm_status, fm_detail = lise_fmcheck.check(s)
                if fm_status == lise_fmcheck.UNSAT:
                    self.rep.fm_confirmed += 1
                    if self.cert_dir:
                        self.write_certificate(msg, loc)
                elif fm_status == lise_fmcheck.INVALID:
                    self.diag(loc, msg, ["INTERNAL ERROR in the independent checker: it claimed a proof but its own "
                                         f"certificate failed validation ({fm_detail}). The proof is NOT accepted."])
                    st.pc.append(goal)
                    return False
                elif fm_status == lise_fmcheck.SAT:
                    self.diag(loc, msg, ["INDEPENDENT CHECKER DISAGREES: both solvers said this holds, but the "
                                         f"solver-free checker found and verified a counterexample ({fm_detail}). "
                                         "A solver or the verifier's encoding is wrong; the proof is NOT accepted."])
                    st.pc.append(goal)
                    return False
                elif self.independent == "require":
                    self.diag(loc, msg, ["not independently confirmed: the solvers accept this, but the solver-free "
                                         f"checker could not re-derive it ({fm_detail}). Lise rejects what it cannot "
                                         "double-check; restructure the code (simpler arithmetic, explicit bounds, "
                                         "smaller expressions) or add intermediate asserts."])
                    st.pc.append(goal)
                    return False
            elif status == lise_xcheck.SAT:
                ok = False
                self.diag(loc, msg, ["SOLVER DISAGREEMENT: Z3 proved this but cvc5 found a counterexample. "
                                     "This is a solver or verifier bug; the proof is NOT accepted."])
                st.pc.append(goal)
                return False
            else:
                ok = False
                self.diag(loc, msg, ["proved by Z3 but not confirmed by the second solver (cvc5: "
                                     f"{detail or 'unknown/timeout'}); unconfirmed proofs are rejected. "
                                     "Simplify the obligation (e.g. avoid heavy nonlinear arithmetic) or add intermediate assertions."])
                st.pc.append(goal)
                return False
        if not ok:
            notes = []
            if r == z3.sat:
                m = s.model()
                vals = []
                for disp, c in self.entry_consts:
                    txt = str(m.eval(c, model_completion=True))
                    vals.append(f"{disp} = {txt if len(txt) < 60 else txt[:57] + '...'}")
                notes.append("counterexample (inputs): " + (", ".join(vals) if vals else "(none)"))
            else:
                notes.append(f"solver returned 'unknown' ({s.reason_unknown()}); "
                             "unknown is rejected. Strengthen contracts/invariants or add assert hints.")
            self.diag(loc, msg, notes)
        st.pc.append(goal)  # assume afterwards to avoid cascading errors
        return ok

    def oblige(self, st, goal, msg, loc):
        """Well-formedness obligation raised while evaluating an expression."""
        if st.trust:
            return True
        return self.prove(st, goal, msg, loc)

    def write_certificate(self, msg, loc):
        import json
        os.makedirs(self.cert_dir, exist_ok=True)
        self.cert_n = getattr(self, "cert_n", 0) + 1
        cert = dict(lise_fmcheck.last_cert)
        cert["meta"] = {"file": self.filename, "function": self.fn.name, "obligation": msg, "line": loc[0]}
        with open(os.path.join(self.cert_dir, f"{self.fn.name}-{self.cert_n:04d}.json"), "w", encoding="utf-8") as fh:
            json.dump(cert, fh)

    def lint(self, loc, msg):
        """A developer-mistake guard: reported as an error (it fails the build) unless a test harness disabled it."""
        if self.lints and (loc, msg) not in self.lint_seen:
            self.lint_seen.add((loc, msg))
            self.diag(loc, "lint: " + msg)

    def unused_lints(self, fn):
        assign_roots, assigned = set(), set()
        for n in walk(fn.body):
            if isinstance(n, Assign):
                root = n.target
                while isinstance(root, (Field, Index)):
                    root = root.obj
                if isinstance(root, Name):
                    assign_roots.add(id(root))
                    assigned.add(root.ident)
                if isinstance(n.value, Name) and isinstance(n.target, Name) and n.value.ident == n.target.ident:
                    self.lint(n.loc, f"'{n.target.ident}' is assigned to itself")
        reads = {n.ident for n in walk(fn.body) if isinstance(n, Name) and id(n) not in assign_roots}
        in_contracts = {n.ident for n in walk([fn.requires, fn.ensures, fn.decreases]) if isinstance(n, Name)}
        for n in walk(fn.body):
            if isinstance(n, Let) and not n.name.startswith("_") and n.name not in reads:
                self.lint(n.loc, f"variable '{n.name}' is never read (if you are ignoring a result on purpose, "
                                 f"name it '_{n.name}')")
        for p in fn.params:
            if not p.name.startswith("_") and p.name not in reads and p.name not in assigned \
                    and p.name not in in_contracts:
                self.lint(p.loc, f"parameter '{p.name}' is never used (rename it '_{p.name}' if that is intended)")

    def feasible(self, st):
        s = z3.Solver()
        s.set("timeout", 2000)
        for p in st.pc:
            s.add(p)
        if s.check() != z3.unsat:
            return True
        # Z3 says the path is dead: prune it (skipping its obligations) only if cvc5 AND the
        # independent checker both agree; otherwise keep the path and prove its obligations.
        if lise_xcheck.check(s, 4000)[0] != lise_xcheck.UNSAT:
            return True
        return lise_fmcheck.check(s)[0] != lise_fmcheck.UNSAT

    # ---------------- helpers on expressions
    def path_of(self, e):
        if isinstance(e, Name):
            return e.ident
        if isinstance(e, Field):
            p = self.path_of(e.obj)
            return None if p is None else p + "." + e.name
        return None

    def expect_int(self, v, node):
        if not z3.is_int(v):
            raise LiseError(f"expected Integer, found {v.sort()}", node.loc)

    def expect_bool(self, v, node):
        if not z3.is_bool(v):
            raise LiseError(f"expected Bool, found {v.sort()}", node.loc)

    def expr_to_type(self, e):
        if isinstance(e, Name):
            return TypeRef(e.ident, [], None, e.loc)
        if isinstance(e, Index) and isinstance(e.obj, Name):
            return TypeRef(e.obj.ident, list(e.indices), None, e.loc)
        raise LiseError(f"expected a type, found '{fmt_expr(e)}'", e.loc)

    # ---------------- type resolution
    def vals(self, tenv):
        return {k: v for k, (kind, v) in tenv.items() if kind == "val"}

    def static_eval(self, e, tenv):
        tmp = State()
        tmp.env = self.vals(tenv)
        tmp.trust = True
        v = self.ev(e, tmp, spec=True)
        return v

    def type_invs(self, rt, term):
        out = []
        for pred, bind in rt.preds:
            tmp = State()
            tmp.env = dict(bind)
            tmp.env["value"] = term
            tmp.trust = True
            g = self.ev(pred, tmp, spec=True)
            self.expect_bool(g, pred)
            out.append(g)
        return out

    def base_facts(self, rt, term):
        facts = self.type_invs(rt, term)
        if rt.kind == "int":
            facts.append(z3.And(term >= I64_MIN, term <= I64_MAX))
        return facts

    def bind_generics(self, gparams, args, tenv, st, loc, depth):
        if len(gparams) != len(args):
            raise LiseError(f"expected {len(gparams)} generic argument(s), got {len(args)}", loc)
        new = {}
        for gp, arg in zip(gparams, args):
            if gp.constraint is None:
                new[gp.name] = ("type", self.resolve_type(self.expr_to_type(arg), tenv, st, depth + 1))
            else:
                term = self.static_eval(arg, tenv)
                crt = self.resolve_type(gp.constraint, new, None, depth + 1)
                if not (term.sort() == crt.sort):
                    raise LiseError(f"generic argument '{fmt_expr(arg)}' has wrong type", arg.loc)
                if st is not None:
                    for g in self.type_invs(crt, term):
                        self.prove(st, g, f"generic argument '{fmt_expr(arg)}' may not satisfy "
                                          f"'{gp.name}: {crt.label}'", arg.loc)
                new[gp.name] = ("val", term)
        return new

    def resolve_type(self, ref, tenv, st=None, depth=0):
        if depth > 40:
            raise LiseError("type is recursive or nested too deeply", ref.loc)
        n = ref.name
        if n in tenv:
            kind, v = tenv[n]
            if kind != "type" or ref.args:
                raise LiseError(f"'{n}' is not a type constructor here", ref.loc)
            base = v
        elif n == "Integer":
            self.no_args(ref)
            base = self.int_rt
        elif n == "Bool":
            self.no_args(ref)
            base = RType("bool", "Bool", sort=z3.BoolSort(), label="Bool")
        elif n == "Void":
            self.no_args(ref)
            base = self.void_rt
        elif n == "Array":
            if len(ref.args) != 2:
                raise LiseError("Array takes 2 arguments: Array[ElementType, Length]", ref.loc)
            elem = self.resolve_type(self.expr_to_type(ref.args[0]), tenv, st, depth + 1)
            if elem.preds or elem.kind in ("array", "record"):
                raise LiseError("array element types must be unrefined scalar types "
                                "(refined/nested element types are not supported yet)", ref.loc)
            length = self.static_eval(ref.args[1], tenv)
            if not z3.is_int(length):
                raise LiseError("array length must be an Integer", ref.args[1].loc)
            if st is not None:
                self.prove(st, length >= 0, "array length may be negative", ref.args[1].loc)
            base = RType("array", "Array", sort=z3.ArraySort(z3.IntSort(), elem.sort),
                         elem=elem, length=length, label=f"Array[{elem.label}, {fmt_expr(ref.args[1])}]")
        elif n == "Outcome":
            if len(ref.args) != 2:
                raise LiseError("Outcome takes 2 arguments: Outcome[Value, Error]", ref.loc)
            for a in ref.args:
                self.resolve_type(self.expr_to_type(a), tenv, st, depth + 1)
            base = RType("outcome", "Outcome", sort=self.outcome_sort, label=fmt_type(TypeRef(n, ref.args)))
        elif n in self.types:
            decl = self.types[n]
            sub = self.bind_generics(decl.gparams, ref.args, tenv, st, ref.loc, depth)
            base = self.resolve_type(decl.base, sub, st, depth + 1)
            base = base.derive([], label=fmt_type(TypeRef(n, ref.args)))
        elif n in self.records:
            decl = self.records[n]
            sub = self.bind_generics(decl.gparams, ref.args, tenv, st, ref.loc, depth)
            base = RType("record", n, decl=decl, tenv=sub, label=fmt_type(TypeRef(n, ref.args)))
        elif n in self.enums:
            self.no_args(ref)
            base = RType("enum", n, sort=self.enums[n][0], label=n)
        else:
            raise LiseError(f"unknown type '{n}'", ref.loc)
        if ref.pred is not None:
            if base.kind in ("array", "record"):
                raise LiseError("'where' refinements on array/record types are not supported", ref.loc)
            base = base.derive([(ref.pred, self.vals(tenv))], label=fmt_type(ref))
        return base

    def no_args(self, ref):
        if ref.args:
            raise LiseError(f"type '{ref.name}' takes no arguments", ref.loc)

    def record_fields(self, rt):
        return [(f.name, self.resolve_type(f.ty, rt.tenv, None)) for f in rt.decl.fields]

    def leaves(self, rt, prefix, depth=0):
        if depth > 16:
            raise LiseError("recursive record types are not supported", (0, 0))
        if rt.kind == "record":
            for fname, frt in self.record_fields(rt):
                yield from self.leaves(frt, prefix + "." + fname, depth + 1)
        else:
            yield prefix, rt

    def record_invs(self, rt, prefix, env, ltypes, depth=0):
        """Record-level `where` invariants (recursively) as z3 booleans."""
        out = []
        if rt.kind != "record" or depth > 16:
            return out
        decl = rt.decl
        if decl.pred is not None:
            tmp = State()
            tmp.trust = True
            tmp.ltypes = ltypes
            tmp.env = dict(self.vals(rt.tenv))
            for fname, frt in self.record_fields(rt):
                p = prefix + "." + fname
                if frt.kind != "record" and p in env:
                    tmp.env[fname] = env[p]
            g = self.ev(decl.pred, tmp, spec=True)
            self.expect_bool(g, decl.pred)
            out.append(g)
        for fname, frt in self.record_fields(rt):
            out.extend(self.record_invs(frt, prefix + "." + fname, env, ltypes, depth + 1))
        return out

    def declare_var(self, st, name, rt, mutable, value=None, entry=False, loc=(0, 0)):
        if name in RESERVED_VARS:
            raise LiseError(f"'{name}' is a reserved name", loc)
        if name in st.vars or name in st.env or name in self.enums:
            raise LiseError(f"'{name}' is already declared (shadowing is not allowed)", loc)
        st.vars[name] = (rt, mutable)
        for path, lt in self.leaves(rt, name):
            if value is not None:
                v = value
            else:
                v = self.fresh(path, lt.sort)
                if entry:
                    self.entry_consts.append((path, v))
                st.pc.extend(self.base_facts(lt, v))
            st.env[path] = v
            st.ltypes[path] = lt

    def remove_var(self, st, name):
        st.vars.pop(name, None)
        st.moved.discard(name)
        for p in [p for p in st.env if p == name or p.startswith(name + ".")]:
            st.env.pop(p, None)
            st.ltypes.pop(p, None)

    def setup_generics(self, gparams, st):
        tenv = {}
        for gp in gparams:
            if gp.name in tenv or gp.name in RESERVED_VARS or gp.name in BUILTIN_TYPES:
                raise LiseError(f"invalid or duplicate generic parameter '{gp.name}'", gp.loc)
            if gp.constraint is None:
                tenv[gp.name] = ("type", RType("opaque", gp.name, sort=z3.DeclareSort(gp.name), label=gp.name))
            else:
                rt = self.resolve_type(gp.constraint, tenv, st)
                if rt.kind != "int":
                    raise LiseError("generic value parameters must have an Integer type", gp.loc)
                c = self.fresh(gp.name, z3.IntSort())
                self.entry_consts.append((gp.name, c))
                tenv[gp.name] = ("val", c)
                st.env[gp.name] = c
                st.ltypes[gp.name] = rt
                st.pc.extend(self.base_facts(rt, c))
        return tenv

    def infer_rtype(self, v, node):
        srt = v.sort()
        if z3.is_int(v):
            return self.int_rt
        if z3.is_bool(v):
            return RType("bool", "Bool", sort=z3.BoolSort(), label="Bool")
        if srt == self.void_sort:
            return self.void_rt
        if srt == self.outcome_sort:
            return RType("outcome", "Outcome", sort=srt, label="Outcome")
        for n, (s, _) in self.enums.items():
            if s == srt:
                return RType("enum", n, sort=s, label=n)
        for k, (kind, t) in self.tenv.items():
            if kind == "type" and t.sort == srt:
                return t
        raise LiseError("add a type annotation: the type of this value cannot be inferred", node.loc)

    # ---------------- ownership (affine) checking
    @staticmethod
    def is_copy(rt):
        return rt.kind in ("int", "bool", "void", "enum", "outcome")

    def check_live(self, st, e, spec):
        if spec:
            return
        base = e.obj if isinstance(e, Index) else e
        p = self.path_of(base)
        if p is not None and p.split(".")[0] in st.moved:
            raise LiseError(f"use of moved value '{p.split('.')[0]}'", e.loc)

    def move_out(self, e, st):
        """`e` is used by value in an owning position (let/assign/return/consume arg).
        Non-Copy variables are moved; Copy values and temporaries are not."""
        if isinstance(e, Index):
            b = self.path_of(e.obj)
            if b in st.ltypes and st.ltypes[b].kind == "array" and not self.is_copy(st.ltypes[b].elem):
                raise LiseError("cannot move an element out of an array", e.loc)
            return
        p = self.path_of(e)
        if p is None:
            return
        root = p.split(".")[0]
        if p in st.vars:
            rt = st.vars[p][0]
        elif p in st.ltypes:
            rt = st.ltypes[p]
        else:
            return
        if self.is_copy(rt):
            return
        if "." in p:
            raise LiseError(f"cannot move '{p}' out of a field; only whole variables can be moved", e.loc)
        if st.in_branch:
            raise LiseError("cannot move a value inside the right side of and/or/implies", e.loc)
        if root in st.borrowed:
            raise LiseError(f"cannot move '{root}': it is a borrowed ('in'/'mutable') parameter; "
                            "declare it 'consume' to take ownership", e.loc)
        st.moved.add(root)

    # ---------------- expression evaluation
    def ev(self, e, st, spec=False):
        if isinstance(e, (Name, Field, Index)):
            self.check_live(st, e, spec)
        if isinstance(e, Num):
            if not spec and not (I64_MIN <= e.value <= I64_MAX):
                raise LiseError("integer literal does not fit in Integer (64-bit)", e.loc)
            return z3.IntVal(e.value)
        if isinstance(e, BoolLit):
            return z3.BoolVal(e.value)
        if isinstance(e, Str):
            raise LiseError('string literals can only be used as the argument of print("...")', e.loc)
        if isinstance(e, Name):
            if e.ident in st.env:
                return st.env[e.ident]
            if e.ident == "Void":
                return self.void_val
            if e.ident in st.vars:
                raise LiseError(f"record value '{e.ident}' cannot be used as a plain value here", e.loc)
            raise LiseError(f"undefined name '{e.ident}'", e.loc)
        if isinstance(e, Field):
            if isinstance(e.obj, Name) and e.obj.ident in self.enums and e.obj.ident not in st.vars:
                variants = self.enums[e.obj.ident][1]
                if e.name not in variants:
                    raise LiseError(f"enum '{e.obj.ident}' has no variant '{e.name}'", e.loc)
                return variants[e.name]
            p = self.path_of(e)
            if p is not None and p in st.env:
                return st.env[p]
            raise LiseError(f"unknown field access '{fmt_expr(e)}'", e.loc)
        if isinstance(e, Index):
            if len(e.indices) != 1:
                raise LiseError("arrays take exactly one index", e.loc)
            p = self.path_of(e.obj)
            if p is None or p not in st.env or st.ltypes[p].kind != "array":
                raise LiseError(f"'{fmt_expr(e.obj)}' is not an array", e.loc)
            i = self.ev(e.indices[0], st, spec)
            self.expect_int(i, e.indices[0])
            self.oblige(st, z3.And(i >= 0, i < st.ltypes[p].length),
                        f"array index '{fmt_expr(e)}' may be out of bounds (need 0 <= index < length)", e.loc)
            return z3.Select(st.env[p], i)
        if isinstance(e, Call):
            return self.ev_call(e, st, spec)
        if isinstance(e, Old):
            if st.old_env is None:
                raise LiseError("old() is only allowed in 'ensures' clauses and loop invariants", e.loc)
            o = State()
            o.env, o.ltypes, o.pc = st.old_env, st.ltypes, list(st.pc)
            o.in_branch, o.trust = True, st.trust
            return self.ev(e.expr, o, spec=True)
        if isinstance(e, Unary):
            v = self.ev(e.operand, st, spec)
            if e.op == "-":
                self.expect_int(v, e.operand)
                r = -v
                if not spec:
                    self.oblige(st, z3.And(r >= I64_MIN, r <= I64_MAX), "integer overflow in negation", e.loc)
                return r
            self.expect_bool(v, e.operand)
            return z3.Not(v)
        if isinstance(e, Binary):
            return self.ev_binary(e, st, spec)
        raise LiseError("unsupported expression", getattr(e, "loc", (0, 0)))

    def ev_binary(self, e, st, spec):
        op = e.op
        if op in ("and", "or", "implies"):
            l = self.ev(e.left, st, spec)
            self.expect_bool(l, e.left)
            guard = z3.Not(l) if op == "or" else l
            ch = st.branch(guard)
            n = len(ch.pc)
            r = self.ev(e.right, ch, spec)
            self.expect_bool(r, e.right)
            new = ch.pc[n:]
            if new:
                st.pc.append(z3.Implies(guard, conj(new)))
            return {"and": z3.And(l, r), "or": z3.Or(l, r), "implies": z3.Implies(l, r)}[op]
        l = self.ev(e.left, st, spec)
        r = self.ev(e.right, st, spec)
        if op in ("+", "-", "*"):
            self.expect_int(l, e.left)
            self.expect_int(r, e.right)
            res = l + r if op == "+" else (l - r if op == "-" else l * r)
            if not spec:
                self.oblige(st, z3.And(res >= I64_MIN, res <= I64_MAX),
                            f"integer overflow in '{fmt_expr(e)}'", e.loc)
            return res
        if op in ("/", "%"):
            self.expect_int(l, e.left)
            self.expect_int(r, e.right)
            self.oblige(st, r != 0, f"division by zero in '{fmt_expr(e)}'", e.loc)
            res = l / r if op == "/" else l % r
            if not spec and op == "/":
                self.oblige(st, z3.And(res >= I64_MIN, res <= I64_MAX),
                            f"integer overflow in '{fmt_expr(e)}'", e.loc)
            if not spec and op == "%":
                # MIN % -1 is undefined behaviour on real hardware / in LLVM (srem)
                self.oblige(st, z3.Not(z3.And(l == I64_MIN, r == -1)),
                            f"integer overflow in '{fmt_expr(e)}' (MIN % -1)", e.loc)
            return res
        if op in ("<", "<=", ">", ">="):
            self.expect_int(l, e.left)
            self.expect_int(r, e.right)
            return {"<": l < r, "<=": l <= r, ">": l > r, ">=": l >= r}[op]
        if op in ("==", "!="):
            if not (l.sort() == r.sort()):
                raise LiseError(f"cannot compare {l.sort()} with {r.sort()}", e.loc)
            return l == r if op == "==" else l != r
        raise LiseError(f"unknown operator '{op}'", e.loc)

    def ev_call(self, e, st, spec):
        agg_ok, self.agg_call_ok = self.agg_call_ok, False
        name = e.name
        if name in ("Success", "Failure"):
            if e.targs is not None or len(e.args) != 1:
                raise LiseError(f"{name} takes exactly one argument", e.loc)
            self.ev(e.args[0], st, spec)  # payload is evaluated (checked) but erased in Phase 1
            if not spec:
                self.move_out(e.args[0], st)
            return self.outcome_ctor[name]
        if name in ("succeeded", "failed"):
            if len(e.args) != 1:
                raise LiseError(f"{name} takes exactly one argument", e.loc)
            v = self.ev(e.args[0], st, spec)
            if not (v.sort() == self.outcome_sort):
                raise LiseError(f"{name} expects an Outcome", e.args[0].loc)
            return self.outcome_sort.is_Success(v) if name == "succeeded" else self.outcome_sort.is_Failure(v)
        if name in ("print", "print_int"):
            if spec:
                raise LiseError(f"'{name}' is not allowed inside contracts", e.loc)
            if e.targs is not None or len(e.args) != 1:
                raise LiseError(f"{name} takes exactly one argument", e.loc)
            a = e.args[0]
            if name == "print":
                if not isinstance(a, Str):
                    raise LiseError('print takes a string literal, e.g. print("hello\\n"); use print_int for Integers', a.loc)
            else:
                v = self.ev(a, st, spec)       # overflow etc. are proven as for any expression
                if not (v.sort() == z3.IntSort()):
                    raise LiseError("print_int takes an Integer", a.loc)
            return self.void_val
        if name == "fill":
            if e.targs is not None or len(e.args) != 1:
                raise LiseError("fill takes exactly one argument: fill(value)", e.loc)
            v = self.ev(e.args[0], st, spec)
            if not spec:
                self.move_out(e.args[0], st)
            return z3.K(z3.IntSort(), v)
        if name in self.records:
            raise LiseError(f"record constructor '{name}(...)' is only allowed as the value of a typed "
                            f"declaration, e.g. var x: {name} := {name}(...)", e.loc)
        if spec:
            raise LiseError("function calls are not allowed inside contracts", e.loc)
        callee = self.fns.get(name)
        if callee is None:
            raise LiseError(f"unknown function '{name}'", e.loc)
        has_mut = any(p.mode == "mutable" for p in callee.params)
        if has_mut and st.in_branch:
            raise LiseError("calls with 'mutable' arguments are not allowed inside the right side of "
                            "and/or/implies", e.loc)
        ctenv = self.bind_generics(callee.gparams, e.targs or [], self.tenv, st, e.loc, 0)
        if (e.targs is None) and callee.gparams:
            raise LiseError(f"'{name}' is generic: pass explicit arguments, e.g. {name}[...](...)", e.loc)
        if len(e.args) != len(callee.params):
            raise LiseError(f"'{name}' expects {len(callee.params)} argument(s), got {len(e.args)}", e.loc)

        cenv = dict(self.vals(ctenv))
        cltypes = {}
        mapping = []       # (callee_path, caller_path, leaf RType) for mutable params
        mut_rec = []       # (caller record path, caller record RType)
        mut_roots = []
        for prm, arg in zip(callee.params, e.args):
            prt = self.resolve_type(prm.ty, ctenv, None)
            if prm.mode == "mutable":
                p = self.path_of(arg)
                if p is None:
                    raise LiseError(f"argument for 'mutable' parameter '{prm.name}' must be a variable or field", arg.loc)
                root = p.split(".")[0]
                if root not in st.vars or not st.vars[root][1]:
                    raise LiseError(f"'{root}' is not mutable (declare it 'var' or pass it as a 'mutable' parameter)", arg.loc)
                mut_roots.append((root, arg))
            if prt.kind == "record":
                p = self.path_of(arg)
                if p is None:
                    raise LiseError(f"record argument for '{prm.name}' must be a variable", arg.loc)
                if p.split(".")[0] in st.moved:
                    raise LiseError(f"use of moved value '{p.split('.')[0]}'", arg.loc)
                crt = self.record_type_at(st, p)
                if crt is None or crt.decl is not prt.decl:
                    raise LiseError(f"argument '{fmt_expr(arg)}' is not a {prt.name}", arg.loc)
                for gname, (kind, tv) in prt.tenv.items():
                    cv = crt.tenv[gname][1]
                    if kind == "type":
                        if not (tv.sort == cv.sort):
                            raise LiseError(f"argument '{fmt_expr(arg)}' has a different type argument '{gname}'", arg.loc)
                    else:
                        self.prove(st, cv == tv, f"record argument '{fmt_expr(arg)}' may have a different '{gname}' "
                                                 f"than '{name}' expects", arg.loc)
                for cpath, lt in self.leaves(prt, prm.name):
                    suffix = cpath[len(prm.name):]
                    cenv[cpath] = st.env[p + suffix]
                    cltypes[cpath] = lt
                    if prm.mode == "mutable":
                        mapping.append((cpath, p + suffix, lt))
                for g in self.record_invs(crt, p, st.env, st.ltypes):
                    self.prove(st, g, f"invariant of '{fmt_expr(arg)}' may not hold at call to '{name}'", arg.loc)
                if prm.mode == "mutable":
                    mut_rec.append((p, crt))
                if prm.mode == "consume":
                    self.move_out(arg, st)
            else:
                v = self.ev(arg, st, spec)
                if not (v.sort() == prt.sort):
                    raise LiseError(f"argument '{fmt_expr(arg)}' has type {v.sort()}, expected {prt.label}", arg.loc)
                for g in self.type_invs(prt, v):
                    self.prove(st, g, f"argument '{fmt_expr(arg)}' may violate parameter type '{prt.label}' of '{name}'", arg.loc)
                cenv[prm.name] = v
                cltypes[prm.name] = prt
                if prm.mode == "mutable":
                    mapping.append((prm.name, self.path_of(arg), prt))
                if prm.mode == "consume":
                    self.move_out(arg, st)
        # exclusivity: a mutable argument may not alias any other argument
        for root, marg in mut_roots:
            for other in e.args:
                if other is marg:
                    continue
                if any(isinstance(n, Name) and n.ident == root for n in walk(other)):
                    raise LiseError(f"'{root}' is passed as 'mutable' and also used in another argument (aliasing)", marg.loc)
        # preconditions
        cs = State()
        cs.env, cs.ltypes, cs.pc = dict(cenv), cltypes, st.pc
        cs.in_branch, cs.trust = st.in_branch, True
        for req in callee.requires:
            g = self.ev(req, cs, spec=True)
            self.prove(cs, g, f"precondition of '{name}' may not hold: {fmt_expr(req)}", e.loc)
        # termination: a call inside the caller's recursion cycle must strictly decrease the measure
        if self.fn.name in self.recursive and name in self.scc.get(self.fn.name, ()):
            mg = self.ev(callee.decreases, cs, spec=True)
            self.prove(cs, mg >= 0, f"termination: the measure of '{name}' may be negative at this call", e.loc)
            self.prove(cs, mg < self.entry_measure,
                       f"termination: the measure of '{name}' ({fmt_expr(callee.decreases)}) may not be smaller "
                       f"than this function's measure on entry ({fmt_expr(self.fn.decreases)})", e.loc)
        # havoc the mutable parameters the callee may modify; the frame rule keeps the rest
        penv = dict(cenv)
        mods = self.callee_mods(callee)
        for cpath, callerpath, lt in mapping:
            if mods is not None and not any(cpath == q or cpath.startswith(q + ".") for q in mods):
                continue            # callee cannot modify this leaf: value (and facts about it) survive
            f = self.fresh(callerpath, lt.sort)
            penv[cpath] = f
            st.env[callerpath] = f
            st.pc.extend(self.base_facts(lt, f))
        ret_rt = self.resolve_type(callee.ret, ctenv, None) if callee.ret else self.void_rt
        ps = State()
        ps.env = dict(penv)
        ps.ltypes = cltypes
        if ret_rt.kind in ("record", "array"):
            if not agg_ok:
                raise LiseError(f"'{name}' returns a {ret_rt.kind}: its result must initialise a typed "
                                f"declaration, e.g. var x: {ret_rt.label} := {name}(...)", e.loc)
            result = {}             # leaf path ("result", "result.f", ...) -> fresh value
            for path, lt in self.leaves(ret_rt, "result"):
                f = self.fresh("call_" + name + path[len("result"):], lt.sort)
                st.pc.extend(self.base_facts(lt, f))
                result[path] = (f, lt)
                ps.env[path] = f
                cltypes[path] = lt
        else:
            result = self.void_val if ret_rt.kind == "void" else self.fresh("call_" + name, ret_rt.sort)
            st.pc.extend(self.base_facts(ret_rt, result))
            ps.env["result"] = result
        ps.pc = st.pc
        ps.old_env = dict(cenv)
        ps.trust = True
        for ens in callee.ensures:
            st.pc.append(self.ev(ens, ps, spec=True))
        for p, crt in mut_rec:
            st.pc.extend(self.record_invs(crt, p, st.env, st.ltypes))
        if isinstance(result, dict):
            st.pc.extend(self.record_invs(ret_rt, "result", ps.env, cltypes))
            return result, ret_rt
        return result

    def callee_mods(self, callee):
        """Frame rule: the parameter-relative paths `callee` may modify through its `mutable`
        parameters (direct assignments, array element writes, and, transitively, through calls).
        None means unknown (call cycle): treat everything as modified.  Everything else is
        guaranteed unchanged by the call, so callers keep what they knew about it."""
        if callee.name in self._mods:
            return self._mods[callee.name]
        self._mods[callee.name] = None            # cycle guard: assume everything
        mp = {p.name for p in callee.params if p.mode == "mutable"}
        mods = set()
        for n in walk(callee.body):
            if isinstance(n, Assign):
                base = n.target.obj if isinstance(n.target, Index) else n.target
                path = self.path_of(base)
                if path is None:
                    self._mods[callee.name] = None
                    return None
                if path.split(".")[0] in mp:
                    mods.add(path)
            elif isinstance(n, Call) and n.name in self.fns:
                sub_fn = self.fns[n.name]
                sub = self.callee_mods(sub_fn)
                for prm, arg in zip(sub_fn.params, n.args):
                    if prm.mode != "mutable":
                        continue
                    ap = self.path_of(arg)
                    if ap is None:
                        self._mods[callee.name] = None
                        return None
                    if ap.split(".")[0] not in mp:
                        continue
                    if sub is None:
                        mods.add(ap)
                    else:
                        for q in sub:
                            if q == prm.name or q.startswith(prm.name + "."):
                                mods.add(ap + q[len(prm.name):])
        self._mods[callee.name] = mods
        return mods

    def record_type_at(self, st, path):
        parts = path.split(".")
        if parts[0] not in st.vars:
            return None
        rt = st.vars[parts[0]][0]
        for part in parts[1:]:
            if rt.kind != "record":
                return None
            for fname, frt in self.record_fields(rt):
                if fname == part:
                    rt = frt
                    break
            else:
                return None
        return rt if rt.kind == "record" else None

    # ---------------- statements
    def exec_block(self, stmts, st0):
        names0 = set(st0.vars)
        live = [st0]
        for s in stmts:
            nxt = []
            for st in live:
                nxt.extend(self.exec_stmt(s, st))
            live = nxt
            if not live:
                rest = stmts[stmts.index(s) + 1:] if s in stmts else []
                if rest:
                    self.lint(getattr(rest[0], "loc", (0, 0)), "unreachable code: no execution can get past the previous statement")
                break
        for st in live:
            for n in [n for n in st.vars if n not in names0]:
                self.remove_var(st, n)
        return live

    def check_sort(self, rt, v, node, what):
        if not (v.sort() == rt.sort):
            raise LiseError(f"type mismatch {what}: expected {rt.label}, found {v.sort()}", node.loc)

    def exec_stmt(self, s, st):
        if isinstance(s, Let):
            if s.ty is not None:
                art = self.resolve_type(s.ty, self.tenv, st)
                if art.kind in ("record", "array"):
                    return self.exec_let_aggregate(s, art, st)
            v = self.ev(s.value, st)
            self.move_out(s.value, st)
            if s.ty is not None:
                rt = self.resolve_type(s.ty, self.tenv, st)
                self.check_sort(rt, v, s.value, f"in declaration of '{s.name}'")
                for g in self.type_invs(rt, v):
                    self.prove(st, g, f"value may violate declared type '{rt.label}' of '{s.name}'", s.value.loc)
            else:
                rt = self.infer_rtype(v, s.value)
            self.declare_var(st, s.name, rt, s.mutable, value=v, loc=s.loc)
            return [st]
        if isinstance(s, Assign):
            return self.exec_assign(s, st)
        if isinstance(s, Assert):
            g = self.ev(s.expr, st, spec=True)
            self.expect_bool(g, s.expr)
            self.prove(st, g, f"assertion may not hold: {fmt_expr(s.expr)}", s.loc)
            return [st]
        if isinstance(s, ExprStmt):
            v = self.ev(s.expr, st)
            if v.sort() == self.outcome_sort:
                raise LiseError("an Outcome result must be used (bind it with 'let' and check it)", s.loc)
            return [st]
        if isinstance(s, Return):
            if s.value is None:
                if self.ret_rt.kind != "void":
                    raise LiseError("this function must return a value", s.loc)
                v = self.void_val
            elif self.ret_rt.kind in ("record", "array"):
                self.return_aggregate(s, st)
                return []
            else:
                v = self.ev(s.value, st)
                self.check_sort(self.ret_rt, v, s.value, "in return")
                self.move_out(s.value, st)
            self.do_return(st, v, s.loc)
            return []
        if isinstance(s, If):
            out = []
            cur = st
            sid = id(s)
            for i, (cond, _) in enumerate(s.branches):
                self.branch_msg.setdefault((sid, i), (cond.loc, f"unreachable code: the condition `{fmt_expr(cond)}` "
                                                               "can never be true here"))
            last = s.branches[-1][0]
            self.branch_msg.setdefault((sid, "else"), (s.else_body[0].loc if s.else_body else last.loc, (
                "unreachable code: the `else` branch can never run (the conditions above are always true here)"
                if s.else_body else f"the condition `{fmt_expr(last)}` is always true here: this `if` can never be skipped")))
            for i, (cond, body) in enumerate(s.branches):
                c = self.ev(cond, cur)
                self.expect_bool(c, cond)
                then_st = cur.fork(c)
                nxt = cur.fork(z3.Not(c))
                if self.feasible(then_st):
                    self.branch_live.add((sid, i))
                    out.extend(self.exec_block(body, then_st))
                cur = nxt
                if not self.feasible(cur):
                    cur = None
                    break
            if cur is not None:
                self.branch_live.add((sid, "else"))
                out.extend(self.exec_block(s.else_body, cur) if s.else_body is not None else [cur])
            return out
        if isinstance(s, While):
            return self.exec_while(s, st)
        raise LiseError("unsupported statement", getattr(s, "loc", (0, 0)))

    def exec_let_aggregate(self, s, rt, st):
        """Local record/array declaration.  Arrays: `fill(x)`.  Records: `T(f1, f2, ...)`
        with one argument per field in declaration order (array fields take `fill(x)`)."""
        v = s.value
        if isinstance(v, Call) and v.name in self.fns:
            self.agg_call_ok = True
            res = self.ev(v, st)
            self.agg_call_ok = False
            if not (isinstance(res, tuple) and isinstance(res[0], dict)):
                raise LiseError(f"'{v.name}' does not return a record/array", v.loc)
            leaves, crt = res
            self.agg_compatible(st, crt, rt, f"result of '{v.name}'", v.loc)
            if s.name in RESERVED_VARS:
                raise LiseError(f"'{s.name}' is a reserved name", s.loc)
            if s.name in st.vars or s.name in st.env or s.name in self.enums:
                raise LiseError(f"'{s.name}' is already declared (shadowing is not allowed)", s.loc)
            st.vars[s.name] = (rt, s.mutable)
            for path, (f, lt) in leaves.items():
                st.env[s.name + path[len("result"):]] = f
                st.ltypes[s.name + path[len("result"):]] = lt
            return [st]
        if rt.kind == "array":
            if not (isinstance(v, Call) and v.name == "fill"):
                raise LiseError("an array local must be initialised with fill(value)", s.value.loc)
            x = self.ev(v.args[0], st) if len(v.args) == 1 and v.targs is None else None
            if x is None:
                raise LiseError("fill takes exactly one argument: fill(value)", v.loc)
            self.check_sort(rt.elem, x, v.args[0], f"in declaration of '{s.name}'")
            self.move_out(v.args[0], st)
            self.declare_var(st, s.name, rt, s.mutable, value=z3.K(z3.IntSort(), x), loc=s.loc)
            return [st]
        if not (isinstance(v, Call) and v.name == rt.name and v.targs is None):
            raise LiseError(f"a record local must be initialised with {rt.name}(...)", s.value.loc)
        fields = self.record_fields(rt)
        if len(v.args) != len(fields):
            raise LiseError(f"{rt.name} has {len(fields)} field(s), got {len(v.args)} argument(s)", v.loc)
        if s.name in RESERVED_VARS:
            raise LiseError(f"'{s.name}' is a reserved name", s.loc)
        if s.name in st.vars or s.name in st.env or s.name in self.enums:
            raise LiseError(f"'{s.name}' is already declared (shadowing is not allowed)", s.loc)
        vals = {}
        for (fname, frt), arg in zip(fields, v.args):
            if frt.kind == "record":
                raise LiseError("records with record-typed fields cannot be constructed yet", arg.loc)
            if frt.kind == "array":
                if not (isinstance(arg, Call) and arg.name == "fill"):
                    raise LiseError(f"array field '{fname}' must be initialised with fill(value)", arg.loc)
            x = self.ev(arg, st)
            self.move_out(arg, st)
            if frt.kind == "array":
                self.check_sort(frt.elem, self.ev(arg.args[0], st), arg.args[0], f"in field '{fname}'")
            else:
                self.check_sort(frt, x, arg, f"in field '{fname}'")
                for g in self.type_invs(frt, x):
                    self.prove(st, g, f"value for field '{fname}' may violate its type '{frt.label}'", arg.loc)
            vals[s.name + "." + fname] = (x, frt)
        st.vars[s.name] = (rt, s.mutable)
        for path, (x, frt) in vals.items():
            st.env[path] = x
            st.ltypes[path] = frt
        for g in self.record_invs(rt, s.name, st.env, st.ltypes):
            self.prove(st, g, f"invariant of '{rt.label}' may not hold for '{s.name}' at construction", s.loc)
        return [st]

    def exec_assign(self, s, st):
        tgt = s.target
        v = self.ev(s.value, st)
        self.move_out(s.value, st)
        base = tgt.obj if isinstance(tgt, Index) else tgt
        p = self.path_of(base)
        if p is None or p not in st.env:
            raise LiseError(f"cannot assign to '{fmt_expr(tgt)}'", tgt.loc)
        root = p.split(".")[0]
        if root in st.moved and not (p == root and isinstance(tgt, Name)):
            raise LiseError(f"use of moved value '{root}'", tgt.loc)
        if root not in st.vars:
            raise LiseError(f"cannot assign to '{root}' (it is a generic parameter)", tgt.loc)
        if not st.vars[root][1]:
            raise LiseError(f"cannot assign to '{root}': it is not mutable "
                            "(use 'var', or a 'mutable' parameter)", tgt.loc)
        lt = st.ltypes[p]
        if isinstance(tgt, Index):
            if lt.kind != "array" or len(tgt.indices) != 1:
                raise LiseError(f"'{fmt_expr(base)}' is not an array", tgt.loc)
            i = self.ev(tgt.indices[0], st)
            self.expect_int(i, tgt.indices[0])
            self.prove(st, z3.And(i >= 0, i < lt.length),
                       f"array index '{fmt_expr(tgt)}' may be out of bounds (need 0 <= index < length)", tgt.loc)
            self.check_sort(lt.elem, v, s.value, f"in assignment to '{fmt_expr(tgt)}'")
            st.env[p] = z3.Store(st.env[p], i, v)
            return [st]
        if lt.kind == "array":
            raise LiseError("whole-array assignment is not supported; assign elements", tgt.loc)
        self.check_sort(lt, v, s.value, f"in assignment to '{fmt_expr(tgt)}'")
        for g in self.type_invs(lt, v):
            self.prove(st, g, f"value assigned to '{fmt_expr(tgt)}' may violate its type '{lt.label}'", s.value.loc)
        st.env[p] = v
        if p == root and isinstance(tgt, Name):
            st.moved.discard(root)  # re-initialisation of a moved variable
        return [st]

    def agg_compatible(self, st, a, b, what, loc):
        """Prove that record/array type `a` is the same type as `b` (type args / lengths equal)."""
        if a.kind != b.kind:
            raise LiseError(f"{what} has type {a.label}, expected {b.label}", loc)
        if a.kind == "record":
            if a.decl is not b.decl:
                raise LiseError(f"{what} is a {a.name}, expected {b.name}", loc)
            for gname, (kind, bv) in b.tenv.items():
                av = a.tenv[gname][1]
                if kind == "type":
                    if not (av.sort == bv.sort):
                        raise LiseError(f"{what} has a different type argument '{gname}'", loc)
                else:
                    self.prove(st, av == bv, f"{what} may have a different '{gname}' than expected", loc)
        else:
            if not (a.elem.sort == b.elem.sort):
                raise LiseError(f"{what} has a different element type", loc)
            self.prove(st, a.length == b.length, f"{what} may have a different length than expected", loc)

    def return_aggregate(self, s, st):
        v = s.value
        if not isinstance(v, Name) or v.ident not in st.vars:
            raise LiseError("a function returning a record/array must `return` a local variable of that type", s.loc)
        name = v.ident
        if name in self.param_names and name not in self.consume_params:
            raise LiseError(f"cannot return '{name}': it is a borrowed ('in'/'mutable') parameter; "
                            "declare it 'consume' to hand its ownership back", v.loc)
        if name in st.moved:
            raise LiseError(f"use of moved value '{name}'", v.loc)
        lrt = st.vars[name][0]
        self.agg_compatible(st, lrt, self.ret_rt, f"returned value '{name}'", v.loc)
        for g in self.record_invs(lrt, name, st.env, st.ltypes):
            self.prove(st, g, f"invariant of '{lrt.label}' may not hold for '{name}' at return", s.loc)
        self.move_out(v, st)
        self.do_return(st, None, s.loc, agg=name)

    def do_return(self, st, v, loc, agg=None):
        rt = self.ret_rt
        if agg is None:
            for g in self.type_invs(rt, v):
                self.prove(st, g, f"returned value may violate return type '{rt.label}'", loc)
        for pname in self.param_names:
            prt = st.vars[pname][0]
            if pname in self.mut_params:
                for g in self.record_invs(prt, pname, st.env, st.ltypes):
                    self.prove(st, g, f"invariant of '{prt.label}' may not hold for '{pname}' at return", loc)
        es = State()
        es.env = {p: (st.old_env[p] if p.split(".")[0] in self.consume_params else st.env[p])
                  for p in self.param_paths}
        es.env.update(self.vals(self.tenv))
        es.ltypes, es.pc, es.old_env = st.ltypes, list(st.pc), st.old_env
        if agg is None:
            es.env["result"] = v
        else:                       # `result.field` / `result[i]` in postconditions = the returned local's leaves
            es.ltypes = dict(st.ltypes)
            for path, lt in self.leaves(st.vars[agg][0], agg):
                suffix = path[len(agg):]
                es.env["result" + suffix] = st.env[path]
                es.ltypes["result" + suffix] = lt
        for clause in self.fn.ensures:
            g = self.ev(clause, es, spec=True)
            self.expect_bool(g, clause)
            self.prove(es, g, f"postcondition may not hold: {fmt_expr(clause)} (at return, line {loc[0]})", clause.loc)

    def modified_paths(self, body, st):
        paths = set()
        for n in walk(body):
            if isinstance(n, Assign):
                base = n.target.obj if isinstance(n.target, Index) else n.target
                p = self.path_of(base)
                if p:
                    paths.add(p)
            elif isinstance(n, Call) and n.name in self.fns:
                for prm, arg in zip(self.fns[n.name].params, n.args):
                    if prm.mode == "mutable":
                        p = self.path_of(arg)
                        if p:
                            paths.add(p)
        out = set()
        for p in paths:
            out.update(q for q in st.env if q == p or q.startswith(p + "."))
        return out

    def exec_while(self, s, st):
        if s.decreases is None:
            raise LiseError("this loop needs a 'decreases' clause (termination must be proven)", s.loc)
        for inv in s.invariants:
            g = self.ev(inv, st, spec=True)
            self.expect_bool(g, inv)
            self.prove(st, g, f"loop invariant may not hold on entry: {fmt_expr(inv)}", inv.loc)
        for p in sorted(self.modified_paths(s.body, st)):
            lt = st.ltypes[p]
            f = self.fresh(p, lt.sort)
            st.env[p] = f
            st.pc.extend(self.base_facts(lt, f))
        saved = st.trust
        st.trust = True
        for inv in s.invariants:
            st.pc.append(self.ev(inv, st, spec=True))
        st.trust = saved
        c = self.ev(s.cond, st)
        self.expect_bool(c, s.cond)
        out = []
        body_st = st.fork(c)
        exit_st = st.fork(z3.Not(c))
        if self.feasible(body_st):
            m0 = self.ev(s.decreases, body_st, spec=True)
            self.expect_int(m0, s.decreases)
            self.prove(body_st, m0 >= 0, f"loop 'decreases' measure may be negative: {fmt_expr(s.decreases)}", s.decreases.loc)
            for e in self.exec_block(s.body, body_st):
                bad = sorted(n for n in (e.moved - st.moved) if n in st.vars)
                if bad:
                    raise LiseError(f"'{bad[0]}' is moved inside a loop body, so it would be used "
                                    "again (moved) in the next iteration", s.loc)
                for inv in s.invariants:
                    g = self.ev(inv, e, spec=True)
                    self.prove(e, g, f"loop invariant may not be preserved by the loop body: {fmt_expr(inv)}", inv.loc)
                m1 = self.ev(s.decreases, e, spec=True)
                self.prove(e, m1 < m0, f"loop 'decreases' measure may not strictly decrease: {fmt_expr(s.decreases)}", s.decreases.loc)
        if self.feasible(exit_st):
            out.append(exit_st)
        return out

    # ---------------- declarations & driver
    def register(self):
        seen = set()
        for d in self.prog.decls:
            if d.name in seen or d.name in BUILTIN_TYPES or d.name in BUILTIN_FNS or d.name in RESERVED_VARS:
                raise LiseError(f"duplicate or reserved declaration name '{d.name}'", d.loc)
            seen.add(d.name)
            if isinstance(d, TypeDecl):
                self.types[d.name] = d
            elif isinstance(d, RecordDecl):
                self.records[d.name] = d
            elif isinstance(d, EnumDecl):
                if len(set(d.variants)) != len(d.variants):
                    raise LiseError(f"enum '{d.name}' has duplicate variants", d.loc)
                # Z3 sort names are process-global: make them unique so several files
                # declaring the same enum can be checked in one run.
                _ENUM_SERIAL[d.name] = _ENUM_SERIAL.get(d.name, 0) + 1
                zname = d.name if _ENUM_SERIAL[d.name] == 1 else f"{d.name}#{_ENUM_SERIAL[d.name]}"
                sort, consts = z3.EnumSort(zname, d.variants)
                self.enums[d.name] = (sort, dict(zip(d.variants, consts)))
            else:
                self.fns[d.name] = d
        for d in self.prog.decls:
            if isinstance(d, (TypeDecl, RecordDecl)) and d.name in self.fns:
                raise LiseError(f"name '{d.name}' used for both a type and a function", d.loc)
        # call graph / recursion
        calls = {n: {c.name for c in walk(f.body) if isinstance(c, Call) and c.name in self.fns}
                 for n, f in self.fns.items()}
        self.calls = calls
        self.recursive = set()
        for n in calls:
            stack, seen2 = list(calls[n]), set()
            while stack:
                m = stack.pop()
                if m == n:
                    self.recursive.add(n)
                    break
                if m in seen2:
                    continue
                seen2.add(m)
                stack.extend(calls.get(m, ()))
        # strongly connected component of every recursive function (mutual recursion)
        self.scc = {}
        for n in self.recursive:
            self.scc[n] = {m for m in self.recursive if self.reaches(n, m) and self.reaches(m, n)} | {n}
        for n in sorted(self.recursive):
            f = self.fns[n]
            if f.decreases is None:
                raise LiseError(f"'{n}' is recursive: add a termination measure, e.g. "
                                f"`decreases <integer expression> max <bound>` (the bound also limits the stack depth)",
                                f.loc)

    def reaches(self, a, b):
        """True if function `a` can call function `b` (directly or transitively)."""
        seen, stack = set(), list(self.calls.get(a, ()))
        while stack:
            m = stack.pop()
            if m == b:
                return True
            if m not in seen:
                seen.add(m)
                stack.extend(self.calls.get(m, ()))
        return False

    def tokhash(self, lo, hi):
        h = hashlib.sha256()
        for t in self.toks[lo:hi]:
            h.update(f"{t.kind}\0{t.text}\0".encode())
        return h.digest()

    def decls_hash(self):
        h = hashlib.sha256()
        for d in self.prog.decls:
            if not isinstance(d, FnDecl):
                h.update(self.tokhash(d.tok_lo, d.tok_hi))
        return h.digest()

    def fn_key(self, fn, dh):
        h = hashlib.sha256()
        h.update(f"lise-{VERSION}|z3-{z3.get_version_string()}|cvc5-{lise_xcheck.version()}|".encode())
        h.update(self.tokhash(fn.tok_lo, fn.tok_hi))
        h.update(dh)
        for c in sorted(self.calls[fn.name]):  # callees: CONTRACT only (signature), not body
            callee = self.fns[c]
            h.update(c.encode())
            h.update(self.tokhash(callee.tok_lo, callee.sig_hi))
            mods = self.callee_mods(callee)   # the frame rule makes callers depend on what callees modify
            h.update(b"*" if mods is None else "|".join(sorted(mods)).encode())
        return h.hexdigest()

    def check_wellformed(self, rt, st, loc):
        tmp = State()
        tmp.env = {k: v for k, v in st.env.items()}
        tmp.ltypes = st.ltypes
        tmp.pc = list(st.pc)
        v = self.fresh("value", rt.sort)
        tmp.env["value"] = v
        for pred, bind in rt.preds:
            t2 = State()
            t2.env = dict(bind)
            t2.env["value"] = v
            t2.pc = list(tmp.pc)
            g = self.ev(pred, t2, spec=True)
            self.expect_bool(g, pred)
            tmp.pc.append(g)

    def check_decl(self, d):
        self.entry_consts = []
        st = State()
        if isinstance(d, TypeDecl):
            tenv = self.setup_generics(d.gparams, st)
            self.tenv = tenv
            rt = self.resolve_type(d.base, tenv, st)
            if rt.kind in ("record", "array"):
                raise LiseError("type aliases of records/arrays are not supported yet", d.loc)
            self.check_wellformed(rt, st, d.loc)
        elif isinstance(d, RecordDecl):
            tenv = self.setup_generics(d.gparams, st)
            self.tenv = tenv
            names = set()
            for f in d.fields:
                if f.name in names or f.name in RESERVED_VARS:
                    raise LiseError(f"duplicate or reserved field name '{f.name}'", f.loc)
                names.add(f.name)
                rt = self.resolve_type(f.ty, tenv, st)
                if rt.kind == "record" and rt.decl is d:
                    raise LiseError("recursive records are not supported", f.loc)
                if rt.kind != "record":
                    self.check_wellformed(rt, st, f.loc)
            tmp = State()
            tmp.env = {}
            vs = self.record_fields_tmp(d, tenv, st, tmp)
            if d.pred is not None:
                g = self.ev(d.pred, tmp, spec=True)
                self.expect_bool(g, d.pred)

    def record_fields_tmp(self, d, tenv, st, tmp):
        tmp.env = dict(self.vals(tenv))
        tmp.pc = list(st.pc)
        tmp.ltypes = {}
        for f in d.fields:
            rt = self.resolve_type(f.ty, tenv, None)
            if rt.kind == "record":
                continue
            v = self.fresh(f.name, rt.sort)
            tmp.env[f.name] = v
            tmp.ltypes[f.name] = rt
            tmp.pc.extend(self.base_facts(rt, v))
        return None

    def verify_fn(self, fn):
        self.fn = fn
        self.branch_msg, self.branch_live = {}, set()
        self.unused_lints(fn)
        self.entry_consts = []
        st = State()
        self.tenv = self.setup_generics(fn.gparams, st)
        self.param_paths, self.param_names = [], []
        self.mut_params = {p.name for p in fn.params if p.mode == "mutable"}
        self.consume_params = {p.name for p in fn.params if p.mode == "consume"}
        for prm in fn.params:
            rt = self.resolve_type(prm.ty, self.tenv, st)
            # 'consume' parameters are owned by the callee, so they are assignable locals.
            self.declare_var(st, prm.name, rt, prm.mode != "in", entry=True, loc=prm.loc)
            if prm.mode != "consume":
                st.borrowed.add(prm.name)
            self.param_names.append(prm.name)
            self.param_paths.extend(p for p, _ in self.leaves(rt, prm.name))
            st.pc.extend(self.record_invs(rt, prm.name, st.env, st.ltypes))
        self.ret_rt = self.resolve_type(fn.ret, self.tenv, st) if fn.ret else self.void_rt
        st.old_env = None
        for r in fn.requires:
            g = self.ev(r, st, spec=True)
            self.expect_bool(g, r)
            st.pc.append(g)
        st.old_env = dict(st.env)
        if self.lints and not self.feasible(st):
            self.lint(fn.loc, f"the preconditions of '{fn.name}' (with its parameter types) are contradictory: no call "
                              "can satisfy them, so every proof inside it would be vacuous")
        self.entry_measure = None
        if fn.decreases is not None:
            m = self.ev(fn.decreases, st, spec=True)
            if not (m.sort() == z3.IntSort()):
                raise LiseError("the decreases measure must be an Integer", fn.decreases.loc)
            self.prove(st, m >= 0, f"the measure ({fmt_expr(fn.decreases)}) may be negative on entry", fn.decreases.loc)
            self.prove(st, m <= fn.dec_max,
                       f"the measure ({fmt_expr(fn.decreases)}) may exceed its declared maximum {fn.dec_max}",
                       fn.decreases.loc)
            self.entry_measure = m
        for e in self.exec_block(fn.body, st):
            if self.ret_rt.kind == "void":
                self.do_return(e, self.void_val, fn.end_loc)
            else:
                self.prove(e, z3.BoolVal(False), f"function '{fn.name}' may reach its end without returning a value", fn.end_loc)
        for key, (loc, msg) in self.branch_msg.items():       # a branch no path ever reached
            if key not in self.branch_live:
                self.lint(loc, msg)

    def run(self):
        try:
            self.register()
        except LiseError as ex:
            self.diag(ex.loc, ex.msg)
            return
        dh = self.decls_hash()
        for d in self.prog.decls:
            if isinstance(d, (TypeDecl, RecordDecl)):
                before = len(self.rep.diags)
                try:
                    self.check_decl(d)
                except LiseError as ex:
                    self.diag(ex.loc if ex.loc != (0, 0) else d.loc, ex.msg)
        for d in self.prog.decls:
            if not isinstance(d, FnDecl):
                continue
            self.rep.functions += 1
            key = self.fn_key(d, dh)
            if self.cache is not None and self.cache.has(key):
                self.rep.cached += 1
                self.rep.verified += 1
                continue
            before = len(self.rep.diags)
            try:
                self.verify_fn(d)
            except LiseError as ex:
                self.diag(ex.loc if ex.loc != (0, 0) else d.loc, f"in '{d.name}': {ex.msg}")
            if len(self.rep.diags) == before:
                self.rep.verified += 1
                if self.cache is not None:
                    self.cache.add(key)


def check_source(src, filename="<input>", timeout_ms=10000, cache=None, independent="require", lints=True,
                 cert_dir=None):
    rep = Report(filename)
    try:
        toks = lex(src)
        prog = Parser(toks).parse_program()
    except LiseError as ex:
        rep.diags.append(Diag(filename, ex.loc, ex.msg))
        return rep
    v = Verifier(prog, toks, filename, timeout_ms, cache, rep)
    v.lints = lints
    v.cert_dir = cert_dir
    v.independent = independent     # "require" (always, for real builds) or "report" (fuzzing harness only)
    v.run()
    return rep
