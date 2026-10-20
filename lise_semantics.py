"""Executable reference semantics of Lise (see SEMANTICS.md).

A deliberately simple, slow, definitional interpreter that runs the REAL parsed AST.  It shares no
code with the verifier, the optimiser-facing backend or the fuzzer's own evaluators, and it is the
normative description of what a Lise program means:

  * Integer is a mathematical integer that must stay inside [-2^63, 2^63-1] in program code
    (anything else is STUCK); contracts, asserts and invariants use unbounded integers.
  * `/` and `%` are Euclidean; division by zero and MIN / -1 are STUCK.
  * Array indices must be in bounds, refinement types must hold whenever a value is bound,
    assigned, passed, returned or constructed; requires / ensures / invariants / asserts /
    decreases measures must hold at run time.  Violating any of them is STUCK, never "undefined".
  * Memory is initialised by construction; records/arrays are never copied (they are moved or
    borrowed), `mutable` parameters alias the caller's storage.

  * Ownership is dynamic here: a value of a non-Copy type (record, array, generic parameter type) is
    MOVED when used by value in an owning position (declaration, assignment, return, `consume`
    argument, constructor / fill argument); reading a moved variable, moving a borrowed (`in` /
    `mutable`) parameter or a field/element, assigning to an immutable variable, and passing a
    `mutable` argument whose storage overlaps another argument are all STUCK (kind "ownership").

A program the verifier accepts must never get STUCK.  Anything the interpreter prints or returns
must equal what the compiled program does.  Both claims are tested (test_lise.py, fuzz_lise.py).
"""
import copy

from lise_ast import *

I64_MIN, I64_MAX = -(2 ** 63), 2 ** 63 - 1


class Stuck(Exception):
    """The program reached a state with no defined meaning (what the verifier promises never happens)."""

    def __init__(self, kind, msg, loc=(0, 0)):
        super().__init__(f"{kind}: {msg}")
        self.kind, self.msg, self.loc = kind, msg, loc


class _Return(Exception):
    def __init__(self, value):
        self.value = value


# ------------------------------------------------------------------ runtime values
class EnumVal:
    def __init__(self, enum, name):
        self.enum, self.name = enum, name

    def __eq__(self, o):
        return isinstance(o, EnumVal) and (self.enum, self.name) == (o.enum, o.name)

    def __hash__(self):
        return hash((self.enum, self.name))

    def __repr__(self):
        return f"{self.enum}.{self.name}"


class Outcome:
    def __init__(self, ok, payload=None):
        self.ok, self.payload = ok, payload


class Rec:
    def __init__(self, desc, fields, fdescs):
        self.desc, self.fields, self.fdescs = desc, fields, fdescs


class Arr:
    def __init__(self, desc, items):
        self.desc, self.items = desc, items


class Desc:
    """A resolved type: kind int|bool|enum|outcome|void|array|record, with its refinement predicates."""

    def __init__(self, kind, **kw):
        self.kind, self.preds = kind, []
        self.elem = self.length = self.decl = self.renv = self.name = None
        self.affine = kind in ("array", "record")     # non-Copy: moved when used by value
        self.__dict__.update(kw)

    def with_pred(self, pred, genv):
        d = copy.copy(self)
        d.preds = self.preds + [(pred, genv)]
        return d


# ------------------------------------------------------------------ storage slots (for lvalues)
class Cell:
    def __init__(self, value, desc, mutable=True, borrowed=False):
        self.value, self.desc = value, desc
        self.mutable, self.borrowed, self.moved = mutable, borrowed, False

    def get(self):
        return self.value

    def put(self, v):
        self.value = v


class FieldSlot:
    def __init__(self, rec, name):
        self.rec, self.name, self.desc = rec, name, rec.fdescs[name]
        self.mutable, self.borrowed, self.moved = True, False, False

    def get(self):
        return self.rec.fields[self.name]

    def put(self, v):
        self.rec.fields[self.name] = v


class IndexSlot:
    def __init__(self, arr, i):
        self.arr, self.i, self.desc = arr, i, arr.desc.elem
        self.mutable, self.borrowed, self.moved = True, False, False

    def get(self):
        return self.arr.items[self.i]

    def put(self, v):
        self.arr.items[self.i] = v


class RefSlot:
    """A `mutable` scalar parameter: writes go to the caller's storage and satisfy BOTH types."""

    def __init__(self, inner, desc):
        self.inner, self.desc = inner, desc
        self.mutable, self.borrowed, self.moved = True, True, False

    def get(self):
        return self.inner.get()

    def put(self, v):
        self.inner.put(v)


class Frame:
    def __init__(self, fn=None, genv=None, parent=None):
        self.env, self.genv, self.old, self.fn, self.parent = {}, genv or {}, None, fn, parent
        self.measure0 = None


# ------------------------------------------------------------------ the machine
class Machine:
    def __init__(self, prog, step_limit=2_000_000, depth_limit=20_000, ownership=True):
        self.own = ownership
        self.types = {d.name: d for d in prog.decls if isinstance(d, TypeDecl)}
        self.records = {d.name: d for d in prog.decls if isinstance(d, RecordDecl)}
        self.enums = {d.name: d for d in prog.decls if isinstance(d, EnumDecl)}
        self.fns = {d.name: d for d in prog.decls if isinstance(d, FnDecl)}
        self.step_limit, self.depth_limit = step_limit, depth_limit
        self.steps = self.depth = 0
        self.out = []
        self.calls = {n: {c.name for c in walk(f.body) if isinstance(c, Call) and c.name in self.fns}
                      for n, f in self.fns.items()}

    # ---------------------------------------------------------------- entry points
    def run_main(self):
        """Run `fn main() -> Integer`; returns (exit status, output text)."""
        v = self.call_fn(self.fns["main"], [], [], None)
        return ((v & 0xFF) if isinstance(v, int) else 0), "".join(self.out)

    def run_function(self, name, args):
        """Call a function with scalar arguments; returns (value, output text)."""
        v = self.call_fn(self.fns[name], [], list(args), None, raw_args=True)
        return v, "".join(self.out)

    # ---------------------------------------------------------------- types
    @staticmethod
    def to_type(e):
        if isinstance(e, Name):
            return TypeRef(e.ident, [], None, e.loc)
        if isinstance(e, Index) and isinstance(e.obj, Name):
            return TypeRef(e.obj.ident, list(e.indices), None, e.loc)
        raise Stuck("type", f"expected a type, found {fmt_expr(e)}", getattr(e, "loc", (0, 0)))

    def bind(self, gparams, args, genv, loc):
        if len(gparams) != len(args):
            raise Stuck("type", "wrong number of generic arguments", loc)
        new = {}
        for gp, a in zip(gparams, args):
            if gp.constraint is None:
                new[gp.name] = ("type", self.resolve(self.to_type(a), genv))
            else:
                v = self.ev(a, Frame(genv=genv), True)
                self.check(self.resolve(gp.constraint, {}), v, f"generic argument {gp.name}", loc)
                new[gp.name] = ("val", v)
        return new

    def resolve(self, ref, genv, depth=0):
        if depth > 40:
            raise Stuck("type", "type nested too deeply", ref.loc)
        n = ref.name
        if n in genv:
            kind, v = genv[n]
            if kind != "type":
                raise Stuck("type", f"{n} is not a type", ref.loc)
            d = v
        elif n == "Integer":
            d = Desc("int")
        elif n == "Bool":
            d = Desc("bool")
        elif n == "Void":
            d = Desc("void")
        elif n == "Outcome":
            d = Desc("outcome")
        elif n == "Array":
            if len(ref.args) != 2:
                raise Stuck("type", "Array takes 2 arguments", ref.loc)
            d = Desc("array", elem=self.resolve(self.to_type(ref.args[0]), genv, depth + 1),
                     length=self.ev(ref.args[1], Frame(genv=genv), True))
        elif n in self.enums:
            d = Desc("enum", name=n)
        elif n in self.types:
            td = self.types[n]
            d = self.resolve(td.base, self.bind(td.gparams, ref.args, genv, ref.loc), depth + 1)
        elif n in self.records:
            rd = self.records[n]
            d = Desc("record", decl=rd, renv=self.bind(rd.gparams, ref.args, genv, ref.loc))
        else:
            raise Stuck("type", f"unknown type {n}", ref.loc)
        if ref.pred is not None:
            d = d.with_pred(ref.pred, genv)
        return d

    def check(self, d, v, what, loc=(0, 0), record_invariants=True):
        """Does value `v` inhabit type `d`?  Raises Stuck('refinement') if not."""
        k = d.kind
        ok = ((k == "int" and type(v) is int and I64_MIN <= v <= I64_MAX) or (k == "bool" and type(v) is bool) or
              (k == "enum" and isinstance(v, EnumVal) and v.enum == d.name) or
              (k == "outcome" and isinstance(v, Outcome)) or (k == "void" and v is None) or
              (k == "array" and isinstance(v, Arr) and len(v.items) == d.length) or
              (k == "record" and isinstance(v, Rec) and v.desc.decl is d.decl))
        if not ok:
            raise Stuck("refinement", f"{what}: value {self.show(v)} does not have the expected type", loc)
        for pred, genv in d.preds:
            fr = Frame(genv=genv)
            fr.env["value"] = Cell(v, d)
            if self.ev(pred, fr, True) is not True:
                raise Stuck("refinement", f"{what}: value {self.show(v)} violates `{fmt_expr(pred)}`", loc)
        if k == "array":
            for i, x in enumerate(v.items):
                self.check(d.elem, x, f"{what}[{i}]", loc, record_invariants)
        if k == "record":
            for fname, fd in v.fdescs.items():
                self.check(fd, v.fields[fname], f"{what}.{fname}", loc, record_invariants)
            if record_invariants and d.decl.pred is not None:
                fr = Frame(genv=d.renv)
                for fname, x in v.fields.items():
                    if not isinstance(x, (Rec, Arr)):
                        fr.env[fname] = Cell(x, v.fdescs[fname])
                if self.ev(d.decl.pred, fr, True) is not True:
                    raise Stuck("invariant", f"{what}: record invariant of {d.decl.name} violated", loc)

    @staticmethod
    def show(v):
        if isinstance(v, Rec):
            return f"{v.desc.decl.name}({', '.join(f'{k}={Machine.show(x)}' for k, x in v.fields.items())})"
        if isinstance(v, Arr):
            return "[" + ", ".join(Machine.show(x) for x in v.items) + "]"
        return str(v)

    def desc_of_value(self, v):
        if isinstance(v, bool):
            return Desc("bool")
        if isinstance(v, int):
            return Desc("int")
        if isinstance(v, EnumVal):
            return Desc("enum", name=v.enum)
        if isinstance(v, Outcome):
            return Desc("outcome")
        if isinstance(v, (Rec, Arr)):
            return v.desc
        return Desc("void")

    # ---------------------------------------------------------------- expressions
    def tick(self):
        self.steps += 1
        if self.steps > self.step_limit:
            raise Stuck("nontermination", "step limit exceeded")

    def lookup(self, fr, name, loc):
        if name in fr.env:
            return fr.env[name].get()
        if name in fr.genv and fr.genv[name][0] == "val":
            return fr.genv[name][1]
        raise Stuck("type", f"unknown name {name}", loc)

    def in_scope(self, fr, name):
        return name in fr.env or (name in fr.genv and fr.genv[name][0] == "val")

    @staticmethod
    def edivmod(a, b):
        r = a % abs(b)
        return (a - r) // b, r

    def arith(self, op, a, b, spec, loc):
        if op in ("/", "%"):
            if b == 0:
                raise Stuck("div_zero", "division by zero", loc)
            q, r = self.edivmod(a, b)
            res = q if op == "/" else r
            if not spec and a == I64_MIN and b == -1:
                raise Stuck("overflow", "INT64_MIN / -1", loc)
        else:
            res = a + b if op == "+" else a - b if op == "-" else a * b
        if not spec and not I64_MIN <= res <= I64_MAX:
            raise Stuck("overflow", f"{a} {op} {b} = {res} does not fit in 64 bits", loc)
        return res

    def ev(self, e, fr, spec=False):
        self.tick()
        if isinstance(e, Num):
            return e.value
        if isinstance(e, BoolLit):
            return e.value
        if isinstance(e, Str):
            raise Stuck("type", "string literal outside print", e.loc)
        if isinstance(e, Name):
            if self.own and not spec and e.ident in fr.env and fr.env[e.ident].moved:
                raise Stuck("ownership", f"use of moved value '{e.ident}'", e.loc)
            return self.lookup(fr, e.ident, e.loc)
        if isinstance(e, Field):
            if isinstance(e.obj, Name) and e.obj.ident in self.enums and not self.in_scope(fr, e.obj.ident):
                if e.name not in self.enums[e.obj.ident].variants:
                    raise Stuck("type", f"enum {e.obj.ident} has no variant {e.name}", e.loc)
                return EnumVal(e.obj.ident, e.name)
            o = self.ev(e.obj, fr, spec)
            if not isinstance(o, Rec) or e.name not in o.fields:
                raise Stuck("type", f"no field {e.name}", e.loc)
            return o.fields[e.name]
        if isinstance(e, Index):
            a = self.ev(e.obj, fr, spec)
            i = self.ev(e.indices[0], fr, spec)
            if not isinstance(a, Arr) or not 0 <= i < len(a.items):
                raise Stuck("index", f"index {i} out of bounds for length {len(getattr(a, 'items', []))}", e.loc)
            return a.items[i]
        if isinstance(e, Old):
            if fr.old is None:
                raise Stuck("type", "old() outside a postcondition", e.loc)
            return self.ev(e.expr, fr.old, True)
        if isinstance(e, Unary):
            v = self.ev(e.operand, fr, spec)
            if e.op == "not":
                return not v
            return self.arith("-", 0, v, spec, e.loc)
        if isinstance(e, Binary):
            return self.binary(e, fr, spec)
        if isinstance(e, Call):
            return self.call(e, fr, spec)
        raise Stuck("type", f"cannot evaluate {fmt_expr(e)}", getattr(e, "loc", (0, 0)))

    def binary(self, e, fr, spec):
        op = e.op
        if op == "and":
            return self.ev(e.left, fr, spec) and self.ev(e.right, fr, spec)
        if op == "or":
            return self.ev(e.left, fr, spec) or self.ev(e.right, fr, spec)
        if op == "implies":
            return (not self.ev(e.left, fr, spec)) or self.ev(e.right, fr, spec)
        a, b = self.ev(e.left, fr, spec), self.ev(e.right, fr, spec)
        if op in ("+", "-", "*", "/", "%"):
            return self.arith(op, a, b, spec, e.loc)
        return {"<": lambda: a < b, "<=": lambda: a <= b, ">": lambda: a > b, ">=": lambda: a >= b,
                "==": lambda: a == b, "!=": lambda: a != b}[op]()

    # ---------------------------------------------------------------- ownership (dynamic)
    def ev_owned(self, e, fr):
        """Evaluate `e` in an owning position: a non-Copy variable is moved out."""
        v = self.ev(e, fr)
        if not self.own:
            return v
        if isinstance(e, Name) and e.ident in fr.env:
            cell = fr.env[e.ident]
            if cell.desc is not None and cell.desc.affine:
                if cell.borrowed:
                    raise Stuck("ownership", f"cannot move '{e.ident}': it is a borrowed parameter", e.loc)
                cell.moved = True
        elif isinstance(e, (Field, Index)):
            slot = self.try_slot(e, fr)
            if slot is not None and slot.desc is not None and slot.desc.affine:
                raise Stuck("ownership", f"cannot move {fmt_expr(e)} out of a field or element", e.loc)
        return v

    @staticmethod
    def opaque(d):
        c = copy.copy(d)
        c.affine = True
        return c

    def try_slot(self, e, fr):
        try:
            return self.lvalue(e, fr)
        except Stuck:
            return None

    def root_name(self, e):
        while isinstance(e, (Field, Index)):
            e = e.obj
        return e.ident if isinstance(e, Name) else None

    @staticmethod
    def base_cell(c):
        while isinstance(c, RefSlot):
            c = c.inner
        return c

    def storage_of(self, e, fr):
        """Storage locations an expression denotes/reads, as tuples; overlap is decided on these."""
        out = set()
        if isinstance(e, Name):
            c = fr.env.get(e.ident)
            if c is not None:
                b = self.base_cell(c)
                out.add(("c", id(b)))
                v = c.get()
                if isinstance(v, (Rec, Arr)):
                    out.add(("o", id(v)))
        elif isinstance(e, Field):
            o = self.try_value(e.obj, fr)
            out |= self.storage_of(e.obj, fr) if not isinstance(o, Rec) else {("f", id(o), e.name)}
        elif isinstance(e, Index):
            a = self.try_value(e.obj, fr)
            i = self.try_value(e.indices[0], fr) if not any(isinstance(n, Call) for n in walk(e.indices[0])) else None
            out |= {("i", id(a), i)} if isinstance(a, Arr) and isinstance(i, int) else \
                   ({("o", id(a))} if isinstance(a, Arr) else set())
            out |= self.storage_of(e.indices[0], fr)
        elif isinstance(e, (Unary,)):
            out |= self.storage_of(e.operand, fr)
        elif isinstance(e, Binary):
            out |= self.storage_of(e.left, fr) | self.storage_of(e.right, fr)
        elif isinstance(e, Call):
            for a in e.args:
                out |= self.storage_of(a, fr)
        return out

    def try_value(self, e, fr):
        if any(isinstance(n, Call) for n in walk(e)):
            return None
        try:
            return self.ev(e, fr, True)
        except Stuck:
            return None

    @staticmethod
    def overlap(a, b):
        if a[0] == "o" or b[0] == "o":
            return a[0] != "c" and b[0] != "c" and a[1] == b[1]
        if a[0] != b[0]:
            return False
        return a[1:] == b[1:] if a[0] != "i" else (a[1] == b[1] and (a[2] == b[2] or a[2] is None or b[2] is None))

    # ---------------------------------------------------------------- lvalues and calls
    def lvalue(self, e, fr):
        if isinstance(e, Name):
            if e.ident not in fr.env:
                raise Stuck("type", f"cannot assign to {e.ident}", e.loc)
            return fr.env[e.ident]
        if isinstance(e, Field):
            o = self.ev(e.obj, fr)
            if not isinstance(o, Rec):
                raise Stuck("type", "field of a non-record", e.loc)
            return FieldSlot(o, e.name)
        if isinstance(e, Index):
            a = self.ev(e.obj, fr)
            i = self.ev(e.indices[0], fr)
            if not isinstance(a, Arr) or not 0 <= i < len(a.items):
                raise Stuck("index", f"index {i} out of bounds", e.loc)
            return IndexSlot(a, i)
        raise Stuck("type", f"{fmt_expr(e)} is not assignable", getattr(e, "loc", (0, 0)))

    def call(self, e, fr, spec):
        n = e.name
        if n in ("Success", "Failure"):
            return Outcome(n == "Success", self.ev(e.args[0], fr, spec) if isinstance(e.args[0], Call) else None)
        if n == "succeeded":
            return self.ev(e.args[0], fr, spec).ok
        if n == "failed":
            return not self.ev(e.args[0], fr, spec).ok
        if n == "print":
            self.out.append(e.args[0].value)
            return None
        if n == "print_int":
            self.out.append(str(self.ev(e.args[0], fr, spec)))
            return None
        if n == "fill":
            raise Stuck("type", "fill(...) outside a typed declaration", e.loc)
        if spec:
            raise Stuck("type", "function call inside a contract", e.loc)
        fn = self.fns.get(n)
        if fn is None:
            raise Stuck("type", f"unknown function {n}", e.loc)
        targs = e.targs or []
        genv = self.bind(fn.gparams, targs, fr.genv, e.loc) if fn.gparams else {}
        if self.own:        # inside the callee a generic type parameter is opaque, hence non-Copy
            genv = {k: (kind, self.opaque(v) if kind == "type" else v) for k, (kind, v) in genv.items()}
        if self.own:
            muts = [(i, a) for i, (p, a) in enumerate(zip(fn.params, e.args)) if p.mode == "mutable"]
            for i, a in muts:
                rn = self.root_name(a)
                if rn is None or rn not in fr.env or not fr.env[rn].mutable:
                    raise Stuck("ownership", f"argument for mutable parameter must be a mutable variable", a.loc)
                mine = self.storage_of(a, fr) if isinstance(a, Name) else self.storage_of(a, fr)
                for j, other in enumerate(e.args):
                    if j == i:
                        continue
                    theirs = self.storage_of(other, fr)
                    if any(self.overlap(x, y) for x in mine for y in theirs):
                        raise Stuck("ownership", f"aliasing: mutable argument {fmt_expr(a)} overlaps argument "
                                    f"{fmt_expr(other)}", a.loc)
        args = []
        for p, a in zip(fn.params, e.args):
            pd = self.resolve(p.ty, genv)
            if p.mode == "mutable" and pd.kind not in ("record", "array"):
                args.append(("slot", self.lvalue(a, fr), pd))
            elif p.mode == "consume":
                args.append(("val", self.ev_owned(a, fr), pd))
            else:
                args.append(("val", self.ev(a, fr), pd))
        return self.call_fn(fn, targs, args, fr, genv=genv, loc=e.loc)

    def call_fn(self, fn, targs, args, caller, genv=None, loc=(0, 0), raw_args=False):
        self.depth += 1
        if self.depth > self.depth_limit:
            raise Stuck("nontermination", "call depth limit exceeded", loc)
        try:
            genv = genv if genv is not None else {}
            fr = Frame(fn, genv, caller)
            old = Frame(fn, genv)
            for i, p in enumerate(fn.params):
                pd = self.resolve(p.ty, genv)
                if raw_args:
                    kind, val = "val", args[i]
                else:
                    kind, val, _ = args[i]
                if kind == "slot":
                    self.check(pd, val.get(), f"argument '{p.name}'", loc)
                    fr.env[p.name] = RefSlot(val, pd)
                    old.env[p.name] = Cell(copy.deepcopy(val.get()), pd)
                else:
                    self.check(pd, val, f"argument '{p.name}'", loc)
                    fr.env[p.name] = Cell(val, pd, mutable=p.mode != "in", borrowed=p.mode != "consume")
                    old.env[p.name] = Cell(copy.deepcopy(val), pd)
            for req in fn.requires:
                if self.ev(req, fr, True) is not True:
                    raise Stuck("precondition", f"`{fmt_expr(req)}` does not hold calling {fn.name}", loc)
            if fn.decreases is not None:
                m = self.ev(fn.decreases, fr, True)
                if not 0 <= m <= fn.dec_max:
                    raise Stuck("measure", f"measure {m} of {fn.name} outside 0..{fn.dec_max}", fn.loc)
                fr.measure0 = m
                c = caller
                while c is not None and c.fn is None:
                    c = c.parent
                if c is not None and c.measure0 is not None and self.reaches(c.fn.name, fn.name) \
                        and self.reaches(fn.name, c.fn.name) and not m < c.measure0:
                    raise Stuck("measure", f"recursive call to {fn.name} does not decrease the measure "
                                f"({m} !< {c.measure0})", loc)
            fr.old = old
            ret = None
            try:
                self.block(fn.body, fr)
                if fn.ret is not None and self.resolve(fn.ret, genv).kind != "void":
                    raise Stuck("fell_off", f"{fn.name} ended without returning a value", fn.end_loc)
            except _Return as r:
                ret = r.value
            if fn.ret is not None:
                rd = self.resolve(fn.ret, genv)
                self.check(rd, ret, f"result of {fn.name}", fn.end_loc)
            for p in fn.params:       # record invariants of borrowed/moved records must hold again on return
                if p.mode in ("mutable", "consume"):
                    pd = self.resolve(p.ty, genv)
                    self.check(pd, fr.env[p.name].get(), f"parameter '{p.name}' on return", fn.end_loc)
            fr.env["result"] = Cell(ret, None)
            for ens in fn.ensures:
                if self.ev(ens, fr, True) is not True:
                    raise Stuck("postcondition", f"`{fmt_expr(ens)}` does not hold at return of {fn.name}", fn.end_loc)
            return ret
        finally:
            self.depth -= 1

    def reaches(self, a, b):
        seen, stack = set(), list(self.calls.get(a, ()))
        while stack:
            m = stack.pop()
            if m == b:
                return True
            if m not in seen:
                seen.add(m)
                stack.extend(self.calls.get(m, ()))
        return False

    # ---------------------------------------------------------------- statements
    def block(self, stmts, fr):
        added = []
        try:
            for s in stmts:
                self.exec(s, fr, added)
        finally:
            for n in added:
                fr.env.pop(n, None)

    def init_value(self, desc, e, fr):
        """Initialise a typed declaration: fill(x), a record constructor, or an ordinary expression."""
        if desc.kind == "array" and isinstance(e, Call) and e.name == "fill":
            x = self.ev_owned(e.args[0], fr)
            return Arr(desc, [copy.deepcopy(x) for _ in range(desc.length)])
        if desc.kind == "record" and isinstance(e, Call) and e.name == desc.decl.name:
            fields, fdescs = {}, {}
            for fd, a in zip(desc.decl.fields, e.args):
                fdescs[fd.name] = self.resolve(fd.ty, desc.renv)
                fields[fd.name] = self.init_value(fdescs[fd.name], a, fr)
            return Rec(desc, fields, fdescs)
        return self.ev_owned(e, fr)

    def exec(self, s, fr, added):
        self.tick()
        if isinstance(s, Let):
            if s.ty is not None:
                d = self.resolve(s.ty, fr.genv)
                v = self.init_value(d, s.value, fr)
                self.check(d, v, f"declaration of '{s.name}'", s.loc)
            else:
                v = self.ev_owned(s.value, fr)
                slot = self.try_slot(s.value, fr) if isinstance(s.value, (Name, Field, Index)) else None
                d = slot.desc if slot is not None and slot.desc is not None else self.desc_of_value(v)
            fr.env[s.name] = Cell(v, d, mutable=bool(getattr(s, "mutable", True)))
            added.append(s.name)
        elif isinstance(s, Assign):
            rn = self.root_name(s.target)
            if self.own and rn is not None and rn in fr.env and not fr.env[rn].mutable:
                raise Stuck("ownership", f"assignment to immutable variable '{rn}'", s.loc)
            v = self.ev_owned(s.value, fr)
            slot = self.lvalue(s.target, fr) if not (isinstance(s.target, Name) and rn in fr.env
                                                      and fr.env[rn].moved) else fr.env[rn]
            self.check(slot.desc, v, f"assignment to {fmt_expr(s.target)}", s.loc, record_invariants=False)
            if isinstance(slot, RefSlot):
                self.check(slot.inner.desc, v, f"assignment to {fmt_expr(s.target)}", s.loc, record_invariants=False)
            slot.put(v)
            if isinstance(s.target, Name) and s.target.ident in fr.env:
                fr.env[s.target.ident].moved = False       # re-initialisation of a moved variable
        elif isinstance(s, Assert):
            if self.ev(s.expr, fr, True) is not True:
                raise Stuck("assert", f"`{fmt_expr(s.expr)}` is false", s.loc)
        elif isinstance(s, ExprStmt):
            self.ev(s.expr, fr)
        elif isinstance(s, Return):
            raise _Return(None if s.value is None else self.ev_owned(s.value, fr))
        elif isinstance(s, If):
            for cond, body in s.branches:
                if self.ev(cond, fr) is True:
                    return self.block(body, fr)
            if s.else_body is not None:
                self.block(s.else_body, fr)
        elif isinstance(s, While):
            prev = None
            while True:
                for inv in s.invariants:
                    if self.ev(inv, fr, True) is not True:
                        raise Stuck("invariant", f"loop invariant `{fmt_expr(inv)}` is false", inv.loc)
                if s.decreases is not None:
                    m = self.ev(s.decreases, fr, True)
                    if m < 0 or (prev is not None and not m < prev):
                        raise Stuck("measure", f"loop measure {m} is negative or did not decrease (was {prev})", s.loc)
                    prev = m
                if self.ev(s.cond, fr) is not True:
                    break
                self.block(s.body, fr)
        else:
            raise Stuck("type", f"cannot execute {type(s).__name__}", getattr(s, "loc", (0, 0)))
