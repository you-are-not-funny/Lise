"""LLVM IR backend.  Runs ONLY after verification succeeds.

Every overflow / bounds / division obligation is proven by the verifier before
any code is generated.  There is exactly ONE kind of Lise program: there is no
unchecked mode and no way to turn the safety rules off.  The proven obligations
are additionally kept as a trap-on-violation backstop (llvm.trap).  In a
correctly verified program a backstop never fires; if the verifier or backend
ever has a bug, the program stops instead of corrupting memory.
Arithmetic never uses nsw/nuw, so it cannot produce LLVM poison/UB.
`/` and `%` are Euclidean.  A static worst-case stack bound is computed
(no heap; recursion only with a proven `decreases ... max B`, which bounds the depth) and the
build fails if it exceeds the limit.

Types (all erased of refinements):
  Integer -> i64     Bool -> i1     enum -> i32 (variant index)
  Outcome[V, E] -> i1 (true = success; payloads are unobservable, so erased)
  Array[T, N] -> [N x T]  (inline)     record -> named LLVM struct
Aggregates (records, arrays) live in memory and are passed by pointer.
Scalar `mutable` parameters are passed by pointer, everything else by value.

Generics are monomorphized: every distinct instantiation (type args must be
scalar types, value args are constants) becomes its own function/struct.

Functions returning a record/array write it through a hidden first pointer
parameter (the caller's fresh variable) with one memcpy at `return`.

Recursion: every recursive function carries a proven termination measure `decreases m max B`
(0 <= m <= B on entry, strictly smaller at each recursive call), so a recursion cycle is at most
B+1 frames deep; the stack bound uses that.

Not yet: Outcome payloads, record-typed record fields as constructor arguments.
Output: print("literal") and print_int(n) call a tiny runtime written in LLVM IR
(`lise_write`, `lise_print_int`) that uses only the POSIX write(2) call: no libc
formatting, no buffers on the heap.  A failed write stops that output and the program
continues; it can never corrupt memory.
Contracts, asserts and `decreases` are erased.
"""
import re

from lise_ast import *
from lise_ast import fmt_expr

INT, BOOL, VOID, OUTC = ("int",), ("bool",), ("void",), ("outcome",)
CMP = {"<": "slt", "<=": "sle", ">": "sgt", ">=": "sge", "==": "eq", "!=": "ne"}


class CodegenError(Exception):
    def __init__(self, msg, loc=(0, 0)):
        super().__init__(msg)
        self.msg, self.loc = msg, loc


def is_agg(t):
    return t[0] in ("array", "record")


def show(t):
    k = t[0]
    if k == "int":
        return "Integer"
    if k == "bool":
        return "Bool"
    if k == "enum":
        return t[1]
    if k == "array":
        return f"Array_{show(t[1])}_{t[2]}"
    if k == "record":
        return t[1] + "".join("_" + (show(v) if kind == "type" else str(v)) for _, kind, v in t[2])
    return k


def mangle(s):
    return re.sub(r"[^A-Za-z0-9_]", "_", s)


RUNTIME_WRITE = """declare i64 @write(i32, ptr, i64)

define internal void @lise_write(ptr %p, i64 %n) {
entry:
  br label %loop
loop:
  %pp = phi ptr [ %p, %entry ], [ %pn, %cont ]
  %nn = phi i64 [ %n, %entry ], [ %nrem, %cont ]
  %done = icmp sle i64 %nn, 0
  br i1 %done, label %exit, label %w
w:
  %r = call i64 @write(i32 1, ptr %pp, i64 %nn)
  %bad = icmp sle i64 %r, 0
  br i1 %bad, label %exit, label %cont
cont:
  %pn = getelementptr inbounds i8, ptr %pp, i64 %r
  %nrem = sub i64 %nn, %r
  br label %loop
exit:
  ret void
}
""".split("\n")

# Decimal conversion on the unsigned magnitude (so INT64_MIN works); at most 19 digits plus '-'
# fit in the 24-byte buffer, filled from the end.
RUNTIME_PRINT_INT = """define internal void @lise_print_int(i64 %x) {
entry:
  %buf = alloca [24 x i8]
  %neg = icmp slt i64 %x, 0
  %nx = sub i64 0, %x
  %u0 = select i1 %neg, i64 %nx, i64 %x
  br label %loop
loop:
  %u = phi i64 [ %u0, %entry ], [ %q, %loop ]
  %pos = phi i64 [ 24, %entry ], [ %pos1, %loop ]
  %q = udiv i64 %u, 10
  %r = urem i64 %u, 10
  %d = trunc i64 %r to i8
  %c = add i8 %d, 48
  %pos1 = sub i64 %pos, 1
  %g = getelementptr inbounds [24 x i8], ptr %buf, i64 0, i64 %pos1
  store i8 %c, ptr %g
  %more = icmp ne i64 %q, 0
  br i1 %more, label %loop, label %sign
sign:
  br i1 %neg, label %minus, label %out
minus:
  %pm = sub i64 %pos1, 1
  %gm = getelementptr inbounds [24 x i8], ptr %buf, i64 0, i64 %pm
  store i8 45, ptr %gm
  br label %out
out:
  %start = phi i64 [ %pos1, %sign ], [ %pm, %minus ]
  %p = getelementptr inbounds [24 x i8], ptr %buf, i64 0, i64 %start
  %len = sub i64 24, %start
  call void @lise_write(ptr %p, i64 %len)
  ret void
}
""".split("\n")


class Codegen:
    def __init__(self, prog, source_name="lise", stack_limit=1 << 20):
        self.stack_limit = stack_limit
        self.frames, self.edges, self.intr, self.names = {}, {}, set(), {}
        self.need_memcpy = False
        self.dec_max = {}
        self.strings, self.uses_print, self.uses_print_int = [], False, False
        self.types = {d.name: d for d in prog.decls if isinstance(d, TypeDecl)}
        self.records = {d.name: d for d in prog.decls if isinstance(d, RecordDecl)}
        self.enums = {d.name: {v: i for i, v in enumerate(d.variants)}
                      for d in prog.decls if isinstance(d, EnumDecl)}
        self.fns = {d.name: d for d in prog.decls if isinstance(d, FnDecl)}
        self.source_name = source_name
        self.rec_names, self.type_defs = {}, []
        self.insts, self.queue, self.used_syms = {}, [], set()
        self.subst = {}

    # ---------------------------------------------------------------- types
    @staticmethod
    def to_type(e):
        if isinstance(e, Name):
            return TypeRef(e.ident, [], None, e.loc)
        if isinstance(e, Index) and isinstance(e.obj, Name):
            return TypeRef(e.obj.ident, list(e.indices), None, e.loc)
        raise CodegenError(f"expected a type, found '{fmt_expr(e)}'", getattr(e, "loc", (0, 0)))

    def const(self, e, subst):
        if isinstance(e, Num):
            return e.value
        if isinstance(e, Name) and e.ident in subst and subst[e.ident][0] == "val":
            return subst[e.ident][1]
        if isinstance(e, Unary) and e.op == "-":
            return -self.const(e.operand, subst)
        if isinstance(e, Binary) and e.op in ("+", "-", "*"):
            a, b = self.const(e.left, subst), self.const(e.right, subst)
            return a + b if e.op == "+" else (a - b if e.op == "-" else a * b)
        raise CodegenError(f"'{fmt_expr(e)}' is not a compile-time constant", getattr(e, "loc", (0, 0)))

    def bind(self, gparams, args, subst, loc):
        if len(args) != len(gparams):
            raise CodegenError(f"expected {len(gparams)} type argument(s), got {len(args)}", loc)
        out = []
        for gp, a in zip(gparams, args):
            if gp.constraint is None:
                t = self.resolve(self.to_type(a), subst)
                if is_agg(t) or t[0] == "void":
                    raise CodegenError("generic type arguments must be scalar types in the backend", loc)
                out.append((gp.name, "type", t))
            else:
                out.append((gp.name, "val", self.const(a, subst)))
        return out

    @staticmethod
    def as_subst(bindings):
        return {n: (k, v) for n, k, v in bindings}

    def resolve(self, ref, subst, depth=0):
        if depth > 40:
            raise CodegenError("type is nested too deeply", ref.loc)
        n = ref.name
        if n in subst:
            k, v = subst[n]
            if k != "type" or ref.args:
                raise CodegenError(f"'{n}' is not a type here", ref.loc)
            return v
        if n == "Integer":
            return INT
        if n == "Bool":
            return BOOL
        if n == "Void":
            return VOID
        if n == "Outcome":
            return OUTC
        if n == "Array":
            if len(ref.args) != 2:
                raise CodegenError("Array takes 2 arguments", ref.loc)
            elem = self.resolve(self.to_type(ref.args[0]), subst, depth + 1)
            if is_agg(elem):
                raise CodegenError("array element types must be scalar in the backend", ref.loc)
            return ("array", elem, self.const(ref.args[1], subst))
        if n in self.enums:
            return ("enum", n)
        if n in self.types:
            d = self.types[n]
            sub = self.as_subst(self.bind(d.gparams, ref.args, subst, ref.loc))
            return self.resolve(d.base, sub, depth + 1)
        if n in self.records:
            d = self.records[n]
            return ("record", n, tuple(self.bind(d.gparams, ref.args, subst, ref.loc)))
        raise CodegenError(f"unknown type '{n}'", ref.loc)

    def fields(self, rt):
        d = self.records[rt[1]]
        sub = self.as_subst(rt[2])
        return [(f.name, self.resolve(f.ty, sub)) for f in d.fields]

    def field_index(self, rt, name, loc):
        for i, (n, t) in enumerate(self.fields(rt)):
            if n == name:
                return i, t
        raise CodegenError(f"record '{rt[1]}' has no field '{name}'", loc)

    def lt(self, t):
        k = t[0]
        if k == "int":
            return "i64"
        if k in ("bool", "outcome"):
            return "i1"
        if k == "void":
            return "void"
        if k == "enum":
            return "i32"
        if k == "array":
            return f"[{t[2]} x {self.lt(t[1])}]"
        if k == "record":
            if t in self.rec_names:
                return self.rec_names[t]
            name = f"%R.{mangle(show(t))}"
            self.rec_names[t] = name
            body = ", ".join(self.lt(ft) for _, ft in self.fields(t))
            self.type_defs.append(f"{name} = type {{ {body} }}")
            return name
        raise CodegenError(f"internal: no LLVM type for {t}")

    # ---------------------------------------------------------------- layout + stack bound
    def size_align(self, t):
        k = t[0]
        if k == "int":
            return 8, 8
        if k in ("bool", "outcome"):
            return 1, 1
        if k == "enum":
            return 4, 4
        if k == "array":
            sz, al = self.size_align(t[1])
            return sz * t[2], al
        if k == "record":
            off, mx = 0, 1
            for _, ft in self.fields(t):
                sz, al = self.size_align(ft)
                off = -(-off // al) * al + sz
                mx = max(mx, al)
            return -(-off // mx) * mx, mx
        return 0, 1

    FRAME_OVERHEAD = 256   # return address, saved registers, spill margin (conservative)

    def stack_bound(self):
        """Worst-case stack bytes per function.  Acyclic call chains add up frame sizes; a recursion
        cycle (strongly connected component) is at most (B+1) frames deep, B = largest declared
        `decreases ... max B` in the cycle, because its measure is a proven strictly decreasing
        non-negative integer starting at most at B."""
        index, low, on, stack, sccs, counter = {}, {}, set(), [], [], [0]

        def strong(v):
            index[v] = low[v] = counter[0]
            counter[0] += 1
            stack.append(v)
            on.add(v)
            for w in self.edges[v]:
                if w not in index:
                    strong(w)
                    low[v] = min(low[v], low[w])
                elif w in on:
                    low[v] = min(low[v], index[w])
            if low[v] == index[v]:
                comp = []
                while True:
                    w = stack.pop()
                    on.discard(w)
                    comp.append(w)
                    if w == v:
                        break
                sccs.append(comp)

        for v in sorted(self.frames):
            if v not in index:
                strong(v)
        cost = {}
        for comp in sccs:                      # callees' components come first
            members = set(comp)
            ext = max((cost[w] for m in comp for w in self.edges[m] if w not in members), default=0)
            cyclic = len(comp) > 1 or comp[0] in self.edges[comp[0]]
            if cyclic:
                bounds = [self.dec_max.get(m) for m in comp]
                if any(b is None for b in bounds):
                    raise CodegenError(f"recursion through '{self.names[comp[0]]}' has no `decreases ... max` bound")
                depth = max(bounds) + 1
                total = depth * max(self.frames[m] + self.FRAME_OVERHEAD for m in comp) + ext
            else:
                total = self.frames[comp[0]] + self.FRAME_OVERHEAD + ext
            for m in comp:
                cost[m] = total
                if total > self.stack_limit:
                    raise CodegenError(f"worst-case stack use of '{self.names[m]}' is about {total} bytes, over the "
                                       f"limit of {self.stack_limit} bytes (raise it with --stack-limit"
                                       f"{', or lower the recursion bound' if cyclic else ''})")
        return cost

    # ---------------------------------------------------------------- module
    def instance(self, fn, bindings):
        key = (fn.name, tuple(bindings))
        if key in self.insts:
            return self.insts[key]
        if len(self.insts) >= 512:
            raise CodegenError("more than 512 generic instantiations (infinitely recursive instantiation?)")
        if not fn.gparams:
            sym = f"lise_{fn.name}"
        else:
            sym = f"lise_{fn.name}__" + mangle("_".join(
                show(v) if k == "type" else str(v) for _, k, v in bindings))
            while sym in self.used_syms:
                sym += "_"
        self.used_syms.add(sym)
        self.insts[key] = sym
        self.queue.append((fn, bindings, sym))
        return sym

    def emit_module(self):
        for fn in self.fns.values():
            if not fn.gparams:
                self.instance(fn, [])
        fn_lines = []
        while self.queue:
            fn, bindings, sym = self.queue.pop(0)
            fn_lines.extend(self.emit_fn(fn, bindings, sym))
            fn_lines.append("")
        if self.uses_print:
            self.frames["lise_write"], self.edges["lise_write"], self.names["lise_write"] = 16, set(), "print"
        if self.uses_print_int:
            self.frames["lise_print_int"], self.names["lise_print_int"] = 32, "print_int"
            self.edges["lise_print_int"] = {"lise_write"}
        self.stack_report = self.stack_bound()
        out = [f"; ModuleID = '{self.source_name}'", f'source_filename = "{self.source_name}"', ""]
        out.extend(self.type_defs)
        if self.type_defs:
            out.append("")
        out.append("declare void @llvm.trap() noreturn nounwind")
        for name in sorted(self.intr):
            out.append(f"declare {{i64, i1}} @llvm.{name}.with.overflow.i64(i64, i64)")
        out.append("")
        if self.need_memcpy:
            out.append("declare void @llvm.memcpy.p0.p0.i64(ptr noalias writeonly, ptr noalias readonly, i64, i1 immarg)")
            out.append("")
        for label, data in self.strings:
            body = "".join(f"\\{b:02X}" for b in data)
            out.append(f'{label} = private unnamed_addr constant [{len(data)} x i8] c"{body}"')
        if self.strings:
            out.append("")
        if self.uses_print:
            out.extend(RUNTIME_WRITE)
        if self.uses_print_int:
            out.extend(RUNTIME_PRINT_INT)
        out.extend(fn_lines)
        return "\n".join(out)

    # ---------------------------------------------------------------- function state helpers
    def tmp(self):
        self.n += 1
        return f"%t{self.n}"

    def lbl(self, hint):
        self.n += 1
        return f"{hint}{self.n}"

    def o(self, s):
        self.body.append("  " + s)

    def start(self, label):
        self.body.append(f"{label}:")
        self.term = False

    def br(self, label):
        if not self.term:
            self.o(f"br label %{label}")
            self.term = True

    def lookup(self, name, loc):
        for sc in reversed(self.scopes):
            if name in sc:
                return sc[name]
        raise CodegenError(f"unknown variable '{name}'", loc)

    def in_scope(self, name):
        return any(name in sc for sc in self.scopes)

    def declare(self, name, ty):
        self.n += 1
        ptr = f"%v{self.n}.{name}"
        self.allocas.append(f"  {ptr} = alloca {self.lt(ty)}")
        self.alloca_tys.append(ty)
        self.scopes[-1][name] = (ptr, ty)
        return ptr

    # ---------------------------------------------------------------- functions
    def emit_fn(self, fn, bindings, sym):
        self.n = 0
        self.body, self.allocas, self.scopes, self.term = [], [], [{}], False
        self.alloca_tys, self.trap_lbl, self.cur_edges = [], None, set()
        self.subst = self.as_subst(bindings)
        ret = self.resolve(fn.ret, self.subst) if fn.ret else VOID
        self.ret_ty = ret
        sig, binds = [], []
        if is_agg(ret):
            sig.append("ptr %ret")          # destination supplied by the caller
        for p in fn.params:
            ty = self.resolve(p.ty, self.subst)
            if ty[0] == "void":
                raise CodegenError(f"'{fn.name}': Void parameter", p.loc)
            by_ptr = is_agg(ty) or p.mode == "mutable"
            sig.append(f"{'ptr' if by_ptr else self.lt(ty)} %arg.{p.name}")
            binds.append((p.name, ty, by_ptr))
        head = f"define {'void' if is_agg(ret) else self.lt(ret)} @{sym}({', '.join(sig)}) {{"
        self.body.append("entry:")
        for name, ty, by_ptr in binds:
            if by_ptr:
                self.scopes[-1][name] = (f"%arg.{name}", ty)
            else:
                ptr = self.declare(name, ty)
                self.o(f"store {self.lt(ty)} %arg.{name}, ptr {ptr}")
        self.block(fn.body)
        if not self.term:
            if ret == VOID:
                self.o("ret void")
            else:
                self.o(f"br label %{self.trap()}  ; proven unreachable; trap if the proof was wrong")
            self.term = True
        if self.trap_lbl:
            self.body.extend([f"{self.trap_lbl}:", "  call void @llvm.trap()", "  unreachable"])
        frame = 0
        for t in self.alloca_tys:
            sz, al = self.size_align(t)
            frame += -(-max(sz, 1) // al) * al
        self.frames[sym] = -(-frame // 16) * 16
        self.edges[sym] = self.cur_edges
        self.names[sym] = fn.name
        self.dec_max[sym] = fn.dec_max
        return [head, self.body[0]] + self.allocas + self.body[1:] + ["}"]

    def block(self, stmts):
        self.scopes.append({})
        for s in stmts:
            if self.term:
                break
            self.stmt(s)
        self.scopes.pop()

    # ---------------------------------------------------------------- trap backstop for proven obligations
    def trap(self):
        if self.trap_lbl is None:
            self.trap_lbl = "trap"
        return self.trap_lbl

    def guard(self, bad):
        """Branch to the trap block if `bad` (i1) is true."""
        ok = self.lbl("ok")
        self.o(f"br i1 {bad}, label %{self.trap()}, label %{ok}")
        self.term = True
        self.start(ok)

    def arith(self, op, l, r):
        """+ - * on i64, trapping on overflow (proven impossible by the verifier)."""
        res = self.tmp()
        name = {"+": "sadd", "-": "ssub", "*": "smul"}[op]
        self.intr.add(name)
        pair, ov = self.tmp(), self.tmp()
        self.o(f"{pair} = call {{i64, i1}} @llvm.{name}.with.overflow.i64(i64 {l}, i64 {r})")
        self.o(f"{res} = extractvalue {{i64, i1}} {pair}, 0")
        self.o(f"{ov} = extractvalue {{i64, i1}} {pair}, 1")
        self.guard(ov)
        return res

    # ---------------------------------------------------------------- statements
    def stmt(self, s):
        if isinstance(s, Let):
            ty = self.resolve(s.ty, self.subst) if s.ty is not None else None
            if ty is not None and is_agg(ty):
                ptr = self.declare(s.name, ty)
                self.init_aggregate(ptr, ty, s.value)
                return
            v, t = self.expr(s.value)
            if ty is not None and ty != t:
                raise CodegenError("internal: type mismatch in let", s.loc)
            if t == VOID:
                raise CodegenError("cannot bind a Void value", s.loc)
            ptr = self.declare(s.name, t)
            self.o(f"store {self.lt(t)} {v}, ptr {ptr}")
        elif isinstance(s, Assign):
            ptr, t = self.addr(s.target)
            if is_agg(t):
                raise CodegenError("whole aggregate assignment is not supported", s.loc)
            v, _ = self.expr(s.value)
            self.o(f"store {self.lt(t)} {v}, ptr {ptr}")
        elif isinstance(s, Assert):
            pass  # proven by the verifier; erased
        elif isinstance(s, ExprStmt):
            self.expr(s.expr)
        elif isinstance(s, Return):
            if s.value is None:
                self.o("ret void")
            elif is_agg(self.ret_ty):
                if not isinstance(s.value, Name):
                    raise CodegenError("only a local variable can be returned as a record/array", s.loc)
                src, t = self.lookup(s.value.ident, s.value.loc)
                self.need_memcpy = True
                size = f"ptrtoint (ptr getelementptr ({self.lt(t)}, ptr null, i32 1) to i64)"
                self.o(f"call void @llvm.memcpy.p0.p0.i64(ptr %ret, ptr {src}, i64 {size}, i1 false)")
                self.o("ret void")
            else:
                v, t = self.expr(s.value)
                self.o(f"ret {self.lt(t)} {v}")
            self.term = True
        elif isinstance(s, If):
            end = self.lbl("endif")
            for cond, body in s.branches:
                c, _ = self.expr(cond)
                then_l, next_l = self.lbl("then"), self.lbl("else")
                self.o(f"br i1 {c}, label %{then_l}, label %{next_l}")
                self.term = True
                self.start(then_l)
                self.block(body)
                self.br(end)
                self.start(next_l)
            if s.else_body is not None:
                self.block(s.else_body)
            self.br(end)
            self.start(end)
        elif isinstance(s, While):
            cl, bl, el = self.lbl("wcond"), self.lbl("wbody"), self.lbl("wend")
            self.br(cl)
            self.start(cl)
            c, _ = self.expr(s.cond)
            self.o(f"br i1 {c}, label %{bl}, label %{el}")
            self.term = True
            self.start(bl)
            self.block(s.body)
            self.br(cl)
            self.start(el)
        else:
            raise CodegenError("unsupported statement", getattr(s, "loc", (0, 0)))

    # ---------------------------------------------------------------- aggregates
    def init_aggregate(self, ptr, ty, value):
        if isinstance(value, Call) and value.name in self.fns:
            self.call(value, dest=ptr)           # function returning a record/array: it fills `ptr`
            return
        if ty[0] == "array":
            if not (isinstance(value, Call) and value.name == "fill" and len(value.args) == 1):
                raise CodegenError("an array must be initialised with fill(value)", getattr(value, "loc", (0, 0)))
            self.fill_array(ptr, ty, value.args[0])
            return
        if not (isinstance(value, Call) and value.name == ty[1]):
            raise CodegenError(f"a {ty[1]} must be initialised with {ty[1]}(...)", getattr(value, "loc", (0, 0)))
        flds = self.fields(ty)
        if len(value.args) != len(flds):
            raise CodegenError(f"{ty[1]} takes {len(flds)} argument(s)", value.loc)
        for i, ((fname, fty), arg) in enumerate(zip(flds, value.args)):
            g = self.tmp()
            self.o(f"{g} = getelementptr inbounds {self.lt(ty)}, ptr {ptr}, i32 0, i32 {i}")
            if fty[0] == "array":
                if not (isinstance(arg, Call) and arg.name == "fill" and len(arg.args) == 1):
                    raise CodegenError(f"array field '{fname}' must be initialised with fill(value)", arg.loc)
                self.fill_array(g, fty, arg.args[0])
            elif is_agg(fty):
                raise CodegenError("record-typed fields cannot be constructed yet", arg.loc)
            else:
                v, _ = self.expr(arg)
                self.o(f"store {self.lt(fty)} {v}, ptr {g}")

    def fill_array(self, ptr, aty, arg):
        n, ety = aty[2], aty[1]
        v, _ = self.expr(arg)
        if n == 0:
            return
        if v in ("0", "false"):
            self.o(f"store {self.lt(aty)} zeroinitializer, ptr {ptr}")
            return
        slot = self.declare(f"fi{self.n}", INT)
        self.o(f"store i64 0, ptr {slot}")
        cl, bl, el = self.lbl("fcond"), self.lbl("fbody"), self.lbl("fend")
        self.br(cl)
        self.start(cl)
        i, c = self.tmp(), self.tmp()
        self.o(f"{i} = load i64, ptr {slot}")
        self.o(f"{c} = icmp slt i64 {i}, {n}")
        self.o(f"br i1 {c}, label %{bl}, label %{el}")
        self.term = True
        self.start(bl)
        g, i2 = self.tmp(), self.tmp()
        self.o(f"{g} = getelementptr inbounds {self.lt(aty)}, ptr {ptr}, i64 0, i64 {i}")
        self.o(f"store {self.lt(ety)} {v}, ptr {g}")
        self.o(f"{i2} = add i64 {i}, 1")
        self.o(f"store i64 {i2}, ptr {slot}")
        self.br(cl)
        self.start(el)

    def addr(self, e):
        """Address of an lvalue: returns (ptr, type)."""
        if isinstance(e, Name):
            return self.lookup(e.ident, e.loc)
        if isinstance(e, Field):
            p, t = self.addr(e.obj)
            if t[0] != "record":
                raise CodegenError(f"'{fmt_expr(e.obj)}' is not a record", e.loc)
            idx, fty = self.field_index(t, e.name, e.loc)
            g = self.tmp()
            self.o(f"{g} = getelementptr inbounds {self.lt(t)}, ptr {p}, i32 0, i32 {idx}")
            return g, fty
        if isinstance(e, Index):
            if len(e.indices) != 1:
                raise CodegenError("arrays take exactly one index", e.loc)
            p, t = self.addr(e.obj)
            if t[0] != "array":
                raise CodegenError(f"'{fmt_expr(e.obj)}' is not an array", e.loc)
            i, _ = self.expr(e.indices[0])
            bad = self.tmp()
            self.o(f"{bad} = icmp uge i64 {i}, {t[2]}")
            self.guard(bad)
            g = self.tmp()
            self.o(f"{g} = getelementptr inbounds {self.lt(t)}, ptr {p}, i64 0, i64 {i}")
            return g, t[1]
        raise CodegenError(f"'{fmt_expr(e)}' is not an assignable location", getattr(e, "loc", (0, 0)))

    # ---------------------------------------------------------------- expressions: (llvm value, type)
    def expr(self, e):
        if isinstance(e, Num):
            return str(e.value), INT
        if isinstance(e, BoolLit):
            return ("true" if e.value else "false"), BOOL
        if isinstance(e, Name):
            if e.ident == "Void" and not self.in_scope("Void"):
                return "0", VOID
            if not self.in_scope(e.ident) and self.subst.get(e.ident, (None,))[0] == "val":
                return str(self.subst[e.ident][1]), INT   # generic value parameter = constant
            return self.load(e)
        if isinstance(e, Field):
            if isinstance(e.obj, Name) and e.obj.ident in self.enums and not self.in_scope(e.obj.ident):
                variants = self.enums[e.obj.ident]
                if e.name not in variants:
                    raise CodegenError(f"enum '{e.obj.ident}' has no variant '{e.name}'", e.loc)
                return str(variants[e.name]), ("enum", e.obj.ident)
            return self.load(e)
        if isinstance(e, Index):
            return self.load(e)
        if isinstance(e, Unary):
            v, t = self.expr(e.operand)
            r = self.tmp()
            if e.op == "-":
                r = self.arith("-", "0", v)
            else:
                self.o(f"{r} = xor i1 {v}, true")
            return r, t
        if isinstance(e, Binary):
            return self.binary(e)
        if isinstance(e, Call):
            return self.call(e)
        raise CodegenError(f"'{fmt_expr(e)}' is not supported by the backend yet", getattr(e, "loc", (0, 0)))

    def load(self, e):
        ptr, t = self.addr(e)
        if is_agg(t):
            raise CodegenError(f"'{fmt_expr(e)}' is a {t[0]}; it can only be passed to functions or indexed", e.loc)
        r = self.tmp()
        self.o(f"{r} = load {self.lt(t)}, ptr {ptr}")
        return r, t

    def call(self, e, dest=None):
        if e.name in ("Success", "Failure"):
            if len(e.args) == 1 and isinstance(e.args[0], Call):
                self.expr(e.args[0])
            return ("true" if e.name == "Success" else "false"), OUTC
        if e.name in ("succeeded", "failed"):
            v, _ = self.expr(e.args[0])
            if e.name == "succeeded":
                return v, BOOL
            r = self.tmp()
            self.o(f"{r} = xor i1 {v}, true")
            return r, BOOL
        if e.name == "fill":
            raise CodegenError("fill(...) is only allowed to initialise an array", e.loc)
        if e.name == "print":
            lit = e.args[0]
            if not isinstance(lit, Str):
                raise CodegenError("print takes a string literal", e.loc)
            label = f"@.str.{len(self.strings)}"
            self.strings.append((label, lit.value.encode("ascii")))
            self.uses_print = True
            self.cur_edges.add("lise_write")
            self.o(f"call void @lise_write(ptr {label}, i64 {len(lit.value)})")
            return "0", VOID
        if e.name == "print_int":
            v, _ = self.expr(e.args[0])
            self.uses_print_int = self.uses_print = True
            self.cur_edges.add("lise_print_int")
            self.o(f"call void @lise_print_int(i64 {v})")
            return "0", VOID
        fn = self.fns.get(e.name)
        if fn is None:
            raise CodegenError(f"call to unknown function '{e.name}'", e.loc)
        if fn.gparams:
            if e.targs is None:
                raise CodegenError(f"'{e.name}' is generic: pass explicit arguments", e.loc)
            bindings = self.bind(fn.gparams, e.targs, self.subst, e.loc)
        else:
            bindings = []
        sub = self.as_subst(bindings)
        sym = self.instance(fn, bindings)
        self.cur_edges.add(sym)
        args = []
        for prm, a in zip(fn.params, e.args):
            pty = self.resolve(prm.ty, sub)
            if is_agg(pty) or prm.mode == "mutable":
                p, _ = self.addr(a)
                args.append(f"ptr {p}")
            else:
                v, _ = self.expr(a)
                args.append(f"{self.lt(pty)} {v}")
        rt = self.resolve(fn.ret, sub) if fn.ret else VOID
        if is_agg(rt):
            if dest is None:
                raise CodegenError(f"'{e.name}' returns a {rt[0]}: use it to initialise a declaration", e.loc)
            self.o(f"call void @{sym}({', '.join([f'ptr {dest}'] + args)})")
            return "0", VOID
        if rt == VOID:
            self.o(f"call void @{sym}({', '.join(args)})")
            return "0", VOID
        r = self.tmp()
        self.o(f"{r} = call {self.lt(rt)} @{sym}({', '.join(args)})")
        return r, rt

    def binary(self, e):
        op = e.op
        if op in ("and", "or", "implies"):
            slot = self.declare(f"sc{self.n}", BOOL)
            l, _ = self.expr(e.left)
            if op == "implies":
                nl = self.tmp()
                self.o(f"{nl} = xor i1 {l}, true")
                l, op = nl, "or"
            self.o(f"store i1 {l}, ptr {slot}")
            rhs, end = self.lbl("rhs"), self.lbl("scend")
            if op == "and":
                self.o(f"br i1 {l}, label %{rhs}, label %{end}")
            else:
                self.o(f"br i1 {l}, label %{end}, label %{rhs}")
            self.term = True
            self.start(rhs)
            r, _ = self.expr(e.right)
            self.o(f"store i1 {r}, ptr {slot}")
            self.br(end)
            self.start(end)
            out = self.tmp()
            self.o(f"{out} = load i1, ptr {slot}")
            return out, BOOL
        l, lty = self.expr(e.left)
        r, rty = self.expr(e.right)
        if op in ("+", "-", "*"):
            return self.arith(op, l, r), INT
        res = self.tmp()
        if op in CMP:
            self.o(f"{res} = icmp {CMP[op]} {self.lt(lty)} {l}, {r}")
            return res, BOOL
        if op in ("/", "%"):
            # Euclidean division; the verifier proved r != 0 and no overflow.
            z, a, b, c, bad = self.tmp(), self.tmp(), self.tmp(), self.tmp(), self.tmp()
            self.o(f"{z} = icmp eq i64 {r}, 0")
            self.o(f"{a} = icmp eq i64 {l}, -9223372036854775808")
            self.o(f"{b} = icmp eq i64 {r}, -1")
            self.o(f"{c} = and i1 {a}, {b}")
            self.o(f"{bad} = or i1 {z}, {c}")
            self.guard(bad)
            rem, neg, bneg, babs = self.tmp(), self.tmp(), self.tmp(), self.tmp()
            self.o(f"{rem} = srem i64 {l}, {r}")
            self.o(f"{neg} = icmp slt i64 {rem}, 0")
            if op == "%":
                self.o(f"{bneg} = icmp slt i64 {r}, 0")
                nb = self.tmp()
                self.o(f"{nb} = sub i64 0, {r}")
                self.o(f"{babs} = select i1 {bneg}, i64 {nb}, i64 {r}")
                fix = self.tmp()
                self.o(f"{fix} = add i64 {rem}, {babs}")
                self.o(f"{res} = select i1 {neg}, i64 {fix}, i64 {rem}")
            else:
                q0, bpos, adj, q1 = self.tmp(), self.tmp(), self.tmp(), self.tmp()
                self.o(f"{q0} = sdiv i64 {l}, {r}")
                self.o(f"{bpos} = icmp sgt i64 {r}, 0")
                self.o(f"{adj} = select i1 {bpos}, i64 -1, i64 1")
                self.o(f"{q1} = add i64 {q0}, {adj}")
                self.o(f"{res} = select i1 {neg}, i64 {q1}, i64 {q0}")
            return res, INT
        raise CodegenError(f"operator '{op}' not supported by the backend", e.loc)


def generate(prog, source_name="lise", stack_limit=1 << 20):
    return Codegen(prog, source_name, stack_limit).emit_module()
