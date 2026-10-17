"""AST node definitions for Lise."""
from dataclasses import dataclass, field, fields, is_dataclass
from typing import Any, List, Optional

Loc = tuple


# ---------- expressions ----------
@dataclass
class Num:
    value: int
    loc: Loc = (0, 0)

@dataclass
class BoolLit:
    value: bool
    loc: Loc = (0, 0)

@dataclass
class Str:
    value: str
    loc: Loc = (0, 0)

@dataclass
class Name:
    ident: str
    loc: Loc = (0, 0)

@dataclass
class Field:
    obj: Any
    name: str
    loc: Loc = (0, 0)

@dataclass
class Index:
    obj: Any
    indices: List[Any]
    loc: Loc = (0, 0)

@dataclass
class Call:
    name: str
    targs: Optional[List[Any]]
    args: List[Any]
    loc: Loc = (0, 0)

@dataclass
class Unary:
    op: str
    operand: Any
    loc: Loc = (0, 0)

@dataclass
class Binary:
    op: str
    left: Any
    right: Any
    loc: Loc = (0, 0)

@dataclass
class Old:
    expr: Any
    loc: Loc = (0, 0)


# ---------- types ----------
@dataclass
class TypeRef:
    name: str
    args: List[Any]
    pred: Optional[Any] = None  # inline `where` refinement
    loc: Loc = (0, 0)

@dataclass
class GParam:
    name: str
    constraint: Optional[TypeRef]  # None => type parameter
    loc: Loc = (0, 0)


# ---------- statements ----------
@dataclass
class Let:
    name: str
    ty: Optional[TypeRef]
    value: Any
    mutable: bool
    loc: Loc = (0, 0)

@dataclass
class Assign:
    target: Any
    value: Any
    loc: Loc = (0, 0)

@dataclass
class If:
    branches: List[Any]      # [(cond, [stmts]), ...]
    else_body: Optional[List[Any]]
    loc: Loc = (0, 0)

@dataclass
class While:
    cond: Any
    invariants: List[Any]
    decreases: Optional[Any]
    body: List[Any]
    loc: Loc = (0, 0)

@dataclass
class Return:
    value: Optional[Any]
    loc: Loc = (0, 0)

@dataclass
class Assert:
    expr: Any
    loc: Loc = (0, 0)

@dataclass
class ExprStmt:
    expr: Any
    loc: Loc = (0, 0)


# ---------- declarations ----------
@dataclass
class TypeDecl:
    name: str
    gparams: List[GParam]
    base: TypeRef
    loc: Loc = (0, 0)
    tok_lo: int = 0
    tok_hi: int = 0

@dataclass
class FieldDecl:
    name: str
    ty: TypeRef
    loc: Loc = (0, 0)

@dataclass
class RecordDecl:
    name: str
    gparams: List[GParam]
    pred: Optional[Any]
    fields: List[FieldDecl]
    loc: Loc = (0, 0)
    tok_lo: int = 0
    tok_hi: int = 0

@dataclass
class EnumDecl:
    name: str
    variants: List[str]
    loc: Loc = (0, 0)
    tok_lo: int = 0
    tok_hi: int = 0

@dataclass
class Param:
    name: str
    mode: str  # in | mutable | consume
    ty: TypeRef
    loc: Loc = (0, 0)

@dataclass
class FnDecl:
    name: str
    gparams: List[GParam]
    params: List[Param]
    ret: Optional[TypeRef]
    requires: List[Any]
    ensures: List[Any]
    body: List[Any]
    loc: Loc = (0, 0)
    end_loc: Loc = (0, 0)
    tok_lo: int = 0
    sig_hi: int = 0
    tok_hi: int = 0
    decreases: Any = None            # termination measure (required for recursive functions)
    dec_max: Optional[int] = None    # declared maximum of the measure: bounds the recursion depth

@dataclass
class Program:
    decls: List[Any]


def walk(n):
    """Yield every AST node reachable from n."""
    if isinstance(n, (list, tuple)):
        for x in n:
            yield from walk(x)
    elif is_dataclass(n) and not isinstance(n, type):
        yield n
        for f in fields(n):
            yield from walk(getattr(n, f.name))


def fmt_expr(e, top=True):
    if isinstance(e, Num):
        return str(e.value)
    if isinstance(e, Str):
        return '"' + e.value.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n").replace("\t", "\\t") + '"'
    if isinstance(e, BoolLit):
        return "true" if e.value else "false"
    if isinstance(e, Name):
        return e.ident
    if isinstance(e, Field):
        return f"{fmt_expr(e.obj, False)}.{e.name}"
    if isinstance(e, Index):
        return f"{fmt_expr(e.obj, False)}[{', '.join(fmt_expr(i) for i in e.indices)}]"
    if isinstance(e, Call):
        t = f"[{', '.join(fmt_expr(a) for a in e.targs)}]" if e.targs is not None else ""
        return f"{e.name}{t}({', '.join(fmt_expr(a) for a in e.args)})"
    if isinstance(e, Unary):
        sp = " " if e.op == "not" else ""
        return f"{e.op}{sp}{fmt_expr(e.operand, False)}"
    if isinstance(e, Old):
        return f"old({fmt_expr(e.expr)})"
    if isinstance(e, Binary):
        s = f"{fmt_expr(e.left, False)} {e.op} {fmt_expr(e.right, False)}"
        return s if top else f"({s})"
    return "?"


def fmt_type(t):
    s = t.name
    if t.args:
        s += f"[{', '.join(fmt_expr(a) for a in t.args)}]"
    if t.pred is not None:
        s += f" where {fmt_expr(t.pred)}"
    return s
