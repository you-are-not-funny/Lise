"""Recursive-descent parser for Lise."""
from lise_lexer import LiseError
from lise_ast import *

CMP_OPS = {"==", "!=", "<", "<=", ">", ">="}
BLOCK_END = {"end", "else", "elif"}


class Parser:
    def __init__(self, toks):
        self.toks = toks
        self.i = 0

    # ----- token helpers -----
    def peek(self, k=0):
        return self.toks[min(self.i + k, len(self.toks) - 1)]

    def loc(self):
        t = self.peek()
        return (t.line, t.col)

    def at_kw(self, text):
        t = self.peek()
        return t.kind == "KW" and t.text == text

    def at_op(self, text):
        t = self.peek()
        return t.kind == "OP" and t.text == text

    def next(self):
        t = self.peek()
        if t.kind != "EOF":
            self.i += 1
        return t

    def err(self, msg):
        raise LiseError(msg, self.loc())

    def expect_kw(self, text):
        if not self.at_kw(text):
            self.err(f"expected '{text}', found {self.describe()}")
        return self.next()

    def expect_op(self, text):
        if not self.at_op(text):
            self.err(f"expected '{text}', found {self.describe()}")
        return self.next()

    def expect_ident(self):
        t = self.peek()
        if t.kind != "IDENT":
            self.err(f"expected a name, found {self.describe()}")
        return self.next()

    def describe(self):
        t = self.peek()
        return "end of file" if t.kind == "EOF" else f"'{t.text}'"

    # ----- program -----
    def parse_program(self):
        decls = []
        while self.peek().kind != "EOF":
            lo = self.i
            if self.at_kw("type"):
                d = self.parse_type_decl()
            elif self.at_kw("record"):
                d = self.parse_record()
            elif self.at_kw("enum"):
                d = self.parse_enum()
            elif self.at_kw("fn"):
                d = self.parse_fn()
            else:
                self.err(f"expected a declaration (type, record, enum, fn), found {self.describe()}")
            d.tok_lo, d.tok_hi = lo, self.i
            decls.append(d)
        return Program(decls)

    def parse_gparams(self):
        ps = []
        if self.at_op("["):
            self.next()
            while True:
                loc = self.loc()
                name = self.expect_ident().text
                cons = None
                if self.at_op(":"):
                    self.next()
                    cons = self.parse_type(allow_where=False)
                ps.append(GParam(name, cons, loc))
                if self.at_op(","):
                    self.next()
                    continue
                break
            self.expect_op("]")
        return ps

    def parse_type(self, allow_where):
        loc = self.loc()
        name = self.expect_ident().text
        args = []
        if self.at_op("["):
            self.next()
            args.append(self.parse_expr())
            while self.at_op(","):
                self.next()
                args.append(self.parse_expr())
            self.expect_op("]")
        pred = None
        if allow_where and self.at_kw("where"):
            self.next()
            pred = self.parse_expr()
        return TypeRef(name, args, pred, loc)

    def parse_type_decl(self):
        loc = self.loc()
        self.expect_kw("type")
        name = self.expect_ident().text
        gps = self.parse_gparams()
        self.expect_op("=")
        base = self.parse_type(allow_where=True)
        return TypeDecl(name, gps, base, loc)

    def parse_record(self):
        loc = self.loc()
        self.expect_kw("record")
        name = self.expect_ident().text
        gps = self.parse_gparams()
        pred = None
        if self.at_kw("where"):
            self.next()
            pred = self.parse_expr()
        fields_ = []
        while not self.at_kw("end"):
            floc = self.loc()
            fname = self.expect_ident().text
            self.expect_op(":")
            fty = self.parse_type(allow_where=True)
            fields_.append(FieldDecl(fname, fty, floc))
        self.expect_kw("end")
        return RecordDecl(name, gps, pred, fields_, loc)

    def parse_enum(self):
        loc = self.loc()
        self.expect_kw("enum")
        name = self.expect_ident().text
        vs = []
        while not self.at_kw("end"):
            vs.append(self.expect_ident().text)
            if self.at_op(","):
                self.next()
        self.expect_kw("end")
        if not vs:
            raise LiseError(f"enum '{name}' needs at least one variant", loc)
        return EnumDecl(name, vs, loc)

    def parse_fn(self):
        loc = self.loc()
        self.expect_kw("fn")
        name = self.expect_ident().text
        gps = self.parse_gparams()
        self.expect_op("(")
        params = []
        if not self.at_op(")"):
            while True:
                ploc = self.loc()
                pname = self.expect_ident().text
                self.expect_op(":")
                mode = "in"
                for m in ("mutable", "consume", "in"):
                    if self.at_kw(m):
                        mode = m
                        self.next()
                        break
                params.append(Param(pname, mode, self.parse_type(allow_where=True), ploc))
                if self.at_op(","):
                    self.next()
                    continue
                break
        self.expect_op(")")
        ret = None
        if self.at_op("->"):
            self.next()
            ret = self.parse_type(allow_where=True)
        reqs, enss, dec, dec_max = [], [], None, None
        while self.at_kw("requires") or self.at_kw("ensures") or self.at_kw("decreases"):
            kwtok = self.next()
            if kwtok.text == "decreases":
                if dec is not None:
                    raise LiseError("a function can have only one 'decreases' clause", (kwtok.line, kwtok.col))
                dec = self.parse_expr()
                t = self.peek()
                if not (t.kind == "IDENT" and t.text == "max"):
                    raise LiseError("expected 'max <integer>' after the decreases measure (it bounds the "
                                    "recursion depth), e.g. decreases n max 100", (t.line, t.col))
                self.next()
                t = self.peek()
                if t.kind != "INT":
                    raise LiseError("the maximum of a decreases measure must be an integer literal", (t.line, t.col))
                dec_max = int(self.next().text)
            else:
                (reqs if kwtok.text == "requires" else enss).append(self.parse_expr())
        sig_hi = self.i
        self.expect_kw("is")
        body = self.parse_block()
        end_loc = self.loc()
        self.expect_kw("end")
        fn = FnDecl(name, gps, params, ret, reqs, enss, body, loc, end_loc)
        fn.decreases, fn.dec_max = dec, dec_max
        fn.sig_hi = sig_hi
        return fn

    # ----- statements -----
    def parse_block(self):
        stmts = []
        while True:
            t = self.peek()
            if t.kind == "EOF":
                self.err("unexpected end of file (missing 'end'?)")
            if t.kind == "KW" and t.text in BLOCK_END:
                return stmts
            stmts.append(self.parse_stmt())

    def parse_stmt(self):
        loc = self.loc()
        if self.at_kw("let") or self.at_kw("var"):
            mutable = self.next().text == "var"
            name = self.expect_ident().text
            ty = None
            if self.at_op(":"):
                self.next()
                ty = self.parse_type(allow_where=True)
            self.expect_op(":=" if mutable else "=")
            return Let(name, ty, self.parse_expr(), mutable, loc)
        if self.at_kw("return"):
            self.next()
            t = self.peek()
            if t.kind == "EOF" or (t.kind == "KW" and t.text in BLOCK_END):
                return Return(None, loc)
            return Return(self.parse_expr(), loc)
        if self.at_kw("assert"):
            self.next()
            return Assert(self.parse_expr(), loc)
        if self.at_kw("if"):
            return self.parse_if()
        if self.at_kw("while"):
            return self.parse_while()
        e = self.parse_expr()
        if self.at_op(":="):
            self.next()
            if not isinstance(e, (Name, Field, Index)):
                raise LiseError("invalid assignment target", loc)
            return Assign(e, self.parse_expr(), loc)
        if not isinstance(e, Call):
            raise LiseError("expected a statement (assignment or call)", loc)
        return ExprStmt(e, loc)

    def parse_if(self):
        loc = self.loc()
        self.expect_kw("if")
        branches = []
        cond = self.parse_expr()
        self.expect_kw("then")
        branches.append((cond, self.parse_block()))
        else_body = None
        while self.at_kw("elif"):
            self.next()
            c = self.parse_expr()
            self.expect_kw("then")
            branches.append((c, self.parse_block()))
        if self.at_kw("else"):
            self.next()
            else_body = self.parse_block()
        self.expect_kw("end")
        return If(branches, else_body, loc)

    def parse_while(self):
        loc = self.loc()
        self.expect_kw("while")
        cond = self.parse_expr()
        invs, dec = [], None
        while self.at_kw("invariant") or self.at_kw("decreases"):
            if self.next().text == "invariant":
                invs.append(self.parse_expr())
            else:
                if dec is not None:
                    self.err("duplicate 'decreases' clause")
                dec = self.parse_expr()
        self.expect_kw("do")
        body = self.parse_block()
        self.expect_kw("end")
        return While(cond, invs, dec, body, loc)

    # ----- expressions -----
    def parse_expr(self):
        return self.parse_implies()

    def parse_implies(self):
        left = self.parse_or()
        if self.at_kw("implies"):
            loc = self.loc()
            self.next()
            return Binary("implies", left, self.parse_implies(), loc)
        return left

    def parse_or(self):
        left = self.parse_and()
        while self.at_kw("or"):
            loc = self.loc()
            self.next()
            left = Binary("or", left, self.parse_and(), loc)
        return left

    def parse_and(self):
        left = self.parse_not()
        while self.at_kw("and"):
            loc = self.loc()
            self.next()
            left = Binary("and", left, self.parse_not(), loc)
        return left

    def parse_not(self):
        if self.at_kw("not"):
            loc = self.loc()
            self.next()
            return Unary("not", self.parse_not(), loc)
        return self.parse_cmp()

    def parse_cmp(self):
        left = self.parse_add()
        t = self.peek()
        if t.kind == "OP" and t.text in CMP_OPS:
            loc = self.loc()
            self.next()
            return Binary(t.text, left, self.parse_add(), loc)
        return left

    def parse_add(self):
        left = self.parse_mul()
        while self.at_op("+") or self.at_op("-"):
            loc = self.loc()
            op = self.next().text
            left = Binary(op, left, self.parse_mul(), loc)
        return left

    def parse_mul(self):
        left = self.parse_unary()
        while self.at_op("*") or self.at_op("/") or self.at_op("%"):
            loc = self.loc()
            op = self.next().text
            left = Binary(op, left, self.parse_unary(), loc)
        return left

    def parse_unary(self):
        if self.at_op("-"):
            loc = self.loc()
            self.next()
            return Unary("-", self.parse_unary(), loc)
        return self.parse_postfix()

    def parse_postfix(self):
        e = self.parse_primary()
        while True:
            if self.at_op("."):
                loc = self.loc()
                self.next()
                e = Field(e, self.expect_ident().text, loc)
            elif self.at_op("["):
                loc = self.loc()
                self.next()
                idx = [self.parse_expr()]
                while self.at_op(","):
                    self.next()
                    idx.append(self.parse_expr())
                self.expect_op("]")
                e = Index(e, idx, loc)
            else:
                return e

    def parse_args(self):
        self.expect_op("(")
        args = []
        if not self.at_op(")"):
            args.append(self.parse_expr())
            while self.at_op(","):
                self.next()
                args.append(self.parse_expr())
        self.expect_op(")")
        return args

    def parse_primary(self):
        t = self.peek()
        loc = (t.line, t.col)
        if t.kind == "INT":
            self.next()
            return Num(int(t.text), loc)
        if t.kind == "STR":
            self.next()
            return Str(t.text, loc)
        if t.kind == "KW" and t.text in ("true", "false"):
            self.next()
            return BoolLit(t.text == "true", loc)
        if t.kind == "KW" and t.text == "old":
            self.next()
            self.expect_op("(")
            e = self.parse_expr()
            self.expect_op(")")
            return Old(e, loc)
        if self.at_op("("):
            self.next()
            e = self.parse_expr()
            self.expect_op(")")
            return e
        if t.kind == "IDENT":
            self.next()
            if self.at_op("["):  # maybe an explicit generic call: f[T, N](...)
                save = self.i
                try:
                    self.next()
                    targs = [self.parse_expr()]
                    while self.at_op(","):
                        self.next()
                        targs.append(self.parse_expr())
                    self.expect_op("]")
                    if self.at_op("("):
                        return Call(t.text, targs, self.parse_args(), loc)
                except LiseError:
                    pass
                self.i = save
                return Name(t.text, loc)
            if self.at_op("("):
                return Call(t.text, None, self.parse_args(), loc)
            return Name(t.text, loc)
        self.err(f"expected an expression, found {self.describe()}")
