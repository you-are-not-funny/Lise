"""Lexer for the Lise language."""
from dataclasses import dataclass


class LiseError(Exception):
    """A compile-time error with a source location (line, col)."""

    def __init__(self, msg, loc=(0, 0)):
        super().__init__(msg)
        self.msg = msg
        self.loc = loc


KEYWORDS = {
    "type", "record", "enum", "fn", "is", "end", "requires", "ensures",
    "where", "while", "do", "invariant", "decreases", "if", "then", "else",
    "elif", "let", "var", "return", "assert", "mutable", "consume", "in",
    "and", "or", "not", "implies", "true", "false", "old",
}

TWO_CHAR = {":=", "==", "!=", "<=", ">=", "->"}
ONE_CHAR = set("+-*/%<>=()[],:.")


@dataclass(frozen=True)
class Token:
    kind: str  # INT | IDENT | KW | OP | EOF
    text: str
    line: int
    col: int


def lex(src):
    toks = []
    i, n = 0, len(src)
    line, col = 1, 1
    while i < n:
        c = src[i]
        if c == "\n":
            i += 1
            line += 1
            col = 1
            continue
        if c in " \t\r":
            i += 1
            col += 1
            continue
        if src.startswith("//", i):
            while i < n and src[i] != "\n":
                i += 1
            continue
        start, scol = i, col
        if c.isascii() and (c.isalpha() or c == "_"):
            while i < n and src[i].isascii() and (src[i].isalnum() or src[i] == "_"):
                i += 1
            text = src[start:i]
            kind = "KW" if text in KEYWORDS else "IDENT"
            toks.append(Token(kind, text, line, scol))
            col += i - start
            continue
        if c.isascii() and c.isdigit():
            while i < n and src[i].isascii() and src[i].isdigit():
                i += 1
            if i < n and src[i].isascii() and (src[i].isalpha() or src[i] == "_"):
                raise LiseError("invalid number literal", (line, scol))
            toks.append(Token("INT", src[start:i], line, scol))
            col += i - start
            continue
        two = src[i:i + 2]
        if two in TWO_CHAR:
            toks.append(Token("OP", two, line, scol))
            i += 2
            col += 2
            continue
        if c in ONE_CHAR:
            toks.append(Token("OP", c, line, scol))
            i += 1
            col += 1
            continue
        raise LiseError(f"unexpected character {c!r}", (line, scol))
    toks.append(Token("EOF", "", line, col))
    return toks
