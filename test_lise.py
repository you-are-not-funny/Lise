"""Run with:  python -m unittest -v   (needs: pip install z3-solver)"""
import os
import shutil
import tempfile
import unittest

from lise_verify import ProofCache
from lise_verify import check_source as _check_source


def check_source(src, filename="<input>", timeout_ms=10000, cache=None, independent="require", lints=False):
    """Most tests are about other rules, so the developer-mistake lints are off by default here; the
    lint tests, the example-program tests and every CLI test run with them ON (the product default)."""
    return _check_source(src, filename, timeout_ms, cache, independent, lints)

HERE = os.path.dirname(os.path.abspath(__file__))

PRELUDE = """
type PositiveSize = Integer where value > 0
type ValidIndex[N: PositiveSize] = Integer where value >= 0 and value < N
record RB[T, N: PositiveSize]
    storage: Array[T, N]
    head: ValidIndex[N]
    tail: ValidIndex[N]
    count: Integer where value >= 0 and value <= N
end
"""


def run(src, **kw):
    return check_source(src, "t.lise", timeout_ms=kw.pop("timeout_ms", 10000), **kw)


def msgs(rep):
    return "\n".join(str(d) for d in rep.diags)


class Examples(unittest.TestCase):
    def read(self, name):
        with open(os.path.join(HERE, name), encoding="utf-8") as f:
            return f.read()

    def test_ok_examples_verify(self):
        for n in ("example_ok_ring_buffer.lise", "example_ok_loops.lise"):
            rep = check_source(self.read(n), n)
            self.assertTrue(rep.ok, msgs(rep))
            self.assertEqual(rep.verified, rep.functions)

    def test_fail_examples_rejected(self):
        rep = check_source(self.read("example_fail_ring_buffer.lise"), "x")
        self.assertFalse(rep.ok)
        self.assertIn("counterexample", msgs(rep))
        rep = check_source(self.read("example_fail_overflow.lise"), "x")
        self.assertIn("integer overflow", msgs(rep))


class MustFail(unittest.TestCase):
    def fails(self, src, needle):
        rep = run(src)
        self.assertFalse(rep.ok, "expected failure but verified:\n" + src)
        self.assertIn(needle, msgs(rep))

    def test_wrong_postcondition(self):
        self.fails(PRELUDE + """
fn push[T, N: PositiveSize](item: consume T, q: mutable RB[T, N])
requires q.count < N
ensures q.count == old(q.count) + 2
is
    q.storage[q.tail] := item
    q.tail := (q.tail + 1) % N
    q.count := q.count + 1
end""", "postcondition may not hold")

    def test_out_of_bounds(self):
        self.fails("""
fn f[N: PositiveSize](a: in Array[Integer, N], i: Integer) -> Integer
is return a[i] end
type PositiveSize = Integer where value > 0""", "out of bounds")

    def test_min_mod_minus_one(self):
        self.fails("fn f(a: Integer, b: Integer where value != 0) -> Integer is return a % b end", "MIN % -1")

    def test_division_by_zero(self):
        self.fails("fn f(a: Integer, b: Integer) -> Integer is return a / b end", "division by zero")

    def test_missing_decreases(self):
        self.fails("""
fn f(n: Integer where value >= 0)
is
    var i: Integer := 0
    while i < n
    invariant i <= n
    do i := i + 1 end
end""", "decreases")

    def test_bad_invariant(self):
        self.fails("""
fn f(n: Integer where value >= 0 and value < 100)
is
    var i: Integer := 0
    while i < n
    invariant i < 5
    decreases n - i
    do i := i + 1 end
end""", "invariant may not be preserved")

    def test_measure_not_decreasing(self):
        self.fails("""
fn f(n: Integer where value >= 0 and value < 100)
is
    var i: Integer := 0
    while i < n
    invariant 0 <= i and i <= n
    decreases i
    do i := i + 1 end
end""", "strictly decrease")

    def test_assign_to_immutable(self):
        self.fails("fn f(x: Integer) is x := 1 end", "not mutable")

    def test_assign_to_let(self):
        self.fails("fn f() is let x = 1\n x := 2 end", "not mutable")

    def test_refinement_violation_on_assign(self):
        self.fails("fn f() is var x: Integer where value > 0 := 1\n x := 0 end", "violate")

    def test_type_mismatch(self):
        self.fails("fn f() -> Integer is return true end", "type mismatch")

    def test_unknown_name(self):
        self.fails("fn f() -> Integer is return y end", "undefined name")

    def test_missing_return(self):
        self.fails("fn f(x: Integer) -> Integer is if x > 0 then return 1 end end", "without returning")

    def test_old_in_requires(self):
        self.fails("fn f(x: Integer) requires old(x) > 0 is end", "old()")

    def test_recursion_rejected(self):
        self.fails("fn f(x: Integer) -> Integer is return f(x) end", "recursi")

    def test_unused_outcome(self):
        self.fails("""
fn g() -> Outcome[Void, Integer] is return Success(Void) end
fn f() is g() end""", "must be used")

    def test_precondition_at_call(self):
        self.fails("""
fn pos(x: Integer where value > 0) -> Integer is return x end
fn f(y: Integer) -> Integer is return pos(y) end""", "may violate parameter type")

    def test_requires_at_call(self):
        self.fails("""
fn g(x: Integer) -> Integer requires x > 10 is return x end
fn f(y: Integer) -> Integer is return g(y) end""", "precondition of 'g'")

    def test_aliasing_rejected(self):
        self.fails("""
fn g(a: mutable Integer, b: Integer) is a := 1 end
fn f() is var x: Integer := 1\n g(x, x) end""", "aliasing")

    def test_shadowing_rejected(self):
        self.fails("fn f(x: Integer) is let x = 1 end", "already declared")

    def test_literal_range(self):
        self.fails("fn f() -> Integer is return 9223372036854775808 end", "does not fit")

    def test_unknown_is_rejected_not_passed(self):
        # Hard nonlinear goal with a tiny timeout: must be an error, never a pass.
        rep = run("""
fn f(a: Integer where value > 0 and value < 100000, b: Integer where value > 0 and value < 100000,
     c: Integer where value > 0 and value < 100000) -> Integer
ensures a*a*a + b*b*b != c*c*c
is return 0 end""", timeout_ms=50)
        self.assertFalse(rep.ok)

    def test_record_invariant_on_return(self):
        self.fails("""
record R
    a: Integer where value >= 0
    b: Integer where value >= 0
end
record R2 where a <= b
    a: Integer where value >= 0
    b: Integer where value >= 0
end
fn f(r: mutable R2) is r.a := r.a + 1 end""", "invariant")

    def test_mutated_in_loop_havoc(self):
        # i is modified in the loop; the compiler must not assume i == 0 afterwards.
        self.fails("""
fn f() -> Integer
ensures result == 0
is
    var i: Integer := 0
    while i < 3
    invariant 0 <= i and i <= 3
    decreases 3 - i
    do i := i + 1 end
    return i
end""", "postcondition")

    # ---- ownership / affine checking
    def test_use_after_move(self):
        self.fails("""
fn eat[T](x: consume T) is end
fn f[T](x: consume T) is
    eat[T](x)
    eat[T](x)
end""", "use of moved value 'x'")

    def test_move_out_of_borrowed_param(self):
        self.fails("fn f[T](x: T) -> T is return x end", "borrowed")

    def test_double_move_in_one_call(self):
        self.fails("""
fn two[T](a: consume T, b: consume T) is end
fn f[T](x: consume T) is two[T](x, x) end""", "moved")

    def test_move_in_loop(self):
        self.fails("""
fn eat[T](x: consume T) is end
fn f[T](x: consume T, n: Integer where value >= 0 and value < 10) is
    var i: Integer := 0
    while i < n
    invariant 0 <= i and i <= n
    decreases n - i
    do
        eat[T](x)
        i := i + 1
    end
end""", "loop")

    def test_use_after_conditional_move(self):
        self.fails("""
fn eat[T](x: consume T) is end
fn f[T](x: consume T, c: Bool) -> Bool is
    if c then eat[T](x) end
    return x == x
end""", "moved")

    def test_use_moved_record(self):
        self.fails(PRELUDE + """
fn eat[T, N: PositiveSize](q: consume RB[T, N]) is end
fn f[T, N: PositiveSize](q: consume RB[T, N]) -> Integer is
    eat[T, N](q)
    return q.count
end""", "moved")

    def test_move_out_of_array(self):
        self.fails("""
type PositiveSize = Integer where value > 0
fn f[T, N: PositiveSize](a: in Array[T, N]) -> T requires N > 1 is return a[0] end""", "array")

    def test_syntax_error(self):
        self.fails("fn f( is end", "expected")


class MustPass(unittest.TestCase):
    def passes(self, src):
        rep = run(src)
        self.assertTrue(rep.ok, msgs(rep))
        return rep

    def test_div_with_requires(self):
        self.passes("fn f(a: Integer, b: Integer) -> Integer requires b > 0 is return a / b end")

    def test_short_circuit_guards(self):
        self.passes("""
type PositiveSize = Integer where value > 0
fn f[N: PositiveSize](a: in Array[Integer, N], i: Integer) -> Bool
is return i >= 0 and i < N and a[i] > 0 end""")

    def test_call_contract_modular(self):
        self.passes("""
fn inc(x: Integer where value < 1000) -> Integer
ensures result == x + 1
is return x + 1 end
fn f() -> Integer
ensures result == 4
is
    let a = inc(1)
    let b = inc(a)
    return inc(b)
end""")

    def test_mutable_scalar_call(self):
        self.passes("""
fn bump(x: mutable Integer where value < 100)
requires x < 99
ensures x == old(x) + 1
is x := x + 1 end
fn f() -> Integer
ensures result == 6
is
    var v: Integer := 5
    bump(v)
    return v
end""")

    def test_unreachable_branch_pruned(self):
        self.passes("""
fn f(x: Integer where value > 0) -> Integer
ensures result > 0
is
    if x <= 0 then return -1 end
    return x
end""")

    def test_consume_and_return_owned(self):
        self.passes("fn f[T](x: consume T) -> T is return x end")

    def test_consume_copy_types_never_moves(self):
        self.passes("""
fn g(x: consume Integer) is end
fn f(n: Integer) -> Integer is
    g(n)
    g(n)
    return n
end""")

    def test_reinitialise_after_move(self):
        self.passes("""
fn eat[T](x: consume T) is end
fn f[T](x: consume T, y: consume T) is
    eat[T](x)
    x := y
    eat[T](x)
end""")

    def test_comparison_does_not_move(self):
        self.passes("fn f[T](x: in T) -> Bool is return x == x end")

    def test_enum(self):
        self.passes("""
enum Color
    Red
    Green
end
fn f(c: Color) -> Bool
ensures result == (c == Color.Red)
is return c == Color.Red end""")


try:
    import ctypes
    import llvmlite.binding as llvm
    HAVE_LLVM = True
except ImportError:  # pragma: no cover
    HAVE_LLVM = False


@unittest.skipUnless(HAVE_LLVM, "pip install llvmlite to run backend tests")
class Backend(unittest.TestCase):
    """Compile Lise -> LLVM IR, JIT it, and compare against Python."""

    @classmethod
    def setUpClass(cls):
        llvm.initialize_native_target()
        llvm.initialize_native_asmprinter()

    def jit(self, src):
        from lise_codegen import generate
        from lise_lexer import lex
        from lise_parser import Parser
        rep = check_source(src, "t")
        self.assertTrue(rep.ok, msgs(rep))
        ir = generate(Parser(lex(src)).parse_program())
        mod = llvm.parse_assembly(ir)
        mod.verify()
        tm = llvm.Target.from_default_triple().create_target_machine()
        eng = llvm.create_mcjit_compiler(mod, tm)
        eng.finalize_object()
        self._keep = (eng, mod)
        return lambda name, nargs: ctypes.CFUNCTYPE(ctypes.c_int64, *([ctypes.c_int64] * nargs))(
            eng.get_function_address("lise_" + name))

    def test_math_example(self):
        with open(os.path.join(HERE, "example_ok_math.lise"), encoding="utf-8") as f:
            get = self.jit(f.read())
        import math
        gcd = get("gcd", 2)
        for a, b in [(48, 18), (0, 5), (7, 0), (17, 13), (1000000, 250000), (0, 0)]:
            self.assertEqual(gcd(a, b), math.gcd(a, b))
        self.assertEqual(get("gcd_diff", 2)(12, 18), 0)
        ed = get("euclid_div", 2)
        for a in (-7, -1, 0, 1, 7, 999, -999):
            for b in (-3, -2, -1, 1, 2, 5, 999):
                q = ed(a, b)
                r = a - b * q
                self.assertTrue(0 <= r < abs(b), (a, b, q, r))   # Euclidean division
        self.assertEqual(get("between", 3)(5, 1, 9), 1)

    def test_loops_example(self):
        with open(os.path.join(HERE, "example_ok_loops.lise"), encoding="utf-8") as f:
            get = self.jit(f.read())
        for n in (0, 1, 10, 1000):
            self.assertEqual(get("sum_to", 1)(n), n * (n + 1) // 2)
        clamp = get("clamp", 3)
        for x in (-5, 0, 5, 10, 99):
            self.assertEqual(clamp(x, 0, 10), min(max(x, 0), 10))
        for x in (-5, 0, 7):
            self.assertEqual(get("safe_abs", 1)(x), abs(x))

    def test_short_circuit_and_nested_control_flow(self):
        get = self.jit("""
fn f(n: Integer where value >= 0 and value < 50) -> Integer
ensures result >= 0
is
    var i: Integer := 0
    var evens: Integer := 0
    while i < n
    invariant 0 <= i and i <= n
    invariant 0 <= evens and evens <= i
    decreases n - i
    do
        if i % 2 == 0 and i > 2 then
            evens := evens + 1
        elif i == 1 or i == 3 then
            evens := evens + 0
        else
            evens := evens + 0
        end
        i := i + 1
    end
    return evens
end""")
        for n in (0, 1, 5, 20, 49):
            self.assertEqual(get("f", 1)(n), sum(1 for i in range(n) if i % 2 == 0 and i > 2))

    def test_no_proof_no_ir_and_unsupported_is_reported(self):
        from lise_codegen import CodegenError, generate
        from lise_lexer import lex
        from lise_parser import Parser
        prog = Parser(lex("record R\n    a: Integer\nend\nfn f(x: in R) -> R\nis\n    return R(1)\nend\nfn g() -> Integer\nis\n    var r: R := f(R(2))\n    return 0\nend")).parse_program()
        with self.assertRaises(CodegenError):
            generate(prog)


class Cache(unittest.TestCase):
    def test_cache_hits_and_invalidation(self):
        d = tempfile.mkdtemp()
        try:
            src = "fn a(x: Integer where value > 0) -> Integer ensures result > 0 is return x end\n" \
                  "fn b() -> Integer is return a(1) end\n"
            c = ProofCache(d)
            r1 = check_source(src, "t", cache=c)
            c.save()
            self.assertTrue(r1.ok)
            self.assertEqual(r1.cached, 0)
            c2 = ProofCache(d)
            r2 = check_source(src, "t", cache=c2)
            self.assertEqual(r2.cached, 2)
            # whitespace/comments do not invalidate
            r3 = check_source("// hi\n" + src.replace(" ", "  "), "t", cache=ProofCache(d))
            self.assertEqual(r3.cached, 2)
            # changing a's BODY re-proves a only (b depends on a's contract)
            r4 = check_source(src.replace("return x end", "return x + 0 end"), "t", cache=ProofCache(d))
            self.assertEqual(r4.cached, 1)
            # changing a's CONTRACT re-proves both
            r5 = check_source(src.replace("result > 0", "result >= 1"), "t", cache=ProofCache(d))
            self.assertEqual(r5.cached, 0)
        finally:
            shutil.rmtree(d)

    def test_failures_are_never_cached(self):
        d = tempfile.mkdtemp()
        try:
            bad = "fn a(x: Integer) -> Integer is return x + 1 end"
            c = ProofCache(d)
            check_source(bad, "t", cache=c)
            c.save()
            r = check_source(bad, "t", cache=ProofCache(d))
            self.assertFalse(r.ok)
        finally:
            shutil.rmtree(d)


if __name__ == "__main__":
    unittest.main()


try:
    import llvmlite.binding  # noqa: F401
    HAVE_AOT = shutil.which("gcc") or shutil.which("cc") or shutil.which("clang")
except ImportError:
    HAVE_AOT = False


@unittest.skipUnless(HAVE_AOT, "needs llvmlite and a C linker for AOT tests")
class AotBuild(unittest.TestCase):
    """Lise -> native executable (ahead of time, no JIT), run as a subprocess."""

    def build_run(self, src, opt=2):
        import subprocess
        from lise_aot import build_executable
        from lise_codegen import generate
        from lise_lexer import lex
        from lise_parser import Parser
        rep = check_source(src, "t.lise")
        self.assertTrue(rep.ok, msgs(rep))
        ir = generate(Parser(lex(src)).parse_program(), "t.lise")
        with tempfile.TemporaryDirectory() as d:
            exe = os.path.join(d, "prog")
            build_executable(ir, exe, opt)
            return subprocess.run([exe]).returncode

    def test_exit_status_is_main_result(self):
        src = "fn main() -> Integer\nis\n    return 42\nend\n"
        self.assertEqual(self.build_run(src), 42)

    def test_loops_and_calls_all_opt_levels(self):
        src = """
fn sum_to(n: Integer where value >= 0 and value <= 10) -> Integer
ensures result >= 0
is
    var i: Integer := 0
    var acc: Integer := 0
    while i < n
    invariant 0 <= i and i <= n
    invariant 0 <= acc and acc <= i * 10
    decreases n - i
    do
        i := i + 1
        acc := acc + i
    end
    return acc
end
fn main() -> Integer
is
    return sum_to(10)
end
"""
        for o in (0, 1, 2, 3):
            self.assertEqual(self.build_run(src, o), 55, f"-O{o}")

    def test_missing_main_is_an_error(self):
        from lise_aot import AotError, build_executable
        from lise_codegen import generate
        from lise_lexer import lex
        from lise_parser import Parser
        ir = generate(Parser(lex("fn f() -> Integer\nis\n    return 1\nend\n")).parse_program())
        with self.assertRaises(AotError):
            build_executable(ir, os.path.join(tempfile.gettempdir(), "never"))

    def test_cli_refuses_binary_when_proof_fails(self):
        import subprocess
        import sys
        with tempfile.TemporaryDirectory() as d:
            p = os.path.join(d, "bad.lise")
            with open(p, "w") as f:
                f.write("fn main() -> Integer\nis\n    return 9223372036854775807 + 1\nend\n")
            r = subprocess.run([sys.executable, os.path.join(HERE, "lise.py"), "build", p,
                                "--exe", "--no-cache"], capture_output=True, text=True, cwd=d)
            self.assertEqual(r.returncode, 1)
            self.assertFalse(os.path.exists(os.path.join(d, "bad")))
            self.assertIn("no proof, no binary", r.stdout)


QUEUE = open(os.path.join(HERE, "example_ok_queue_main.lise"), encoding="utf-8").read()


class LocalAggregates(unittest.TestCase):
    """Verifier: local records/arrays via fill(...) and T(...) constructors."""

    def test_queue_program_verifies(self):
        rep = check_source(QUEUE, "q.lise")
        self.assertTrue(rep.ok, msgs(rep))

    def test_constructor_must_satisfy_field_types(self):
        bad = QUEUE.replace("RingBuffer(fill(0), 0, 0, 0)", "RingBuffer(fill(0), 0, 0, 5)")
        rep = check_source(bad, "q.lise")
        self.assertFalse(rep.ok)
        self.assertIn("may violate its type", msgs(rep))

    def test_push_on_full_queue_rejected(self):
        bad = QUEUE.replace("    let x = pop[4](q)", "    let c = push[Integer, 4](1, q)\n    let d = push[Integer, 4](2, q)\n    let e = push[Integer, 4](3, q)\n    let x = pop[4](q)")
        rep = check_source(bad, "q.lise")
        self.assertFalse(rep.ok)
        self.assertIn("precondition of 'push' may not hold", msgs(rep))

    def test_pop_on_empty_queue_rejected(self):
        bad = QUEUE.replace("    let y = pop[4](q)", "    let y = pop[4](q)\n    let z = pop[4](q)")
        rep = check_source(bad, "q.lise")
        self.assertFalse(rep.ok)
        self.assertIn("precondition of 'pop' may not hold", msgs(rep))

    def test_array_local_bounds_checked(self):
        src = "fn main() -> Integer\nis\n    var a: Array[Integer, 3] := fill(7)\n    return a[3]\nend\n"
        rep = check_source(src, "t.lise")
        self.assertFalse(rep.ok)
        self.assertIn("out of bounds", msgs(rep))


@unittest.skipUnless(HAVE_AOT, "needs llvmlite and a C linker for AOT tests")
class AotAggregates(AotBuild):
    def test_generic_ring_buffer_native(self):
        self.assertEqual(self.build_run(QUEUE), 42)

    def test_fifo_order_and_wraparound(self):
        src = QUEUE.replace("""    let x = pop[4](q)
    let y = pop[4](q)
    return x % 100 + y % 100""", """    let x = pop[4](q)
    let c = push[Integer, 4](3, q)
    let d = push[Integer, 4](4, q)
    let e = push[Integer, 4](5, q)
    var total: Integer := x % 10
    var i: Integer := 0
    while i < 4
    invariant 0 <= i and i <= 4
    invariant q.count == 4 - i
    invariant total >= 0 and total <= 9 + i * 9
    decreases 4 - i
    do
        let v = pop[4](q)
        total := total + v % 10
        i := i + 1
    end
    return total""")
        # queue after x: [132]; push 3,4,5 -> [132,3,4,5] (tail wraps around)
        # total = 10%10 + 132%10 + 3 + 4 + 5 = 0 + 2 + 3 + 4 + 5 = 14
        rep = check_source(src, "t.lise")
        self.assertTrue(rep.ok, msgs(rep))
        self.assertEqual(self.build_run(src), 14)

    def test_fill_nonzero_loop_and_bool_array(self):
        src = """
fn main() -> Integer
is
    var a: Array[Integer, 5] := fill(3)
    var f: Array[Bool, 2] := fill(true)
    a[4] := 10
    if f[1] then
        return a[0] + a[4]
    end
    return 0
end
"""
        self.assertEqual(self.build_run(src), 13)


class CallLoopSoundness(unittest.TestCase):
    """Calls with `mutable` args inside loops must forget what the callee may change."""

    def test_loop_invariant_ignoring_mutating_call_is_rejected(self):
        bad = QUEUE.replace("""    let x = pop[4](q)
    let y = pop[4](q)
    return x % 100 + y % 100""", """    var i: Integer := 0
    while i < 2
    invariant 0 <= i and i <= 2
    invariant q.count == 2
    decreases 2 - i
    do
        let v = pop[4](q)
        i := i + 1
    end
    return 0""")
        rep = check_source(bad, "q.lise")
        self.assertFalse(rep.ok)
        self.assertIn("invariant", msgs(rep))

    def test_mutable_alias_with_field_rejected(self):
        src = PRELUDE + """
fn two(a: mutable RB[Integer, 4], i: Integer)
is
    a.count := a.count
end
fn bad(q: mutable RB[Integer, 4])
is
    two(q, q.count)
end
"""
        rep = check_source(src, "t.lise")
        self.assertFalse(rep.ok)
        self.assertIn("aliasing", msgs(rep))


@unittest.skipUnless(HAVE_AOT, "needs llvmlite and a C linker for AOT tests")
class Safety(unittest.TestCase):
    def native(self, src, stack_limit=1 << 20):
        import subprocess
        from lise_aot import build_executable
        from lise_codegen import generate
        from lise_lexer import lex
        from lise_parser import Parser
        ir = generate(Parser(lex(src)).parse_program(), "t", stack_limit)  # NO verifier on purpose
        with tempfile.TemporaryDirectory() as d:
            exe = os.path.join(d, "p")
            build_executable(ir, exe, 2)
            return subprocess.run([exe]).returncode

    BAD = {
        "overflow": "fn main() -> Integer\nis\n    return 9223372036854775807 + 1\nend\n",
        "negate_min": "fn main() -> Integer\nis\n    let m = -9223372036854775807 - 1\n    return -m\nend\n",
        "div_zero": "fn main() -> Integer\nis\n    let z = 1 - 1\n    return 5 / z\nend\n",
        "min_div_minus1": "fn main() -> Integer\nis\n    let m = -9223372036854775807 - 1\n    let k = 0 - 1\n    return m / k\nend\n",
        "oob": "fn main() -> Integer\nis\n    var a: Array[Integer, 3] := fill(1)\n    let i = 2 + 2\n    return a[i]\nend\n",
        "oob_negative": "fn main() -> Integer\nis\n    var a: Array[Integer, 3] := fill(1)\n    let i = 0 - 1\n    return a[i]\nend\n",
    }

    def test_backstop_traps_when_a_proof_would_be_wrong(self):
        import subprocess
        from lise_aot import build_executable
        from lise_codegen import generate
        from lise_lexer import lex
        from lise_parser import Parser
        for name, src in self.BAD.items():
            ir = generate(Parser(lex(src)).parse_program(), "t", 1 << 20)        # NO verifier on purpose
            with tempfile.TemporaryDirectory() as d:
                exe = os.path.join(d, "p")
                build_executable(ir, exe, 2)
                r = subprocess.run([exe], capture_output=True)
            self.assertEqual(r.returncode, 71, f"{name}: the backstop must stop the program with exit status 71")
            self.assertIn(b"internal safety check failed", r.stderr, name)

    def test_stack_bound_rejects_huge_frames(self):
        from lise_codegen import CodegenError, generate
        from lise_lexer import lex
        from lise_parser import Parser
        src = "fn main() -> Integer\nis\n    var a: Array[Integer, 1000000] := fill(0)\n    return a[1]\nend\n"
        with self.assertRaises(CodegenError) as cm:
            generate(Parser(lex(src)).parse_program(), "t")
        self.assertIn("worst-case stack", str(cm.exception))
        generate(Parser(lex(src)).parse_program(), "t", 16 << 20)  # fits under a bigger limit

    def test_stack_bound_sums_call_chain(self):
        from lise_codegen import Codegen
        from lise_lexer import lex
        from lise_parser import Parser
        src = """
fn leaf() -> Integer
is
    var a: Array[Integer, 100] := fill(0)
    return a[0]
end
fn mid() -> Integer
is
    var b: Array[Integer, 100] := fill(0)
    return b[0] + leaf()
end
fn main() -> Integer
is
    return mid()
end
"""
        cg = Codegen(Parser(lex(src)).parse_program(), "t")
        cg.emit_module()
        self.assertGreaterEqual(cg.stack_report["lise_main"], 1600)  # 2 x 800 byte arrays


class BuildsNeverTrustCache(unittest.TestCase):
    def test_build_reports_zero_cached(self):
        import subprocess
        import sys
        with tempfile.TemporaryDirectory() as d:
            ex = os.path.join(HERE, "example_ok_main.lise")
            cli = os.path.join(HERE, "lise.py")
            subprocess.run([sys.executable, cli, "check", ex], cwd=d, capture_output=True)
            r = subprocess.run([sys.executable, cli, "build", ex], cwd=d, capture_output=True, text=True)
            self.assertIn("0 from cache", r.stdout)


class FuzzSmoke(unittest.TestCase):
    @unittest.skipUnless(HAVE_LLVM, "needs llvmlite")
    def test_fuzzer_finds_no_bug_in_a_short_run(self):
        import subprocess
        import sys
        r = subprocess.run([sys.executable, os.path.join(HERE, "fuzz_lise.py"), "25", "7000"],
                           capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertIn("BUGS=0", r.stdout)


class SecondSolver(unittest.TestCase):
    """Every proof must be confirmed by cvc5, an independent solver."""

    SRC = """fn f(x: Integer where value >= 0 and value <= 10) -> Integer
is
    return x + 1
end
"""
    DEAD = """fn g(x: Integer where value >= 0) -> Integer
is
    if x < 0 then
        return 1 / 0
    end
    return x
end
"""

    def with_result(self, src, status, detail=""):
        import lise_xcheck
        real = lise_xcheck.check
        lise_xcheck.check = lambda s, ms: (status, detail)
        try:
            return check_source(src, "t.lise")
        finally:
            lise_xcheck.check = real

    def test_agreement_is_required_and_counted(self):
        rep = check_source(self.SRC, "t.lise")
        self.assertTrue(rep.ok, msgs(rep))
        self.assertEqual(rep.confirmed, rep.obligations)
        self.assertGreater(rep.obligations, 0)

    def test_disagreement_is_a_hard_error(self):
        rep = self.with_result(self.SRC, "sat")
        self.assertFalse(rep.ok)
        self.assertIn("SOLVER DISAGREEMENT", msgs(rep))

    def test_unconfirmed_proof_is_rejected(self):
        rep = self.with_result(self.SRC, "unknown", "timeout")
        self.assertFalse(rep.ok)
        self.assertIn("not confirmed by the second solver", msgs(rep))

    def test_dead_path_pruning_needs_confirmation(self):
        self.assertTrue(check_source(self.DEAD, "t.lise").ok)          # both solvers agree: dead
        rep = self.with_result(self.DEAD, "unknown")                   # cvc5 can't confirm: not pruned
        self.assertFalse(rep.ok)

    def test_cli_has_no_unchecked_flag(self):
        import subprocess
        import sys
        r = subprocess.run([sys.executable, os.path.join(HERE, "lise.py"), "build",
                            os.path.join(HERE, "example_ok_main.lise"), "--unchecked"],
                           capture_output=True, text=True)
        self.assertNotEqual(r.returncode, 0)


FRAME = """record R
    a: Integer where value >= 0 and value <= 10
    c: Integer where value >= 0 and value <= 10
    d: Array[Integer, 3]
end
fn touch_a(r: mutable R)
ensures r.a == 1
is
    r.a := 1
end
fn touch_d(r: mutable R)
is
    r.d[1] := 9
end
fn via(r: mutable R)
is
    touch_a(r)
end
fn main() -> Integer
is
    var r: R := R(5, 7, fill(0))
    touch_a(r)
    assert r.c == 7
    assert r.d[1] == 0
    via(r)
    assert r.c == 7
    return r.c
end
"""


class FrameRule(unittest.TestCase):
    """A call only forgets what the callee can modify; everything else survives."""

    def test_untouched_fields_survive_calls(self):
        rep = check_source(FRAME, "t.lise")
        self.assertTrue(rep.ok, msgs(rep))

    def test_touched_field_is_forgotten(self):
        bad = FRAME.replace("    assert r.c == 7\n    assert r.d[1] == 0", "    assert r.a == 5")
        rep = check_source(bad, "t.lise")
        self.assertFalse(rep.ok)
        self.assertIn("assertion may not hold", msgs(rep))

    def test_array_write_is_forgotten(self):
        bad = FRAME.replace("    touch_a(r)\n    assert r.c == 7\n    assert r.d[1] == 0",
                            "    touch_d(r)\n    assert r.d[1] == 0")
        rep = check_source(bad, "t.lise")
        self.assertFalse(rep.ok)

    def test_transitive_modification_is_forgotten(self):
        bad = FRAME.replace("    via(r)\n    assert r.c == 7", "    via(r)\n    assert r.a == 1")
        rep = check_source(bad, "t.lise")      # via() promises nothing about r.a
        self.assertFalse(rep.ok)

    def test_cache_is_invalidated_when_callee_modifies_more(self):
        """The frame rule makes callers depend on callee BODIES; a stale proof must not be reused."""
        with tempfile.TemporaryDirectory() as d:
            cache = ProofCache(d)
            good = """record R
    a: Integer where value >= 0 and value <= 10
    c: Integer where value >= 0 and value <= 10
end
fn helper(r: mutable R)
is
    r.a := 1
end
fn caller() -> Integer
is
    var r: R := R(5, 7)
    helper(r)
    assert r.c == 7
    return 0
end
"""
            self.assertTrue(check_source(good, "t.lise", cache=cache).ok)
            cache.save()
            worse = good.replace("    r.a := 1\n", "    r.a := 1\n    r.c := 2\n")   # signature unchanged!
            rep = check_source(worse, "t.lise", cache=ProofCache(d))
            self.assertFalse(rep.ok, "stale cached proof of caller() was reused")


RET = """type PositiveSize = Integer where value > 0
type ValidIndex[N: PositiveSize] = Integer where value >= 0 and value < N
record RB[T, N: PositiveSize]
    storage: Array[T, N]
    head: ValidIndex[N]
    tail: ValidIndex[N]
    count: Integer where value >= 0 and value <= N
end
fn make_queue(start: Integer where value >= 0 and value < 4) -> RB[Integer, 4]
ensures result.count == 0
ensures result.head == start
is
    var q: RB[Integer, 4] := RB(fill(5), start, start, 0)
    return q
end
fn zeros() -> Array[Integer, 3]
ensures result[1] == 7
is
    var a: Array[Integer, 3] := fill(7)
    a[2] := 9
    return a
end
fn main() -> Integer
is
    var q: RB[Integer, 4] := make_queue(3)
    assert q.head == 3
    var z: Array[Integer, 3] := zeros()
    return q.head + q.storage[3] % 100 + z[1] + z[2] % 100
end
"""


class ReturnAggregates(unittest.TestCase):
    def ok(self, src):
        rep = check_source(src, "t.lise")
        self.assertTrue(rep.ok, msgs(rep))

    def bad(self, src, text):
        rep = check_source(src, "t.lise")
        self.assertFalse(rep.ok)
        self.assertIn(text, msgs(rep))

    def test_returns_and_callers_use_the_contract(self):
        self.ok(RET)

    def test_caller_cannot_assume_more_than_the_contract(self):
        self.bad(RET.replace("assert q.head == 3", "assert q.tail == 3"), "assertion may not hold")
        self.bad(RET.replace("var z: Array[Integer, 3] := zeros()\n    return",
                             "var z: Array[Integer, 3] := zeros()\n    assert z[2] == 9\n    return"),
                 "assertion may not hold")

    def test_callee_must_prove_its_postcondition(self):
        self.bad(RET.replace("ensures result.count == 0", "ensures result.count == 1"), "postcondition may not hold")
        self.bad(RET.replace("ensures result[1] == 7", "ensures result[2] == 7"), "postcondition may not hold")

    def test_result_must_initialise_a_typed_declaration(self):
        self.bad(RET.replace("var z: Array[Integer, 3] := zeros()", "let z = zeros()"), "must initialise a typed")
        self.bad(RET.replace("var z: Array[Integer, 3] := zeros()", "zeros()\n    var z: Array[Integer, 3] := fill(7)"),
                 "must initialise a typed")

    def test_wrong_declared_type_is_rejected(self):
        self.bad(RET.replace("var z: Array[Integer, 3] := zeros()", "var z: Array[Integer, 4] := zeros()"),
                 "different length")
        self.bad(RET.replace("var q: RB[Integer, 4] := make_queue(3)", "var q: RB[Integer, 8] := make_queue(3)"),
                 "different")

    def test_cannot_return_borrowed_or_moved_or_non_local(self):
        base = """record R
    a: Integer where value >= 0 and value <= 9
end
fn %s
"""
        self.bad(base % "f(x: R) -> R\nis\n    return x\nend", "borrowed")
        self.bad(base % "g(x: mutable R) -> R\nis\n    return x\nend", "borrowed")
        self.bad(base % "h() -> R\nis\n    return R(1)\nend", "local variable")
        self.ok(base % "k() -> R\nis\n    var r: R := R(1)\n    var s: R := R(2)\n    return r\n    return r\nend")  # 2nd return unreachable
        self.ok(base % "m(x: consume R) -> R\nis\n    return x\nend")

    def test_consume_param_roundtrip_keeps_old_facts(self):
        self.ok("""record R
    a: Integer where value >= 0 and value <= 9
end
fn id(x: consume R) -> R
ensures result.a == old(x.a)
is
    return x
end
fn main() -> Integer
is
    var r: R := R(4)
    var s: R := id(r)
    assert s.a == 4
    return s.a
end
""")


@unittest.skipUnless(HAVE_AOT, "needs llvmlite and a C linker for AOT tests")
class AotReturns(AotBuild):
    def test_records_and_arrays_returned_natively(self):
        self.assertEqual(self.build_run(RET), 24)

    def test_generic_return_and_nested_calls(self):
        src = """type PositiveSize = Integer where value > 0
record P[N: PositiveSize]
    xs: Array[Integer, N]
    n: Integer where value >= 0
end
fn make[N: PositiveSize](v: Integer) -> P[N]
ensures result.n == 3
is
    var p: P[N] := P(fill(v), 3)
    return p
end
fn bump(p: mutable P[4]) is
    p.xs[0] := 1
end
fn main() -> Integer
is
    var p: P[4] := make[4](9)
    bump(p)
    return p.n + p.xs[0] % 100 + p.xs[3] % 100
end
"""
        rep = check_source(src, "t.lise")
        self.assertTrue(rep.ok, msgs(rep))
        self.assertEqual(self.build_run(src), 3 + 1 + 9)


class Strings(unittest.TestCase):
    def lex_err(self, src):
        from lise_lexer import LiseError, lex
        with self.assertRaises(LiseError):
            lex(src)

    def test_string_literal_lexing(self):
        from lise_lexer import lex
        t = [x for x in lex('"a\\tb\\n\\\\\\"c"') if x.kind == "STR"]
        self.assertEqual(t[0].text, 'a\tb\n\\"c')

    def test_bad_string_literals_rejected(self):
        self.lex_err('"unterminated')
        self.lex_err('"line\nbreak"')
        self.lex_err('"bad \\q escape"')
        self.lex_err('"non-ascii \u00e9"')
        self.lex_err('"tab\there"')          # raw control characters must be written as escapes

    def check(self, body):
        return check_source("fn main() -> Integer\nis\n" + body + "    return 0\nend\n", "t.lise")

    def test_print_accepts_literals_and_integers(self):
        rep = self.check('    print("hi\\n")\n    print_int(42)\n')
        self.assertTrue(rep.ok, msgs(rep))

    def test_strings_only_as_print_argument(self):
        for body in ('    let s = "x"\n', '    print(5)\n', '    print("a", "b")\n', '    print_int("x")\n',
                     '    print_int(true)\n', '    assert "x" == "x"\n'):
            rep = self.check(body)
            self.assertFalse(rep.ok, body)

    def test_print_int_argument_is_overflow_checked(self):
        rep = self.check("    print_int(9223372036854775807 + 1)\n")
        self.assertFalse(rep.ok)
        self.assertIn("overflow", msgs(rep))

    def test_print_not_allowed_in_contracts_and_not_redefinable(self):
        rep = check_source("fn f() -> Integer\nensures print_int(1) == 0\nis\n    return 0\nend\n", "t.lise")
        self.assertFalse(rep.ok)
        rep = check_source("fn print(x: Integer) -> Integer\nis\n    return x\nend\n", "t.lise")
        self.assertFalse(rep.ok)


@unittest.skipUnless(HAVE_AOT, "needs llvmlite and a C linker for AOT tests")
class AotOutput(unittest.TestCase):
    def run_prog(self, src):
        import subprocess
        from lise_aot import build_executable
        from lise_codegen import generate
        from lise_lexer import lex
        from lise_parser import Parser
        rep = check_source(src, "t.lise")
        self.assertTrue(rep.ok, msgs(rep))
        ir = generate(Parser(lex(src)).parse_program(), "t.lise")
        with tempfile.TemporaryDirectory() as d:
            exe = os.path.join(d, "prog")
            build_executable(ir, exe, 2)
            r = subprocess.run([exe], capture_output=True)
            return r.returncode, r.stdout

    def test_hello(self):
        rc, out = self.run_prog('fn main() -> Integer\nis\n    print("hello, world\\n")\n    return 7\nend\n')
        self.assertEqual((rc, out), (7, b"hello, world\n"))

    def test_print_int_matches_python_on_edge_and_random_values(self):
        import random
        rng = random.Random(1234)
        vals = [0, 1, -1, 9, 10, 11, 99, 100, 101, 999, 1000, 10 ** 9, 10 ** 18, 10 ** 18 - 1, 2 ** 31, -2 ** 31,
                2 ** 32, 2 ** 62, 2 ** 63 - 1, -(2 ** 63 - 1), -(2 ** 63), -(2 ** 63) + 1, 9223372036854775800]
        vals += [rng.randint(-2 ** 63, 2 ** 63 - 1) for _ in range(150)]
        vals += [rng.randint(-1000, 1000) for _ in range(60)]
        vals += [rng.choice([-1, 1]) * 10 ** rng.randint(0, 18) + rng.randint(-1, 1) for _ in range(60)]
        vals = [max(-(2 ** 63), min(2 ** 63 - 1, v)) for v in vals]
        lines = []
        for v in vals:
            e = "(-9223372036854775807 - 1)" if v == -(2 ** 63) else (str(v) if v >= 0 else f"(-{-v})")
            lines.append(f"    print_int({e})\n    print(\"\\n\")")
        src = "fn main() -> Integer\nis\n" + "\n".join(lines) + "\n    return 0\nend\n"
        rc, out = self.run_prog(src)
        self.assertEqual(rc, 0)
        self.assertEqual(out.decode().split("\n")[:-1], [str(v) for v in vals])

    def test_print_in_loops_and_functions(self):
        src = """fn show(n: Integer)
is
    print("n=")
    print_int(n)
    print("\\n")
end
fn main() -> Integer
is
    var i: Integer := 0
    while i < 3
    invariant 0 <= i and i <= 3
    decreases 3 - i
    do
        show(i * 10)
        i := i + 1
    end
    return 0
end
"""
        rc, out = self.run_prog(src)
        self.assertEqual(out, b"n=0\nn=10\nn=20\n")

    def test_runtime_adds_to_stack_bound(self):
        from lise_codegen import Codegen
        from lise_lexer import lex
        from lise_parser import Parser
        cg = Codegen(Parser(lex('fn main() -> Integer\nis\n    print_int(1)\n    return 0\nend\n')).parse_program(), "t")
        cg.emit_module()
        self.assertGreaterEqual(cg.stack_report["lise_main"], 32 + 3 * cg.FRAME_OVERHEAD)


SUM = """fn sum_to(n: Integer where value >= 0 and value <= 20) -> Integer
decreases n max 20
ensures result >= 0 and result <= 1000 * n
is
    if n == 0 then
        return 0
    end
    let t = sum_to(n - 1)
    return n + t
end
"""


class Recursion(unittest.TestCase):
    def ok(self, src):
        rep = check_source(src, "t.lise")
        self.assertTrue(rep.ok, msgs(rep))

    def bad(self, src, text=""):
        rep = check_source(src, "t.lise")
        self.assertFalse(rep.ok)
        self.assertIn(text, msgs(rep))

    def test_structural_recursion_verifies(self):
        self.ok(SUM)

    def test_recursion_needs_a_measure(self):
        self.bad(SUM.replace("decreases n max 20\n", ""), "is recursive")

    def test_non_decreasing_calls_rejected(self):
        for step in ("n", "n + 1", "20", "n * 2"):
            rep = check_source(SUM.replace("sum_to(n - 1)", f"sum_to({step})"), "t.lise")
            self.assertFalse(rep.ok, step)

    def test_measure_must_be_non_negative_and_bounded_on_entry(self):
        self.bad(SUM.replace("n: Integer where value >= 0 and", "n: Integer where value >= -3 and"), "negative")
        self.bad(SUM.replace("decreases n max 20", "decreases n max 10"), "declared maximum")

    def test_measure_can_go_below_zero_only_if_call_is_rejected(self):
        self.bad(SUM.replace("sum_to(n - 1)", "sum_to(n - 2)"), "")     # n = 1: argument -1 / measure < 0

    def test_decreases_clause_must_be_well_formed(self):
        from lise_lexer import LiseError
        for src in (SUM.replace("max 20", ""), SUM.replace("max 20", "max n"), SUM.replace("decreases n max 20",
                    "decreases n max 20\ndecreases n max 20")):
            with self.assertRaises(LiseError):
                check_source(src, "t.lise") if False else __import__("lise_parser").Parser(
                    __import__("lise_lexer").lex(src)).parse_program()

    def test_boolean_measure_rejected(self):
        self.bad(SUM.replace("decreases n max 20", "decreases n > 0 max 20"), "")

    MUTUAL = """fn is_even(n: Integer where value >= 0 and value <= 50) -> Bool
decreases n max 50
ensures result == (n % 2 == 0)
is
    if n == 0 then
        return true
    end
    return is_odd(n - 1)
end
fn is_odd(n: Integer where value >= 0 and value <= 50) -> Bool
decreases n max 50
ensures result == (n % 2 == 1)
is
    if n == 0 then
        return false
    end
    return is_even(n - 1)
end
"""

    def test_mutual_recursion(self):
        self.ok(self.MUTUAL)
        self.bad(self.MUTUAL.replace("return is_even(n - 1)", "return is_even(n)"), "termination")
        self.bad(self.MUTUAL.replace("decreases n max 50\nensures result == (n % 2 == 1)",
                                     "ensures result == (n % 2 == 1)"), "is recursive")

    def test_postcondition_of_recursive_function_is_really_proven(self):
        self.bad(SUM.replace("result <= 1000 * n", "result <= 5 * n"), "postcondition may not hold")

    def test_recursion_through_mutable_record(self):
        self.ok("""record C
    total: Integer where value >= 0 and value <= 1000
end
fn add_down(c: mutable C, n: Integer where value >= 0 and value <= 10)
decreases n max 10
requires c.total + 10 * n <= 1000
ensures c.total == old(c.total) + 10 * n
is
    if n == 0 then
        return
    end
    c.total := c.total + 10
    add_down(c, n - 1)
end
""")

    def test_cache_depends_on_measure(self):
        with tempfile.TemporaryDirectory() as d:
            cache = ProofCache(d)
            self.assertTrue(check_source(SUM, "t.lise", cache=cache).ok)
            cache.save()
            rep = check_source(SUM.replace("sum_to(n - 1)", "sum_to(n)"), "t.lise", cache=ProofCache(d))
            self.assertFalse(rep.ok)


@unittest.skipUnless(HAVE_AOT, "needs llvmlite and a C linker for AOT tests")
class AotRecursion(unittest.TestCase):
    MAIN = """
fn main() -> Integer
is
    print_int(sum_to(%d))
    print("\\n")
    return sum_to(%d) %% 256
end
"""

    def build(self, src, opt=2, stack_limit=1 << 20):
        from lise_aot import build_executable
        from lise_codegen import Codegen
        from lise_lexer import lex
        from lise_parser import Parser
        cg = Codegen(Parser(lex(src)).parse_program(), "t", stack_limit)
        ir = cg.emit_module()
        d = tempfile.mkdtemp()
        exe = os.path.join(d, "prog")
        build_executable(ir, exe, opt)
        return exe, cg

    def test_recursive_program_runs(self):
        import subprocess
        src = SUM + self.MAIN % (20, 20)
        self.assertTrue(check_source(src, "t.lise").ok)
        exe, _ = self.build(src)
        r = subprocess.run([exe], capture_output=True)
        self.assertEqual((r.returncode, r.stdout), (210, b"210\n"))

    def test_mutual_recursion_runs(self):
        import subprocess
        src = Recursion.MUTUAL + """
fn main() -> Integer
is
    if is_even(40) and is_odd(37) then
        return 11
    end
    return 22
end
"""
        self.assertTrue(check_source(src, "t.lise").ok)
        exe, _ = self.build(src)
        self.assertEqual(subprocess.run([exe]).returncode, 11)

    def test_stack_bound_covers_depth_times_frame(self):
        src = SUM + self.MAIN % (20, 20)
        _, cg = self.build(src)
        self.assertGreaterEqual(cg.stack_report["lise_sum_to"], 21 * cg.FRAME_OVERHEAD)   # (max 20 + 1) frames

    def test_too_deep_recursion_is_a_compile_error(self):
        from lise_codegen import CodegenError
        big = SUM.replace("value <= 20", "value <= 1000000").replace("max 20", "max 1000000") \
                 .replace("result <= 1000 * n", "result <= 1000000 * n")
        with self.assertRaises(CodegenError) as cm:
            self.build(big + "fn main() -> Integer\nis\n    return sum_to(3)\nend\n")
        self.assertIn("worst-case stack", str(cm.exception))

    def test_bound_holds_on_a_real_small_stack(self):
        """Run an unoptimised recursive program (largest frames) under an OS stack limit equal to
        the computed bound plus slack: it must finish.  With a far smaller limit it must crash
        (proving the test can fail)."""
        import resource
        import subprocess
        src = SUM.replace("value <= 20", "value <= 1000").replace("max 20", "max 1000") \
                 .replace("result <= 1000 * n", "result <= 1000 * n") + self.MAIN % (1000, 1000)
        self.assertTrue(check_source(src, "t.lise").ok)
        exe, cg = self.build(src, opt=0)
        bound = cg.stack_report["lise_main"]

        def limit(n):
            return lambda: resource.setrlimit(resource.RLIMIT_STACK, (n, n))

        ok = subprocess.run([exe], capture_output=True, preexec_fn=limit(bound + 256 * 1024))
        self.assertEqual(ok.returncode, 1000 * 1001 // 2 % 256, ok.stderr)
        crash = subprocess.run([exe], capture_output=True, preexec_fn=limit(24 * 1024))
        self.assertLess(crash.returncode, 0, "a 24 KiB stack must overflow at depth 1000")


def random_formula(rng, depth=3):
    """Random integer/boolean formula over small variables (for testing the independent checker)."""
    import z3
    xs = [z3.Int(n) for n in "xyz"]
    ps = [z3.Bool(n) for n in "pq"]
    arr = z3.Array("a", z3.IntSort(), z3.IntSort())

    def term(d):
        r = rng.random()
        if d == 0 or r < .3:
            return rng.choice(xs) if rng.random() < .7 else z3.IntVal(rng.randint(-9, 9))
        if r < .5:
            return term(d - 1) + term(d - 1)
        if r < .6:
            return term(d - 1) - term(d - 1)
        if r < .7:
            return rng.choice([-3, -2, 2, 3, 5]) * term(d - 1)
        if r < .78:
            return term(d - 1) / rng.choice([2, 3, -3, 5, 7])
        if r < .86:
            return term(d - 1) % rng.choice([2, 3, -3, 4, 7])
        if r < .92:
            return z3.If(formula(d - 1), term(d - 1), term(d - 1))
        if r < .96:
            return term(d - 1) * term(d - 1)              # nonlinear: abstracted
        return arr[term(d - 1)]                            # array read: abstracted

    def atom(d):
        a, b = term(d), term(d)
        return rng.choice([a < b, a <= b, a > b, a >= b, a == b, a != b])

    def formula(d):
        r = rng.random()
        if d == 0 or r < .35:
            return atom(max(d - 1, 0)) if rng.random() < .85 else rng.choice(ps)
        if r < .55:
            return z3.And(formula(d - 1), formula(d - 1))
        if r < .75:
            return z3.Or(formula(d - 1), formula(d - 1))
        if r < .85:
            return z3.Not(formula(d - 1))
        if r < .92:
            return z3.Implies(formula(d - 1), formula(d - 1))
        if r < .96:
            return formula(d - 1) == formula(d - 1)
        return z3.If(formula(d - 1), formula(d - 1), formula(d - 1))

    bounds = [z3.And(x >= -rng.randint(0, 9), x <= rng.randint(0, 9)) for x in xs if rng.random() < .7]
    return bounds + [formula(depth) for _ in range(rng.randint(1, 3))]


class IndependentChecker(unittest.TestCase):
    """lise_fmcheck shares no code with Z3/cvc5.  It must never claim UNSAT for a satisfiable formula."""

    def test_known_cases(self):
        import z3
        import lise_fmcheck as fm
        x, y, n, i, j = z3.Ints("x y n i j")
        a = z3.Array("a", z3.IntSort(), z3.IntSort())
        unsat = [[x >= 0, x <= 10, x + 1 > 11], [2 * x == 1], [x >= 0, x <= 8, x / 3 > 2], [x % 4 < 0],
                 [z3.If(x > 0, y == x, y == 0 - x), y < 0], [z3.Implies(x > 3, y > 3), x > 5, y < 2],
                 [a[x] > 5, a[x] < 3], [x * y > 5, x * y < 3], [x > y, y > x], [3 * x + 3 * y == 1],
                 [x >= 0, x <= 10, y >= 0, y <= 10, x * y > 100], [x * x < 0], [x * y != y * x],
                 [n >= 1, n <= 8, x >= 0, x % n >= n], [n > 0, i >= 0, i < n, (i + 1) % n >= n],
                 [n < 0, x % n >= -n], [n >= 1, x >= 0, x / n > x], [x > -1000, x < 1000, n > -1000, n < 1000, n != 0,
                                                                     x / n > 1000],
                 [z3.Store(a, i, 5)[i] != 5], [i != j, z3.Store(a, i, 5)[j] != a[j]], [i == j, a[i] != a[j]],
                 [z3.K(z3.IntSort(), 7)[i] != 7], [n == 0, n % 2 != 0], [n == 1, n % 2 == 0],
                 [x >= 9, x <= 10, y >= 9, y <= 10, x * y < 5]]          # needs the McCormick lower envelope, not just corners
        for asrt in unsat:
            self.assertEqual(fm.check_assertions(asrt)[0], fm.UNSAT, asrt)
        sat = [[x % 4 == 3], [x > 0, y > 0, x + y < 5], [x / 2 == -3], [x * y == 6], [x >= 0, x <= 2 ** 63 - 1, x + 1 > 2 ** 63 - 1],
               [n >= 2, x % n == 1], [x >= 1, x <= 3, y >= 1, y <= 3, x * y == 2], [x >= 1, x <= 3, y >= 1, y <= 3, x * y == 4],
               [n >= 1, n <= 3, x >= 0, x <= 10, x / n == 5], [n >= -3, n <= -1, x >= 0, x <= 10, x / n == -5]]
        for asrt in sat:
            status, detail, env = fm.check_assertions_env(asrt)
            self.assertEqual(status, fm.SAT, asrt)
            s = z3.Solver()                     # the model it found must really satisfy the assertions (z3 as test oracle)
            s.add(*asrt)
            s.add(*[z3.Int(k) == v for k, v in env.items() if isinstance(v, int)])
            self.assertEqual(s.check(), z3.sat, (asrt, env))

    def test_never_wrong_in_either_direction_on_random_formulas(self):
        """UNSAT only for unsatisfiable formulas, SAT only with a model that really satisfies them."""
        import random
        import z3
        import lise_fmcheck as fm
        rng = random.Random(int(os.environ.get("LISE_FM_SEED", "20260101")))
        confirmed = sat_found = z3_unsat = 0
        n = int(os.environ.get("LISE_FM_CASES", "150"))
        for i in range(n):
            asrt = random_formula(rng, rng.choice([1, 2, 3]))
            s = z3.Solver()
            s.set("timeout", 3000)
            s.add(*asrt)
            truth = s.check()
            status, detail, env = fm.check_assertions_env(asrt)
            if status == fm.UNSAT:
                self.assertEqual(truth, z3.unsat, f"UNSOUND (claimed unsat) on case {i}: {asrt}")
                confirmed += 1
            elif status == fm.SAT:
                self.assertEqual(truth, z3.sat, f"WRONG (claimed a counterexample) on case {i}: {asrt} {detail}")
                sat_found += 1
            z3_unsat += truth == z3.unsat
        self.assertGreater(z3_unsat, n // 8, "generator produced too few unsatisfiable formulas")
        self.assertGreater(confirmed, z3_unsat // 2, f"checker confirmed only {confirmed}/{z3_unsat}")
        self.assertGreater(sat_found, 0)


class IndependentGate(unittest.TestCase):
    """Z3 and cvc5 are not enough: the solver-free checker must re-derive every proof, and it can stop the
    build on its own by finding a verified counterexample."""
    LINEAR = "fn f(x: Integer where value >= 0 and value <= 100) -> Integer\nensures result == x + 1\nis\n    return x + 1\nend\n"
    BOUNDED_PRODUCT = "fn f(x: Integer where value >= 0 and value <= 100) -> Integer\nensures result >= 0\nis\n    return x * x\nend\n"
    BEYOND = "fn f(x: Integer, y: Integer) -> Integer\nensures x * x * x * x + y * y * y * y >= 2 * x * x * y * y\nis\n    return 0\nend\n"
    OVERFLOW = "fn f(x: Integer where value >= 0 and value <= 9223372036854775807) -> Integer\nis\n    return x + 1\nend\n"

    def test_linear_and_bounded_nonlinear_proofs_are_rederived(self):
        for src in (self.LINEAR, self.BOUNDED_PRODUCT):
            rep = check_source(src, "t.lise")
            self.assertTrue(rep.ok, msgs(rep))
            self.assertEqual(rep.fm_confirmed, rep.obligations)

    def test_what_the_checker_cannot_rederive_is_rejected(self):
        import lise_xcheck
        real = lise_xcheck.check
        lise_xcheck.check = lambda s, ms: ("unsat", "")        # a true statement that both solvers accept ...
        try:
            rep = check_source(self.BEYOND, "t.lise")
        finally:
            lise_xcheck.check = real
        self.assertFalse(rep.ok)                                  # ... but the checker cannot re-derive: rejected
        self.assertIn("not independently confirmed", msgs(rep))

    def test_there_is_no_way_to_turn_the_gate_off_in_the_cli(self):
        import subprocess
        import sys
        with tempfile.TemporaryDirectory() as d:
            path = os.path.join(d, "b.lise")
            open(path, "w").write(self.BEYOND)
            for flag in ([], ["--independent"], ["--no-independent"]):
                r = subprocess.run([sys.executable, os.path.join(HERE, "lise.py"), "check", path, "--no-cache"] + flag,
                                   capture_output=True, text=True, cwd=d)
                self.assertNotEqual(r.returncode, 0, flag)

    def test_checker_stops_the_build_when_both_solvers_wrongly_accept(self):
        """Simulate a soundness bug in BOTH solvers: they claim every obligation is proved."""
        import z3
        import lise_xcheck
        rep = check_source(self.OVERFLOW, "t.lise")                  # sanity: the real verdict is "overflow"
        self.assertFalse(rep.ok)
        real_check, real_xcheck = z3.Solver.check, lise_xcheck.check
        z3.Solver.check = lambda self, *a: z3.unsat
        lise_xcheck.check = lambda s, ms: ("unsat", "")
        try:
            rep = check_source(self.OVERFLOW, "t.lise")
        finally:
            z3.Solver.check, lise_xcheck.check = real_check, real_xcheck
        self.assertFalse(rep.ok)
        text = msgs(rep)
        self.assertIn("INDEPENDENT CHECKER DISAGREES", text)
        self.assertIn("x@0 = 9223372036854775807", text)               # the verified counterexample

    def test_gate_also_guards_dead_path_pruning(self):
        import z3
        import lise_xcheck
        # a branch that is NOT dead, but both solvers claim it is: it must still be checked (and rejected)
        src = "fn f(x: Integer where value >= 0 and value <= 9) -> Integer\nis\n    if x > 4 then\n        return 1 / (x - x)\n    end\n    return 0\nend\n"
        self.assertFalse(check_source(src, "t.lise").ok)
        real_check, real_xcheck = z3.Solver.check, lise_xcheck.check
        z3.Solver.check = lambda self, *a: z3.unsat
        lise_xcheck.check = lambda s, ms: ("unsat", "")
        try:
            rep = check_source(src, "t.lise")
        finally:
            z3.Solver.check, lise_xcheck.check = real_check, real_xcheck
        self.assertFalse(rep.ok)


def interpret(src, fn=None, args=()):
    import sys
    from lise_lexer import lex
    from lise_parser import Parser
    from lise_semantics import Machine
    sys.setrecursionlimit(50000)
    m = Machine(Parser(lex(src)).parse_program())
    return m.run_main() if fn is None else m.run_function(fn, args)


class ReferenceSemantics(unittest.TestCase):
    """The executable semantics: what a program means, including every way it can get stuck."""

    def stuck(self, src, kind, fn=None, args=()):
        from lise_semantics import Stuck
        with self.assertRaises(Stuck) as cm:
            interpret(src, fn, args)
        self.assertEqual(cm.exception.kind, kind, str(cm.exception))

    def main(self, body, pre=""):
        return pre + "fn main() -> Integer\nis\n" + body + "end\n"

    def test_euclidean_division_and_remainder(self):
        src = """fn f(a: Integer, b: Integer where value != 0) -> Integer
is
    return (a / b) * 1000 + a % b
end
"""
        for a in (7, -7, 0, 5, -5, 100, -100):
            for b in (2, -2, 7, -7, 1, -1, 3):
                r = a % abs(b)
                self.assertEqual(interpret(src, "f", (a, b))[0], ((a - r) // b) * 1000 + r, (a, b))

    def test_stuck_states(self):
        M = self.main
        self.stuck(M("    return 9223372036854775807 + 1\n"), "overflow")
        self.stuck(M("    let m = -9223372036854775807 - 1\n    return -m\n"), "overflow")
        self.stuck(M("    let z = 0\n    return 5 / z\n"), "div_zero")
        self.stuck(M("    let z = 0\n    return 5 % z\n"), "div_zero")
        self.stuck(M("    let m = -9223372036854775807 - 1\n    let k = -1\n    return m / k\n"), "overflow")
        self.stuck(M("    var a: Array[Integer, 3] := fill(0)\n    var i: Integer := 3\n    return a[i]\n"), "index")
        self.stuck(M("    var a: Array[Integer, 3] := fill(0)\n    var i: Integer := -1\n    a[i] := 1\n    return 0\n"), "index")
        self.stuck(M("    assert 1 == 2\n    return 0\n"), "assert")
        self.stuck(M("    var x: Integer where value >= 0 := 5\n    x := -1\n    return x\n"), "refinement")
        self.stuck(M("    let x: Integer where value > 3 = 2\n    return x\n"), "refinement")
        self.stuck(M("    var i: Integer := 0\n    while i < 3\n    invariant i < 2\n    do\n        i := i + 1\n    end\n    return 0\n"),
                   "invariant")
        self.stuck(M("    var i: Integer := 0\n    while i < 3\n    decreases 3 - i\n    do\n    end\n    return 0\n"), "measure")
        self.stuck("fn f() -> Integer\nensures result == 2\nis\n    return 1\nend\n", "postcondition", "f")
        self.stuck("fn f(x: Integer) -> Integer\nrequires x > 0\nis\n    return x\nend\n", "precondition", "f", (0,))
        self.stuck("fn f(x: Integer where value > 0) -> Integer\nis\n    return x\nend\n", "refinement", "f", (0,))
        self.stuck("fn f(x: Integer) -> Integer\nis\n    if x > 0 then\n        return 1\n    end\nend\n", "fell_off", "f", (0,))

    def test_contracts_use_unbounded_integers_but_code_does_not(self):
        ok = "fn f(x: Integer where value >= 0 and value <= 10) -> Integer\nensures 4611686018427387904 * x >= 0\nis\n    return x\nend\n"
        self.assertEqual(interpret(ok, "f", (9,))[0], 9)
        self.stuck("fn f(x: Integer where value >= 0 and value <= 10) -> Integer\nis\n    return 4611686018427387904 * x\nend\n",
                   "overflow", "f", (9,))

    def test_short_circuit_and_old_and_result(self):
        src = """fn f(x: Integer where value >= 0 and value <= 5) -> Integer
ensures result == old(x) + 1
is
    var y: Integer := x
    y := y + 1
    if x > 100 and 1 / (x - x) == 0 then
        return 0
    end
    if x == 0 or 1 / x == 1 then
        y := y
    end
    return y
end
"""
        for x in range(0, 6):
            self.assertEqual(interpret(src, "f", (x,))[0], x + 1)

    def test_mutable_scalar_parameter_aliases_caller_storage(self):
        src = """record R
    a: Integer where value >= 0 and value <= 9
end
fn bump(x: mutable Integer where value >= 0 and value <= 9)
is
    x := x + 1
end
fn main() -> Integer
is
    var r: R := R(4)
    bump(r.a)
    var arr: Array[Integer, 2] := fill(7)
    bump(arr[1])
    return r.a * 10 + arr[1] - 8 + 1
end
"""
        # r.a == 5; arr[1] == 8  ->  5*10 + 8 - 8 + 1 ... bump on arr[1] (7 -> 8)
        self.assertEqual(interpret(src)[0], 5 * 10 + 8 - 8 + 1)
        self.stuck(src.replace("R(4)", "R(9)"), "refinement")          # 9 + 1 violates the field type

    def test_record_invariant_is_checked_at_construction_and_return(self):
        src = """record P where lo <= hi
    lo: Integer
    hi: Integer
end
fn main() -> Integer
is
    var p: P := P(%s, %s)
    return p.hi - p.lo
end
"""
        self.assertEqual(interpret(src % (1, 5))[0], 4)
        self.stuck(src % (5, 1), "invariant")

    def test_loop_and_recursion_measures(self):
        self.stuck(SUM.replace("sum_to(n - 1)", "sum_to(n)") + "fn main() -> Integer\nis\n    return sum_to(3)\nend\n",
                   "measure")
        self.assertEqual(interpret(SUM + "fn main() -> Integer\nis\n    return sum_to(5)\nend\n")[0], 15)

    def test_outcome_enum_and_print(self):
        self.assertEqual(interpret(QUEUE), (42, ""))
        src = 'fn main() -> Integer\nis\n    print("a\\n")\n    print_int(-5)\n    print("\\t!")\n    return 300\nend\n'
        self.assertEqual(interpret(src), (300 & 0xFF, "a\n-5\t!"))


@unittest.skipUnless(HAVE_AOT, "needs llvmlite and a C linker for AOT tests")
class ReferenceVsNative(unittest.TestCase):
    """The compiled program must do exactly what the reference semantics says."""

    def native(self, src):
        import subprocess
        from lise_aot import build_executable
        from lise_codegen import generate
        from lise_lexer import lex
        from lise_parser import Parser
        ir = generate(Parser(lex(src)).parse_program(), "t.lise")
        with tempfile.TemporaryDirectory() as d:
            exe = os.path.join(d, "prog")
            build_executable(ir, exe, 2)
            r = subprocess.run([exe], capture_output=True)
            return r.returncode, r.stdout.decode()

    def test_all_example_programs_agree(self):
        import glob
        n = 0
        for path in sorted(glob.glob(os.path.join(HERE, "example_ok_*.lise"))):
            src = open(path, encoding="utf-8").read()
            if "fn main()" not in src:
                continue
            rep = check_source(src, path, lints=True)
            self.assertTrue(rep.ok, path + "\n" + msgs(rep))
            self.assertEqual(self.native(src), interpret(src), os.path.basename(path))
            n += 1
        self.assertGreaterEqual(n, 4)

    def test_test_suite_programs_agree(self):
        for src in (QUEUE, RET, SUM + "fn main() -> Integer\nis\n    print_int(sum_to(20))\n    return sum_to(7)\nend\n",
                    Recursion.MUTUAL + "fn main() -> Integer\nis\n    if is_even(40) and is_odd(37) then\n        return 11\n    end\n    return 22\nend\n"):
            self.assertTrue(check_source(src, "t.lise").ok)
            self.assertEqual(self.native(src), interpret(src))


OWN = """record R
    a: Integer where value >= 0 and value <= 9
    b: Integer where value >= 0 and value <= 9
end
fn take(r: consume R) -> Integer
is
    return r.a
end
fn peek(r: R) -> Integer
is
    return r.a
end
fn bump(r: mutable R)
is
    r.a := 1
end
fn both(x: mutable R, y: R) -> Integer
is
    x.a := 2
    return y.b
end
"""


class OwnershipRules(unittest.TestCase):
    """Each rule is enforced twice, independently: statically by the verifier and dynamically (by
    storage identity) by the reference semantics.  Rule-breaking programs must be rejected by the
    verifier AND be STUCK(ownership) when interpreted; good programs must do neither."""

    def program(self, body):
        return OWN + "fn main() -> Integer\nis\n" + body + "    return 0\nend\n"

    BAD = {
        "use after move": "    var r: R := R(1, 2)\n    let x = take(r)\n    let y = peek(r)\n",
        "double move": "    var r: R := R(1, 2)\n    let x = take(r)\n    let y = take(r)\n",
        "field of moved": "    var r: R := R(1, 2)\n    let x = take(r)\n    r.a := 3\n",
        "assign to let": "    let r: R = R(1, 2)\n    r.a := 3\n",
        "mutable arg is let": "    let r: R = R(1, 2)\n    bump(r)\n",
        "aliased mutable args": "    var r: R := R(1, 2)\n    let x = both(r, r)\n",
        "mutable arg also read": "    var r: R := R(1, 2)\n    var s: Integer := 0\n    mix2(r, r.a)\n",
        "moved in a loop": "    var r: R := R(1, 2)\n    var i: Integer := 0\n    while i < 2\n    invariant 0 <= i and i <= 2\n    decreases 2 - i\n    do\n        let x = take(r)\n        i := i + 1\n    end\n",
        "conditional move then use": "    var r: R := R(1, 2)\n    if 1 == 1 then\n        let x = take(r)\n    end\n    let y = peek(r)\n",
    }
    GOOD = {
        "plain": "    var r: R := R(1, 2)\n    let x = peek(r)\n    bump(r)\n    let y = take(r)\n",
        "two records": "    var r: R := R(1, 2)\n    var s: R := R(3, 4)\n    let x = both(r, s)\n    let y = take(s)\n",
        "disjoint fields are conservatively refused": None,
    }

    def test_rule_breaking_programs_are_rejected_and_stuck(self):
        from lise_semantics import Stuck
        src_extra = "fn mix2(x: mutable R, k: Integer where value >= 0 and value <= 9)\nis\n    x.a := k\nend\n"
        for name, body in self.BAD.items():
            src = OWN + src_extra + "fn main() -> Integer\nis\n" + body + "    return 0\nend\n"
            rep = check_source(src, "t.lise")
            self.assertFalse(rep.ok, f"verifier accepted: {name}")
            with self.assertRaises(Stuck, msg=name) as cm:
                interpret(src)
            self.assertEqual(cm.exception.kind, "ownership", f"{name}: {cm.exception}")

    def test_good_programs_are_accepted_and_run(self):
        for name, body in self.GOOD.items():
            if body is None:
                continue
            src = self.program(body)
            self.assertTrue(check_source(src, "t.lise").ok, name)
            self.assertEqual(interpret(src)[0], 0)

    def test_moving_borrowed_parameters_and_fields(self):
        from lise_semantics import Stuck
        for helper in ("fn f(r: R) -> Integer\nis\n    return take(r)\nend\n",
                       "fn f(r: mutable R) -> Integer\nis\n    return take(r)\nend\n",
                       "fn f(r: R)\nis\n    r.a := 1\nend\n"):
            src = OWN + helper + "fn main() -> Integer\nis\n    var r: R := R(1, 2)\n    return 0\nend\n"
            self.assertFalse(check_source(src, "t.lise").ok, helper)
            call = OWN + helper + "fn main() -> Integer\nis\n    var r: R := R(1, 2)\n    f(r)\n    return 0\nend\n"
            with self.assertRaises(Stuck):
                interpret(call.replace("    f(r)\n", "    let z = f(r)\n") if "-> Integer" in helper else call)

    def test_reinitialising_a_moved_variable_is_allowed(self):
        src = """fn main() -> Integer
is
    var n: Integer := 5
    n := n + 1
    return n
end
"""
        self.assertTrue(check_source(src, "t.lise").ok)
        self.assertEqual(interpret(src)[0], 6)

    def test_generic_type_parameters_are_move_only_inside_the_function(self):
        gen = """record Box[T]
    item: T
end
fn dup[T](x: consume T, b: mutable Box[T]) -> Integer
is
    b.item := x
    b.item := x
    return 0
end
fn main() -> Integer
is
    var b: Box[Integer] := Box(1)
    return dup[Integer](2, b)
end
"""
        from lise_semantics import Stuck
        self.assertFalse(check_source(gen, "t.lise").ok)                  # x moved twice
        with self.assertRaises(Stuck) as cm:
            interpret(gen)
        self.assertEqual(cm.exception.kind, "ownership")
        ok = gen.replace("    b.item := x\n    b.item := x\n", "    b.item := x\n")
        self.assertTrue(check_source(ok, "t.lise").ok, msgs(check_source(ok, "t.lise")))
        self.assertEqual(interpret(ok)[0], 0)
        # a CONCRETE type is Copy: the same double assignment is fine when T is written as Integer
        concrete = """record Box2
    item: Integer
end
fn dup2(x: Integer, b: mutable Box2) -> Integer
is
    b.item := x
    b.item := x
    return 0
end
fn main() -> Integer
is
    var b: Box2 := Box2(1)
    return dup2(2, b)
end
"""
        self.assertTrue(check_source(concrete, "t.lise").ok)
        self.assertEqual(interpret(concrete)[0], 0)


class OwnershipFuzzSmoke(unittest.TestCase):
    def test_ownership_fuzzer_finds_nothing_in_a_short_run(self):
        import subprocess
        import sys
        r = subprocess.run([sys.executable, os.path.join(HERE, "fuzz_own.py"), "30", "9000"],
                           capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertIn("BUGS=0", r.stdout)


class DeveloperGuards(unittest.TestCase):
    """Mistakes a tired developer makes are build errors, not warnings: unused values (including ignored
    results), contradictory preconditions, code that can never run, self-assignment."""

    def lint(self, src):
        return check_source(src, "t.lise", lints=True)

    def bad(self, src, text):
        rep = self.lint(src)
        self.assertFalse(rep.ok, "accepted: " + src)
        self.assertIn(text, msgs(rep))

    def ok(self, src):
        rep = self.lint(src)
        self.assertTrue(rep.ok, msgs(rep))

    def fn(self, body, params="x: Integer where value >= 0 and value <= 9", extra=""):
        return f"fn f({params}) -> Integer\n{extra}is\n{body}end\n"

    def test_unused_variables_and_ignored_results(self):
        self.bad(self.fn("    let y = 5\n    return x\n"), "variable 'y' is never read")
        self.bad(self.fn("    var y: Integer := 1\n    y := 2\n    return x\n"), "variable 'y' is never read")
        self.bad("fn g() -> Integer\nis\n    return 1\nend\n" + self.fn("    let r = g()\n    return x\n"), "never read")
        self.ok(self.fn("    let _y = 5\n    return x\n"))                         # explicit "ignore on purpose"
        self.ok(self.fn("    let y = x + 1\n    return y\n"))

    def test_ignored_outcome_is_caught_even_when_bound_to_a_name(self):
        self.bad(RET.replace("var q: RB[Integer, 4] := make_queue(3)\n    assert q.head == 3",
                             "var q: RB[Integer, 4] := make_queue(3)\n    let ignored = zeros()\n    assert q.head == 3")
                 .replace("var z: Array[Integer, 3] := zeros()", "var z: Array[Integer, 3] := fill(7)"), "never read")

    def test_unused_parameters(self):
        self.bad(self.fn("    return 1\n"), "parameter 'x' is never used")
        self.ok(self.fn("    return 1\n", params="_x: Integer"))
        self.ok(self.fn("    return 1\n", extra="ensures x >= 0\n"))                 # used in a contract: fine
        self.ok("fn f(r: mutable R2)\nis\n    r.a := 1\nend\nrecord R2\n    a: Integer where value >= 0 and value <= 9\nend\n")

    def test_contradictory_preconditions_are_vacuous(self):
        self.bad(self.fn("    return x\n", extra="requires x > 5 and x < 3\n"), "contradictory")
        self.bad(self.fn("    return x\n", extra="requires x > 100\n"), "contradictory")      # clashes with x <= 9
        self.ok(self.fn("    return x\n", extra="requires x > 3\n"))

    def test_unreachable_code(self):
        self.bad(self.fn("    return x\n    return 1\n"), "unreachable code")
        self.bad(self.fn("    if x > 100 then\n        return 1\n    end\n    return x\n"), "can never be true")
        self.bad(self.fn("    if x < 100 then\n        return 1\n    end\n    return 0\n"), "always true")
        self.bad(self.fn("    if x < 100 then\n        return 1\n    else\n        return 2\n    end\n"), "`else` branch can never run")
        self.ok(self.fn("    if x > 4 then\n        return 1\n    end\n    return x\n"))
        self.ok(self.fn("    if x > 4 then\n        return 1\n    else\n        return 2\n    end\n"))

    def test_branch_live_in_only_some_paths_is_fine(self):
        self.ok("fn f(a: Integer where value >= 0 and value <= 1, b: Integer where value >= 0 and value <= 1) -> Integer\nis\n"
                "    var r: Integer := 0\n    if a == 1 then\n        r := 1\n    end\n    if r == 1 then\n        r := 5\n    end\n"
                "    return r + b\nend\n")

    def test_self_assignment(self):
        self.bad(self.fn("    var y: Integer := x\n    y := y\n    return y\n"), "assigned to itself")

    def test_lints_are_on_in_the_cli_and_cannot_be_disabled(self):
        import subprocess
        import sys
        with tempfile.TemporaryDirectory() as d:
            path = os.path.join(d, "l.lise")
            with open(path, "w") as f:
                f.write(self.fn("    let y = 5\n    return x\n"))
            for flags in ([], ["--no-lints"], ["--no-cache"]):
                r = subprocess.run([sys.executable, os.path.join(HERE, "lise.py"), "check", path] + flags,
                                   capture_output=True, text=True, cwd=d)
                self.assertNotEqual(r.returncode, 0, flags)
            self.assertIn("lint:", r.stdout)


def cert_con(coeffs, const):
    return [[[v, a] for v, a in sorted(coeffs.items())], const]


class CertificateValidator(unittest.TestCase):
    """lise_certcheck is the small trusted core (standard library only).  It must accept good certificates
    and reject every kind of bogus one."""

    def verify(self, formulas, proof, rels=()):
        import lise_certcheck as cc
        return cc.verify({"version": 1, "formulas": formulas, "rels": [list(r) for r in rels], "proof": proof})[0]

    LO1 = ["lit", cert_con({"x": -1}, 1)]          # x >= 1
    HI0 = ["lit", cert_con({"x": 1}, 0)]           # x <= 0

    def test_valid_certificates_are_accepted(self):
        self.assertTrue(self.verify([self.LO1, self.HI0], ["derive", [["comb", 1, 0, "x"], ["contra", 2]]]))
        # 2x == 1 over the integers needs tightening
        two = [["lit", cert_con({"x": 2}, -1)], ["lit", cert_con({"x": -2}, 1)]]
        self.assertTrue(self.verify(two, ["derive", [["tighten", 0], ["tighten", 1], ["comb", 2, 3, "x"], ["contra", 4]]]))
        # a case split: (x <= 0 or x >= 5) and 1 <= x <= 4   (facts: 0 = the chosen alternative, 1 = x>=1, 2 = x<=4)
        f = [["or", [["lit", cert_con({"x": 1}, 0)], ["lit", cert_con({"x": -1}, 5)]]],
             ["lit", cert_con({"x": -1}, 1)], ["lit", cert_con({"x": 1}, -4)]]
        self.assertTrue(self.verify(f, ["split", [["derive", [["comb", 0, 1, "x"], ["contra", 3]]],
                                                   ["derive", [["comb", 2, 0, "x"], ["contra", 3]]]]]))

    def test_bogus_certificates_are_rejected(self):
        feasible = [["lit", cert_con({"x": -1}, 1)], ["lit", cert_con({"x": 2}, -2)]]        # x >= 1, 2x <= 2: x = 1 works
        self.assertFalse(self.verify(feasible, ["derive", [["tighten", 1], ["comb", 2, 0, "x"], ["contra", 3]]]))
        same_sign = [["lit", cert_con({"x": 1}, -5)], ["lit", cert_con({"x": 1}, -3)]]       # combining two upper bounds
        self.assertFalse(self.verify(same_sign, ["derive", [["comb", 0, 1, "x"], ["contra", 2]]]))
        zero = [["lit", cert_con({"x": 1}, 0)], ["lit", cert_con({"x": -1}, 0)]]            # 0 <= 0 is no contradiction
        self.assertFalse(self.verify(zero, ["derive", [["comb", 0, 1, "x"], ["contra", 2]]]))
        orf = ["or", [["lit", cert_con({"x": 1}, 0)], ["lit", cert_con({"x": -1}, 5)]]]       # incomplete case split
        f = [orf, ["lit", cert_con({"x": -1}, 1)], ["lit", cert_con({"x": 1}, -4)]]
        self.assertFalse(self.verify(f, ["split", [["derive", [["comb", 0, 1, "x"], ["contra", 3]]]]]))
        self.assertFalse(self.verify(f, ["derive", [["contra", 0]]]))
        self.assertFalse(self.verify([self.LO1, self.HI0], ["closed"]))
        self.assertFalse(self.verify([self.LO1, self.HI0], ["closed", [["comb", 1, 0, "x"], ["contra", 2]]]))   # wrong node kind
        self.assertFalse(self.verify([self.LO1, self.HI0], ["derive", [["comb", 1, 0, "x"]]]))          # no contradiction step
        self.assertFalse(self.verify([self.LO1, self.HI0], ["derive", [["contra", 7]]]))                # dangling reference
        self.assertFalse(self.verify([self.LO1], ["derive", [["comb", 0, 0, "x"], ["contra", 1]]]))

    def test_product_facts_are_recomputed_not_trusted(self):
        rels = [("a", "b", "m")]
        lo_a, hi_a = ["lit", cert_con({"a": -1}, 0)], ["lit", cert_con({"a": 1}, -10)]      # 0 <= a <= 10
        lo_b, hi_b = ["lit", cert_con({"b": -1}, 0)], ["lit", cert_con({"b": 1}, -10)]
        big = ["lit", cert_con({"m": -1}, 101)]                                            # m >= 101
        f = [lo_a, hi_a, lo_b, hi_b, big]
        good = ["derive", [["pf", "chi", 0, 0, 1, 2, 3], ["comb", 5, 4, "m"], ["contra", 6]]]
        self.assertTrue(self.verify(f, good, rels))
        bad_refs = ["derive", [["pf", "chi", 0, 1, 1, 2, 3], ["comb", 5, 4, "m"], ["contra", 6]]]   # wrong bound references
        self.assertFalse(self.verify(f, bad_refs, rels))
        wrong_kind = ["derive", [["pf", "clo", 0, 0, 1, 2, 3], ["comb", 5, 4, "m"], ["contra", 6]]]   # clo gives a LOWER bound only
        self.assertFalse(self.verify(f, wrong_kind, rels))
        weak = [lo_a, ["lit", cert_con({"a": 1}, -10)], lo_b, ["lit", cert_con({"b": 1}, -10)], ["lit", cert_con({"m": -1}, 50)]]
        self.assertFalse(self.verify(weak, ["derive", [["pf", "chi", 0, 0, 1, 2, 3], ["comb", 5, 4, "m"], ["contra", 6]]], rels))

    def test_real_certificates_validate_and_tampering_is_detected(self):
        import copy
        import json
        import lise_certcheck as cc
        import lise_fmcheck as fm
        import z3
        x, y = z3.Ints("x y")
        asrt = [x >= 0, x <= 10, y >= 0, y <= 10, x * y > 100]
        self.assertEqual(fm.check_assertions(asrt)[0], fm.UNSAT)
        cert = json.loads(json.dumps(fm.last_cert))
        self.assertTrue(cc.verify(cert)[0])

        def derivations(node, out):
            if node[0] == "derive":
                out.append(node[1])
            elif node[0] == "split":
                for sub in node[1]:
                    derivations(sub, out)
        ds = []
        derivations(cert["proof"], ds)
        self.assertTrue(ds)
        tampered = 0
        for variant in ("drop_last_comb", "change_ref", "flip_const"):
            c = copy.deepcopy(cert)
            d = []
            derivations(c["proof"], d)
            steps = d[0]
            if variant == "drop_last_comb" and len(steps) > 1:
                del steps[-2]
            elif variant == "change_ref":
                for st in steps:
                    if st[0] == "comb":
                        st[1] = max(0, st[1] - 1)
                        break
            else:
                c["formulas"] = json.loads(json.dumps(c["formulas"]).replace("100", "99", 1)) if "100" in json.dumps(c["formulas"]) else c["formulas"]
            if c != cert:
                tampered += 1
                self.assertFalse(cc.verify(c)[0], variant)
        self.assertGreaterEqual(tampered, 2)

    def test_a_buggy_prover_cannot_get_a_proof_accepted(self):
        """The search code is untrusted: if its arithmetic is wrong, the validator refuses its certificate."""
        import lise_fmcheck as fm
        import z3
        x = z3.Int("x")
        real = fm.tighten
        fm.tighten = lambda c: ({v: a // max(1, abs(a)) * (1 if a > 0 else 1) for v, a in c[0].items()}, c[1] - 1) if c[0] else c
        try:
            status, detail = fm.check_assertions([x >= 1, x <= 3, 2 * x == 3, x * 0 == 0])[:2]
        finally:
            fm.tighten = real
        self.assertNotEqual(status, fm.UNSAT)

    def test_validator_needs_nothing_but_the_standard_library(self):
        import glob
        import subprocess
        import sys
        with tempfile.TemporaryDirectory() as d:
            r = subprocess.run([sys.executable, os.path.join(HERE, "lise.py"), "check", "--no-cache",
                                os.path.join(HERE, "example_ok_math.lise"), "--certificates", d], capture_output=True, text=True)
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertGreaterEqual(len(glob.glob(os.path.join(d, "*.json"))), 10)
            # -S: no site-packages at all, so z3 / cvc5 / llvmlite are not importable
            v = subprocess.run([sys.executable, "-S", os.path.join(HERE, "lise_certcheck.py"), d], capture_output=True, text=True)
            self.assertEqual(v.returncode, 0, v.stdout + v.stderr)
            self.assertIn("certificates valid", v.stdout)
            some = sorted(glob.glob(os.path.join(d, "*.json")))[0]
            text = open(some).read().replace('"contra"', '"contrX"', 1)
            open(some, "w").write(text)
            v = subprocess.run([sys.executable, "-S", os.path.join(HERE, "lise_certcheck.py"), d], capture_output=True, text=True)
            self.assertNotEqual(v.returncode, 0)


@unittest.skipUnless(HAVE_AOT, "needs llvmlite and a C linker for AOT tests")
class RuntimeHardening(unittest.TestCase):
    """A compiled program must not die in an uncontrolled way because of its environment."""

    def build(self, src, opt=2):
        from lise_aot import build_executable
        from lise_codegen import Codegen
        from lise_lexer import lex
        from lise_parser import Parser
        cg = Codegen(Parser(lex(src)).parse_program(), "t")
        ir = cg.emit_module()
        d = tempfile.mkdtemp()
        exe = os.path.join(d, "prog")
        build_executable(ir, exe, opt, cg.stack_report["lise_main"])
        return exe, cg.stack_report["lise_main"]

    PROG = SUM + r"""
fn main() -> Integer
is
    print_int(sum_to(20))
    print("\n")
    return 5
end
"""

    def test_missing_stack_is_a_clean_exit_not_a_crash(self):
        import resource
        import subprocess
        exe, need = self.build(self.PROG)
        self.assertTrue(check_source(self.PROG, "t.lise").ok)

        def limit(n):
            return lambda: resource.setrlimit(resource.RLIMIT_STACK, (n, n))
        poor = subprocess.run([exe], capture_output=True, preexec_fn=limit(32 * 1024))
        self.assertEqual(poor.returncode, 70)
        self.assertIn(b"not enough stack", poor.stderr)
        self.assertEqual(poor.stdout, b"")                      # it stopped BEFORE running anything
        rich = subprocess.run([exe], capture_output=True, preexec_fn=limit(need + 512 * 1024))
        self.assertEqual((rich.returncode, rich.stdout), (5, b"210\n"))
        unlimited = subprocess.run([exe], capture_output=True,
                                   preexec_fn=lambda: resource.setrlimit(resource.RLIMIT_STACK, (resource.RLIM_INFINITY, resource.RLIM_INFINITY)))
        self.assertEqual(unlimited.returncode, 5)

    def test_closed_output_pipe_does_not_kill_the_program(self):
        import subprocess
        src = r"""fn main() -> Integer
is
    var i: Integer := 0
    while i < 20000
    invariant 0 <= i and i <= 20000
    decreases 20000 - i
    do
        print("some output that nobody reads\n")
        i := i + 1
    end
    return 3
end
"""
        self.assertTrue(check_source(src, "t.lise").ok)
        exe, _ = self.build(src)
        p = subprocess.Popen([exe], stdout=subprocess.PIPE)
        p.stdout.read(10)
        p.stdout.close()                                        # the reader goes away: SIGPIPE on the next write
        self.assertEqual(p.wait(timeout=60), 3)                 # it still runs to completion (output is dropped)
