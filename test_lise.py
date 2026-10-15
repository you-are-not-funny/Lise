"""Run with:  python -m unittest -v   (needs: pip install z3-solver)"""
import os
import shutil
import tempfile
import unittest

from lise_verify import ProofCache, check_source

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
        prog = Parser(lex("record R\n    a: Integer\nend\nfn f(x: in R) -> R is return x end")).parse_program()
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
    def native(self, src, checked, stack_limit=1 << 20):
        import subprocess
        from lise_aot import build_executable
        from lise_codegen import generate
        from lise_lexer import lex
        from lise_parser import Parser
        ir = generate(Parser(lex(src)).parse_program(), "t", checked, stack_limit)  # NO verifier on purpose
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

    def test_checked_build_traps_when_a_proof_would_be_wrong(self):
        for name, src in self.BAD.items():
            self.assertLess(self.native(src, True), 0, f"{name}: checked build must die by signal (trap)")

    def test_stack_bound_rejects_huge_frames(self):
        from lise_codegen import CodegenError, generate
        from lise_lexer import lex
        from lise_parser import Parser
        src = "fn main() -> Integer\nis\n    var a: Array[Integer, 1000000] := fill(0)\n    return a[1]\nend\n"
        with self.assertRaises(CodegenError) as cm:
            generate(Parser(lex(src)).parse_program(), "t")
        self.assertIn("worst-case stack", str(cm.exception))
        generate(Parser(lex(src)).parse_program(), "t", True, 16 << 20)  # fits under a bigger limit

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
        r = subprocess.run([sys.executable, os.path.join(HERE, "fuzz_lise.py"), "40", "7000"],
                           capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertIn("BUGS=0", r.stdout)
