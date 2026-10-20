"""Ahead-of-time (AOT) native build: LLVM IR text -> optimized object -> executable.

No JIT anywhere. Pipeline:
    verified Lise -> LLVM IR (lise_codegen) -> add C entry point -> verify IR
    -> O2 pipeline -> native object file -> system linker -> executable

Needs `llvmlite` (LLVM) and a C linker driver (`gcc`, `cc` or `clang`) on PATH.
Entry point: `fn main() -> Integer` (no params). Its value is the process exit
status (low 8 bits on POSIX).
"""
import os
import shutil
import subprocess
import tempfile

ENTRY = "main"


class AotError(Exception):
    pass


STACK_SLACK = 128 * 1024        # C runtime start-up, argv/environment, signal frames
EXIT_STACK = 70                 # EX_SOFTWARE: the program cannot run here; reported before it starts
SIGPIPE, RLIMIT_STACK = 13, 3   # the same numbers on Linux and macOS


def entry_wrapper(ir, stack_need=None):
    """Append the C-ABI `main` that calls @lise_main. Rejects a bad Lise main.

    The wrapper makes the program robust against the environment, so that it never dies half-way:
      * it first checks that the OS stack limit covers the program's proven worst-case stack use
        (`stack_need`); if not it exits at once with status 70 and a message (a controlled failure
        at start-up instead of a crash at an arbitrary later point);
      * it ignores SIGPIPE, so a closed output pipe drops output instead of killing the program."""
    marker = "define i64 @lise_main()"
    if marker not in ir:
        raise AotError("an executable needs `fn main() -> Integer` with no parameters")
    out = ["", "declare i32 @getrlimit(i32, ptr)", "declare ptr @signal(i32, ptr)"]
    if "declare i64 @write(" not in ir:
        out.append("declare i64 @write(i32, ptr, i64)")
    need = (stack_need or 0) + STACK_SLACK
    msg = (f"lise: not enough stack: this program needs at least {-(-need // 1024)} KiB "
           f"(raise the limit, e.g. `ulimit -s {-(-need // 1024)}`)\n").encode()
    body = "".join(f"\\{b:02X}" for b in msg)
    out.append(f'@.lise.stackmsg = private unnamed_addr constant [{len(msg)} x i8] c"{body}"')
    out.append("define i32 @main() {")
    out.append("entry:")
    if stack_need is not None:
        out += [
            "  %rl = alloca [2 x i64]",
            f"  %gr = call i32 @getrlimit(i32 {RLIMIT_STACK}, ptr %rl)",
            "  %known = icmp eq i32 %gr, 0",
            "  br i1 %known, label %chk, label %run",
            "chk:",
            "  %cur = load i64, ptr %rl",
            "  %unlimited = icmp ugt i64 %cur, 4611686018427387904",
            f"  %enough = icmp uge i64 %cur, {need}",
            "  %fine = or i1 %unlimited, %enough",
            "  br i1 %fine, label %run, label %fail",
            "fail:",
            f"  %w = call i64 @write(i32 2, ptr @.lise.stackmsg, i64 {len(msg)})",
            f"  ret i32 {EXIT_STACK}",
        ]
    else:
        out.append("  br label %run")
    out += [
        "run:",
        f"  %sig = call ptr @signal(i32 {SIGPIPE}, ptr inttoptr (i64 1 to ptr))",
        "  %r = call i64 @lise_main()",
        "  %c = trunc i64 %r to i32",
        "  ret i32 %c",
        "}",
        "",
    ]
    return ir + "\n".join(out)


def find_linker():
    for name in ("gcc", "cc", "clang"):
        p = shutil.which(name)
        if p:
            return p
    raise AotError("no C linker driver found (need gcc, cc or clang on PATH)")


def compile_object(ir, opt=2, triple=None):
    """IR text -> native object bytes (optimized, verified)."""
    try:
        import llvmlite.binding as llvm
    except ImportError as ex:
        raise AotError("native build needs llvmlite: pip install llvmlite") from ex
    llvm.initialize_native_target()
    llvm.initialize_native_asmprinter()
    try:
        mod = llvm.parse_assembly(ir)
        mod.verify()
    except RuntimeError as ex:
        raise AotError(f"internal: backend produced invalid LLVM IR: {ex}") from ex
    target = llvm.Target.from_triple(triple) if triple else llvm.Target.from_default_triple()
    tm = target.create_target_machine(opt=opt, reloc="pic", codemodel="default")
    mod.triple = tm.triple if hasattr(tm, "triple") else llvm.get_default_triple()
    mod.data_layout = str(tm.target_data)
    if opt > 0:
        pb = llvm.create_pass_builder(tm, llvm.create_pipeline_tuning_options(opt))
        pb.getModulePassManager().run(mod, pb)
    return tm.emit_object(mod)


def build_executable(ir, out_path, opt=2, stack_need=None):
    """Full AOT build. Returns out_path.  `stack_need` = the proven worst-case stack bound of main (bytes)."""
    obj = compile_object(entry_wrapper(ir, stack_need), opt=opt)
    linker = find_linker()
    with tempfile.TemporaryDirectory() as d:
        o = os.path.join(d, "lise.o")
        with open(o, "wb") as f:
            f.write(obj)
        r = subprocess.run([linker, o, "-o", out_path], capture_output=True, text=True)
        if r.returncode != 0:
            raise AotError(f"link failed: {r.stderr.strip()}")
    return out_path
