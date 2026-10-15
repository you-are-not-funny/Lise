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


def entry_wrapper(ir):
    """Append the C-ABI `main` that calls @lise_main. Rejects a bad Lise main."""
    marker = "define i64 @lise_main()"
    if marker not in ir:
        raise AotError("an executable needs `fn main() -> Integer` with no parameters")
    return ir + (
        "\ndefine i32 @main() {\n"
        "entry:\n"
        "  %r = call i64 @lise_main()\n"
        "  %c = trunc i64 %r to i32\n"
        "  ret i32 %c\n"
        "}\n"
    )


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


def build_executable(ir, out_path, opt=2):
    """Full AOT build. Returns out_path."""
    obj = compile_object(entry_wrapper(ir), opt=opt)
    linker = find_linker()
    with tempfile.TemporaryDirectory() as d:
        o = os.path.join(d, "lise.o")
        with open(o, "wb") as f:
            f.write(obj)
        r = subprocess.run([linker, o, "-o", out_path], capture_output=True, text=True)
        if r.returncode != 0:
            raise AotError(f"link failed: {r.stderr.strip()}")
    return out_path
