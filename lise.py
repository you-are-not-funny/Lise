#!/usr/bin/env python3
"""Lise reference compiler: parse + verify + AOT native code generation.

usage:
  python lise.py check FILE_OR_DIR... [--timeout-ms N] [--no-cache]
  python lise.py build FILE [-o OUT.ll] [--timeout-ms N] [--no-cache]
      verify FILE, then emit LLVM IR (no proof => no output)
  python lise.py build FILE --exe [-o OUT] [-O0|-O1|-O2|-O3] [--timeout-ms N]
      verify, then compile ahead-of-time to a native executable (needs `fn main() -> Integer`)
  python lise.py run FILE [--timeout-ms N]
      build a native executable in a temp dir, run it, exit with its status

safety options (build/run):
  default            proofs are re-done from scratch (never trusts the cache) and the
                     proven runtime checks are ALSO compiled in and trap on failure
  --unchecked        erase the proven checks (zero cost; trusts the verifier fully)
  --stack-limit N    reject if the static worst-case stack bound exceeds N bytes (default 1048576)
  python lise.py version
"""
import os
import subprocess
import sys
import tempfile

from lise_aot import AotError, build_executable
from lise_codegen import CodegenError, generate
from lise_lexer import lex
from lise_parser import Parser
from lise_verify import ProofCache, VERSION, check_source


def collect(paths):
    out = []
    for p in paths:
        if os.path.isdir(p):
            for root, _, files in sorted(os.walk(p)):
                out.extend(os.path.join(root, f) for f in sorted(files) if f.endswith(".lise"))
        else:
            out.append(p)
    return out


def main(argv):
    if len(argv) >= 2 and argv[1] == "version":
        print(f"lise {VERSION}")
        return 0
    if len(argv) < 3 or argv[1] not in ("check", "build", "run"):
        print(__doc__)
        return 2
    cmd = argv[1]
    build = cmd in ("build", "run")
    timeout, use_cache, paths, out_path = 10000, True, [], None
    exe, opt = cmd == "run", 2
    checked, stack_limit = True, 1 << 20
    args = argv[2:]
    i = 0
    while i < len(args):
        if args[i] == "--timeout-ms" and i + 1 < len(args):
            timeout = int(args[i + 1])
            i += 2
        elif args[i] == "-o" and i + 1 < len(args):
            out_path = args[i + 1]
            i += 2
        elif args[i] == "--no-cache":
            use_cache = False
            i += 1
        elif args[i] == "--unchecked":
            checked = False
            i += 1
        elif args[i] == "--stack-limit" and i + 1 < len(args):
            stack_limit = int(args[i + 1])
            i += 2
        elif args[i] == "--exe":
            exe = True
            i += 1
        elif args[i] in ("-O0", "-O1", "-O2", "-O3"):
            opt = int(args[i][2])
            i += 1
        else:
            paths.append(args[i])
            i += 1
    files = collect(paths)
    if build and len(files) != 1:
        print(f"{cmd} takes exactly one file")
        return 2
    if not files:
        print("no .lise files given")
        return 2
    # Builds never trust the proof cache: a tampered cache must not produce a binary.
    cache = ProofCache() if (use_cache and not build) else None
    failed = 0
    run_status = None
    for f in files:
        try:
            with open(f, encoding="utf-8") as fh:
                src = fh.read()
        except OSError as ex:
            print(f"{f}: cannot read: {ex}")
            failed += 1
            continue
        rep = check_source(src, f, timeout, cache)
        for d in rep.diags:
            print(d)
        if rep.ok:
            print(f"{f}: OK  ({rep.verified}/{rep.functions} functions proved, "
                  f"{rep.cached} from cache, {rep.obligations} proof obligations)")
        else:
            failed += 1
            print(f"{f}: FAILED ({len(rep.diags)} error(s))")
        if build and rep.ok:
            try:
                ir = generate(Parser(lex(src)).parse_program(), os.path.basename(f),
                              checked, stack_limit)
            except CodegenError as ex:
                print(f"{f}:{ex.loc[0]}:{ex.loc[1]}: error: backend: {ex.msg}")
                failed += 1
                continue
            if exe:
                tmpdir = tempfile.mkdtemp() if cmd == "run" else None
                target = out_path or (os.path.join(tmpdir, "a.out") if tmpdir
                                      else os.path.splitext(f)[0])
                try:
                    build_executable(ir, target, opt)
                except AotError as ex:
                    print(f"{f}: error: native build: {ex}")
                    failed += 1
                    continue
                if cmd == "run":
                    run_status = subprocess.run([target]).returncode
                else:
                    print(f"wrote {target} (native, -O{opt})")
            else:
                target = out_path or os.path.splitext(f)[0] + ".ll"
                with open(target, "w", encoding="utf-8") as fh:
                    fh.write(ir)
                print(f"wrote {target}")
        elif build:
            print("no output written: verification failed (no proof, no binary)")
    if cache is not None:
        cache.save()
    if run_status is not None and not failed:
        return run_status
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
