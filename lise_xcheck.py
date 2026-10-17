"""Second-solver cross-check.

Z3 is a large piece of software and a bug in it could "prove" something false.
Every obligation Z3 discharges (negation UNSAT) is therefore re-checked by a
completely independent solver, cvc5.  The verifier accepts a proof only when
BOTH agree:

  cvc5 unsat    -> confirmed
  cvc5 sat      -> DISAGREEMENT (a solver or encoding bug): hard error
  cvc5 unknown / timeout / parse error -> not confirmed: rejected (safe side)
"""
import cvc5

UNSAT, SAT, UNKNOWN = "unsat", "sat", "unknown"


def version():
    try:
        return cvc5.Solver().getVersion()
    except Exception:  # pragma: no cover
        return "unknown"


def check(z3_solver, timeout_ms):
    """Re-run the assertions of a z3 Solver through cvc5.  Returns (status, detail)."""
    try:
        smt = "(set-logic ALL)\n" + z3_solver.to_smt2()
        slv = cvc5.Solver()
        slv.setOption("tlimit-per", str(int(timeout_ms)))
        slv.setOption("arrays-exp", "true")   # needed for constant arrays (fill); experimental in cvc5
        sm = cvc5.SymbolManager(slv)
        parser = cvc5.InputParser(slv, sm)
        parser.setStringInput(cvc5.InputLanguage.SMT_LIB_2_6, smt, "obligation")
        result = None
        while True:
            cmd = parser.nextCommand()
            if cmd.isNull():
                break
            out = cmd.invoke(slv, sm).strip()
            if out in (UNSAT, SAT, UNKNOWN):
                result = out
            elif out.startswith("(error"):
                return UNKNOWN, out[:200]
        if result is None:
            return UNKNOWN, "no result"
        return result, ""
    except Exception as ex:  # any failure of the second solver means "not confirmed"
        return UNKNOWN, f"{type(ex).__name__}: {ex}"
