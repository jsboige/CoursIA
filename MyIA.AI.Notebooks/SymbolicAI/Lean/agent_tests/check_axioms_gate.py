#!/usr/bin/env python3
"""Local CLI for the B.3 "Proof integrity (axiom check)" review gate (#8677).

Mirrors the `Proof integrity (axiom check)` step of `.github/workflows/lean-build.yml`
(input `axiom-gate: true`), so a reviewer can satisfy criterion B.3 of
`pr-review-discipline.md` on a lake that does not (yet) enable the CI gate -- or
reproduce a CI verdict locally.

For every module passed on the command line, it enumerates the declarations and
runs `#print axioms` on each (namespace-aware, fully-qualified names), in the
review-gate policy `fail_on_sorry=True`: a proof that depends on `sorryAx` --
even transitively (a sorry buried in a dependency no `grep` sees) -- FAILS.
This is precisely the value the gate adds over textual `grep -c sorry` counting.

Usage (run from the Lake project root, or pass it via --project):

    cd MyIA.AI.Notebooks/SymbolicAI/Lean/knot_lean
    python3 ../../agent_tests/check_axioms_gate.py Knots.Basic Knots.Invariant

Exit code: 0 if every module is clean, 1 if any module fails (forbidden axiom or
sorryAx), 2 on usage/IO error. Output format matches the CI step:
`  [PASS] <module>: ...` / `  [FAIL] <module>: ... HAS SORRY (sorryAx)`.

See criterion B.3 of `.claude/rules/pr-review-discipline.md`.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

# Allow invocation from anywhere: add this script's dir to sys.path so the
# sibling `lean_server` import resolves regardless of cwd.
sys.path.insert(0, str(Path(__file__).resolve().parent))

from lean_server import LeanVerifier  # noqa: E402


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Local B.3 axiom-check gate (review-gate policy).",
    )
    parser.add_argument(
        "modules",
        nargs="+",
        help="Dotted module names to check (e.g. Knots.Basic Knots.Invariant).",
    )
    parser.add_argument(
        "--project",
        "-p",
        default=".",
        help="Lake project root (default: cwd). LeanVerifier re-roots to the "
        "real Lake root if cwd lacks a lakefile.",
    )
    parser.add_argument(
        "--allow-sorry",
        action="store_true",
        help="Prover policy: tolerate sorryAx (default: review-gate policy, "
        "sorryAx FAILS). Use this only to inspect, not to satisfy B.3.",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=300,
        help="Seconds per module for `lake env lean --stdin` (default 300). "
        "The cost is loading the import closure (Mathlib); cold that can "
        "exceed the prover's tight 60s default.",
    )
    args = parser.parse_args()

    project = Path(args.project).resolve()
    if not project.is_dir():
        print(f"ERROR: project dir not found: {project}", file=sys.stderr)
        return 2

    v = LeanVerifier(project_dir=str(project), verbose=False)
    fail_on_sorry = not args.allow_sorry
    policy = "prover (sorryAx tolerated)" if args.allow_sorry else "review-gate (sorryAx FAILS)"
    print(f"=== Proof integrity (axiom check) -- policy: {policy} ===")
    failed = False
    for mod in args.modules:
        r = v.check_axioms(mod, fail_on_sorry=fail_on_sorry, timeout=args.timeout)
        # Surface the error whenever the check did not succeed -- a subprocess
        # failure (timeout / lake env missing) after enumeration reports
        # declarations>0 but success=False with an `error`; that must read as
        # ERROR, not a bare [FAIL] that hides the cause from the reviewer.
        if not r["success"] and r.get("error"):
            print(f"  [ERROR] {mod}: {r['error']}")
            failed = True
            continue
        status = "PASS" if r["success"] else "FAIL"
        extra = ""
        if r.get("has_sorry"):
            extra = " | HAS SORRY (sorryAx)"
        if r["forbidden"]:
            extra += f" | forbidden={r['forbidden']}"
        print(
            f"  [{status}] {mod}: decls={len(r.get('declarations', []))} "
            f"axioms={r['axioms']}{extra}"
        )
        if not r["success"]:
            failed = True

    if failed:
        print("\nFAIL: one or more modules depend on forbidden axioms (incl. sorryAx).")
        return 1
    print("\nOK: all modules pass the axiom-integrity gate.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
