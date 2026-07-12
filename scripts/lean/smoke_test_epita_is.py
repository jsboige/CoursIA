#!/usr/bin/env python3
"""Smoke-test all Lean notebooks for EPITA-IS sessions.

Executes each notebook via the lean4-wsl kernel (papermill inside WSL)
and verifies: all cells executed, 0 errors, execution_count set.

Usage:
    python scripts/lean/smoke_test_epita_is.py
    python scripts/lean/smoke_test_epita_is.py --quick   # skip execution, check status only
    python scripts/lean/smoke_test_epita_is.py --notebooks "Lean-2*,Lean-3*"
"""

import argparse
import json
import sys
import time
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
NOTEBOOKS_DIR = REPO_ROOT / "MyIA.AI.Notebooks"

# Notebooks for the 3 EPITA-IS sessions
SESSION_MONDAY_2H = [  # Monday 2h Lean intro
    "SymbolicAI/Lean/Lean-1-Setup.ipynb",
    "SymbolicAI/Lean/Lean-2-Dependent-Types.ipynb",
    "SymbolicAI/Lean/Lean-3-Propositions-Proofs.ipynb",
    "SymbolicAI/Lean/Lean-4-Quantifiers.ipynb",
]
SESSION_WEEK_4H_LEAN = [  # Week 4h Lean+GameTheory
    "SymbolicAI/Lean/Lean-5-Tactics.ipynb",
    "SymbolicAI/Lean/Lean-6-Mathlib-Essentials.ipynb",
    "GameTheory/GameTheory-15b-Lean-CooperativeGames.ipynb",
    "GameTheory/GameTheory-2b-Lean-Definitions.ipynb",
]
ALL_NOTEBOOKS = SESSION_MONDAY_2H + SESSION_WEEK_4H_LEAN


def check_notebook(nb_path: Path) -> dict:
    """Check execution status of a notebook without re-executing."""
    nb = json.loads(nb_path.read_text(encoding="utf-8"))
    code_cells = [c for c in nb["cells"] if c["cell_type"] == "code"]
    total = len(code_cells)
    executed = sum(1 for c in code_cells if c.get("execution_count") is not None)
    errors = sum(
        1
        for c in code_cells
        if any(o.get("output_type") == "error" for o in c.get("outputs", []))
    )
    return {
        "path": str(nb_path.relative_to(NOTEBOOKS_DIR)),
        "total": total,
        "executed": executed,
        "errors": errors,
        "ok": executed == total and errors == 0,
    }


def main():
    parser = argparse.ArgumentParser(description="Smoke-test Lean EPITA-IS notebooks")
    parser.add_argument("--quick", action="store_true", help="Check status only (no execution)")
    parser.add_argument("--notebooks", type=str, default=None, help="Glob pattern filter")
    args = parser.parse_args()

    notebooks = ALL_NOTEBOOKS
    if args.notebooks:
        import fnmatch
        patterns = [p.strip() for p in args.notebooks.split(",")]
        notebooks = [n for n in notebooks if any(fnmatch.fnmatch(n, p) for p in patterns)]

    print(f"Lean EPITA-IS Smoke Test — {len(notebooks)} notebooks")
    print("=" * 60)

    results = []
    for rel_path in notebooks:
        nb_path = NOTEBOOKS_DIR / rel_path
        if not nb_path.exists():
            print(f"  MISSING: {rel_path}")
            results.append({"path": rel_path, "ok": False, "error": "file not found"})
            continue

        if args.quick:
            r = check_notebook(nb_path)
            status = "OK" if r["ok"] else f"FAIL ({r['executed']}/{r['total']} exec, {r['errors']} err)"
            print(f"  {rel_path.split('/')[-1]:45s} {status}")
            results.append(r)
        else:
            print(f"  Executing: {rel_path.split('/')[-1]} ...", end=" ", flush=True)
            t0 = time.time()
            try:
                import subprocess
                cmd = [
                    sys.executable,
                    str(REPO_ROOT / "scripts/notebook_tools/wsl_papermill.py"),
                    "execute", str(nb_path),
                    "--kernel", "lean4-wsl",
                    "--timeout", "600",
                ]
                proc = subprocess.run(cmd, capture_output=True, text=True, timeout=600)
                elapsed = time.time() - t0
                r = check_notebook(nb_path)
                r["elapsed_s"] = round(elapsed, 1)
                status = f"OK ({r['executed']}/{r['total']} cells, {elapsed:.1f}s)" if r["ok"] else f"FAIL ({r['executed']}/{r['total']} exec, {r['errors']} err)"
                print(status)
                results.append(r)
            except subprocess.TimeoutExpired:
                print(f"TIMEOUT (600s)")
                results.append({"path": rel_path, "ok": False, "error": "timeout"})
            except Exception as e:
                print(f"ERROR: {e}")
                results.append({"path": rel_path, "ok": False, "error": str(e)})

    print("=" * 60)
    ok_count = sum(1 for r in results if r.get("ok"))
    fail_count = len(results) - ok_count
    print(f"Results: {ok_count}/{len(results)} passed, {fail_count} failed")

    if fail_count > 0:
        print("\nFailed notebooks:")
        for r in results:
            if not r.get("ok"):
                print(f"  - {r['path']}")

    return 0 if fail_count == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
