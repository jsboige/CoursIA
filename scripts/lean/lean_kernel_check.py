#!/usr/bin/env python3
"""Canonical kernel.json wrapper check for the lean4-wsl Jupyter kernel.

Single source of truth for detecting the 2026-05-27 regression (issue #1618)
where ``kernel.json`` pointed to the OLD bash wrapper
``~/lean4-jupyter-wrapper.sh`` instead of the CORRECT Python wrapper
``~/.lean4-kernel-wrapper.py`` (v5). The bash wrapper lacks Windows->WSL path
conversion and NTFS permission handling, so the kernel times out at startup.

Before this module the same check lived (divergently) in three places:
  - scripts/lean/setup_lean4_all.py            (check_wrapper_registration)
  - SymbolicAI/Lean/scripts/validate_lean_setup.py (check_kernel_wrapper)
  - GameTheory/scripts/validate_lean_setup.py  (was MISSING entirely)

``inspect_kernel_wrapper`` is print-agnostic: it returns a structured result so
each caller can format it with its own style (unicode / ASCII / section header).

Usage as a module:
    from lean_kernel_check import inspect_kernel_wrapper
    status, message = inspect_kernel_wrapper("lean4-wsl")

Usage as a CLI:
    python scripts/lean/lean_kernel_check.py            # check lean4-wsl
    python scripts/lean/lean_kernel_check.py --kernel lean4-wsl
"""

import argparse
import json
import os
import sys
from pathlib import Path

OLD_BASH_WRAPPER = "lean4-jupyter-wrapper.sh"
CORRECT_PY_WRAPPER = ".lean4-kernel-wrapper.py"


def candidate_kernel_json_paths(kernel_name="lean4-wsl"):
    """Return the kernel.json locations to probe, in priority order.

    Covers both the WSL-side install (~/.local/share/jupyter) and the
    Windows-side registration (%APPDATA%/jupyter).
    """
    candidates = [
        Path.home() / ".local" / "share" / "jupyter" / "kernels" / kernel_name / "kernel.json",
    ]
    appdata = os.environ.get("APPDATA")
    if appdata:
        candidates.append(Path(appdata) / "jupyter" / "kernels" / kernel_name / "kernel.json")
    return candidates


def inspect_kernel_wrapper(kernel_name="lean4-wsl", kernel_json_path=None):
    """Inspect kernel.json and classify the wrapper it points to.

    Returns a ``(status, message)`` tuple where ``status`` is one of:
      - "ok"      : kernel.json points to the correct Python wrapper (v5)
      - "error"   : kernel.json points to the old bash wrapper (regression #1618)
      - "warning" : kernel.json not found, unreadable, or unknown argv

    ``kernel_json_path`` overrides the auto-detected location (used by tests).
    """
    if kernel_json_path is not None:
        kernel_json = Path(kernel_json_path)
        candidates = [kernel_json]
    else:
        candidates = candidate_kernel_json_paths(kernel_name)
        kernel_json = next((p for p in candidates if p.exists()), None)

    if kernel_json is None or not kernel_json.exists():
        probed = [str(p) for p in candidates]
        return ("warning", f"kernel.json: aucun ({kernel_name}) trouve dans {probed}")

    try:
        with open(kernel_json, "r", encoding="utf-8") as f:
            spec = json.load(f)
        argv = " ".join(str(a) for a in spec.get("argv", []))
    except Exception as exc:  # noqa: BLE001 - report any read/parse failure as a warning
        return ("warning", f"kernel.json ({kernel_name}): erreur lecture ({exc})")

    if OLD_BASH_WRAPPER in argv:
        return (
            "error",
            f"kernel.json ({kernel_name}): pointe vers l'ancien wrapper bash "
            f"({OLD_BASH_WRAPPER}) — regression #1618. Re-executer "
            "`python scripts/lean/setup_lean4_all.py --register` pour pointer "
            f"vers ~/{CORRECT_PY_WRAPPER} (v5).",
        )
    if CORRECT_PY_WRAPPER in argv:
        return ("ok", f"kernel.json ({kernel_name}): wrapper Python v5 correct")
    return ("warning", f"kernel.json ({kernel_name}): wrapper inconnu — argv={argv[:120]}")


def main():
    parser = argparse.ArgumentParser(
        description="Verifie que kernel.json pointe vers le bon wrapper Lean 4 (issue #1618)."
    )
    parser.add_argument("--kernel", default="lean4-wsl", help="Nom du kernel (defaut: lean4-wsl)")
    args = parser.parse_args()

    status, message = inspect_kernel_wrapper(args.kernel)
    prefix = {"ok": "OK:", "error": "ERROR:", "warning": "WARNING:"}[status]
    print(f"{prefix} {message}")
    sys.exit(0 if status == "ok" else 1)


if __name__ == "__main__":
    main()
