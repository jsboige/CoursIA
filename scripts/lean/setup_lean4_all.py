#!/usr/bin/env python3
"""Single entry point for Lean 4 kernel setup (WSL + Windows registration + validation).

Orchestrates the 3 setup steps:
1. WSL installation (elan, lean, venv, wrapper) via GameTheory/scripts/setup_wsl_lean4.sh
2. Windows kernel registration via GameTheory/scripts/setup_lean4_kernel.ps1
3. Validation via SymbolicAI/Lean/scripts/validate_lean_setup.py

Usage:
    python scripts/lean/setup_lean4_all.py              # Full setup (1+2+3)
    python scripts/lean/setup_lean4_all.py --wsl-only    # Step 1 only
    python scripts/lean/setup_lean4_all.py --register    # Step 2 only
    python scripts/lean/setup_lean4_all.py --validate    # Step 3 only
    python scripts/lean/setup_lean4_all.py --check-wrapper  # Check kernel.json wrapper
"""

import argparse
import json
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
GT_SCRIPTS = REPO_ROOT / "MyIA.AI.Notebooks" / "GameTheory" / "scripts"
LEAN_SCRIPTS = REPO_ROOT / "MyIA.AI.Notebooks" / "SymbolicAI" / "Lean" / "scripts"


def step_wsl_install():
    """Step 1: Install Lean 4 stack in WSL."""
    print("=" * 60)
    print("STEP 1: WSL Installation (elan + lean + venv + wrapper)")
    print("=" * 60)
    script = GT_SCRIPTS / "setup_wsl_lean4.sh"
    if not script.exists():
        print(f"ERROR: {script} not found")
        return False
    print(f"Running: wsl -d Ubuntu -- bash {script}")
    result = subprocess.run(
        ["wsl", "-d", "Ubuntu", "--", "bash", str(script)],
        cwd=str(REPO_ROOT),
    )
    if result.returncode != 0:
        print(f"FAILED: WSL setup exited with code {result.returncode}")
        return False
    print("OK: WSL installation complete")
    return True


def step_register_kernel():
    """Step 2: Register lean4-wsl kernel on Windows."""
    print("=" * 60)
    print("STEP 2: Windows Kernel Registration")
    print("=" * 60)
    script = GT_SCRIPTS / "setup_lean4_kernel.ps1"
    if not script.exists():
        print(f"ERROR: {script} not found")
        return False
    print(f"Running: powershell -File {script}")
    result = subprocess.run(
        ["powershell", "-ExecutionPolicy", "Bypass", "-File", str(script)],
        cwd=str(REPO_ROOT),
    )
    if result.returncode != 0:
        print(f"FAILED: Kernel registration exited with code {result.returncode}")
        return False
    print("OK: Kernel registration complete")
    return True


def step_validate():
    """Step 3: Validate the full Lean 4 setup."""
    print("=" * 60)
    print("STEP 3: Validation")
    print("=" * 60)
    script = LEAN_SCRIPTS / "validate_lean_setup.py"
    if not script.exists():
        print(f"ERROR: {script} not found")
        return False
    print(f"Running: python {script}")
    result = subprocess.run(
        [sys.executable, str(script)],
        cwd=str(REPO_ROOT),
    )
    if result.returncode != 0:
        print("FAILED: Validation failed")
        return False
    print("OK: Validation passed")
    return True


def check_wrapper_registration():
    """Check that kernel.json points to the CORRECT Python wrapper (not old bash)."""
    print("=" * 60)
    print("CHECK: kernel.json wrapper registration")
    print("=" * 60)

    kernel_path = Path.home() / "AppData" / "Roaming" / "jupyter" / "kernels" / "lean4-wsl"
    kernel_json = kernel_path / "kernel.json"

    if not kernel_json.exists():
        print(f"ERROR: kernel.json not found at {kernel_json}")
        print("  Run: python scripts/lean/setup_lean4_all.py --register")
        return False

    with open(kernel_json, encoding="utf-8") as f:
        config = json.load(f)

    argv = config.get("argv", [])
    cmd_str = " ".join(argv)

    print(f"kernel.json location: {kernel_json}")
    print(f"argv: {cmd_str}")

    # Check: must contain the Python wrapper, NOT the old bash wrapper
    has_python_wrapper = any("lean4-kernel-wrapper.py" in a for a in argv)
    has_old_bash_wrapper = any("lean4-jupyter-wrapper.sh" in a for a in argv)

    if has_old_bash_wrapper:
        print("ERROR: kernel.json points to OLD bash wrapper (lean4-jupyter-wrapper.sh)")
        print("  The bash wrapper lacks Windows->WSL path conversion and will fail.")
        print("  Fix: python scripts/lean/setup_lean4_all.py --register")
        return False

    if has_python_wrapper:
        print("OK: kernel.json points to correct Python wrapper (.lean4-kernel-wrapper.py)")
        return True

    print(f"WARNING: kernel.json has unexpected argv. Expected .lean4-kernel-wrapper.py")
    return False


def main():
    parser = argparse.ArgumentParser(
        description="Lean 4 kernel setup orchestrator (single entry point)"
    )
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--wsl-only", action="store_true", help="WSL install only (step 1)")
    group.add_argument("--register", action="store_true", help="Kernel registration only (step 2)")
    group.add_argument("--validate", action="store_true", help="Validation only (step 3)")
    group.add_argument("--check-wrapper", action="store_true", help="Check kernel.json wrapper")
    args = parser.parse_args()

    results = []

    if args.check_wrapper:
        ok = check_wrapper_registration()
        sys.exit(0 if ok else 1)

    if args.wsl_only:
        ok = step_wsl_install()
        sys.exit(0 if ok else 1)

    if args.register:
        ok = step_register_kernel()
        sys.exit(0 if ok else 1)

    if args.validate:
        ok = step_validate()
        sys.exit(0 if ok else 1)

    # Full setup: all 3 steps
    print("Lean 4 Kernel Setup — Full Installation")
    print()

    results.append(("WSL Install", step_wsl_install()))
    if not results[-1][1]:
        print("\nStep 1 FAILED. Fix WSL issues before continuing.")
        sys.exit(1)

    results.append(("Kernel Registration", step_register_kernel()))
    results.append(("Validation", step_validate()))
    results.append(("Wrapper Check", check_wrapper_registration()))

    print()
    print("=" * 60)
    print("RESULTS")
    print("=" * 60)
    for name, ok in results:
        status = "OK" if ok else "FAILED"
        print(f"  {name:30s} {status}")
    all_ok = all(ok for _, ok in results)
    print()
    if all_ok:
        print("All steps passed. Lean 4 kernel ready.")
    else:
        print("Some steps failed. See output above.")
    sys.exit(0 if all_ok else 1)


if __name__ == "__main__":
    main()
