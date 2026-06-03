#!/usr/bin/env python3
"""Execute Jupyter notebooks via papermill inside WSL.

Workaround for the jupyter_client cross-OS connection issue:
Windows-side jupyter_client cannot connect to WSL kernels because
WSL strips backslashes from connection file paths. This script runs
papermill natively inside WSL, avoiding the cross-OS boundary entirely.

Prerequisites (one-time setup):
    wsl -e bash -c "python3 -m venv ~/coursia-wsl"
    wsl -e bash -c "source ~/coursia-wsl/bin/activate && pip install nashpy matplotlib papermill ipykernel scipy numpy"
    wsl -e bash -c "source ~/coursia-wsl/bin/activate && python3 -m ipykernel install --user --name python3"

Usage:
    python wsl_papermill.py execute <notebook.ipynb> [--output <path>] [--kernel python3]
    python wsl_papermill.py batch <dir> [--pattern "*.ipynb"] [--kernel python3]
    python wsl_papermill.py check-env

Examples:
    python wsl_papermill.py execute MyIA.AI.Notebooks/GameTheory/GameTheory-1-Setup.ipynb
    python wsl_papermill.py batch MyIA.AI.Notebooks/GameTheory/ --kernel python3
"""

import argparse
import json
import subprocess
import sys
import time
from pathlib import Path

WSL_VENV = "~/coursia-wsl"
WSL_PAPERMILL_CMD = f"source {WSL_VENV}/bin/activate && papermill"
REPO_ROOT = Path(__file__).resolve().parent.parent.parent


def win_to_wsl_path(win_path: str) -> str:
    """Convert Windows path to WSL path."""
    p = Path(win_path).resolve()
    drive = p.drive[0].lower()
    return f"/mnt/{drive}{p.as_posix()[2:]}"


def run_wsl(cmd: str, timeout: int = 300) -> tuple[int, str, str]:
    """Run a command in WSL and return (exit_code, stdout, stderr)."""
    result = subprocess.run(
        ["wsl", "-e", "bash", "-c", cmd],
        capture_output=True, text=True, timeout=timeout
    )
    return result.returncode, result.stdout, result.stderr


def check_env() -> bool:
    """Verify WSL papermill environment is set up."""
    print("Checking WSL papermill environment...")
    ok = True

    # Check venv exists
    rc, out, _ = run_wsl(f"test -d {WSL_VENV} && echo OK || echo MISSING")
    if "OK" in out:
        print(f"  venv: {WSL_VENV} OK")
    else:
        print(f"  venv: MISSING — run: wsl -e bash -c 'python3 -m venv {WSL_VENV}'")
        ok = False

    # Check packages
    pkgs = ["papermill", "ipykernel", "nashpy", "matplotlib", "numpy", "scipy"]
    rc, out, _ = run_wsl(f"source {WSL_VENV}/bin/activate && pip list --format=columns 2>/dev/null")
    for pkg in pkgs:
        if pkg.lower() in out.lower():
            print(f"  {pkg}: OK")
        else:
            print(f"  {pkg}: MISSING")
            ok = False

    return ok


def execute_notebook(notebook: str, output: str | None = None,
                     kernel: str = "python3", timeout: int = 300,
                     in_place: bool = False) -> int:
    """Execute a single notebook via WSL papermill."""
    nb_path = Path(notebook).resolve()
    if not nb_path.exists():
        print(f"ERROR: {nb_path} not found")
        return 1

    wsl_input = win_to_wsl_path(str(nb_path))

    if in_place:
        wsl_output = wsl_input
    elif output:
        wsl_output = win_to_wsl_path(str(Path(output).resolve()))
    else:
        wsl_output = f"/tmp/{nb_path.stem}_wsl_output.ipynb"

    cmd = f'{WSL_PAPERMILL_CMD} --kernel {kernel} "{wsl_input}" "{wsl_output}"'
    print(f"Executing: {nb_path.name} ...")

    start = time.time()
    try:
        rc, stdout, stderr = run_wsl(cmd, timeout=timeout)
        elapsed = time.time() - start
    except subprocess.TimeoutExpired:
        print(f"  TIMEOUT after {timeout}s")
        return 2

    if rc != 0:
        print(f"  FAILED ({elapsed:.1f}s)")
        if stderr:
            for line in stderr.strip().split("\n")[-10:]:
                print(f"    {line}")
        return 1

    # Parse output to count cells/errors
    if wsl_output != wsl_input:
        # Copy output back to Windows
        cp_rc, _, _ = run_wsl(f'cp "{wsl_output}" "{wsl_input}"')
        if cp_rc != 0:
            print(f"  WARNING: could not copy output back ({elapsed:.1f}s)")
            return 1

    # Validate output
    try:
        content = nb_path.read_text(encoding="utf-8")
        nb = json.loads(content)
        code_cells = [c for c in nb["cells"] if c["cell_type"] == "code"]
        exec_count = sum(1 for c in code_cells if c.get("execution_count"))
        errors = sum(
            1 for c in code_cells
            if any(o.get("output_type") == "error" for o in c.get("outputs", []))
        )
        print(f"  OK: {exec_count}/{len(code_cells)} cells executed, {errors} errors ({elapsed:.1f}s)")
        return 0 if errors == 0 else 3
    except Exception as e:
        print(f"  WARNING: could not validate output: {e}")
        return 0


def batch_execute(directory: str, pattern: str = "*.ipynb",
                  kernel: str = "python3", timeout: int = 300) -> int:
    """Execute all matching notebooks in a directory."""
    nb_dir = Path(directory).resolve()
    if not nb_dir.exists():
        print(f"ERROR: {nb_dir} not found")
        return 1

    notebooks = sorted(nb_dir.glob(pattern))
    if not notebooks:
        print(f"No notebooks matching {pattern} in {nb_dir}")
        return 0

    print(f"Found {len(notebooks)} notebooks in {nb_dir}")
    results = {"ok": 0, "fail": 0, "timeout": 0, "errors": 0}

    for i, nb in enumerate(notebooks, 1):
        print(f"\n[{i}/{len(notebooks)}] {nb.name}")
        rc = execute_notebook(str(nb), kernel=kernel, timeout=timeout, in_place=True)
        if rc == 0:
            results["ok"] += 1
        elif rc == 2:
            results["timeout"] += 1
        elif rc == 3:
            results["errors"] += 1
        else:
            results["fail"] += 1

    print(f"\n{'='*50}")
    print(f"Total: {len(notebooks)} | OK: {results['ok']} | Errors: {results['errors']} | Failed: {results['fail']} | Timeout: {results['timeout']}")
    return 1 if results["fail"] > 0 or results["timeout"] > 0 else 0


def main():
    parser = argparse.ArgumentParser(description="Execute notebooks via WSL papermill")
    sub = parser.add_subparsers(dest="command")

    # execute
    p_exec = sub.add_parser("execute", help="Execute a single notebook")
    p_exec.add_argument("notebook", help="Path to notebook")
    p_exec.add_argument("--output", help="Output path (default: in-place)")
    p_exec.add_argument("--kernel", default="python3", help="Kernel name")
    p_exec.add_argument("--timeout", type=int, default=300, help="Timeout in seconds")

    # batch
    p_batch = sub.add_parser("batch", help="Execute all notebooks in directory")
    p_batch.add_argument("directory", help="Directory containing notebooks")
    p_batch.add_argument("--pattern", default="*.ipynb", help="Glob pattern")
    p_batch.add_argument("--kernel", default="python3", help="Kernel name")
    p_batch.add_argument("--timeout", type=int, default=300, help="Timeout per notebook")

    # check-env
    sub.add_parser("check-env", help="Check WSL papermill environment")

    args = parser.parse_args()
    if args.command == "execute":
        sys.exit(execute_notebook(args.notebook, args.output, args.kernel, args.timeout))
    elif args.command == "batch":
        sys.exit(batch_execute(args.directory, args.pattern, args.kernel, args.timeout))
    elif args.command == "check-env":
        sys.exit(0 if check_env() else 1)
    else:
        parser.print_help()


if __name__ == "__main__":
    main()
