#!/usr/bin/env python3
"""Execute Jupyter notebooks via papermill (native or WSL).

On macOS/Linux: runs papermill natively via the system Python.
On Windows: runs papermill inside WSL (cross-OS kernel workaround).

The WSL mode works around the jupyter_client cross-OS connection issue:
Windows-side jupyter_client cannot connect to WSL kernels because
WSL strips backslashes from connection file paths. WSL mode runs
papermill natively inside WSL, avoiding the cross-OS boundary entirely.

Prerequisites (WSL, one-time setup):
    wsl -e bash -c "python3 -m venv ~/coursia-wsl"
    wsl -e bash -c "source ~/coursia-wsl/bin/activate && pip install nashpy matplotlib papermill ipykernel scipy numpy"
    wsl -e bash -c "source ~/coursia-wsl/bin/activate && python3 -m ipykernel install --user --name python3"

Prerequisites (native macOS/Linux):
    pip install papermill ipykernel
    (plus any notebook-specific dependencies: nashpy, matplotlib, numpy, scipy, etc.)

Usage:
    python wsl_papermill.py execute <notebook.ipynb> [--output <path>] [--kernel python3] [--mode auto]
    python wsl_papermill.py batch <dir> [--pattern "*.ipynb"] [--kernel python3] [--mode auto]
    python wsl_papermill.py check-env [--mode auto]

Examples:
    python wsl_papermill.py execute MyIA.AI.Notebooks/GameTheory/GameTheory-1-Setup.ipynb
    python wsl_papermill.py batch MyIA.AI.Notebooks/GameTheory/ --kernel python3
    python wsl_papermill.py check-env --mode native
"""

import argparse
import json
import platform
import shutil
import subprocess
import sys
import time
from pathlib import Path

WSL_VENV = "~/coursia-wsl"
WSL_PAPERMILL_CMD = f"source {WSL_VENV}/bin/activate && papermill"
REPO_ROOT = Path(__file__).resolve().parent.parent.parent


def _default_mode() -> str:
    """Auto-detect execution mode based on platform."""
    return "wsl" if platform.system() == "Windows" else "native"


# =============================================================================
# WSL mode (Windows only)
# =============================================================================

_WIN_DRIVE_RE = __import__("re").compile(r"^([A-Za-z]:)[\\/](.*)$")


def win_to_wsl_path(win_path: str) -> str:
    """Convert a Windows path (e.g. ``D:\\projects\\repo``) to its WSL mount
    form (``/mnt/d/projects/repo``).

    Works cross-platform: do NOT rely on ``pathlib.Path.drive`` — under
    WSL/POSIX the path parser is ``PurePosixPath`` which does not recognise a
    ``X:`` drive prefix (``p.drive == ""``), and ``Path.resolve()`` rewrites
    the path to ``/mnt/d/...`` which strips the drive letter entirely. Detect
    the Windows drive prefix with a regex so the conversion is identical on
    Windows, WSL, and Linux CI (#2871 part 2). A path without a drive prefix
    is returned unchanged.
    """
    m = _WIN_DRIVE_RE.match(win_path)
    if not m:
        return win_path  # no Windows drive prefix — already POSIX, leave as-is
    drive = m.group(1)[0].lower()
    rest = m.group(2).replace("\\", "/")
    return f"/mnt/{drive}/{rest}"


def run_wsl(cmd: str, timeout: int = 300) -> tuple[int, str, str]:
    """Run a command in WSL and return (exit_code, stdout, stderr)."""
    # Login shell (-l) so ~/.profile is sourced: kernels that shell out to
    # lake/lean (lean_dojo tracing, Lean-10) need ~/.elan/bin on PATH.
    result = subprocess.run(
        ["wsl", "-e", "bash", "-lc", cmd],
        capture_output=True, text=True, timeout=timeout
    )
    return result.returncode, result.stdout, result.stderr


def check_env_wsl() -> bool:
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


def execute_notebook_wsl(notebook: str, output: str | None = None,
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
    print(f"Executing (WSL): {nb_path.name} ...")

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

    return _validate_output(nb_path, elapsed)


# =============================================================================
# Native mode (macOS/Linux)
# =============================================================================

def check_env_native() -> bool:
    """Verify native papermill environment is set up."""
    print("Checking native papermill environment...")
    ok = True

    # Check papermill
    if shutil.which("papermill") or _find_papermill():
        print("  papermill: OK")
    else:
        print("  papermill: MISSING — run: pip install papermill ipykernel")
        ok = False

    # Check common packages
    pkgs = ["jupyter", "ipykernel"]
    for pkg in pkgs:
        try:
            __import__(pkg)
            print(f"  {pkg}: OK")
        except ImportError:
            print(f"  {pkg}: MISSING")
            ok = False

    # Check Lean tools if relevant
    for tool in ["lake", "lean"]:
        if shutil.which(tool):
            print(f"  {tool}: OK ({shutil.which(tool)})")
        else:
            print(f"  {tool}: not found (optional for Lean notebooks)")

    return ok


def _find_papermill() -> str | None:
    """Find papermill executable (may be in same Python as sys.executable)."""
    # Try running papermill via current Python
    try:
        result = subprocess.run(
            [sys.executable, "-m", "papermill", "--version"],
            capture_output=True, text=True, timeout=10
        )
        if result.returncode == 0:
            return sys.executable
    except Exception:
        pass
    return None


def execute_notebook_native(notebook: str, output: str | None = None,
                            kernel: str = "python3", timeout: int = 300,
                            in_place: bool = False) -> int:
    """Execute a single notebook via native papermill (macOS/Linux)."""
    nb_path = Path(notebook).resolve()
    if not nb_path.exists():
        print(f"ERROR: {nb_path} not found")
        return 1

    if output:
        out_path = str(Path(output).resolve())
    elif in_place:
        out_path = str(nb_path)
    else:
        out_path = str(nb_path.parent / f"{nb_path.stem}_output.ipynb")

    cmd = [
        sys.executable, "-m", "papermill",
        str(nb_path), out_path,
        "--kernel", kernel,
        "--cwd", str(nb_path.parent),
    ]

    print(f"Executing (native): {nb_path.name} ...")

    start = time.time()
    try:
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        elapsed = time.time() - start
    except subprocess.TimeoutExpired:
        print(f"  TIMEOUT after {timeout}s")
        return 2

    if result.returncode != 0:
        print(f"  FAILED ({elapsed:.1f}s)")
        if result.stderr:
            for line in result.stderr.strip().split("\n")[-10:]:
                print(f"    {line}")
        return 1

    # Copy output back if different from input
    if out_path != str(nb_path) and Path(out_path).exists():
        shutil.copy2(out_path, str(nb_path))

    return _validate_output(nb_path, elapsed)


# =============================================================================
# Shared validation
# =============================================================================

def _validate_output(nb_path: Path, elapsed: float) -> int:
    """Validate executed notebook output. Returns 0 (OK), 3 (errors), 0 (warning)."""
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


# =============================================================================
# Unified dispatch
# =============================================================================

def execute_notebook(notebook: str, output: str | None = None,
                     kernel: str = "python3", timeout: int = 300,
                     in_place: bool = False, mode: str = "auto") -> int:
    """Execute a single notebook, dispatching to native or WSL mode."""
    if mode == "auto":
        mode = _default_mode()

    if mode == "wsl":
        return execute_notebook_wsl(notebook, output, kernel, timeout, in_place)
    elif mode == "native":
        return execute_notebook_native(notebook, output, kernel, timeout, in_place)
    else:
        print(f"ERROR: unknown mode '{mode}' (use 'wsl', 'native', or 'auto')")
        return 1


def batch_execute(directory: str, pattern: str = "*.ipynb",
                  kernel: str = "python3", timeout: int = 300,
                  mode: str = "auto") -> int:
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
        rc = execute_notebook(str(nb), kernel=kernel, timeout=timeout,
                              in_place=True, mode=mode)
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


def check_env(mode: str = "auto") -> bool:
    """Check environment for the given mode."""
    if mode == "auto":
        mode = _default_mode()

    if mode == "wsl":
        return check_env_wsl()
    elif mode == "native":
        return check_env_native()
    else:
        print(f"ERROR: unknown mode '{mode}'")
        return False


def main():
    parser = argparse.ArgumentParser(
        description="Execute notebooks via papermill (native or WSL)")
    sub = parser.add_subparsers(dest="command")

    # execute
    p_exec = sub.add_parser("execute", help="Execute a single notebook")
    p_exec.add_argument("notebook", help="Path to notebook")
    p_exec.add_argument("--output", help="Output path (default: in-place)")
    p_exec.add_argument("--kernel", default="python3", help="Kernel name")
    p_exec.add_argument("--timeout", type=int, default=300, help="Timeout in seconds")
    p_exec.add_argument("--mode", default="auto",
                        choices=["auto", "wsl", "native"],
                        help="Execution mode (default: auto-detected)")

    # batch
    p_batch = sub.add_parser("batch", help="Execute all notebooks in directory")
    p_batch.add_argument("directory", help="Directory containing notebooks")
    p_batch.add_argument("--pattern", default="*.ipynb", help="Glob pattern")
    p_batch.add_argument("--kernel", default="python3", help="Kernel name")
    p_batch.add_argument("--timeout", type=int, default=300, help="Timeout per notebook")
    p_batch.add_argument("--mode", default="auto",
                         choices=["auto", "wsl", "native"],
                         help="Execution mode (default: auto-detected)")

    # check-env
    p_check = sub.add_parser("check-env", help="Check papermill environment")
    p_check.add_argument("--mode", default="auto",
                         choices=["auto", "wsl", "native"],
                         help="Environment to check (default: auto-detected)")

    args = parser.parse_args()
    if args.command == "execute":
        sys.exit(execute_notebook(args.notebook, args.output, args.kernel,
                                  args.timeout, mode=args.mode))
    elif args.command == "batch":
        sys.exit(batch_execute(args.directory, args.pattern, args.kernel,
                               args.timeout, mode=args.mode))
    elif args.command == "check-env":
        sys.exit(0 if check_env(args.mode) else 1)
    else:
        parser.print_help()


if __name__ == "__main__":
    main()
