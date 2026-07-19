"""
lean_notebook_utils - Cross-platform utilities for Lean 4 notebook execution

Provides a unified interface for running Lean 4 code from Jupyter notebooks
on Windows (via WSL), Linux, and macOS (native lake/lean via elan).

Usage:
    from lean_notebook_utils import (
        find_lean_project, get_lean_project_path,
        run_lake, run_lean_snippet, count_sorry,
        display_lean_module, read_lean_module,
        is_native_platform
    )

    # Find and build a Lean project
    project_path = get_lean_project_path("grothendieck_lean")
    rc, out, err = run_lake(project_path, "build Grothendieck", timeout=1500)

    # Run a Lean snippet
    result = run_lean_snippet(project_path, "#eval 2 + 2")

    # Count sorry in .lean files
    n = count_sorry(project_path, "Grothendieck/")

Epic #2314, Issue #2315.
"""

import subprocess
import tempfile
import platform
import shutil
import os
import re
import textwrap
from pathlib import Path
from typing import Optional, Tuple


# ---------------------------------------------------------------------------
# Platform detection
# ---------------------------------------------------------------------------

def is_native_platform() -> bool:
    """True on Linux/macOS where lake/lean run natively (no WSL needed)."""
    return platform.system() in ("Linux", "Darwin")


def is_windows() -> bool:
    """True on Windows (WSL bridge required for Lean)."""
    return platform.system() == "Windows"


def _find_lake() -> str:
    """Find the lake executable for native execution."""
    lake = shutil.which("lake")
    if lake:
        return lake
    elan_bin = Path.home() / ".elan" / "bin"
    for name in ("lake", "lake.exe"):
        candidate = elan_bin / name
        if candidate.exists():
            return str(candidate)
    raise FileNotFoundError(
        "lake not found. Install Lean 4 via elan:\n"
        "  curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh"
    )


# ---------------------------------------------------------------------------
# Project discovery
# ---------------------------------------------------------------------------

def find_lean_project(project_name: str) -> Path:
    """Find a Lake project directory by walking parent directories.

    Searches from multiple starting points to handle both interactive use
    and Papermill execution (where CWD may differ from notebook location).

    Args:
        project_name: Directory name of the Lake project (e.g. "grothendieck_lean")

    Returns:
        Absolute Path to the project directory.

    Raises:
        FileNotFoundError: If the project cannot be found.
    """
    starts = [Path.cwd().resolve()]

    # Papermill passes the notebook path as a parameter
    nb_file = os.environ.get("NB_FILE") or globals().get("__vsc_ipynb_file__")
    if nb_file:
        starts.append(Path(nb_file).resolve().parent)

    for start in starts:
        current = start
        for _ in range(12):
            candidate = current / project_name
            if candidate.exists() and (candidate / "lakefile.lean").exists():
                return candidate.resolve()
            current = current.parent
            if current == current.parent:
                break

    raise FileNotFoundError(
        f"{project_name}/ not found — check working directory. "
        f"Searched from: {starts}"
    )


def win_to_wsl(win_path: Path) -> str:
    """Convert a Windows path to a WSL mount path (C:\\x -> /mnt/c/x).

    On Linux/macOS, returns the path as-is (posix string).

    Args:
        win_path: A Windows Path object.

    Returns:
        WSL-compatible path string.
    """
    p = win_path.resolve()
    drive_letter = p.drive

    if not drive_letter or len(drive_letter) < 2:
        s = str(p)
        if s.startswith("/mnt/"):
            return s  # Already a WSL path
        # Fallback: try to detect from common mount points
        drive_letter = "C:"

    drive = drive_letter[0].lower()
    return f"/mnt/{drive}{p.as_posix()[2:]}"


def get_lean_project_path(project_name: str) -> str:
    """Get the appropriate path for a Lean project based on platform.

    On Windows: returns a WSL path (/mnt/c/...) for use in WSL commands.
    On Linux/macOS: returns the native absolute path.

    Args:
        project_name: Directory name of the Lake project.

    Returns:
        Path string suitable for the current platform.
    """
    win_path = find_lean_project(project_name)
    if is_native_platform():
        return str(win_path.resolve())
    return win_to_wsl(win_path)


def _run_capture(cmd, timeout, cwd=None):
    """Run ``cmd`` capturing stdout/stderr via temp files.

    Avoids ``subprocess.run(capture_output=True)`` whose per-stream
    ``_readerthread`` race on Windows can silently drop output when the process
    exits (the Lean-15/15b/Kochen-Specker C.2 defect: committed notebook outputs
    were only an ``Exception in thread (_readerthread)`` trace, with no real Lean
    output). Returns ``(returncode, stdout, stderr)``; raises
    ``subprocess.TimeoutExpired`` and ``FileNotFoundError`` like ``subprocess.run``.
    See PRs #3216 (Lean-15), #3222 (Lean-15b).
    """
    out_f = tempfile.NamedTemporaryFile('wb', delete=False, suffix='.out')
    err_f = tempfile.NamedTemporaryFile('wb', delete=False, suffix='.err')
    out_path, err_path = out_f.name, err_f.name
    out_f.close()
    err_f.close()
    try:
        with open(out_path, 'wb') as o, open(err_path, 'wb') as e:
            r = subprocess.run(cmd, stdout=o, stderr=e, cwd=cwd, timeout=timeout)
        out = Path(out_path).read_text(encoding='utf-8', errors='replace')
        err = Path(err_path).read_text(encoding='utf-8', errors='replace')
        return r.returncode, out, err
    finally:
        for p in (out_path, err_path):
            try:
                Path(p).unlink()
            except OSError:
                pass


# ---------------------------------------------------------------------------
# Lean command execution
# ---------------------------------------------------------------------------

def run_lake(
    project_path: str,
    args: str,
    timeout: int = 600,
    tail: int = 20,
) -> Tuple[int, str, str]:
    """Run a lake command in the specified project directory.

    On Windows: executes via WSL Ubuntu.
    On Linux/macOS: executes natively.

    Args:
        project_path: Path to the Lake project (from get_lean_project_path).
        args: Lake arguments (e.g. "build Grothendieck").
        timeout: Timeout in seconds (default 600).
        tail: Number of lines to keep from the end of output (WSL mode only).

    Returns:
        Tuple of (returncode, stdout, stderr).
    """
    if is_native_platform():
        lake = _find_lake()
        try:
            return _run_capture([lake] + args.split(), timeout, cwd=project_path)
        except subprocess.TimeoutExpired:
            return -1, "", f"TIMEOUT after {timeout}s"
        except FileNotFoundError:
            return -2, "", f"lake executable not found: {lake}"
    else:
        cmd = (
            f"source ~/.elan/env 2>/dev/null; "
            f"cd {project_path} && lake {args} 2>&1 | tail -{tail}"
        )
        try:
            return _run_capture(["wsl", "-d", "Ubuntu", "--", "bash", "-lc", cmd], timeout)
        except subprocess.TimeoutExpired:
            return -1, "", f"TIMEOUT after {timeout}s"
        except FileNotFoundError:
            return -2, "", (
                "WSL introuvable. Ce notebook requiert Windows + WSL Ubuntu, "
                "ou Linux/macOS avec elan installe."
            )


def run_lean_snippet(
    project_path: str,
    snippet: str,
    timeout: int = 300,
    snippet_id: str = "snippet",
) -> str:
    """Run a Lean code snippet against a Lake project.

    Writes the snippet to a temp file and executes it with `lake env lean`.

    Args:
        project_path: Path to the Lake project.
        snippet: Lean source code to execute.
        timeout: Timeout in seconds.
        snippet_id: Identifier for the temp file (to avoid collisions).

    Returns:
        Combined stdout + stderr as a string.
    """
    snippet = textwrap.dedent(snippet).strip() + "\n"
    tmp_file = f"/tmp/lean_{snippet_id}.lean"

    if is_native_platform():
        lake = _find_lake()
        tmp_path = Path(tmp_file)
        tmp_path.write_text(snippet, encoding="utf-8")
        try:
            _rc, out, err = _run_capture([lake, "env", "lean", str(tmp_path)], timeout, cwd=project_path)
            return (out or "") + (err or "")
        except subprocess.TimeoutExpired:
            return f"TIMEOUT after {timeout}s"
        finally:
            tmp_path.unlink(missing_ok=True)
    else:
        write_cmd = f"cat > {tmp_file} << 'LEAN_EOF'\n{snippet}LEAN_EOF"
        lean_cmd = f"cd {project_path} && lake env lean {tmp_file} 2>&1"
        full_cmd = f"{write_cmd}\n{lean_cmd}"
        try:
            _rc, out, err = _run_capture(["wsl", "-d", "Ubuntu", "--", "bash", "-lc", full_cmd], timeout)
            return (out or "") + (err or "")
        except subprocess.TimeoutExpired:
            return f"TIMEOUT after {timeout}s"
        except FileNotFoundError:
            return "WSL introuvable. Requiert Windows + WSL ou Linux/macOS natif."


# ---------------------------------------------------------------------------
# Sorry counting
# ---------------------------------------------------------------------------

_SORRY_TOKEN_RE = re.compile(r"\bsorry\b")


def _strip_lean_comments(content: str) -> str:
    """Strip Lean line comments (``--``) and nested block comments (``/- -/``).

    Character-level scan handling nested block comments (Lean allows them).
    Byte-identical twin of the canonical ``strip_lean_comments`` in
    ``agent_tests/prover/lean_utils.py`` (FX-6 #1453): kept local here to avoid
    coupling the notebook utility to the prover harness package. If you edit
    one, edit the other to keep the two counters from drifting.

    No string-literal awareness: Lean proofs virtually never contain the token
    ``sorry`` inside a string literal, and over-stripping there cannot create a
    false token.
    """
    out = []
    i, n, depth = 0, len(content), 0
    while i < n:
        two = content[i:i + 2]
        if depth == 0 and two == "--":
            j = content.find("\n", i)
            i = n if j < 0 else j
            continue
        if two == "/-":
            depth += 1
            i += 2
            continue
        if depth > 0 and two == "-/":
            depth -= 1
            i += 2
            continue
        if depth == 0:
            out.append(content[i])
        i += 1
    return "".join(out)


def count_sorry(project_path: str, subdir: str = "") -> int:
    """Count REAL ``sorry`` tactics in ``.lean`` source (cross-platform).

    Excludes ``sorry`` mentions in block comments (``/- ... -/``) and line
    comments (``-- ...``), and skips the ``.lake`` build/package cache so only
    authored source is tallied. Pure-Python (no ``grep``/WSL fork) so the count
    is identical on every platform.

    Mirrors the canonical ``count_real_sorries`` semantics
    (``agent_tests/prover/lean_utils.py``, FX-6 #1453): after stripping comments,
    the word-bounded token catches every real form (``exact sorry``,
    ``:= by sorry``, bare ``sorry``, ``sorry -- inline``) and ignores prose
    mentions in docstrings/comments. See issue #7414 for the docstring/impl
    mismatch this corrects: the previous bare ``grep -rc sorry`` counted every
    ``sorry`` token (including prose in docstrings/comments and vendored
    ``.lake`` source), inflating the tally on lakes with sorry-rich prose.

    Args:
        project_path: Path to the Lake project.
        subdir: Optional subdirectory to scan (e.g. "Grothendieck/").

    Returns:
        Number of real ``sorry`` tactics in production source, or ``-1`` if the
        project directory cannot be read. ``0`` if the directory exists but has
        no ``.lean`` source.
    """
    search_dir = os.path.join(project_path, subdir) if subdir else project_path
    if not os.path.isdir(search_dir):
        return -1

    total = 0
    for root, dirs, files in os.walk(search_dir):
        # Skip the Lake build cache + vendored deps (compiled artifacts and
        # Mathlib source, not authored content).
        dirs[:] = [d for d in dirs if d != ".lake"]
        for name in files:
            if not name.endswith(".lean"):
                continue
            try:
                with open(os.path.join(root, name), encoding="utf-8") as f:
                    content = f.read()
            except OSError:
                continue
            total += len(_SORRY_TOKEN_RE.findall(_strip_lean_comments(content)))
    return total


# ---------------------------------------------------------------------------
# File reading (cross-platform, reads from native filesystem)
# ---------------------------------------------------------------------------

def read_lean_module(
    project_name: str,
    module_path: str,
) -> str:
    """Read a .lean source file from a Lake project.

    Works on all platforms by reading from the native filesystem
    (the project directory is accessible directly on Windows too).

    Args:
        project_name: Directory name of the Lake project.
        module_path: Relative path to the .lean file (e.g. "Grothendieck/CategoryAndSites.lean").

    Returns:
        File content as a string.
    """
    project_dir = find_lean_project(project_name)
    path = project_dir / module_path
    if not path.exists():
        return f"[FICHIER INTROUVABLE] {path}"
    return path.read_text(encoding="utf-8")


def display_lean_module(
    project_name: str,
    module_path: str,
    max_lines: Optional[int] = None,
    highlight: Optional[list] = None,
):
    """Display a .lean source file with line numbers.

    Args:
        project_name: Directory name of the Lake project.
        module_path: Relative path to the .lean file.
        max_lines: If set, only show the first N lines.
        highlight: List of line numbers to mark with '>>>' (1-indexed).
    """
    content = read_lean_module(project_name, module_path)
    if content.startswith("[FICHIER INTROUVABLE]"):
        print(content)
        return

    lines = content.splitlines()
    if max_lines:
        lines = lines[:max_lines]

    highlight = set(highlight or [])
    module_name = Path(module_path).stem
    print(f"--- {module_path} ---")
    for i, line in enumerate(lines, 1):
        marker = " >>>" if i in highlight else "    "
        print(f"{marker} {i:>3d} | {line}")

    total = len(content.splitlines())
    if max_lines and total > max_lines:
        print(f"    ... ({total - max_lines} lignes restantes sur {total} total)")
    print(f"--- fin ({total} lignes) ---")
