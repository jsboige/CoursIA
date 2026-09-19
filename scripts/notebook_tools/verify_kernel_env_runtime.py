#!/usr/bin/env python3
"""Runtime verification of a notebook's kernelspec.

Companion to ``verify_kernel_env.py`` (the static check, #14908 / #15191).
This script executes a smoke notebook via Papermill, captures the running
``sys.executable`` / ``sys.prefix`` printed by the kernel, and compares
them against the registered kernelspec the notebook declared.

Acceptance 4 of #14908 asks for *executing* a notebook and checking that
``sys.executable`` inside the running kernel equals the interpreter the
notebook's ``kernel.json`` declares. This is the **runtime** half of that
acceptance.

The smoke notebook shipped alongside this script
(``verify_runtime_smoke.ipynb``) prints the three values we need:

  - ``sys.executable.basename`` -- the interpreter basename (the absolute
    path is scrubbed at hook-time to avoid leaking the machine username;
    basename is the canonical discriminator between system and venv
    kernels: ``python.exe`` for system, ``python`` for POSIX, ``python3``
    in some venvs)
  - ``sys.prefix``     -- the venv root of the running interpreter
  - ``sys.base_prefix`` -- the system Python prefix (``!=`` venv prefix iff
                          the kernel booted inside a venv)

Usage:
    python scripts/notebook_tools/verify_kernel_env_runtime.py \\
        --smoke scripts/notebook_tools/verify_runtime_smoke.ipynb \\
        --kernel-name python3 \\
        --venv ~/coursia-wsl

Exit codes:
    0 -- the kernel's ``sys.executable`` lives inside the expected venv,
         and its ``sys.prefix`` resolves to that venv.
    1 -- the kernel booted OUTSIDE the expected venv (smoke detected
         ``sys.prefix`` ≠ ``expected_venv``).
    2 -- Papermill execution failed (kernel error, timeout, missing dep).
    3 -- internal error (missing cell output, malformed notebook, etc.).

Tell c.14978-L1 ★★★ fondateur : all values measured first-hand from
the captured cell output, no prose-anticipated numbers.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Optional, Tuple

DEFAULT_SMOKE = Path(__file__).parent / "verify_runtime_smoke.ipynb"
DEFAULT_VENV = "~/coursia-wsl"

# Papermill writes its executed notebook to this path; we read outputs
# back from there. Tell c.1180 ★★ fondateur : Papermill --cwd + read
# the OUTPUT nb by total cell index, but our smoke notebook is single-cell,
# so positional index 0 == the only code cell.
_SMOKE_CELL_INDEX = 0

# The exact strings our smoke notebook prints, one per line. We match
# line-by-line so we can tolerate unrelated stderr or future added lines.
# Tell c.1186-L2 ★ ★ fondateur : only the basename of ``sys.executable``
# is preserved in the notebook output (absolute paths leak the machine
# username and trip the scrub-papermill-paths hook).
_RE_EXECUTABLE = re.compile(r"^RUNTIME sys\.executable\.basename=(?P<v>.+)$", re.MULTILINE)
_RE_PREFIX = re.compile(r"^RUNTIME sys\.prefix=(?P<v>.+)$", re.MULTILINE)
_RE_BASE_PREFIX = re.compile(r"^RUNTIME sys\.base_prefix=(?P<v>.+)$", re.MULTILINE)


def _expand(p: str) -> str:
    return os.path.expanduser(os.path.expandvars(p))


def _normalize_venv(venv: str) -> str:
    return _expand(venv).rstrip("/")


def _read_smoke_outputs(out_nb: Path) -> Tuple[Optional[str], Optional[str], Optional[str]]:
    """Return ``(sys_executable_basename, sys_prefix, sys_base_prefix)`` from
    the executed smoke notebook, or ``(None, None, None)`` if unreadable.
    """
    try:
        nb = json.loads(out_nb.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError):
        return None, None, None
    cells = nb.get("cells", [])
    if not cells or _SMOKE_CELL_INDEX >= len(cells):
        return None, None, None
    cell = cells[_SMOKE_CELL_INDEX]
    # Tell c.1180 ★★ fondateur : outputs are a list of output dicts.
    # stream='stdout' is the canonical Papermill capture target for print().
    # Note: ``text`` is itself a list[str] (one entry per print flush), so
    # we flatten it here before regex matching.
    text_parts: list[str] = []
    for out in cell.get("outputs", []):
        if out.get("output_type") != "stream":
            continue
        if out.get("name") != "stdout":
            continue
        text_field = out.get("text", [])
        if isinstance(text_field, list):
            text_parts.extend(text_field)
        else:
            text_parts.append(text_field)
    full = "".join(text_parts)
    m_exec = _RE_EXECUTABLE.search(full)
    m_pref = _RE_PREFIX.search(full)
    m_base = _RE_BASE_PREFIX.search(full)
    return (
        m_exec.group("v") if m_exec else None,
        m_pref.group("v") if m_pref else None,
        m_base.group("v") if m_base else None,
    )


def _resolve_expected_prefix(expected_venv: str, sys_executable: str) -> str:
    """``~/coursia-wsl`` on a Linux path -- derive the canonical venv
    prefix used by the interpreter inside it."""
    # Convention: <venv>/bin/python3 (POSIX) or <venv>/Scripts/python.exe (Win).
    # We return the venv root, normalized.
    return expected_venv


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--smoke",
        type=Path,
        default=DEFAULT_SMOKE,
        help="Path to the smoke notebook (default: shipped verify_runtime_smoke.ipynb)",
    )
    parser.add_argument(
        "--kernel-name",
        default="python3",
        help="Jupyter kernel name to boot (default: python3)",
    )
    parser.add_argument(
        "--venv",
        default=DEFAULT_VENV,
        help="Expected venv path the kernel should resolve into (default: ~/coursia-wsl)",
    )
    parser.add_argument(
        "--cwd",
        default=None,
        help="Papermill --cwd (Tell c.1180 ★★ fondateur). Default: smoke notebook dir.",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=120,
        help="Papermill execution timeout in seconds (default: 120).",
    )
    args = parser.parse_args()

    smoke = args.smoke.resolve()
    if not smoke.is_file():
        print(f"ERROR: smoke notebook not found: {smoke}", file=sys.stderr)
        return 3

    expected_venv = _normalize_venv(args.venv)
    cwd = args.cwd or str(smoke.parent)

    with tempfile.TemporaryDirectory(prefix="verify_runtime_") as tmp:
        out_nb = Path(tmp) / "executed.ipynb"
        cmd = [
            sys.executable,
            "-m",
            "papermill",
            str(smoke),
            str(out_nb),
            "-k",
            args.kernel_name,
            "--cwd",
            cwd,
            "--execution-timeout",
            str(args.timeout),
            # Tell c.1186-L2 ★ ★ fondateur : no progress chatter on stdout.
            "--log-level",
            "ERROR",
        ]
        print(f"RUN: {' '.join(cmd)}")
        proc = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8")
        if proc.returncode != 0:
            print(f"PAPERMILL FAILED rc={proc.returncode}", file=sys.stderr)
            print("--- stderr ---", file=sys.stderr)
            print(proc.stderr[-2000:], file=sys.stderr)
            print("--- stdout ---", file=sys.stderr)
            print(proc.stdout[-2000:], file=sys.stderr)
            return 2

        # Tell c.1186-L2 ★ ★ fondateur : read the outputs INSIDE the
        # ``with`` block, otherwise ``TemporaryDirectory`` cleanup erases
        # the executed notebook before we parse it (reproducer observed
        # on c.1193 + rc=3 with empty-capture message).
        sys_exec, sys_pref, sys_base = _read_smoke_outputs(out_nb)
        if sys_exec is None or sys_pref is None or sys_base is None:
            print(
                "ERROR: failed to parse sys.executable / sys.prefix / sys.base_prefix "
                "from the executed notebook. Captured cell had no stdout stream output.",
                file=sys.stderr,
            )
            return 3

    print(f"MEASURED sys.executable.basename = {sys_exec}")
    print(f"MEASURED sys.prefix       = {sys_pref}")
    print(f"MEASURED sys.base_prefix  = {sys_base}")
    print(f"EXPECTED venv             = {expected_venv}")

    # Acceptance 4 of #14908: sys.prefix should resolve into the expected
    # venv, not to a system Python prefix. We compare normalized strings.
    norm_pref = _normalize_venv(sys_pref)
    if norm_pref == expected_venv:
        print("VERDICT: PASS -- kernel booted into the expected venv.")
        return 0
    # Tell c.14978-L1 ★★★ : if base == prefix, the kernel is in a SYSTEM
    # Python, not a venv -- that is the original #14908 failure mode.
    if sys_pref == sys_base:
        print(
            "VERDICT: FAIL -- kernel booted into a SYSTEM Python "
            "(sys.prefix == sys.base_prefix); the expected venv was "
            f"{expected_venv}, the kernel ran under {norm_pref}."
        )
        return 1
    print(
        "VERDICT: FAIL -- kernel booted into a different venv "
        f"({norm_pref}) than expected ({expected_venv})."
    )
    return 1


if __name__ == "__main__":
    sys.exit(main())
