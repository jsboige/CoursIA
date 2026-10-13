"""Resolve a bash that actually honors POSIX semantics for the test suite.

`shutil.which("bash")` follows the PATH order, and on some Windows machines
`C:\Windows\System32` precedes Git-for-Windows -- so `which("bash")` lands on
the WSL legacy launcher stub, which corrupts both `-c` strings (shell
assignments silently vanish: `X=1; echo $X` prints `X=`) and Windows script
paths passed as arguments (backslashes and the drive colon are swallowed:
`D:\Dev\...` becomes `D:Dev...`, exit 127). Issue #17201 measured all 7
stable Windows-local reds in scripts/tests/ against this single cause.

The sanity probe below is the discriminator: a real bash (native, Git's,
or reached through `wsl.exe -e`) prints `1`; the legacy stub prints an
empty value. Tests importing this module keep their POSIX semantics on
every machine, and skip honestly where no sane bash exists.
"""
from __future__ import annotations

import shutil
import subprocess
from pathlib import Path

# Git-for-Windows standard install locations, in case the PATH hit is the
# WSL stub (order matters: PATH first so CI and dev boxes keep their
# existing resolution whenever it is sane).
_GIT_BASH_CANDIDATES = (
    r"C:\Program Files\Git\bin\bash.exe",
    r"C:\Program Files (x86)\Git\bin\bash.exe",
)


def _bash_is_sane(candidate: str) -> bool:
    """True if `candidate` honors shell assignment + `$VAR` expansion."""
    try:
        probe = subprocess.run(
            [candidate, "-c", "X=1; echo $X"],
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=10,
        )
    except (OSError, subprocess.TimeoutExpired):
        return False
    return probe.returncode == 0 and probe.stdout.strip() == "1"


def resolve_bash() -> str | None:
    """Return a bash binary that passes the sanity probe, else None.

    Candidates: PATH hit first (preserves CI/native behavior), then
    Git-for-Windows standard locations. Callers should skip (not fail)
    when this returns None.
    """
    candidates: list[str] = []
    which_hit = shutil.which("bash")
    if which_hit:
        candidates.append(which_hit)
    for location in _GIT_BASH_CANDIDATES:
        if location not in candidates and Path(location).exists():
            candidates.append(location)
    for candidate in candidates:
        if _bash_is_sane(candidate):
            return candidate
    return None
