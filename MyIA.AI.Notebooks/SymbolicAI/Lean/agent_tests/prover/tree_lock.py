"""Per-Lean-project-tree lockfile for prover BG runs (See #6790).

Incident 2026-07-16 (DEMO 62, HashlifeCorrectness.lean): two prover runs
(run-6 and run-7) executed concurrently on the SAME working tree. Run-6
materialized a build-passing +28-line candidate; run-7, launched by another
session on the same tree, suffered sorry-line drift from run-6's in-place
edit, made zero attempts, and its end-of-run cleanup reverted the tree —
destroying run-6's validated work. Two `lake` processes also shared one
`.lake` directory (spurious-verify contention). Lesson: UN SEUL acteur
prover par arbre.

This module provides an advisory lockfile at `<lake_root>/.prover.lock`
(gitignored). Acquisition is atomic (O_CREAT | O_EXCL). The lock records
holder pid / host / demo_id / start time so a second launcher can print an
actionable refusal instead of corrupting the tree.

Staleness: a lock whose holder pid is dead is broken automatically — but
ONLY when the recorded host matches ours. PIDs are meaningless across the
Windows/WSL boundary (separate pid namespaces), so a foreign-host lock is
never auto-broken; the operator decides via --force-lock.

WARNING (Windows): never probe pid liveness with ``os.kill(pid, 0)`` — on
Windows CPython that call TERMINATES the target process (TerminateProcess
with exit code 0). ``pid_alive`` below uses OpenProcess/GetExitCodeProcess
via ctypes instead.
"""

from __future__ import annotations

import ctypes
import json
import os
import platform
import time
from pathlib import Path

LOCK_BASENAME = ".prover.lock"

_LAKEFILE_NAMES = ("lakefile.lean", "lakefile.toml")

# GetExitCodeProcess reports this while the process is still running.
_STILL_ACTIVE = 259
_PROCESS_QUERY_LIMITED_INFORMATION = 0x1000


def host_id() -> str:
    """Stable-enough identity of this pid namespace (node + os family)."""
    return f"{platform.node()}/{os.name}"


def pid_alive(pid: int) -> bool:
    """True if ``pid`` is a live process on THIS host. Never signals it."""
    if pid <= 0:
        return False
    if os.name == "nt":
        kernel32 = ctypes.windll.kernel32
        handle = kernel32.OpenProcess(
            _PROCESS_QUERY_LIMITED_INFORMATION, False, pid
        )
        if not handle:
            return False
        try:
            exit_code = ctypes.c_ulong()
            ok = kernel32.GetExitCodeProcess(handle, ctypes.byref(exit_code))
            return bool(ok) and exit_code.value == _STILL_ACTIVE
        finally:
            kernel32.CloseHandle(handle)
    try:
        os.kill(pid, 0)  # POSIX: signal 0 = existence probe, sends nothing
    except ProcessLookupError:
        return False
    except PermissionError:
        return True  # exists, owned by someone else
    return True


def find_lean_project_root(filepath: str | Path) -> Path | None:
    """Walk up from ``filepath`` to the enclosing lake root (lakefile.*)."""
    p = Path(filepath).resolve()
    if p.is_file() or not p.exists():
        p = p.parent
    for candidate in (p, *p.parents):
        if any((candidate / name).exists() for name in _LAKEFILE_NAMES):
            return candidate
    return None


def read_lock(lock_path: Path) -> dict:
    """Best-effort parse of an existing lock. Corrupt lock -> {} (treated
    as unreadable-foreign: refused unless --force-lock)."""
    try:
        return json.loads(lock_path.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return {}


def acquire_tree_lock(
    root: Path,
    demo_id: int | str,
    force: bool = False,
) -> tuple[Path | None, str]:
    """Try to take the advisory lock for ``root``.

    Returns ``(lock_path, message)`` on success, ``(None, reason)`` on
    refusal. Auto-breaks a same-host lock whose holder pid is dead;
    ``force=True`` breaks anything (operator decision).
    """
    lock_path = root / LOCK_BASENAME
    payload = json.dumps(
        {
            "pid": os.getpid(),
            "host": host_id(),
            "demo_id": demo_id,
            "started_utc": time.strftime(
                "%Y-%m-%dT%H:%M:%SZ", time.gmtime()
            ),
            "started_epoch": time.time(),
        },
        indent=2,
    )

    for _ in range(2):  # second pass after breaking a stale/forced lock
        try:
            fd = os.open(
                str(lock_path), os.O_CREAT | os.O_EXCL | os.O_WRONLY
            )
        except FileExistsError:
            holder = read_lock(lock_path)
            h_pid = int(holder.get("pid") or -1)
            h_host = holder.get("host", "<unreadable>")
            h_age = time.time() - float(
                holder.get("started_epoch") or time.time()
            )
            desc = (
                f"holder pid={h_pid} host={h_host} "
                f"demo={holder.get('demo_id')} age={h_age:.0f}s"
            )
            same_host = h_host == host_id()
            if force or (same_host and not pid_alive(h_pid)):
                why = "forced" if force else "stale (holder pid dead)"
                try:
                    lock_path.unlink()
                except OSError as exc:
                    return None, f"REFUSED cannot break lock ({exc}): {desc}"
                # Loop back and race for a fresh O_EXCL create — if another
                # launcher wins that race, the retry hits FileExistsError
                # with a live holder and is refused (no double-break).
                print(
                    f"[BG] TREE_LOCK_BROKEN reason={why} {desc}", flush=True
                )
                continue
            hint = (
                "another prover is active on this tree (UN SEUL acteur "
                "prover par arbre, #6790); wait for it or re-run with "
                "--force-lock if you are certain it is gone"
            )
            return None, f"REFUSED {desc} — {hint}"
        with os.fdopen(fd, "w", encoding="utf-8") as fh:
            fh.write(payload)
        return lock_path, f"acquired {lock_path}"
    return None, "REFUSED could not acquire after breaking existing lock"


def release_tree_lock(lock_path: Path | None) -> None:
    """Remove the lock IF it is still ours (pid match). Never raises."""
    if lock_path is None:
        return
    try:
        holder = read_lock(Path(lock_path))
        if int(holder.get("pid") or -1) == os.getpid():
            Path(lock_path).unlink()
    except OSError:
        pass  # best-effort: a stale lock is auto-broken by the next run
