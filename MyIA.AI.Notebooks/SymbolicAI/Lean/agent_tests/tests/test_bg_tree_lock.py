"""Unit tests for the per-tree prover lockfile (prover/tree_lock.py, #6790).

Incident 2026-07-16 (DEMO 62): two prover runs shared one working tree;
run-7's end-of-run cleanup reverted run-6's build-passing candidate. The
advisory lock makes the second launch refuse instead (exit 3 in
run_prover_bg.py).

All tests are offline — no lake, no Lean, tmp_path only.

Run from `agent_tests/`:
    python -m pytest tests/test_bg_tree_lock.py -q
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

# Make `prover/` importable regardless of how pytest was invoked.
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT))

from prover.tree_lock import (  # noqa: E402
    LOCK_BASENAME,
    acquire_tree_lock,
    find_lean_project_root,
    host_id,
    pid_alive,
    read_lock,
    release_tree_lock,
)


# ──────────────────────────────────────────────────────────────────────────
# find_lean_project_root — walks up to the enclosing lakefile
# ──────────────────────────────────────────────────────────────────────────


def test_project_root_found_from_nested_file(tmp_path):
    (tmp_path / "lakefile.lean").write_text("-- lake", encoding="utf-8")
    nested = tmp_path / "Conway" / "Life"
    nested.mkdir(parents=True)
    target = nested / "HashlifeCorrectness.lean"
    target.write_text("theorem t : True := by sorry", encoding="utf-8")

    assert find_lean_project_root(target) == tmp_path


def test_project_root_prefers_nearest_lakefile(tmp_path):
    """A vendored sub-lake (e.g. .lake/packages/mathlib) must lock ITS root,
    not the outer one — nearest lakefile wins."""
    (tmp_path / "lakefile.lean").write_text("-- outer", encoding="utf-8")
    inner = tmp_path / "vendored"
    inner.mkdir()
    (inner / "lakefile.toml").write_text("# inner", encoding="utf-8")
    target = inner / "Foo.lean"
    target.write_text("-- x", encoding="utf-8")

    assert find_lean_project_root(target) == inner


def test_project_root_none_without_lakefile(tmp_path):
    target = tmp_path / "Loose.lean"
    target.write_text("-- x", encoding="utf-8")
    assert find_lean_project_root(target) is None


# ──────────────────────────────────────────────────────────────────────────
# pid_alive — must never signal/kill (Windows os.kill(pid, 0) TERMINATES)
# ──────────────────────────────────────────────────────────────────────────


def test_pid_alive_self():
    assert pid_alive(os.getpid()) is True


def test_pid_alive_dead_child():
    """A spawned-then-exited child is reliably dead on this host."""
    proc = subprocess.Popen(
        [sys.executable, "-c", "pass"],
        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
    )
    proc.wait()
    assert pid_alive(proc.pid) is False


def test_pid_alive_rejects_nonpositive():
    assert pid_alive(0) is False
    assert pid_alive(-1) is False


# ──────────────────────────────────────────────────────────────────────────
# acquire / release lifecycle
# ──────────────────────────────────────────────────────────────────────────


def test_acquire_creates_lock_and_release_removes(tmp_path):
    lock_path, msg = acquire_tree_lock(tmp_path, demo_id=62)
    assert lock_path == tmp_path / LOCK_BASENAME
    assert lock_path.exists()
    holder = read_lock(lock_path)
    assert holder["pid"] == os.getpid()
    assert holder["host"] == host_id()
    assert holder["demo_id"] == 62

    release_tree_lock(lock_path)
    assert not lock_path.exists()


def test_second_acquire_refused_while_holder_alive(tmp_path):
    """The #6790 scenario: a second launcher on the same tree must be
    refused while the first (here: our own live pid) holds the lock."""
    lock_path, _ = acquire_tree_lock(tmp_path, demo_id=62)
    assert lock_path is not None

    second, reason = acquire_tree_lock(tmp_path, demo_id=63)
    assert second is None
    assert "REFUSED" in reason
    assert "--force-lock" in reason  # actionable refusal
    # The original lock is untouched.
    assert read_lock(lock_path)["demo_id"] == 62
    release_tree_lock(lock_path)


def test_stale_same_host_lock_is_auto_broken(tmp_path):
    """Holder pid dead + same host -> the lock is stale (e.g. run-6's
    silent death would have left one) and a new run takes over."""
    proc = subprocess.Popen(
        [sys.executable, "-c", "pass"],
        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
    )
    proc.wait()
    stale = tmp_path / LOCK_BASENAME
    stale.write_text(json.dumps({
        "pid": proc.pid, "host": host_id(), "demo_id": 9,
        "started_epoch": 0,
    }), encoding="utf-8")

    lock_path, _ = acquire_tree_lock(tmp_path, demo_id=62)
    assert lock_path is not None
    assert read_lock(lock_path)["pid"] == os.getpid()
    release_tree_lock(lock_path)


def test_foreign_host_lock_never_auto_broken(tmp_path):
    """PIDs are meaningless across the WSL/Windows boundary: a foreign-host
    lock must be refused even if that pid happens to be dead HERE."""
    foreign = tmp_path / LOCK_BASENAME
    foreign.write_text(json.dumps({
        "pid": 1, "host": "other-machine/posix", "demo_id": 9,
        "started_epoch": 0,
    }), encoding="utf-8")

    lock_path, reason = acquire_tree_lock(tmp_path, demo_id=62)
    assert lock_path is None
    assert "REFUSED" in reason
    assert foreign.exists()  # untouched


def test_force_lock_breaks_anything(tmp_path):
    foreign = tmp_path / LOCK_BASENAME
    foreign.write_text(json.dumps({
        "pid": os.getpid(), "host": "other-machine/posix", "demo_id": 9,
        "started_epoch": 0,
    }), encoding="utf-8")

    lock_path, _ = acquire_tree_lock(tmp_path, demo_id=62, force=True)
    assert lock_path is not None
    assert read_lock(lock_path)["pid"] == os.getpid()
    release_tree_lock(lock_path)


def test_corrupt_lock_refused_without_force(tmp_path):
    """An unreadable lock is treated as foreign (operator decides), never
    silently clobbered."""
    (tmp_path / LOCK_BASENAME).write_text("not json{", encoding="utf-8")

    lock_path, reason = acquire_tree_lock(tmp_path, demo_id=62)
    assert lock_path is None
    assert "REFUSED" in reason

    forced, _ = acquire_tree_lock(tmp_path, demo_id=62, force=True)
    assert forced is not None
    release_tree_lock(forced)


def test_release_only_removes_own_lock(tmp_path):
    """release_tree_lock must not remove a lock taken over by another pid
    (e.g. after a force-break race)."""
    other = tmp_path / LOCK_BASENAME
    other.write_text(json.dumps({
        "pid": os.getpid() + 424242, "host": host_id(),
        "started_epoch": 0,
    }), encoding="utf-8")

    release_tree_lock(other)
    assert other.exists()  # not ours -> untouched


def test_release_none_is_noop():
    release_tree_lock(None)  # must not raise


# ──────────────────────────────────────────────────────────────────────────
# run_prover_bg CLI wiring — BOTH launchers (the run-7 result JSON came from
# the INNER prover/run_prover_bg.py, so that one is the actual incident path)
# ──────────────────────────────────────────────────────────────────────────


def test_inner_launcher_refuses_locked_tree(tmp_path):
    """prover/run_prover_bg.run_prover must refuse a tree whose lock is held
    (returns result_kind='locked' BEFORE touching the file or any LLM)."""
    from prover.run_prover_bg import run_prover

    (tmp_path / "lakefile.lean").write_text("-- lake", encoding="utf-8")
    target = tmp_path / "Foo.lean"
    target.write_text("theorem t : True := by sorry", encoding="utf-8")

    # Simulate run-6 already active on this tree (live pid = our own).
    lock_path, _ = acquire_tree_lock(tmp_path, demo_id="run-6")
    try:
        summary = run_prover(filepath=str(target), line=1)
        assert summary["result_kind"] == "locked"
        assert "REFUSED" in summary["reason"]
        # The first holder's lock is untouched.
        assert read_lock(lock_path)["demo_id"] == "run-6"
    finally:
        release_tree_lock(lock_path)


def test_inner_launcher_signature_has_force_lock():
    import inspect
    from prover.run_prover_bg import run_prover

    sig = inspect.signature(run_prover)
    assert "force_lock" in sig.parameters
    assert sig.parameters["force_lock"].default is False


def test_launcher_exposes_force_lock_flag():
    """The launcher must accept --force-lock (operator override, exit 3
    contract documented in the module docstring)."""
    import importlib

    mod = importlib.import_module("run_prover_bg")
    # parse_args reads sys.argv — probe the parser via a controlled argv.
    old_argv = sys.argv
    try:
        sys.argv = ["run_prover_bg.py", "62", "--force-lock"]
        args = mod.parse_args()
        assert args.force_lock is True
        sys.argv = ["run_prover_bg.py", "62"]
        args = mod.parse_args()
        assert args.force_lock is False
    finally:
        sys.argv = old_argv
