#!/usr/bin/env python3
"""Unit tests for check_coordinator_identity.py -- the lane identity guard.

Founding incident (2026-09-11): a machine reboot killed the coordinator session
and its cron. Two CoursIA sessions were then live on `myia-ai-01` and nothing in
`ListAgents` said which one should coordinate -- session names do not encode the
lane. Worse, ai-01 carries *two* clones of the repo (`D:/CoursIA` and
`D:/dev/CoursIA`) whose basenames are identical, so the lane string alone cannot
tell them apart either.

The cases below are the ones the guard exists to catch; a detection pattern is
validated by its false negatives, so each one asserts the *downgrade*, not just
the happy path.

Run:
    python -m pytest scripts/tests/test_check_coordinator_identity.py
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import check_coordinator_identity as cci  # noqa: E402


def _report(monkeypatch, machine, root, expect="auto"):
    monkeypatch.setattr(cci, "measure_machine", lambda: machine)
    monkeypatch.setattr(cci, "measure_repo_root", lambda start=None: Path(root))
    return cci.build_report(expect)


def test_coordinator_lane_on_canonical_clone(monkeypatch):
    r = _report(monkeypatch, "myia-ai-01", "D:/CoursIA", "coordinator")
    assert r["lane"] == "myia-ai-01:CoursIA"
    assert r["role"] == "coordinator"
    assert r["command"] == "/coordinate"
    assert r["ok"] is True


def test_twin_clone_same_lane_string_is_downgraded(monkeypatch):
    """The case the lane string cannot see: same lane, different clone."""
    r = _report(monkeypatch, "myia-ai-01", "D:/dev/CoursIA", "coordinator")
    assert r["lane"] == "myia-ai-01:CoursIA"  # identical to the canonical one
    assert r["clone_ok"] is False
    assert r["role"] == "worker"  # fail-CLOSED
    assert r["command"] == "/continue"
    assert r["ok"] is False


def test_adjoint_lane_routes_to_coordinate_adjoint(monkeypatch):
    r = _report(monkeypatch, "myia-po-2025", "D:/CoursIA-2")
    assert r["lane"] == "myia-po-2025:CoursIA-2"
    assert r["role"] == "adjoint"
    assert r["command"] == "/coordinate-adjoint"


def test_coordinator_workspace_on_another_machine_is_a_worker(monkeypatch):
    """Right workspace name, wrong machine -- the reboot-clone failure mode."""
    r = _report(monkeypatch, "myia-po-2027", "D:/CoursIA", "coordinator")
    assert r["role"] == "worker"
    assert r["ok"] is False


def test_coursia_2_on_ai01_is_a_worker_not_the_adjoint(monkeypatch):
    """`CoursIA-2` alone does not make an adjoint -- the machine is half the lane."""
    r = _report(monkeypatch, "myia-ai-01", "D:/CoursIA-2")
    assert r["role"] == "worker"
    assert r["command"] == "/continue"


def test_uniqueness_is_never_claimed(monkeypatch):
    """Scope of the instrument is written into every verdict (never assumed)."""
    r = _report(monkeypatch, "myia-ai-01", "D:/CoursIA", "coordinator")
    assert r["uniqueness_measured"] is False
    assert "unicite" in cci.render(r).lower()


def test_outside_a_git_repo_fails_loudly(monkeypatch):
    monkeypatch.setattr(cci, "measure_machine", lambda: "myia-ai-01")
    monkeypatch.setattr(cci, "measure_repo_root", lambda start=None: None)
    r = cci.build_report("coordinator")
    assert r["ok"] is False
    assert r["error"] is not None
    assert cci.main is not None
