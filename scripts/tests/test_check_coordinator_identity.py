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
    # Assertion reelle (l'ancienne `cci.main is not None` etait vacante :
    # vraie pour n'importe quel symbole importe) : le chemin d'erreur rend
    # bien l'erreur.
    assert "MESURE IMPOSSIBLE" in cci.render(r)


def test_twin_clone_named_in_non_canonical_case_is_caught(monkeypatch):
    """NTFS: a twin clone whose basename case misses the raw table key.

    Before the fix, `myia-ai-01:coursia` missed CANONICAL_ROOTS entirely
    (raw key lookup), so `canonical was None` made clone_ok silently True
    and the twin guard never ran.
    """
    r = _report(monkeypatch, "myia-ai-01", "D:/dev/coursia", "coordinator")
    assert r["lane"] == "myia-ai-01:coursia"  # real case preserved (display identity)
    assert r["canonical_root"] == "d:/coursia"  # lookup found it despite the case
    assert r["clone_ok"] is False  # twin detected, not silently passed
    assert r["role"] == "worker"  # fail-CLOSED, exactly like D:/dev/CoursIA
    assert r["ok"] is False


def test_canonical_clone_spelled_in_non_canonical_case_still_coordinates(monkeypatch):
    """`D:/coursia` IS the canonical clone on case-insensitive NTFS: no false positive.

    Case-insensitive lookup must not downgrade the canonical clone when its
    path is merely spelled with a different case.
    """
    r = _report(monkeypatch, "myia-ai-01", "D:/coursia", "coordinator")
    assert r["clone_ok"] is True
    assert r["role"] == "coordinator"
    assert r["ok"] is True


def test_auto_default_reports_without_claiming_conformity(monkeypatch, capsys):
    """Default mode (`--expect auto`) cannot render a conformity verdict.

    Before the fix, `expected_role = role` made `ok` tautologically True and
    exit code 0 unconditional -- the default invocation could never fail.
    """
    r = _report(monkeypatch, "myia-ai-01", "D:/CoursIA")  # expect defaults to "auto"
    assert r["ok"] is None
    assert r["verified"] is False
    assert cci.main([]) == 3  # distinct from 0 (verified conform) and 1 (verified not)
    out = capsys.readouterr().out
    assert "non verifie" in out.lower()


def test_wrong_expect_exits_1(monkeypatch, capsys):
    """Positive control: an explicit wrong --expect still yields exit code 1."""
    monkeypatch.setattr(cci, "measure_machine", lambda: "myia-ai-01")
    monkeypatch.setattr(cci, "measure_repo_root", lambda start=None: Path("D:/CoursIA"))
    assert cci.main(["--expect", "worker"]) == 1


def test_outside_repo_exit_2_keeps_portee_line(monkeypatch, capsys):
    """Exit-2 path: exit code asserted, and the PORTEE guard line survives.

    Before the fix, render() returned early on error and the PORTEE line
    (the wanted-omnipresent scope guard) disappeared from the exit-2 output.
    """
    monkeypatch.setattr(cci, "measure_machine", lambda: "myia-ai-01")
    monkeypatch.setattr(cci, "measure_repo_root", lambda start=None: None)
    assert cci.main(["--expect", "coordinator"]) == 2
    out = capsys.readouterr().out
    assert "PORTEE" in out
    assert "unicite" in out.lower()
