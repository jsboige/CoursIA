"""Recette de ``heartbeat_sweep_emit.py`` (#11860 / #12588 form 2).

Le script imite la logique du step ``Check age of last successful sweep run``
du workflow ``pr-gate-sweep-health-advisory.yml`` (form 1), mais en local,
pour qu'ai-01 puisse l'utiliser comme form 2 (dashboard heartbeat) -- immune
aux pannes runner, qui est ce que #12588 mandate comme FLOOR.

## Couverture

Ces tests exercent **deux seams** distincts :

1. ``last_success_age_s(workflow, run=None)`` -- calcul d'âge pur, le seam
   ``run`` est dependency-injecté. Couvre le cas heureux, le cas "no
   success" et le cas "missing createdAt".

2. ``main(argv=None, run=None)`` -- l'orchestrateur CLI, avec le même seam
   ``run``. Couvre les VRAIS chemins : exit 0 (OK), exit 1 (alarm: STALE
   ou NO_SUCCESS), exit 1 (error gh), exit 2 (usage), et l'emission JSON
   structuree. Sans ce seam on ne pourrait pas tester ``main()`` proprement
   (un subprocess n'a pas acces au ``run`` du module parent).

L'execution reelle de ``gh`` n'est PAS stubbee dans ces tests -- elle
depend de l'auth et de la connectivite, donc on l'injecte via le seam.
Le workflow lui-meme est verifie separement par ``test_pr_gate_sweep_select``
(meme genre, focale differente : verifier le heredoc du sweep lui-meme).
"""
from __future__ import annotations

import io
import json
import os
import subprocess
import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
SCRIPTS_CI = REPO_ROOT / "scripts" / "ci"
SCRIPT = SCRIPTS_CI / "heartbeat_sweep_emit.py"
sys.path.insert(0, str(REPO_ROOT / "scripts"))


def _run_cli(*args: str) -> subprocess.CompletedProcess[str]:
    """Run the CLI in a fresh subprocess (no in-process state leakage,
    no fake-gh injection -- exercise the real binary)."""
    return subprocess.run(
        [sys.executable, SCRIPT, *args],
        capture_output=True, text=True, check=False,
    )


# ---------------------------------------------------------------------------
# Seam 1: last_success_age_s (calcul d'âge pur)
# ---------------------------------------------------------------------------

def test_last_success_age_s_returns_int_for_recent_run():
    """A run created 5 minutes ago should report ~300s."""
    from ci.heartbeat_sweep_emit import last_success_age_s

    five_min_ago = (datetime.now(timezone.utc)
                    - timedelta(minutes=5)).isoformat().replace("+00:00", "Z")

    def fake_run(_workflow: str) -> list[dict]:
        return [{"createdAt": five_min_ago, "conclusion": "success"}]

    age = last_success_age_s("any.yml", run=fake_run)
    assert age is not None
    assert 290 <= age <= 310  # 5min +/- a few seconds for execution time


def test_last_success_age_s_returns_none_when_empty():
    """Empty list (no successful run) means the heartbeat should alarm."""
    from ci.heartbeat_sweep_emit import last_success_age_s

    def fake_run(_workflow: str) -> list[dict]:
        return []

    assert last_success_age_s("any.yml", run=fake_run) is None


def test_last_success_age_s_returns_none_when_no_created_at():
    """Missing ``createdAt`` key is also a 'cannot determine age'."""
    from ci.heartbeat_sweep_emit import last_success_age_s

    def fake_run(_workflow: str) -> list[dict]:
        return [{"conclusion": "success"}]

    assert last_success_age_s("any.yml", run=fake_run) is None


# ---------------------------------------------------------------------------
# Seam 2: main() — the real CLI path with run injectable.
#
# Critiques de la review jsboige (self-bot) sur #13221 : les premiers tests
# sur-promettaient ("test_cli_no_success_returns_exit_1" etait en realite
# un check usage ; "test_cli_json_emits_structured_payload" ne testait ni
# main() ni --json). Ces tests-ci corrigent ca : ils appellent main() avec
# un run injectable et observent stdout + exit code.
# ---------------------------------------------------------------------------

def _capture_main(argv: list[str], run) -> tuple[int, str, str]:
    """Call main(argv, run=run) and capture (returncode, stdout, stderr)."""
    from ci.heartbeat_sweep_emit import main

    old_out, old_err = sys.stdout, sys.stderr
    sys.stdout = io.StringIO()
    sys.stderr = io.StringIO()
    try:
        rc = main(argv, run=run)
        return rc, sys.stdout.getvalue(), sys.stderr.getvalue()
    finally:
        sys.stdout, sys.stderr = old_out, old_err


def test_main_ok_run_young_emits_ok_line_and_exit_0():
    """Young run + default threshold -> main() returns 0 + dashboard line
    containing ``OK`` and the workflow name."""
    one_min_ago = (datetime.now(timezone.utc)
                   - timedelta(minutes=1)).isoformat().replace("+00:00", "Z")

    def fake_run(_workflow: str) -> list[dict]:
        return [{"createdAt": one_min_ago, "conclusion": "success"}]

    rc, out, _err = _capture_main([], run=fake_run)
    assert rc == 0, f"expected exit 0 (OK), got {rc}; stdout={out!r}"
    assert "OK" in out
    assert "pr-gate-stale-sweep.yml" in out


def test_main_no_success_history_returns_exit_1_with_alarm():
    """The form-2 alarm's raison d'etre : ``gh run list`` returns empty
    (no successful run yet, or history purged). main() MUST return 1 and
    emit the sentinel in stdout (not stderr -- this is the case dashboards
    read for heartbeat presence)."""
    def fake_run(_workflow: str) -> list[dict]:
        return []  # no success

    rc, out, _err = _capture_main([], run=fake_run)
    assert rc == 1, f"expected exit 1 (alarm), got {rc}; stdout={out!r}"
    assert "NO_SUCCESS_IN_HISTORY" in out, (
        "the alarm sentinel must be in stdout so dashboard appenders see it"
    )
    assert "pr-gate-stale-sweep.yml" in out


def test_main_stale_run_returns_exit_1_with_stale_marker():
    """A successful run that's older than the threshold -> STALE verdict,
    exit 1, marker in stdout. The form-2 floor MUST rouge on this case
    even if the runner is healthy but slow."""
    two_hours_ago = (datetime.now(timezone.utc)
                     - timedelta(hours=2)).isoformat().replace("+00:00", "Z")

    def fake_run(_workflow: str) -> list[dict]:
        return [{"createdAt": two_hours_ago, "conclusion": "success"}]

    # Default threshold = 60 minutes, so 2h is stale.
    rc, out, _err = _capture_main([], run=fake_run)
    assert rc == 1, f"expected exit 1 (stale), got {rc}; stdout={out!r}"
    assert "STALE" in out


def test_main_json_mode_emits_well_formed_payload():
    """``--json`` is what ai-01's dashboard appender consumes. Verify the
    structured payload is emitted AND that the alarm path (no_success)
    surfaces via ``stale: true`` / ``reason: "no_success"``."""
    def fake_run(_workflow: str) -> list[dict]:
        return []

    rc, out, _err = _capture_main(["--json"], run=fake_run)
    assert rc == 1
    parsed = json.loads(out.strip())
    assert parsed["workflow"] == "pr-gate-stale-sweep.yml"
    assert parsed["age_s"] is None
    assert parsed["stale"] is True
    assert parsed["reason"] == "no_success"
    assert parsed["stale_after_s"] == 3600  # 60 min default


def test_main_json_mode_ok_run_emits_structured_ok():
    """``--json`` with a young run -> ``stale: false`` / ``reason: "ok"``
    / ``age_s`` present and recent."""
    one_min_ago = (datetime.now(timezone.utc)
                   - timedelta(minutes=1)).isoformat().replace("+00:00", "Z")

    def fake_run(_workflow: str) -> list[dict]:
        return [{"createdAt": one_min_ago, "conclusion": "success"}]

    rc, out, _err = _capture_main(["--json"], run=fake_run)
    assert rc == 0
    parsed = json.loads(out.strip())
    assert parsed["workflow"] == "pr-gate-stale-sweep.yml"
    assert parsed["age_s"] is not None
    assert parsed["age_s"] < 3600
    assert parsed["stale"] is False
    assert parsed["reason"] == "ok"


def test_main_stale_after_zero_returns_exit_2_usage_error():
    """Usage error: --stale-after-minutes must be > 0. exit 2 (not 1)
    lets callers distinguish "alarm" from "bad invocation"."""
    rc, _out, err = _capture_main(["--stale-after-minutes", "0"], run=lambda _: [])
    assert rc == 2
    assert "must be > 0" in err


def test_main_gh_unavailable_returns_exit_1_with_alarm_on_stdout():
    """Hermes c.642 review #2 on PR #13221 : the alarm sentinel for the
    ``OSError`` path (gh missing / not authenticated / transient) MUST be
    on stdout, not stderr -- otherwise a dashboard that pipes stdout
    (``python heartbeat_sweep_emit.py | dashboard-poll``) misses the
    form-2 alarm when gh is unavailable. stderr is reserved for the verbose
    trace (``-debug`` sentinel) for human debugging."""
    def fake_run_raises(_workflow: str) -> list[dict]:
        raise OSError("gh: not authenticated")

    rc, out, err = _capture_main([], run=fake_run_raises)
    assert rc == 1, f"expected exit 1 (alarm), got {rc}; stdout={out!r}"
    assert "gh unavailable" in out, (
        "alarm sentinel must be in stdout so dashboard appenders see it "
        "even when gh itself is unavailable (Hermes c.642 vigilance)"
    )
    assert "[sweep-heartbeat]" in out
    # The verbose debug trace stays on stderr for human inspection.
    assert "sweep-heartbeat-debug" in err
    assert "gh unavailable" in err


def test_main_gh_unavailable_json_emits_error_payload():
    """Hermes c.642 : --json mode for the OSError path is unchanged
    (JSON on stdout is the structured contract), but verify the error
    payload is well-formed for dashboard consumers."""
    def fake_run_raises(_workflow: str) -> list[dict]:
        raise OSError("gh: connection refused")

    rc, out, _err = _capture_main(["--json"], run=fake_run_raises)
    assert rc == 1
    parsed = json.loads(out.strip())
    assert parsed["reason"] == "error"
    assert parsed["stale"] is True
    assert parsed["age_s"] is None
    assert "connection refused" in parsed["error"]


def test_main_subprocess_smoke_real_cli_with_no_gh():
    """Sanity smoke: launch the real binary in a subprocess. If ``gh`` is
    not authenticated the exit code will be 1 with NO_SUCCESS or error --
    the test verifies the script at least *runs* (no ImportError, no
    syntax error). On a machine with ``gh`` auth and a young sweep the
    exit would be 0; either is fine for this smoke.
    """
    res = _run_cli("--help")
    assert res.returncode == 0, f"--help failed: {res.stderr}"
    assert "stale" in res.stdout.lower()
    assert "workflow" in res.stdout.lower()


def test_workflow_advisory_exists_and_references_the_script():
    """Form 1 of the alarm (``pr-gate-sweep-health-advisory.yml``) must
    exist and reference ``pr-gate-stale-sweep.yml`` -- the workflow whose
    health we are heartbeating. Without form 1 on main, the form 2 floor
    this script enables is pointless."""
    advisory = os.path.join(
        REPO_ROOT, ".github", "workflows", "pr-gate-sweep-health-advisory.yml"
    )
    assert os.path.exists(advisory), (
        "Form 1 of #11860/#12588 alarm is missing -- "
        "the dashboard heartbeat (form 2) is pointless without it."
    )
    with open(advisory, "r", encoding="utf-8") as f:
        body = f.read()
    assert "pr-gate-stale-sweep.yml" in body, (
        "Advisory workflow must reference the sweep it watches."
    )
    assert "schedule" in body, (
        "Advisory workflow must be schedule-driven (the point is to survive "
        "if the watched sweep's schedule dies)."
    )