#!/usr/bin/env python3
"""Offline tests for scripts/ci/gh_queue_health.py.

All tests use the `--input` snapshot mode so they are hermetic -- no live
`gh run list` calls. They cover the four interesting behaviors:

1. Pure ghost floor (the CoursIA 18-of-2026-08-19 scenario).
2. Pure live cohort (no ghosts, no parse failures -> CLEAN).
3. Mixed cohort with parse failures -> INCOMPLETE, exit 2.
4. Snapshot envelope unwrapping (`{snapshot: {workflow_runs: [...]}}`).

Plus a direct CLI test asserting EXIT_GHOST on a real CoursIA-shaped snapshot.
"""
from __future__ import annotations

import datetime as dt
import json
import subprocess
import sys
from pathlib import Path

SCRIPT = Path(__file__).resolve().parent.parent / "ci" / "gh_queue_health.py"


def _run(*args: str, stdin_payload: str | None = None) -> subprocess.CompletedProcess:
    cmd = [sys.executable, str(SCRIPT), *args]
    return subprocess.run(
        cmd,
        input=stdin_payload,
        capture_output=True,
        text=True,
        encoding="utf-8",
        check=False,
    )


def _make_snapshot(runs: list[dict], *, envelope: bool = False) -> str:
    body: dict | list = (
        {"snapshot": {"workflow_runs": runs}} if envelope
        else {"workflow_runs": runs}
    )
    return json.dumps(body)


# ---------------------------------------------------------------------------
# classify_runs / verdict via module import (fast path)
# ---------------------------------------------------------------------------

def test_classify_pure_ghost_floor() -> None:
    sys.path.insert(0, str(SCRIPT.parent))
    import gh_queue_health as mod  # noqa: WPS433 (intentional import-after-path)

    runs = [
        {"id": i, "name": f"ghost-{i}", "created_at": f"2026-08-19T03:{i:02d}:00Z",
         "html_url": f"https://gh/ghost/{i}"}
        for i in range(18)
    ]
    cutoff = dt.datetime(2026, 8, 20, tzinfo=dt.timezone.utc)
    out = mod.classify_runs(runs, cutoff)
    assert len(out["ghosts"]) == 18
    assert len(out["live"]) == 0
    assert len(out["parse_failures"]) == 0
    assert mod.verdict(18, 0, 0) == "STALE_FLOOR"


def test_classify_pure_live_yields_clean() -> None:
    sys.path.insert(0, str(SCRIPT.parent))
    import gh_queue_health as mod  # noqa: WPS433

    runs = [
        {"id": 100, "name": "live-1", "created_at": "2026-08-25T12:00:00Z",
         "html_url": "https://gh/live/100"},
        {"id": 101, "name": "live-2", "created_at": "2026-08-25T12:05:00Z",
         "html_url": "https://gh/live/101"},
    ]
    cutoff = dt.datetime(2026, 8, 20, tzinfo=dt.timezone.utc)
    out = mod.classify_runs(runs, cutoff)
    assert len(out["ghosts"]) == 0
    assert len(out["live"]) == 2
    assert mod.verdict(0, 2, 0) == "CLEAN"


def test_classify_mixed_with_parse_failure_is_incomplete() -> None:
    sys.path.insert(0, str(SCRIPT.parent))
    import gh_queue_health as mod  # noqa: WPS433

    runs = [
        {"id": 200, "name": "live", "created_at": "2026-08-25T12:00:00Z",
         "html_url": "https://gh/live/200"},
        {"id": 201, "name": "no-date"},  # missing created_at
        {"id": 202, "name": "bad-date", "created_at": "not-a-timestamp"},
    ]
    cutoff = dt.datetime(2026, 8, 20, tzinfo=dt.timezone.utc)
    out = mod.classify_runs(runs, cutoff)
    assert len(out["ghosts"]) == 0
    assert len(out["live"]) == 1
    assert len(out["parse_failures"]) == 2
    assert mod.verdict(0, 1, 2) == "INCOMPLETE"


def test_classify_uses_cutoff_inclusive_for_live_bucket() -> None:
    """A run created exactly at midnight on the cutoff is treated as live.

    Defensive against off-by-one floor contamination -- the docs of
    classify_runs call this out explicitly.
    """
    sys.path.insert(0, str(SCRIPT.parent))
    import gh_queue_health as mod  # noqa: WPS433

    runs = [{"id": 300, "name": "edge", "created_at": "2026-08-20T00:00:00Z",
             "html_url": "https://gh/edge/300"}]
    cutoff = dt.datetime(2026, 8, 20, tzinfo=dt.timezone.utc)
    out = mod.classify_runs(runs, cutoff)
    assert len(out["ghosts"]) == 0
    assert len(out["live"]) == 1


# ---------------------------------------------------------------------------
# parse_date
# ---------------------------------------------------------------------------

def test_parse_date_rejects_invalid_format() -> None:
    sys.path.insert(0, str(SCRIPT.parent))
    import gh_queue_health as mod  # noqa: WPS433

    try:
        mod.parse_date("08/20/2026")
    except mod.InstrumentError as exc:
        assert "invalid date" in str(exc)
    else:
        raise AssertionError("expected InstrumentError for slash format")


# ---------------------------------------------------------------------------
# CLI tests (offline snapshot mode)
# ---------------------------------------------------------------------------

def test_cli_ghost_floor_snapshot_exits_one(tmp_path: Path) -> None:
    runs = [
        {"id": i, "name": f"ghost-{i}", "created_at": f"2026-08-19T03:{i:02d}:00Z",
         "html_url": f"https://gh/ghost/{i}"}
        for i in range(18)
    ]
    snapshot = tmp_path / "ghost.json"
    snapshot.write_text(_make_snapshot(runs), encoding="utf-8")
    proc = _run("--input", str(snapshot))
    assert proc.returncode == mod.EXIT_GHOST if False else proc.returncode == 1, (
        f"expected EXIT_GHOST=1, got {proc.returncode}; stderr={proc.stderr}"
    )
    body = json.loads(proc.stdout)
    assert body["verdict"] == "STALE_FLOOR"
    assert body["counts"]["ghosts"] == 18
    assert body["counts"]["live"] == 0
    assert body["counts"]["parse_failures"] == 0
    assert body["snapshot_size"] == 18


def test_cli_clean_snapshot_exits_zero(tmp_path: Path) -> None:
    runs = [{"id": 1, "name": "live", "created_at": "2026-08-25T00:00:00Z",
             "html_url": "https://gh/live/1"}]
    snapshot = tmp_path / "clean.json"
    snapshot.write_text(_make_snapshot(runs), encoding="utf-8")
    proc = _run("--input", str(snapshot))
    assert proc.returncode == 0, f"expected EXIT_OK=0, got {proc.returncode}; stderr={proc.stderr}"
    body = json.loads(proc.stdout)
    assert body["verdict"] == "CLEAN"


def test_cli_envelope_snapshot_is_unwrapped(tmp_path: Path) -> None:
    """A `{snapshot: {workflow_runs: [...]}}` envelope is accepted and unwrapped."""
    runs = [{"id": 9, "name": "live", "created_at": "2026-08-25T00:00:00Z",
             "html_url": "https://gh/live/9"}]
    snapshot = tmp_path / "env.json"
    snapshot.write_text(_make_snapshot(runs, envelope=True), encoding="utf-8")
    proc = _run("--input", str(snapshot))
    assert proc.returncode == 0
    body = json.loads(proc.stdout)
    assert body["counts"]["total"] == 1


def test_cli_writes_output_file_when_flag_given(tmp_path: Path) -> None:
    runs = [{"id": 1, "name": "live", "created_at": "2026-08-25T00:00:00Z",
             "html_url": "https://gh/live/1"}]
    snapshot = tmp_path / "in.json"
    snapshot.write_text(_make_snapshot(runs), encoding="utf-8")
    out = tmp_path / "out.json"
    proc = _run("--input", str(snapshot), "--output", str(out))
    assert proc.returncode == 0
    assert out.exists()
    body = json.loads(out.read_text(encoding="utf-8"))
    assert body["verdict"] == "CLEAN"


def test_cli_parse_failure_exits_two(tmp_path: Path) -> None:
    runs = [{"id": 1, "name": "no-date"}]
    snapshot = tmp_path / "broken.json"
    snapshot.write_text(_make_snapshot(runs), encoding="utf-8")
    proc = _run("--input", str(snapshot))
    assert proc.returncode == 2, f"expected EXIT_BROKEN=2, got {proc.returncode}"
    assert "BROKEN INSTRUMENT" in proc.stderr


def test_cli_repo_without_input_rejects(tmp_path: Path) -> None:
    """The --repo/--input group is required, so the parser rejects both-empty."""
    proc = _run()
    assert proc.returncode != 0
    assert "one of the arguments" in proc.stderr or "required" in proc.stderr


# ---------------------------------------------------------------------------
# #13966: 3 advisory defects in PR #13909 review.
# ---------------------------------------------------------------------------

def test_incident_floor_count_is_named_constant_13966() -> None:
    """#13966 §1: `verdict()` must reference INCIDENT_FLOOR_COUNT, not the
    literal `18`. The asymmetry with the named date made the floor invisible
    when expectations drifted.
    """
    sys.path.insert(0, str(SCRIPT.parent))
    import gh_queue_health as mod  # noqa: WPS433

    # The named constant must exist and equal 18 (the historical CoursIA floor).
    assert hasattr(mod, "INCIDENT_FLOOR_COUNT")
    assert mod.INCIDENT_FLOOR_COUNT == 18
    # The literal `18` must NOT appear in verdict()'s source anymore.
    import inspect
    src = inspect.getsource(mod.verdict)
    assert "18" not in src.replace("INCIDENT_FLOOR_COUNT", ""), (
        f"verdict() still hardcodes `18` outside INCIDENT_FLOOR_COUNT: {src!r}"
    )


def test_stale_floor_docstring_mentions_conjunction_13966() -> None:
    """#13966 §2: STALE_FLOOR requires BOTH `ghosts == floor` AND `live == 0`.
    The original docstring only stated the first half -- a reader expecting
    'STALE_FLOOR if there are 18 ghosts' would be surprised when a CI surge
    with live runs classifies as GHOST_RUNS_DETECTED instead.
    """
    sys.path.insert(0, str(SCRIPT.parent))
    import gh_queue_health as mod  # noqa: WPS433

    doc = mod.verdict.__doc__ or ""
    # The conjunctive condition must be explicit (live == 0 is load-bearing).
    assert "live == 0" in doc, f"verdict() docstring missing `live == 0`: {doc!r}"
    # The named constant must replace the bare `18` reference in the prose.
    assert "INCIDENT_FLOOR_COUNT" in doc


def test_stale_floor_with_live_runs_is_ghost_runs_detected_13966() -> None:
    """#13966 §2 (positive control): the conjunctive condition means 18 ghosts
    + N live > 0 must classify as GHOST_RUNS_DETECTED, NOT STALE_FLOOR.
    This is the failure mode the docstring would have hidden.
    """
    sys.path.insert(0, str(SCRIPT.parent))
    import gh_queue_health as mod  # noqa: WPS433

    # The historical 18-floor PLUS a fresh live run = GHOST_RUNS_DETECTED.
    assert mod.verdict(18, 1, 0) == "GHOST_RUNS_DETECTED"
    assert mod.verdict(18, 5, 0) == "GHOST_RUNS_DETECTED"
    # Without live: still STALE_FLOOR (the canonical CoursIA signature).
    assert mod.verdict(18, 0, 0) == "STALE_FLOOR"


def test_replay_incomplete_prior_analysis_yields_non_incomplete_13966(tmp_path: Path) -> None:
    """#13966 §3: replaying a snapshot whose original verdict was INCOMPLETE
    yields CLEAN or GHOST_RUNS_DETECTED -- the verdict class changes at
    replay because load_snapshot cannot resynthesise the parse_failures
    from the timestamps alone (a missing `created_at` looks identical to
    an unrecoverable parse failure). This test pins the loss as a
    documented contract, not a silent bug.
    """
    sys.path.insert(0, str(SCRIPT.parent))
    import gh_queue_health as mod  # noqa: WPS433

    # A prior analysis output with ghosts=18, live=0, parse_failures=2 -> the
    # original verdict was INCOMPLETE. After load_snapshot + classify_runs,
    # parse_failures disappears (the synthetic list only carries ghosts and
    # live with their `created_at`), and classify_runs produces 0 failures.
    prior_analysis = {
        "cutoff": "2026-08-20",
        "verdict": "INCOMPLETE",
        "counts": {"total": 20, "ghosts": 18, "live": 0, "parse_failures": 2},
        "snapshot_size": 20,
        "ghosts": [
            {"id": i, "name": f"ghost-{i}", "created_at": f"2026-08-19T03:{i:02d}:00Z",
             "html_url": f"https://gh/ghost/{i}"}
            for i in range(18)
        ],
        "live": [],
        "parse_failures": [
            {"id": 901, "reason": "missing created_at"},
            {"id": 902, "reason": "bad created_at 'not-a-timestamp'"},
        ],
    }
    snapshot = tmp_path / "incomplete.json"
    snapshot.write_text(json.dumps(prior_analysis), encoding="utf-8")

    raw_runs = mod.load_snapshot(snapshot)
    classification = mod.classify_runs(
        raw_runs, dt.datetime(2026, 8, 20, tzinfo=dt.timezone.utc)
    )
    # The structural loss: parse_failures count drops from 2 to 0 on replay.
    assert len(classification["parse_failures"]) == 0
    # The corollary verdict shift: INCOMPLETE -> STALE_FLOOR (or CLEAN).
    repl_verdict = mod.verdict(
        len(classification["ghosts"]),
        len(classification["live"]),
        len(classification["parse_failures"]),
    )
    assert repl_verdict == "STALE_FLOOR"
    assert repl_verdict != "INCOMPLETE", (
        "Replay must NOT reproduce INCOMPLETE because load_snapshot cannot "
        "resynthesise the original parse failures from timestamps alone. "
        "This loss is documented in load_snapshot's docstring (#13966)."
    )

    # The docstring must call the loss out explicitly so a reader comparing
    # two verdicts through a snapshot does not conclude falsely.
    assert "INCOMPLETE" in (mod.load_snapshot.__doc__ or "")
    assert "parse_failures" in (mod.load_snapshot.__doc__ or "")
    assert "cannot" in (mod.load_snapshot.__doc__ or "").lower() or \
           "not recoverable" in (mod.load_snapshot.__doc__ or "").lower()
