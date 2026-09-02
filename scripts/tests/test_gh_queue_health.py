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
# #13966 follow-ups: INCIDENT_FLOOR_COUNT naming, STALE_FLOOR docstring
# conjonction, INCOMPLETE preservation across replay
# ---------------------------------------------------------------------------


def test_13966_incident_floor_count_constant_is_18() -> None:
    """#13966 follow-up 1 -- INCIDENT_FLOOR_COUNT = 18, used at the verdict site.

    The bare number `18` next to `INCIDENT_FLOOR_DATE` was an asymmetry that
    degraded the signature silently. The constant named makes the change loud.
    """
    sys.path.insert(0, str(SCRIPT.parent))
    import gh_queue_health as mod  # noqa: WPS433

    assert mod.INCIDENT_FLOOR_COUNT == 18
    assert mod.INCIDENT_FLOOR_DATE == "2026-08-19"
    # Both used together: 18 ghosts AND no live -> STALE_FLOOR
    assert mod.verdict(18, 0, 0) == "STALE_FLOOR"
    # 18 ghosts WITH live runs -> GHOST_RUNS_DETECTED (signature augmented)
    assert mod.verdict(18, 1, 0) == "GHOST_RUNS_DETECTED"
    # Different ghost count -> GHOST_RUNS_DETECTED (no false STALE_FLOOR on
    # other repos with a different number of historical ghosts)
    assert mod.verdict(5, 0, 0) == "GHOST_RUNS_DETECTED"


def test_13966_load_snapshot_returns_tuple_with_parse_failures_preserved() -> None:
    """#13966 follow-up 3 -- load_snapshot returns (runs, preserved_pf).

    A prior analysis output (the shape written by --output) carries a
    `parse_failures` bucket that cannot be re-derived from the synthesized
    runs. The new signature preserves it so replay reproduces the verdict.
    """
    sys.path.insert(0, str(SCRIPT.parent))
    import gh_queue_health as mod  # noqa: WPS433

    analysis = {
        "cutoff": "2026-08-20",
        "verdict": "INCOMPLETE",
        "counts": {"total": 3, "ghosts": 0, "live": 1, "parse_failures": 2},
        "snapshot_size": 3,
        "ghosts": [],
        "live": [
            {"id": 200, "name": "live", "created_at": "2026-08-25T12:00:00Z",
             "html_url": "https://gh/live/200"},
        ],
        "parse_failures": [
            {"id": 201, "reason": "missing created_at"},
            {"id": 202, "reason": "bad created_at 'not-a-timestamp'"},
        ],
    }
    tmp = SCRIPT.parent / "_tmp_13966_analysis.json"
    try:
        tmp.write_text(json.dumps(analysis), encoding="utf-8")
        runs, preserved_pf = mod.load_snapshot(tmp)
        # The 1 live run is synthesized into the runs list
        assert len(runs) == 1
        assert runs[0]["id"] == 200
        # The 2 parse_failures are preserved verbatim
        assert len(preserved_pf) == 2
        assert preserved_pf[0]["id"] == 201
        assert preserved_pf[1]["id"] == 202
    finally:
        if tmp.exists():
            tmp.unlink()


def test_13966_replay_of_incomplete_snapshot_keeps_incomplete_verdict(tmp_path: Path) -> None:
    """#13966 follow-up 3 -- replaying an INCOMPLETE snapshot must stay INCOMPLETE.

    Before this fix, `load_snapshot` synthesized only ghosts + live, dropping
    parse_failures. The replayed verdict then computed as `CLEAN` or
    `GHOST_RUNS_DETECTED` -- the verdict CLASS changed across replay, which
    defeats the purpose of replaying a snapshot. The fix preserves the
    parse_failures bucket, so the replayed verdict matches the original.
    """
    analysis = {
        "cutoff": "2026-08-20",
        "verdict": "INCOMPLETE",
        "counts": {"total": 3, "ghosts": 0, "live": 1, "parse_failures": 2},
        "snapshot_size": 3,
        "ghosts": [],
        "live": [
            {"id": 200, "name": "live", "created_at": "2026-08-25T12:00:00Z",
             "html_url": "https://gh/live/200"},
        ],
        "parse_failures": [
            {"id": 201, "reason": "missing created_at"},
            {"id": 202, "reason": "bad created_at 'not-a-timestamp'"},
        ],
    }
    snapshot = tmp_path / "incomplete.json"
    snapshot.write_text(json.dumps(analysis), encoding="utf-8")
    proc = _run("--input", str(snapshot))
    # INCOMPLETE -> EXIT_BROKEN = 2 (per main() / verdict() mapping)
    assert proc.returncode == 2, (
        f"expected EXIT_BROKEN=2 (INCOMPLETE), got {proc.returncode}; "
        f"stderr={proc.stderr}"
    )
    body = json.loads(proc.stdout)
    assert body["verdict"] == "INCOMPLETE"
    assert body["counts"]["parse_failures"] == 2


def test_13966_replay_of_stale_floor_snapshot_keeps_stale_floor(tmp_path: Path) -> None:
    """#13966 follow-up 3 (control positive) -- replay of STALE_FLOOR still works.

    Sanity check: the prior behavior on a clean STALE_FLOOR snapshot
    (no parse_failures) is preserved by the fix.
    """
    analysis = {
        "cutoff": "2026-08-20",
        "verdict": "STALE_FLOOR",
        "counts": {"total": 18, "ghosts": 18, "live": 0, "parse_failures": 0},
        "snapshot_size": 18,
        "ghosts": [
            {"id": i, "name": f"ghost-{i}",
             "created_at": f"2026-08-19T03:{i:02d}:00Z",
             "html_url": f"https://gh/ghost/{i}"}
            for i in range(18)
        ],
        "live": [],
        "parse_failures": [],
    }
    snapshot = tmp_path / "stale.json"
    snapshot.write_text(json.dumps(analysis), encoding="utf-8")
    proc = _run("--input", str(snapshot))
    assert proc.returncode == 1, f"expected EXIT_GHOST=1, got {proc.returncode}"
    body = json.loads(proc.stdout)
    assert body["verdict"] == "STALE_FLOOR"
    assert body["counts"]["ghosts"] == 18


def test_13966_load_snapshot_raw_shape_returns_empty_preserved(tmp_path: Path) -> None:
    """#13966 follow-up 3 (control) -- raw snapshot shape returns [] preserved.

    A raw snapshot (list of runs, {workflow_runs: [...]}, or envelope) does
    not have a pre-classified `parse_failures` bucket; `classify_runs`
    derives them from the runs. `load_snapshot` must return an empty
    preserved list so the caller does not double-count.
    """
    sys.path.insert(0, str(SCRIPT.parent))
    import gh_queue_health as mod  # noqa: WPS433

    raw_list = [{"id": 1, "name": "r1", "created_at": "2026-08-25T00:00:00Z",
                 "html_url": "https://gh/r/1"}]
    snapshot = tmp_path / "raw.json"
    snapshot.write_text(json.dumps(raw_list), encoding="utf-8")
    runs, preserved = mod.load_snapshot(snapshot)
    assert len(runs) == 1
    assert preserved == []
