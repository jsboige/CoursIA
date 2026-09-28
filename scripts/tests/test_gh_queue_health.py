#!/usr/bin/env python3
"""Offline tests for scripts/ci/gh_queue_health.py.

All tests use the `--input` snapshot mode so they are hermetic -- no live
`gh run list` calls. They cover the interesting behaviors:

1. Pure ghost floor (the CoursIA 18-of-2026-08-19 pre-cutoff scenario).
2. Pure live cohort (no ghosts, no parse failures -> CLEAN).
3. Mixed cohort with parse failures -> INCOMPLETE, exit 2.
4. Snapshot envelope unwrapping (`{snapshot: {workflow_runs: [...]}}`).
5. The pr-closed ghost class (#18215): a queued pull_request run whose PR
   is closed is a permanent ghost regardless of age, and a prior-analysis
   snapshot replays its ghost class through `_ghost_reason`.

Plus direct CLI tests asserting EXIT_GHOST / EXIT_OK on CoursIA-shaped
snapshots.
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
# #18215: pr-closed ghost class, two-incident steady state, replay fidelity
# ---------------------------------------------------------------------------


def test_18215_classify_pr_closed_ghost_class() -> None:
    """A post-cutoff pull_request run whose PR is closed is a permanent ghost.

    The measured incident: PR #15946 (wt/vibe-g2-quantconnect) closed
    2026-09-13T18:05Z while 35 of its runs awaited admission -- the API
    reports them queued forever and refuses to cancel a run "that has not
    been queued yet". An open PR (or a missing one) stays live: an open PR
    can still be admitted, so a wedged open-PR run must surface as a live
    queue that never drains (the 2026-08-19 detection shape).
    """
    sys.path.insert(0, str(SCRIPT.parent))
    import gh_queue_health as mod  # noqa: WPS433

    cutoff = dt.datetime(2026, 8, 20, tzinfo=dt.timezone.utc)
    runs = [
        {"id": 1, "name": "closed-pr-run", "created_at": "2026-09-13T09:10:00Z",
         "event": "pull_request", "head_branch": "wt/vibe-g2-quantconnect"},
        {"id": 2, "name": "open-pr-run", "created_at": "2026-09-13T09:10:00Z",
         "event": "pull_request", "head_branch": "feature/still-open"},
        {"id": 3, "name": "no-pr-run", "created_at": "2026-09-13T09:10:00Z",
         "event": "push", "head_branch": "wt/stray"},
    ]
    states = {"wt/vibe-g2-quantconnect": "closed", "feature/still-open": "open",
              "wt/stray": "missing"}
    out = mod.classify_runs(runs, cutoff, states)
    assert [g["reason"] for g in out["ghosts"]] == ["pr-closed"]
    assert out["ghosts"][0]["id"] == 1
    assert {entry["id"] for entry in out["live"]} == {2, 3}
    # Entries carry the classification context for replay and audit.
    assert out["ghosts"][0]["event"] == "pull_request"
    assert out["ghosts"][0]["head_branch"] == "wt/vibe-g2-quantconnect"


def test_18215_classify_without_pr_states_keeps_post_cutoff_live() -> None:
    """Control: no pr_states passed (snapshot replay) -> cutoff-only split.

    A raw-shape replay is offline by design -- it has no PR-state channel,
    so a pr-closed run created after the cutoff replays as live. The prior-
    analysis replay (which carries `reason`) is the fidelity-preserving
    path, pinned by its own test below.
    """
    sys.path.insert(0, str(SCRIPT.parent))
    import gh_queue_health as mod  # noqa: WPS433

    cutoff = dt.datetime(2026, 8, 20, tzinfo=dt.timezone.utc)
    runs = [{"id": 1, "name": "would-be-pr-closed", "created_at": "2026-09-13T09:10:00Z",
             "event": "pull_request", "head_branch": "wt/vibe-g2-quantconnect"}]
    out = mod.classify_runs(runs, cutoff)
    assert out["ghosts"] == []
    assert len(out["live"]) == 1


def test_18215_classify_replayed_reason_is_authoritative() -> None:
    """A synthesized ghost entry with `_ghost_reason` replays as that class.

    Without this, a pr-closed ghost created after the cutoff would replay
    as live and flip the verdict class -- the exact replay-fidelity failure
    #13966 fixed for parse_failures, reborn for ghost classes.
    """
    sys.path.insert(0, str(SCRIPT.parent))
    import gh_queue_health as mod  # noqa: WPS433

    cutoff = dt.datetime(2026, 8, 20, tzinfo=dt.timezone.utc)
    runs = [{"id": 1, "name": "replayed", "created_at": "2026-09-13T09:10:00Z",
             "event": "pull_request", "head_branch": "wt/vibe-g2-quantconnect",
             "_ghost_reason": "pr-closed"}]
    out = mod.classify_runs(runs, cutoff)
    assert [g["reason"] for g in out["ghosts"]] == ["pr-closed"]
    assert out["live"] == []


def test_18215_fetch_pr_states_closed_open_missing(monkeypatch) -> None:
    """fetch_pr_states maps each distinct branch to open/closed/missing.

    One `gh api pulls?head=` call per distinct branch, via the shared
    transport; a non-list payload is an InstrumentError (fail loud, never
    guess a state that would misclassify a live run as ghost).
    """
    sys.path.insert(0, str(SCRIPT.parent))
    import gh_queue_health as mod  # noqa: WPS433

    calls: list[str] = []

    class _Proc:
        def __init__(self, payload):
            self.returncode, self.stdout, self.stderr = 0, json.dumps(payload), ""

    def fake_run(cmd, **kwargs):
        endpoint = cmd[-1]
        calls.append(endpoint)
        if "wt/closed-branch" in endpoint:
            return _Proc([{"state": "closed"}])
        if "wt/open-branch" in endpoint:
            return _Proc([{"state": "open"}])
        if "wt/gone-branch" in endpoint:
            return _Proc([])
        return _Proc({"unexpected": "dict"})

    monkeypatch.setattr(mod.subprocess, "run", fake_run)
    states = mod.fetch_pr_states(
        "jsboige/CoursIA",
        ["wt/open-branch", "wt/closed-branch", "wt/gone-branch", "wt/closed-branch"],
    )
    assert states == {"wt/closed-branch": "closed", "wt/open-branch": "open",
                      "wt/gone-branch": "missing"}
    # Deduplicated: one call per DISTINCT branch.
    assert len(calls) == 3
    assert all("head=jsboige:" in c for c in calls)
    # Non-list payload -> broken instrument, not a silent guess.
    try:
        mod.fetch_pr_states("jsboige/CoursIA", ["wt/bad"])
    except mod.InstrumentError:
        pass
    else:
        raise AssertionError("expected InstrumentError on non-list pulls payload")


def test_18215_two_incident_steady_state_is_stale_floor() -> None:
    """Ghost COUNT carries no signal since #18215 -- classes do.

    The floor grew from 18 (pre-cutoff, #13579) to 55 when the pr-closed
    class absorbed the 37 runs stranded by PR #15946 (#18215), and any
    future closed-PR wave grows it further. What must stay sharp is: an
    empty live queue with explained ghosts is steady state (STALE_FLOOR /
    watch OK), and any live queue coexisting with ghosts is drift.
    """
    sys.path.insert(0, str(SCRIPT.parent))
    import gh_queue_health as mod  # noqa: WPS433

    # Historical floor alone, queue empty.
    assert mod.verdict(18, 0, 0) == "STALE_FLOOR"
    # Two-incident floor (18 pre-cutoff + 37 pr-closed), queue empty.
    assert mod.verdict(55, 0, 0) == "STALE_FLOOR"
    # A different repo's smaller explained floor is steady state too.
    assert mod.verdict(5, 0, 0) == "STALE_FLOOR"
    # Ghosts WITH a live queue -> drift, whatever the floor size.
    assert mod.verdict(18, 1, 0) == "GHOST_RUNS_DETECTED"
    assert mod.verdict(55, 31, 0) == "GHOST_RUNS_DETECTED"
    # The watch collapses the steady states to OK and the drifts to DRIFT.
    assert mod.watch_verdict(55, 0, 0) == "OK"
    assert mod.watch_verdict(55, 1, 0) == "DRIFT"


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


# ---------------------------------------------------------------------------
# watch_verdict / --watch CLI  (#14367 guard anti-derive)
# ---------------------------------------------------------------------------

def test_watch_verdict_clean_collapses_to_ok() -> None:
    """No ghosts at all -> watch verdict OK (matches measurement CLEAN)."""
    sys.path.insert(0, str(SCRIPT.parent))
    import gh_queue_health as mod  # noqa: WPS433

    assert mod.watch_verdict(0, 5, 0) == "OK"
    assert mod.watch_verdict(0, 0, 0) == "OK"


def test_watch_verdict_stale_floor_collapses_to_ok() -> None:
    """The historical 18 ghosts + 0 live -> watch verdict OK (steady state).

    This is the routine CoursIA signature: the 18 ghosts of 2026-08-19 are
    unpurgeable, but the queue is otherwise empty. The watch should NOT
    fire an alert on this shape -- only on genuine drift.
    """
    sys.path.insert(0, str(SCRIPT.parent))
    import gh_queue_health as mod  # noqa: WPS433

    assert mod.watch_verdict(18, 0, 0) == "OK"


def test_watch_verdict_count_drift_with_empty_queue_is_ok() -> None:
    """Ghost count drift with an empty live queue -> watch verdict OK (#18215).

    Before #18215 the watch fired DRIFT whenever the ghost count left the
    pinned 18. That pinned the SECOND incident (37 pr-closed runs) into a
    permanent false alert: every closed-PR wave grows the explained floor
    by construction. The count is no longer a signal -- an empty live queue
    is, whatever the floor size.
    """
    sys.path.insert(0, str(SCRIPT.parent))
    import gh_queue_health as mod  # noqa: WPS433

    assert mod.watch_verdict(19, 0, 0) == "OK"
    assert mod.watch_verdict(55, 0, 0) == "OK"


def test_watch_verdict_drift_on_live_activity() -> None:
    """18 ghosts + live activity -> watch verdict DRIFT.

    The historical floor is 18 ghosts with 0 live. Live activity (jobs in
    the queue) means the runner pool is being asked to do work -- this is
    the actionable signal even if the floor count is unchanged.
    """
    sys.path.insert(0, str(SCRIPT.parent))
    import gh_queue_health as mod  # noqa: WPS433

    assert mod.watch_verdict(18, 1, 0) == "DRIFT"


def test_watch_verdict_incomplete_collapses_to_broken() -> None:
    """Parse failures -> watch verdict BROKEN (instrument cannot conclude).

    The watch must not silently collapse INCOMPLETE to DRIFT: a broken
    instrument and a real drift require different responses (redeploy vs
    investigate).
    """
    sys.path.insert(0, str(SCRIPT.parent))
    import gh_queue_health as mod  # noqa: WPS433

    assert mod.watch_verdict(0, 0, 1) == "BROKEN"
    assert mod.watch_verdict(18, 0, 3) == "BROKEN"


def test_cli_watch_stale_floor_exits_zero(tmp_path: Path) -> None:
    """--watch on the steady-state CoursIA shape exits 0 (no alert)."""
    runs = [
        {"id": i, "name": f"ghost-{i}", "created_at": f"2026-08-19T03:{i:02d}:00Z",
         "html_url": f"https://gh/ghost/{i}"}
        for i in range(18)
    ]
    snapshot = tmp_path / "ghost.json"
    snapshot.write_text(_make_snapshot(runs), encoding="utf-8")
    proc = _run("--watch", "--input", str(snapshot))
    assert proc.returncode == 0, (
        f"expected watch OK=0 on STALE_FLOOR, got {proc.returncode}; "
        f"stderr={proc.stderr}"
    )
    body = json.loads(proc.stdout)
    assert body["verdict_watch"] == "OK"
    assert body["verdict_measurement"] == "STALE_FLOOR"


def test_cli_watch_drift_exits_one(tmp_path: Path) -> None:
    """--watch on ghosts coexisting with a live queue exits 1 (alert).

    Since #18215 the alert condition is the live queue, not a count drift:
    a queued run that belongs to no ghost class (here a post-cutoff run on
    an open PR) sits in live and pins the watch at DRIFT until it drains
    or gets classified -- the shape that caught the 2026-08-19 class.
    """
    runs = [
        {"id": i, "name": f"ghost-{i}", "created_at": f"2026-08-19T03:{i:02d}:00Z",
         "html_url": f"https://gh/ghost/{i}"}
        for i in range(18)
    ]
    runs.append({"id": 99, "name": "stuck-open-pr", "created_at": "2026-09-28T04:15:00Z",
                 "html_url": "https://gh/live/99", "event": "pull_request",
                 "head_branch": "feature/stuck"})
    snapshot = tmp_path / "drift.json"
    snapshot.write_text(_make_snapshot(runs), encoding="utf-8")
    proc = _run("--watch", "--input", str(snapshot))
    assert proc.returncode == 1, (
        f"expected watch DRIFT=1, got {proc.returncode}; stderr={proc.stderr}"
    )
    body = json.loads(proc.stdout)
    assert body["verdict_watch"] == "DRIFT"
    assert body["verdict_measurement"] == "GHOST_RUNS_DETECTED"
    assert body["counts"]["live"] == 1


def test_cli_watch_two_incident_floor_replay_exits_zero(tmp_path: Path) -> None:
    """--watch on the two-incident steady state (prior-analysis replay) exits 0.

    The replay path that must NOT flip verdict class (#13966 fidelity,
    extended to ghost reasons in #18215): a prior output's ghosts carry
    their `reason`, the synthesized entries replay through `_ghost_reason`,
    and the 55-ghost 0-live shape stays STALE_FLOOR/OK even though 37 of
    those ghosts were created AFTER the cutoff.
    """
    analysis = {
        "cutoff": "2026-08-20",
        "verdict": "STALE_FLOOR",
        "counts": {"total": 55, "ghosts": 55, "live": 0, "parse_failures": 0},
        "snapshot_size": 55,
        "ghosts": (
            [{"id": i, "name": f"corruption-{i}",
              "created_at": f"2026-08-19T03:{i:02d}:00Z",
              "html_url": f"https://gh/ghost/{i}", "reason": "pre-cutoff"}
             for i in range(18)]
            + [{"id": 400 + i, "name": f"limbo-{i}",
                "created_at": f"2026-09-13T09:{i:02d}:00Z",
                "html_url": f"https://gh/limbo/{i}", "reason": "pr-closed",
                "event": "pull_request", "head_branch": "wt/vibe-g2-quantconnect"}
               for i in range(37)]
        ),
        "live": [],
        "parse_failures": [],
    }
    snapshot = tmp_path / "twofloor.json"
    snapshot.write_text(json.dumps(analysis), encoding="utf-8")
    proc = _run("--watch", "--input", str(snapshot))
    assert proc.returncode == 0, (
        f"expected watch OK=0 on two-incident STALE_FLOOR, got {proc.returncode}; "
        f"stderr={proc.stderr}"
    )
    body = json.loads(proc.stdout)
    assert body["verdict_watch"] == "OK"
    assert body["verdict_measurement"] == "STALE_FLOOR"
    assert body["counts"]["ghosts"] == 55
    assert body["counts"]["live"] == 0


def test_cli_watch_broken_exits_two(tmp_path: Path) -> None:
    """--watch on a parse failure exits 2 (broken instrument, do not alert).

    Without the BROKEN collapse, the watch would fire DRIFT alerts on
    transient API hiccups -- alert fatigue is the failure mode the
    three-bucket split exists to prevent.
    """
    runs = [{"id": 1, "name": "no-date"}]  # missing created_at
    snapshot = tmp_path / "broken.json"
    snapshot.write_text(_make_snapshot(runs), encoding="utf-8")
    proc = _run("--watch", "--input", str(snapshot))
    assert proc.returncode == 2, (
        f"expected watch BROKEN=2, got {proc.returncode}; stderr={proc.stderr}"
    )
    body = json.loads(proc.stdout)
    assert body["verdict_watch"] == "BROKEN"
