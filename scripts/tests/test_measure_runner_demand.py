from __future__ import annotations

import importlib.util
import json
from datetime import datetime, timezone
from pathlib import Path

import pytest

MODULE_PATH = Path(__file__).resolve().parents[1] / "ci" / "measure_runner_demand.py"
SPEC = importlib.util.spec_from_file_location("measure_runner_demand", MODULE_PATH)
mod = importlib.util.module_from_spec(SPEC)
assert SPEC.loader
SPEC.loader.exec_module(mod)

UTC = timezone.utc


def dt(hour=0, minute=0, second=0):
    return datetime(2026, 8, 24, hour, minute, second, tzinfo=UTC)


def run(run_id, created, repo="jsboige/CoursIA", name="Build", conclusion="success"):
    return {
        "id": run_id,
        "name": name,
        "event": "pull_request",
        "status": "completed",
        "conclusion": conclusion,
        "created_at": mod.iso_z(created),
        "run_started_at": mod.iso_z(created),
        "updated_at": mod.iso_z(created),
        "head_repository": {"full_name": repo} if repo is not None else None,
        "pull_requests": [{"number": 12}],
    }


def job(job_id, created, started, completed, conclusion="success"):
    return {
        "id": job_id,
        "name": f"job-{job_id}",
        "status": "completed" if completed else "queued",
        "conclusion": conclusion,
        "created_at": mod.iso_z(created) if created else None,
        "started_at": mod.iso_z(started) if started else None,
        "completed_at": mod.iso_z(completed) if completed else None,
        "runner_name": "GitHub Actions 1" if started else None,
        "labels": ["ubuntu-latest"],
    }


def snapshot(runs, since=dt(0), until=dt(1)):
    return {
        "schema_version": 1,
        "repo": "jsboige/CoursIA",
        "since": mod.iso_z(since),
        "until": mod.iso_z(until),
        "runs": runs,
    }


def with_jobs(row, jobs):
    return mod._minimal_run(row, jobs)


def test_run_pagination_beyond_100_is_complete():
    rows = [run(i, dt(0, 0, i % 60)) for i in range(150)]

    def fetch(endpoint):
        page = int(endpoint.split("page=")[-1])
        chunk = rows[(page - 1) * 100:page * 100]
        return {"total_count": 150, "workflow_runs": chunk}

    found = mod.collect_runs("jsboige/CoursIA", dt(0), dt(1), fetch)
    assert len(found) == 150


def test_empty_page_before_total_is_broken():
    calls = 0

    def fetch(_endpoint):
        nonlocal calls
        calls += 1
        if calls == 1:
            return {"total_count": 101, "workflow_runs": [run(i, dt()) for i in range(100)]}
        return {"total_count": 101, "workflow_runs": []}

    with pytest.raises(mod.MeasurementError, match="empty before total_count"):
        mod.collect_runs("jsboige/CoursIA", dt(0), dt(1), fetch)


def test_cap_bisects_time_and_deduplicates_boundary():
    calls = []
    left = run(1, dt(0, 10))
    boundary = run(2, dt(0, 30))
    right = run(3, dt(0, 50))

    def fetch(endpoint):
        calls.append(endpoint)
        if len(calls) == 1:
            return {"total_count": 1000, "workflow_runs": []}
        if len(calls) == 2:
            return {"total_count": 2, "workflow_runs": [left, boundary]}
        return {"total_count": 2, "workflow_runs": [boundary, right]}

    found = mod.collect_runs("jsboige/CoursIA", dt(0), dt(1), fetch)
    assert [row["id"] for row in found] == [1, 2, 3]
    assert len(calls) == 3


def test_one_second_slice_still_capped_is_broken():
    def fetch(_endpoint):
        return {"total_count": 1000, "workflow_runs": []}

    with pytest.raises(mod.MeasurementError, match="one-second slice"):
        mod.collect_runs("jsboige/CoursIA", dt(0), dt(0, 0, 1), fetch)


def test_jobs_paginate_beyond_100():
    rows = [job(i, dt(), dt(), dt(0, 0, 1)) for i in range(125)]

    def fetch(endpoint):
        page = int(endpoint.split("page=")[-1])
        return {"total_count": 125, "jobs": rows[(page - 1) * 100:page * 100]}

    assert len(mod.collect_jobs("jsboige/CoursIA", 9, fetch)) == 125


def test_wait_and_runtime_use_job_timestamps_not_run_started_at():
    row = run(1, dt())
    row["run_started_at"] = row["created_at"]
    data = snapshot([with_jobs(row, [job(1, dt(), dt(0, 10), dt(0, 12))])])
    result = mod.analyze(data)
    assert result["runner"]["runner_minutes"] == 2.0
    assert result["runner"]["queue_minutes_for_timed_jobs"] == 10.0
    assert result["runner"]["runner_minutes_per_wall_hour"] == 2.0


def test_started_cancelled_job_consumes_runner_but_skipped_does_not():
    jobs = [
        job(1, dt(), dt(0, 1), dt(0, 4), conclusion="cancelled"),
        job(2, dt(), None, None, conclusion="skipped"),
    ]
    result = mod.analyze(snapshot([with_jobs(run(1, dt()), jobs)]))
    assert result["runner"]["runner_minutes"] == 3.0
    assert result["denominators"] == {
        "runs": 1,
        "jobs": 2,
        "timed_jobs": 1,
        "incomplete_or_untimed_jobs": 1,
        "timestamp_skew_jobs": 0,
        "skipped_without_start": 1,
        "timing_coverage": 0.5,
    }


def test_one_second_github_timestamp_skew_is_counted_not_zeroed():
    bad = job(1, dt(), dt(0, 10, 1), dt(0, 10))
    result = mod.analyze(snapshot([with_jobs(run(1, dt()), [bad])]))
    assert result["runner"]["runner_minutes"] == 0.0
    assert result["denominators"]["timed_jobs"] == 0
    assert result["denominators"]["timestamp_skew_jobs"] == 1


def test_larger_negative_timestamp_is_broken_not_zero():
    bad = job(1, dt(), dt(0, 10), dt(0, 9))
    with pytest.raises(mod.MeasurementError, match="negative duration"):
        mod.analyze(snapshot([with_jobs(run(1, dt()), [bad])]))


def test_started_job_without_created_at_is_broken():
    bad = job(1, None, dt(0, 1), dt(0, 2))
    with pytest.raises(mod.MeasurementError, match="has no created_at"):
        mod.analyze(snapshot([with_jobs(run(1, dt()), [bad])]))


def test_workflow_breakdown_keeps_run_conclusions():
    rows = [
        with_jobs(run(1, dt(0, 1), name="PR gate", conclusion="success"), []),
        with_jobs(run(2, dt(0, 2), name="PR gate", conclusion="failure"), []),
        with_jobs(run(3, dt(0, 3), name="Build", conclusion="cancelled"), []),
    ]
    result = mod.analyze(snapshot(rows))
    by_name = {row["workflow"]: row for row in result["by_workflow"]}
    assert by_name["PR gate"]["run_conclusions"] == {"failure": 1, "success": 1}
    assert by_name["Build"]["run_conclusions"] == {"cancelled": 1}


def test_workflow_breakdown_keeps_run_conclusions():
    rows = [
        with_jobs(run(1, dt(0, 1), name="PR gate", conclusion="success"), []),
        with_jobs(run(2, dt(0, 2), name="PR gate", conclusion="failure"), []),
        with_jobs(run(3, dt(0, 3), name="Build", conclusion="cancelled"), []),
    ]
    result = mod.analyze(snapshot(rows))
    by_name = {row["workflow"]: row for row in result["by_workflow"]}
    assert by_name["PR gate"]["run_conclusions"] == {"failure": 1, "success": 1}
    assert by_name["Build"]["run_conclusions"] == {"cancelled": 1}


def test_provenance_has_same_repo_fork_and_unknown():
    rows = [
        with_jobs(run(1, dt(0, 1)), []),
        with_jobs(run(2, dt(0, 2), repo="student/fork"), []),
        with_jobs(run(3, dt(0, 3), repo=None), []),
    ]
    assert mod.analyze(snapshot(rows))["provenance"] == {
        "same_repo": 1,
        "fork": 1,
        "unknown": 1,
    }


def test_empty_window_is_valid_and_explicit():
    result = mod.analyze(snapshot([]))
    assert result["denominators"]["runs"] == 0
    assert result["denominators"]["jobs"] == 0
    assert result["denominators"]["timing_coverage"] is None
    assert result["runner"]["runner_minutes_per_wall_hour"] == 0.0


def test_offline_replay_accepts_prior_output(tmp_path):
    source = snapshot([with_jobs(run(1, dt()), [job(1, dt(), dt(), dt(0, 2))])])
    previous = tmp_path / "previous.json"
    previous.write_text(json.dumps({"snapshot": source, "analysis": mod.analyze(source)}), encoding="utf-8")
    output = tmp_path / "replayed.json"
    assert mod.main(["--input", str(previous), "--output", str(output)]) == 0
    replayed = json.loads(output.read_text(encoding="utf-8"))
    assert replayed["analysis"] == mod.analyze(source)


def test_main_returns_two_for_broken_snapshot(tmp_path):
    source = tmp_path / "bad.json"
    source.write_text("{}", encoding="utf-8")
    assert mod.main(["--input", str(source)]) == mod.EXIT_BROKEN
