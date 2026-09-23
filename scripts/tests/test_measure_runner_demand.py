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


def job(
    job_id,
    created,
    started,
    completed,
    conclusion="success",
    runner_name=None,
    labels=None,
):
    return {
        "id": job_id,
        "name": f"job-{job_id}",
        "status": "completed" if completed else "queued",
        "conclusion": conclusion,
        "created_at": mod.iso_z(created) if created else None,
        "started_at": mod.iso_z(started) if started else None,
        "completed_at": mod.iso_z(completed) if completed else None,
        "runner_name": runner_name or ("GitHub Actions 1" if started else None),
        "labels": ["ubuntu-latest"] if labels is None else labels,
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


def test_larger_negative_timestamp_is_skew_not_fatal():
    # Real-world datum (job 98968836743, 2026-08-28): GitHub inverted runtime
    # by 6 s. The duration is unmeasurable -- count it as skew, never fatal
    # (a datum-level anomaly must not kill a 1400-run measurement).
    bad = job(1, dt(), dt(0, 10), dt(0, 9, 54))
    result = mod.analyze(snapshot([with_jobs(run(1, dt()), [bad])]))
    assert result["runner"]["runner_minutes"] == 0.0
    assert result["denominators"]["timed_jobs"] == 0
    assert result["denominators"]["timestamp_skew_jobs"] == 1


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


def test_label_and_runner_breakdowns_include_percentiles_and_denominators():
    jobs = [
        job(
            1, dt(), dt(0, 1), dt(0, 3), runner_name="runner-b",
            labels=["self-hosted", "coursia-linux"],
        ),
        job(
            2, dt(), dt(0, 2), dt(0, 6), runner_name="runner-a",
            labels=["self-hosted", "coursia-linux"],
        ),
        job(
            3, dt(), dt(0, 3), dt(0, 9), runner_name="runner-b",
            labels=["self-hosted", "coursia-linux"],
        ),
        job(
            4, dt(), dt(0, 4), dt(0, 12), runner_name="runner-a",
            labels=["self-hosted", "coursia-linux"],
        ),
        job(
            5, dt(), dt(0, 5), dt(0, 15), runner_name="runner-b",
            labels=["self-hosted", "coursia-linux"],
        ),
    ]
    result = mod.analyze(snapshot([with_jobs(run(1, dt()), jobs)]))

    assert [row["label"] for row in result["by_label"]] == [
        "coursia-linux", "self-hosted",
    ]
    label = result["by_label"][0]
    assert label["jobs"] == 5
    assert label["timed_jobs"] == 5
    assert label["timing_coverage"] == 1.0
    assert label["queue_wait_minutes"] == {"p50": 3.0, "p90": 4.6, "max": 5.0}
    assert label["runtime_minutes"] == {"p50": 6.0, "p90": 9.2, "max": 10.0}

    assert [row["runner_name"] for row in result["by_runner"]] == [
        "runner-a", "runner-b",
    ]
    runner_a = result["by_runner"][0]
    assert runner_a["queue_wait_minutes"] == {"p50": 3.0, "p90": 3.8, "max": 4.0}
    assert runner_a["runtime_minutes"] == {"p50": 6.0, "p90": 7.6, "max": 8.0}


def test_group_breakdowns_expose_incomplete_skew_and_missing_identity():
    incomplete = job(1, dt(), None, None, labels=[])
    skew = job(
        2, dt(), dt(0, 2), dt(0, 1), runner_name="runner-z",
        labels=["self-hosted"],
    )
    result = mod.analyze(snapshot([with_jobs(run(1, dt()), [incomplete, skew])]))

    labels = {row["label"]: row for row in result["by_label"]}
    assert labels["<unlabelled>"]["incomplete_or_untimed_jobs"] == 1
    assert labels["<unlabelled>"]["queue_wait_minutes"]["p50"] is None
    assert labels["self-hosted"]["timestamp_skew_jobs"] == 1
    assert labels["self-hosted"]["timed_jobs"] == 0

    runners = {row["runner_name"]: row for row in result["by_runner"]}
    assert runners["<unassigned>"]["incomplete_or_untimed_jobs"] == 1
    assert runners["runner-z"]["timestamp_skew_jobs"] == 1


def test_non_string_job_label_is_broken():
    invalid = job(1, dt(), dt(), dt(0, 1), labels=["self-hosted", 3])
    with pytest.raises(mod.MeasurementError, match="labels must be a list of strings"):
        mod.analyze(snapshot([with_jobs(run(1, dt()), [invalid])]))


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


# --- Co-residence #15574 -----------------------------------------------------
#
# L'hote est presume du nom du runner ; la concurrence est echantillonnee au
# point median de chaque job. Ce qui doit rester vrai : deux slots d'un meme
# hote se regroupent, un nom non attribuable n'est PAS un hote, et une
# concurrence non observable ne se lit pas comme une absence de concurrence.

def job_on(job_id, runner, start_min, end_min, day_minutes=0):
    """Un job borne en minutes depuis dt(0), pour lire les recouvrements a l'oeil."""
    base = dt(0, day_minutes // 60, day_minutes % 60)
    started = base.replace(minute=0) + mod.timedelta(minutes=start_min)
    return job(
        job_id,
        created=started,
        started=started,
        completed=started + mod.timedelta(minutes=end_min),
        runner_name=runner,
    )


def test_host_of_groups_slots_and_refuses_unattributable_names():
    assert mod.host_of("myia-po-2024-linux-docker-1") == "myia-po-2024-linux-docker"
    assert mod.host_of("myia-po-2024-linux-docker-12") == "myia-po-2024-linux-docker"
    # Deux slots du meme hote partagent donc bien leur prefixe.
    assert (
        mod.host_of("myia-po-2024-linux-docker-1")
        == mod.host_of("myia-po-2024-linux-docker-9")
    )
    # Un nom sans suffixe numerique n'est pas un hote : le deviner fabriquerait
    # un hote d'un seul slot, c'est-a-dire le chiffre meme qu'on mesure.
    assert mod.host_of("GitHub Actions 1") is None
    assert mod.host_of("myia-po-2024-linux-docker") is None
    assert mod.host_of("<unassigned>") is None
    assert mod.host_of(None) is None


def test_coresidence_separates_solo_from_shared_on_the_same_host():
    # Deux jobs du meme hote se recouvrent (0-20 et 10-30) ; un troisieme est
    # seul (40-50). Le job de 20 min en concurrence doit sortir « shared », le
    # job seul « solo » -- sans quoi la correlation duree/concurrence serait
    # mesuree sur un melange.
    rows = [
        snapshot([run(1, dt(0), name="W")]),
    ]
    jobs = [
        job_on(11, "myia-po-2024-linux-docker-1", 0, 20),
        job_on(12, "myia-po-2024-linux-docker-2", 10, 30),
        job_on(13, "myia-po-2024-linux-docker-3", 40, 50),
    ]
    rows[0]["runs"] = [with_jobs(run(1, dt(0), name="W"), jobs)]
    result = mod.analyze(rows[0])

    block = result["co_residence"]
    assert block["summary"]["hosts"] == 1
    assert block["summary"]["jobs_placed"] == 3
    assert block["summary"]["jobs_unplaced"] == 0
    assert block["summary"]["solo_jobs"] == 1
    assert block["summary"]["shared_jobs"] == 2
    host = block["hosts"][0]
    assert host["host"] == "myia-po-2024-linux-docker"
    assert host["slots_observed"] == 3
    assert host["max_concurrency_observed"] == 2


def test_coresidence_counts_two_hosts_apart():
    # Deux jobs simultanes mais sur deux hotes distincts ne sont PAS en
    # concurrence : c'est tout l'objet de la derivation d'hote.
    jobs = [
        job_on(21, "myia-po-2024-linux-docker-1", 0, 30),
        job_on(22, "myia-ai-01-linux-1", 0, 30),
    ]
    snap = snapshot([with_jobs(run(1, dt(0), name="W"), jobs)])
    block = mod.analyze(snap)["co_residence"]
    assert block["summary"]["hosts"] == 2
    assert block["summary"]["shared_jobs"] == 0
    assert {host["max_concurrency_observed"] for host in block["hosts"]} == {1}


def test_coresidence_reports_unplaced_instead_of_inventing_a_host():
    jobs = [
        job_on(31, "myia-po-2024-linux-docker-1", 0, 10),
        job_on(32, "some-unlabelled-runner", 0, 10),
    ]
    snap = snapshot([with_jobs(run(1, dt(0), name="W"), jobs)])
    block = mod.analyze(snap)["co_residence"]
    assert block["summary"]["jobs_unplaced"] == 1
    assert block["summary"]["jobs_placed"] == 1
    assert [host["host"] for host in block["hosts"]] == ["myia-po-2024-linux-docker"]


def test_coresidence_declares_its_own_caveats():
    snap = snapshot([with_jobs(run(1, dt(0), name="W"), [job_on(41, "h-1", 0, 5)])])
    block = mod.analyze(snap)["co_residence"]
    joined = " ".join(block["caveats"])
    assert "borne inferieure" in joined
    assert "presume" in joined


def test_coresidence_ratio_is_none_when_nothing_is_shared():
    snap = snapshot([with_jobs(run(1, dt(0), name="W"), [job_on(51, "h-1", 0, 5)])])
    summary = mod.analyze(snap)["co_residence"]["summary"]
    assert summary["shared_jobs"] == 0
    assert summary["shared_over_solo_p50_ratio"] is None


# --- Inventaire des runners (moitie statique) --------------------------------

def test_runners_inventory_groups_slots_per_host():
    snap = snapshot([])
    snap["runners"] = [
        {"id": 1, "name": "myia-po-2024-linux-docker-1", "status": "online", "busy": False,
         "labels": ["self-hosted", "coursia-ephemeral"]},
        {"id": 2, "name": "myia-po-2024-linux-docker-2", "status": "online", "busy": True,
         "labels": ["self-hosted", "coursia-ephemeral"]},
        {"id": 3, "name": "myia-ai-01-linux-1", "status": "offline", "busy": False,
         "labels": ["self-hosted"]},
    ]
    inv = mod.analyze(snap)["runners_inventory"]
    assert inv["availability"] == "measured"
    assert inv["total_runners"] == 3
    assert inv["unplaced_runners"] == 0
    by_host = {row["host"]: row for row in inv["hosts"]}
    assert by_host["myia-po-2024-linux-docker"]["slots"] == 2
    assert by_host["myia-po-2024-linux-docker"]["online"] == 2
    assert by_host["myia-po-2024-linux-docker"]["busy"] == 1
    assert by_host["myia-ai-01-linux"]["slots"] == 1
    assert by_host["myia-ai-01-linux"]["online"] == 0


def test_runners_inventory_distinguishes_unavailable_from_empty():
    # Un refus de lecture n'est pas un parc vide : les deux doivent rester
    # distinguables jusque dans la sortie.
    unavailable = mod.analyze({**snapshot([]), "runners": {"error": "gh api failed: 403"}})
    assert unavailable["runners_inventory"]["availability"] == "unavailable"
    assert "403" in unavailable["runners_inventory"]["detail"]

    not_collected = mod.analyze(snapshot([]))["runners_inventory"]
    assert not_collected["availability"] == "not_collected"


def test_runners_inventory_does_not_invent_a_host_for_an_unattributable_name():
    snap = snapshot([])
    snap["runners"] = [{"id": 9, "name": "ephemeral", "status": "online", "busy": False,
                        "labels": []}]
    inv = mod.analyze(snap)["runners_inventory"]
    assert inv["unplaced_runners"] == 1
    assert inv["hosts"] == []
