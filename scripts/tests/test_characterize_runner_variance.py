"""Tests de scripts/ci/characterize_runner_variance.py (#15574 items 1-2).

La collecte est injectable : aucun test ne parle au reseau. Les fixtures
construisent des reponses d'API gh minimales (workflow_runs + jobs) et
verifient l'attribution d'hote, le decompte de co-residence et les
agregats -- les trois grandeurs que la decision item 3 arbore.
"""
from __future__ import annotations

import json
import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import characterize_runner_variance as crv  # noqa: E402

UTC = timezone.utc


def _ts(minutes: float) -> str:
    return (datetime(2026, 10, 1, 12, 0, tzinfo=UTC) + timedelta(minutes=minutes)).isoformat()


def _run(run_id: int, completed_at: str, created_at: str | None = None) -> dict:
    # Le pre-filtre de fenetre lit created_at (le endpoint LIST ne porte pas
    # completed_at de facon fiable) ; les deux champs sont donc fournis.
    return {"id": run_id, "created_at": created_at or completed_at, "completed_at": completed_at}


def _job(name: str, runner: str, started: str, completed: str, conclusion: str = "success") -> dict:
    return {
        "name": name,
        "runner_name": runner,
        "status": "completed",
        "conclusion": conclusion,
        "started_at": started,
        "completed_at": completed,
    }


class FakeRunner:
    """Renvoie des payloads gh api sequences par motif d'URL."""

    def __init__(self, runs_payload: dict, jobs_by_run: dict[int, dict]):
        self.runs_payload = runs_payload
        self.jobs_by_run = jobs_by_run
        self.calls: list[list[str]] = []

    def __call__(self, argv: list[str]) -> str:
        self.calls.append(argv)
        url = argv[2] if len(argv) > 2 else ""
        if "/jobs" in url:
            run_id = int(url.split("/runs/")[1].split("/")[0])
            return json.dumps(self.jobs_by_run.get(run_id, {"jobs": []}))
        return json.dumps(self.runs_payload)


# --- host_of / is_heavy ----------------------------------------------------


def test_host_of_strips_slot_suffix_per_family():
    assert crv.host_of("myia-po-2024-linux-docker-7") == "myia-po-2024"
    assert crv.host_of("myia-po-2024-lean-docker-2") == "myia-po-2024"
    assert crv.host_of("myia-po-2024-linux-waiter-11") == "myia-po-2024"
    assert crv.host_of("myia-ai-01-wsl-7") == "myia-ai-01-wsl-7"


def test_is_heavy_distinguishes_families():
    assert crv.is_heavy("myia-po-2024-linux-docker-1")
    assert crv.is_heavy("myia-po-2024-lean-docker-2")
    assert not crv.is_heavy("myia-po-2024-linux-waiter-3")
    assert not crv.is_heavy("myia-ai-01-wsl-7")


# --- collect_jobs -----------------------------------------------------------


def test_collect_jobs_keeps_selfhosted_and_drops_unplaced():
    runs = {"workflow_runs": [_run(1, _ts(60))], "next_page_url": None}
    jobs = {
        1: {
            "jobs": [
                _job("Scripts Tests (CPU)", "myia-po-2024-linux-docker-4", _ts(0), _ts(30)),
                _job("Hosted leg", "", _ts(0), _ts(5)),
                {
                    "name": "En cours",
                    "runner_name": "myia-po-2024-linux-docker-5",
                    "status": "in_progress",
                    "conclusion": None,
                    "started_at": _ts(0),
                    "completed_at": None,
                },
            ]
        }
    }
    collected = crv.collect_jobs("jsboige/CoursIA", "scripts-tests.yml", datetime(2026, 9, 30, tzinfo=UTC), runner=FakeRunner(runs, jobs))
    assert len(collected) == 1
    job = collected[0]
    assert job["runner_name"] == "myia-po-2024-linux-docker-4"
    assert job["host"] == "myia-po-2024"
    assert job["duration_s"] == 1800.0


def test_collect_jobs_paginates_via_page_param():
    # gh api n'expose pas next_page_url dans le corps JSON : la pagination se
    # pilote par &page=N jusqu'a une page courte (<100 runs).
    page1 = {"workflow_runs": [_run(i, _ts(60 + i)) for i in range(100)]}
    page2 = {"workflow_runs": [_run(101, _ts(200))]}
    jobs = {1: {"jobs": [_job("A", "myia-po-2024-linux-docker-1", _ts(0), _ts(10))]},
            101: {"jobs": [_job("B", "myia-po-2024-linux-docker-2", _ts(61), _ts(80))]}}

    calls: list[list[str]] = []

    def runner(argv: list[str]) -> str:
        calls.append(argv)
        url = argv[2]
        if "/jobs" in url:
            run_id = int(url.split("/runs/")[1].split("/")[0])
            return json.dumps(jobs.get(run_id, {"jobs": []}))
        if "page=2" in url:
            return json.dumps(page2)
        return json.dumps(page1)

    collected = crv.collect_jobs("jsboige/CoursIA", "scripts-tests.yml", datetime(2026, 9, 30, tzinfo=UTC), runner=runner)
    assert sorted(job["name"] for job in collected) == ["A", "B"]
    assert any("page=2" in argv[2] for argv in calls), "page 2 jamais demandee"


def test_collect_jobs_drops_runs_before_window():
    early_done = datetime(2026, 9, 28, 12, 0, tzinfo=UTC).isoformat()
    early_created = datetime(2026, 9, 28, 10, 0, tzinfo=UTC).isoformat()
    runs = {"workflow_runs": [_run(1, early_done, created_at=early_created)], "next_page_url": None}
    jobs = {1: {"jobs": [_job("A", "myia-po-2024-linux-docker-1", early_created, early_done)]}}
    collected = crv.collect_jobs("jsboige/CoursIA", "scripts-tests.yml", datetime(2026, 9, 30, tzinfo=UTC), runner=FakeRunner(runs, jobs))
    assert collected == []


# --- overlap_counts ---------------------------------------------------------


def test_overlap_counts_two_concurrent_heavy_jobs_on_same_host():
    jobs = [
        {"run_id": 1, "name": "A", "runner_name": "myia-po-2024-linux-docker-1", "host": "myia-po-2024", "heavy": True,
         "conclusion": "success", "started_at": _ts(0), "completed_at": _ts(30), "duration_s": 1800.0},
        {"run_id": 2, "name": "B", "runner_name": "myia-po-2024-lean-docker-2", "host": "myia-po-2024", "heavy": True,
         "conclusion": "success", "started_at": _ts(10), "completed_at": _ts(40), "duration_s": 1800.0},
    ]
    assert crv.overlap_counts(jobs) == {1: 2}


def test_overlap_counts_sequential_heavy_jobs_do_not_overlap():
    jobs = [
        {"run_id": 1, "name": "A", "runner_name": "myia-po-2024-linux-docker-1", "host": "myia-po-2024", "heavy": True,
         "conclusion": "success", "started_at": _ts(0), "completed_at": _ts(10), "duration_s": 600.0},
        {"run_id": 2, "name": "B", "runner_name": "myia-po-2024-lean-docker-2", "host": "myia-po-2024", "heavy": True,
         "conclusion": "success", "started_at": _ts(10), "completed_at": _ts(20), "duration_s": 600.0},
    ]
    assert crv.overlap_counts(jobs) == {0: 2}


def test_overlap_counts_ignores_waiters_and_foreign_hosts():
    jobs = [
        {"run_id": 1, "name": "A", "runner_name": "myia-po-2024-linux-docker-1", "host": "myia-po-2024", "heavy": True,
         "conclusion": "success", "started_at": _ts(0), "completed_at": _ts(30), "duration_s": 1800.0},
        {"run_id": 2, "name": "w", "runner_name": "myia-po-2024-linux-waiter-3", "host": "myia-po-2024", "heavy": False,
         "conclusion": "success", "started_at": _ts(0), "completed_at": _ts(30), "duration_s": 1800.0},
        {"run_id": 3, "name": "C", "runner_name": "myia-ai-01-wsl-7", "host": "myia-ai-01-wsl-7", "heavy": False,
         "conclusion": "success", "started_at": _ts(0), "completed_at": _ts(30), "duration_s": 1800.0},
    ]
    assert crv.overlap_counts(jobs) == {0: 1}


def test_overlap_counts_boundary_touch_is_not_overlap():
    # fin de A == debut de B : chevauchement strict requis (o_start < end).
    jobs = [
        {"run_id": 1, "name": "A", "runner_name": "myia-po-2024-linux-docker-1", "host": "myia-po-2024", "heavy": True,
         "conclusion": "success", "started_at": _ts(0), "completed_at": _ts(10), "duration_s": 600.0},
        {"run_id": 2, "name": "B", "runner_name": "myia-po-2024-lean-docker-1", "host": "myia-po-2024", "heavy": True,
         "conclusion": "success", "started_at": _ts(10), "completed_at": _ts(20), "duration_s": 600.0},
    ]
    assert crv.overlap_counts(jobs) == {0: 2}


# --- analyze ----------------------------------------------------------------


def test_analyze_buckets_by_runner_host_and_hour():
    jobs = [
        {"run_id": 1, "name": "A", "runner_name": "myia-po-2024-linux-docker-1", "host": "myia-po-2024", "heavy": True,
         "conclusion": "success", "started_at": _ts(0), "completed_at": _ts(10), "duration_s": 600.0},
        {"run_id": 2, "name": "B", "runner_name": "myia-po-2024-linux-docker-1", "host": "myia-po-2024", "heavy": True,
         "conclusion": "success", "started_at": _ts(60), "completed_at": _ts(75), "duration_s": 900.0},
    ]
    analysis = crv.analyze(jobs)
    assert analysis["jobs_total"] == 2
    assert analysis["jobs_heavy"] == 2
    runner_stats = analysis["per_runner"]["myia-po-2024-linux-docker-1"]
    assert runner_stats["n"] == 2
    assert runner_stats["median_s"] == 750.0
    assert analysis["per_host"]["myia-po-2024"]["n"] == 2
    assert "12" in analysis["per_hour"]


def test_analyze_duration_by_overlap_bucket():
    # Deux jobs lourds simultanes (1 chevauchement chacun, dures differentes
    # volontairement : A rapide malgre le voisin, B lent) + un job lourd seul.
    jobs = [
        {"run_id": 1, "name": "A", "runner_name": "myia-po-2024-linux-docker-1", "host": "myia-po-2024", "heavy": True,
         "conclusion": "success", "started_at": _ts(0), "completed_at": _ts(6), "duration_s": 360.0},
        {"run_id": 2, "name": "B", "runner_name": "myia-po-2024-lean-docker-1", "host": "myia-po-2024", "heavy": True,
         "conclusion": "success", "started_at": _ts(0), "completed_at": _ts(30), "duration_s": 1800.0},
        {"run_id": 3, "name": "C", "runner_name": "myia-po-2024-linux-docker-2", "host": "myia-po-2024", "heavy": True,
         "conclusion": "success", "started_at": _ts(60), "completed_at": _ts(70), "duration_s": 600.0},
    ]
    analysis = crv.analyze(jobs)
    assert analysis["per_overlap"]["0"]["n"] == 1
    assert analysis["per_overlap"]["0"]["median_s"] == 600.0
    assert analysis["per_overlap"]["1"]["n"] == 2
    assert analysis["per_overlap"]["1"]["median_s"] == 1080.0


def test_analyze_collapses_high_overlap_into_bucket():
    # 4 jobs lourds mutuellement chevauches -> chacun 3 voisins -> bucket 3+.
    jobs = [
        {"run_id": i, "name": f"J{i}", "runner_name": f"myia-po-2024-linux-docker-{i}", "host": "myia-po-2024",
         "heavy": True, "conclusion": "success", "started_at": _ts(0), "completed_at": _ts(10),
         "duration_s": 100.0 * (i + 1)}
        for i in range(4)
    ]
    analysis = crv.analyze(jobs)
    assert set(analysis["per_overlap"].keys()) == {"3+"}
    assert analysis["per_overlap"]["3+"]["n"] == 4


def test_analyze_median_overall():
    jobs = [
        {"run_id": i, "name": f"J{i}", "runner_name": "myia-po-2024-linux-docker-1", "host": "myia-po-2024", "heavy": True,
         "conclusion": "success", "started_at": _ts(i), "completed_at": _ts(i + 1), "duration_s": float(100 * (i + 1))}
        for i in range(5)
    ]
    assert crv.analyze(jobs)["median_s"] == 300.0


# --- main -------------------------------------------------------------------


def test_main_json_shape(capsys, monkeypatch):
    runs = {"workflow_runs": [_run(1, _ts(60))], "next_page_url": None}
    jobs = {1: {"jobs": [_job("Scripts Tests (CPU)", "myia-po-2024-linux-docker-4", _ts(0), _ts(30))]}}
    real_collect = crv.collect_jobs
    monkeypatch.setattr(
        crv, "collect_jobs", lambda *a, **k: real_collect(*a, **{**k, "runner": FakeRunner(runs, jobs)})
    )
    rc = crv.main(["--json", "--days", "3"])
    assert rc == crv.EXIT_OK
    out = json.loads(capsys.readouterr().out)
    assert out["workflow"] == crv.DEFAULT_WORKFLOW
    assert out["jobs_total"] == 1
    assert "overlap_histogram" in out


def test_main_broken_api_returns_panne(capsys, monkeypatch):
    def boom(*a, **k):
        raise RuntimeError("gh down")

    monkeypatch.setattr(crv, "collect_jobs", boom)
    rc = crv.main(["--days", "1"])
    assert rc == crv.EXIT_BROKEN
    assert "[PANNE]" in capsys.readouterr().err
