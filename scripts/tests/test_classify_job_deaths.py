#!/usr/bin/env python3
"""Tests for classify_job_deaths.py — issue #15055.

Classification is unit-tested on synthetic job + annotation payloads
matching the API shapes measured on the four red cases of 2026-09-06/07.
No network access: the classifier is a pure function.
"""
from __future__ import annotations

import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "scripts" / "ci"))

from classify_job_deaths import classify_job  # noqa: E402


def _job(conclusion: str, steps: list[dict] | None = None) -> dict:
    return {
        "id": 1,
        "name": "test-job",
        "conclusion": conclusion,
        "runner_name": "some-runner",
        "steps": steps or [],
    }


ANN_NOT_ACQUIRED = [{"message": (
    "The job was not acquired by Runner of type self-hosted even after "
    "multiple attempts"
)}]
ANN_LOST_COMM = [{"message": (
    "The self-hosted runner lost communication with the server. Verify the "
    "machine is running and has a healthy network connection"
)}]
ANN_TIMEOUT = [{"message": (
    "The job running on runner X has exceeded the maximum execution time "
    "of 60 minutes"
)}]


def test_no_runner_acquired():
    """#14945/#14931 : cancelled, 0/0 steps, annotation d'echec d'acquisition."""
    job = _job("cancelled", steps=[])
    assert classify_job(job, ANN_NOT_ACQUIRED) == "NO_RUNNER_ACQUIRED"


def test_no_runner_acquired_runner_empty_is_not_required():
    """La classe tient sur l'annotation, pas sur runner_name vide (le champ
    peut etre absent selon la version d'API) — la regression du discriminant
    serait silencieuse autrement."""
    job = _job("cancelled", steps=[])
    job.pop("runner_name")
    assert classify_job(job, ANN_NOT_ACQUIRED) == "NO_RUNNER_ACQUIRED"


def test_runner_lost_comm():
    """#14958/#14854 : failure, N/M steps resolues, aucune en failure."""
    steps = [
        {"number": 1, "name": "Set up job", "conclusion": "success"},
        {"number": 2, "name": "Checkout", "conclusion": "success"},
        {"number": 3, "name": "Build", "conclusion": None},
        {"number": 4, "name": "Test", "conclusion": None},
    ]
    assert classify_job(_job("failure", steps), ANN_LOST_COMM) == "RUNNER_LOST_COMM"


def test_real_step_failure_wins_over_infra_annotation():
    """Une etape reellement echouee est un rouge de contenu, meme si le
    runner est mort ensuite (steps de post-processing)."""
    steps = [
        {"number": 1, "name": "Checkout", "conclusion": "success"},
        {"number": 2, "name": "Run tests", "conclusion": "failure"},
    ]
    assert classify_job(_job("failure", steps), ANN_LOST_COMM) == "REAL_STEP_FAILURE"


def test_timeout():
    steps = [{"number": 1, "name": "Build", "conclusion": "success"}]
    assert classify_job(_job("failure", steps), ANN_TIMEOUT) == "TIMEOUT"


def test_cancelled_without_annotation_is_other():
    """Quarto (cancel-in-progress inconditionnel) : cancelled sans annotation
    d'acquisition -> classe distincte de NO_RUNNER_ACQUIRED."""
    assert classify_job(_job("cancelled", steps=[]), []) == "CANCELLED_OTHER"


def test_uncategorized_failure():
    steps = [{"number": 1, "name": "Build", "conclusion": "success"}]
    assert classify_job(_job("failure", steps), []) == "UNCATEGORIZED_FAILURE"


def test_shutdown_signal_is_lost_comm():
    """Variante d'agent : shutdown signal recu pendant le job."""
    ann = [{"message": "The runner has received a shutdown signal"}]
    assert classify_job(_job("failure", []), ann) == "RUNNER_LOST_COMM"


def test_run_cancelled_no_jobs_is_a_distinct_signature():
    """Batch de supersession mesure le 2026-09-07T23:02:33Z : run cancelled
    avec ZERO jobs (annulation avant creation). analyse_runs doit l'emettre
    en RUN_CANCELLED_NO_JOBS — sinon il est compté scanné mais invisible."""
    import classify_job_deaths as mod

    run = {
        "id": 42,
        "name": "Secret Scan",
        "conclusion": "cancelled",
        "created_at": "2026-09-07T23:02:33Z",
        "updated_at": "2026-09-07T23:02:40Z",
        "head_sha": "f5b46030",
    }
    orig_jobs, orig_ann = mod.fetch_run_jobs, mod.fetch_annotations
    mod.fetch_run_jobs = lambda run_id: []
    mod.fetch_annotations = lambda job_id: []
    try:
        payload = mod.analyse_runs([run])
    finally:
        mod.fetch_run_jobs = orig_jobs
        mod.fetch_annotations = orig_ann
    assert len(payload["rows"]) == 1
    assert payload["rows"][0]["class"] == "RUN_CANCELLED_NO_JOBS"


if __name__ == "__main__":
    for name, fn in sorted(globals().items()):
        if name.startswith("test_") and callable(fn):
            fn()
            print(f"{name} OK")
    print("All tests passed.")
