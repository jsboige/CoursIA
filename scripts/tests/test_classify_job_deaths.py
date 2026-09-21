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


def test_fetch_annotations_tolerates_only_true_404():
    """Review ai-01 : seuls les 404 (job sans annotations) sont une classe
    valide ; un 401 (auth perimee) ou une panne reseau doit remonter
    bruyamment, jamais se fondre dans CANCELLED_OTHER."""
    import classify_job_deaths as mod

    mod.gh_api = lambda *a, **k: (_ for _ in ()).throw(
        RuntimeError("gh api repos/jsboige/CoursIA/check-runs/1/annotations "
                     "failed: gh: HTTP 404: Not Found (HTTP 404)")
    )
    assert mod.fetch_annotations(1) == []
    mod.gh_api = lambda *a, **k: (_ for _ in ()).throw(
        RuntimeError("gh api repos/jsboige/CoursIA/check-runs/1/annotations "
                     "failed: gh: HTTP 401: Bad credentials (HTTP 401)")
    )
    try:
        mod.fetch_annotations(1)
        raise AssertionError("401 doit propager, pas rendre []")
    except RuntimeError:
        pass
    mod.gh_api = lambda *a, **k: (_ for _ in ()).throw(
        RuntimeError("gh api repos/jsboige/CoursIA/check-runs/1/annotations "
                     "failed: connection refused")
    )
    try:
        mod.fetch_annotations(1)
        raise AssertionError("panne reseau doit propager, pas rendre []")
    except RuntimeError:
        pass


def test_sha_validation_is_hex_40_and_rejects_non_hex():
    """Review ai-01 : --sha exige exactement [0-9a-fA-F]{40}, pas seulement
    une longueur de 40 — sinon un sha non-hex rend un zero propre."""
    from classify_job_deaths import is_valid_sha

    assert is_valid_sha("f" * 40)
    assert is_valid_sha("0" * 40)
    assert not is_valid_sha("g" * 40)
    assert not is_valid_sha("z" * 40)
    assert not is_valid_sha("f" * 39)
    assert not is_valid_sha("f" * 41)
    assert not is_valid_sha("f" * 40 + "g")
    assert not is_valid_sha("")


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


def test_window_from_hours_is_a_rolling_window():
    """--hours est un raccourci CALCULE de --created : la borne haute est
    l'instant present, la basse son decalage exact. Deterministe par `now`
    injecte — sans horloge reelle dans le test."""
    from datetime import datetime, timedelta, timezone

    from classify_job_deaths import window_from_hours

    now = datetime(2026, 9, 21, 9, 40, 0, tzinfo=timezone.utc)
    assert window_from_hours(24, now) == "2026-09-20T09:40:00Z..2026-09-21T09:40:00Z"
    assert window_from_hours(6, now) == "2026-09-21T03:40:00Z..2026-09-21T09:40:00Z"
    # Le franchissement d'un mois n'est pas un cas special : c'est le meme
    # `timedelta`, et un census mensuel (`--hours 720`) y passe.
    assert window_from_hours(720, now) == (
        "2026-08-22T09:40:00Z..2026-09-21T09:40:00Z"
    )
    assert timedelta(hours=24) == timedelta(days=1)


def test_window_from_hours_rejects_non_positive():
    """0 ou negatif rendrait `START..END` a l'envers : l'API repondrait 0 run,
    un zero propre indiscernable d'une absence reelle (meme piege que --sha
    tronque). Fail bruyant plutot que silence."""
    from classify_job_deaths import window_from_hours

    for bad in (0, -1):
        try:
            window_from_hours(bad)
            raise AssertionError(f"--hours {bad} doit refuser")
        except SystemExit:
            pass


def test_hours_reaches_the_api_window(monkeypatch, capsys):
    """Cablage de bout en bout : `--hours 24` doit arriver a l'appel API en
    fenetre START..END de 24 h. Tester le helper seul laisserait passer la
    regression qui compte ici — un `--hours` accepte puis IGNORE (l'appelant
    retombant sur sa valeur par defaut) rendrait un census silencieusement
    faux, non un crash."""
    import re as _re

    import classify_job_deaths as mod

    captured: dict[str, str] = {}

    def fake_iter_red_runs(branch, event, created, max_runs):
        captured["created"] = created
        return []

    monkeypatch.setattr(mod, "iter_red_runs", fake_iter_red_runs)
    monkeypatch.setattr(
        sys, "argv", ["classify_job_deaths.py", "--hours", "24"]
    )
    assert mod.main() == 0

    window = captured["created"]
    match = _re.fullmatch(
        r"(\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z)\.\."
        r"(\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z)",
        window,
    )
    assert match, f"fenetre non conforme : {window!r}"
    from datetime import datetime

    fmt = "%Y-%m-%dT%H:%M:%SZ"
    span = datetime.strptime(match.group(2), fmt) - datetime.strptime(
        match.group(1), fmt
    )
    assert span.total_seconds() == 24 * 3600


def test_hours_and_created_are_mutually_exclusive():
    """Deux fenetres contradictoires dans le meme appel : argparse doit
    refuser (rc 2) plutot que d'en privilegier une en silence."""
    import subprocess

    script = REPO_ROOT / "scripts" / "ci" / "classify_job_deaths.py"
    result = subprocess.run(
        [
            sys.executable,
            str(script),
            "--hours",
            "24",
            "--created",
            "2026-09-06..2026-09-07",
        ],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 2
    assert "not allowed with" in result.stderr


if __name__ == "__main__":
    for name, fn in sorted(globals().items()):
        if name.startswith("test_") and callable(fn):
            fn()
            print(f"{name} OK")
    print("All tests passed.")
