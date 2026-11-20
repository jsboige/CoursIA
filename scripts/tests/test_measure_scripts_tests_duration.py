#!/usr/bin/env python3
"""Tests pour scripts/ci/measure_scripts_tests_duration.py (#27171).

La mesure est lue a la source (API Actions) ; le contrat teste ici est le
**classement** avant/apres autour de l'instant de coupure, l'exclusion des
runs `cancelled` (un push suivant annule le precedent : sa duree ne mesure
rien) et le calcul des statistiques.

Run:
    python -m pytest scripts/tests/test_measure_scripts_tests_duration.py
"""
from __future__ import annotations

import importlib.util
import sys
from datetime import datetime, timezone
from pathlib import Path

MODULE_PATH = (
    Path(__file__).resolve().parents[1] / "ci" / "measure_scripts_tests_duration.py"
)

spec = importlib.util.spec_from_file_location("measure_scripts_tests_duration", MODULE_PATH)
assert spec and spec.loader
measure = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = measure
spec.loader.exec_module(measure)


def _run(run_id: int, created_at: str, head_sha: str = "abc123def456") -> dict:
    return {
        "id": run_id,
        "head_branch": "main",
        "head_sha": head_sha,
        "created_at": created_at,
    }


def _job(name: str, started: str, completed: str | None, conclusion: str = "success") -> dict:
    return {
        "name": name,
        "started_at": started,
        "completed_at": completed,
        "conclusion": conclusion,
    }


class FakeActions:
    """Actions injectables : aucun reseau dans les tests."""

    def __init__(self, runs: list[dict], jobs: dict[int, list[dict]]) -> None:
        self._runs = runs
        self._jobs = jobs

    def runs(self, workflow: str, branch: str, limit: int) -> list[dict]:
        return self._runs[:limit]

    def jobs(self, run_id: int) -> list[dict]:
        return self._jobs.get(run_id, [])


def _collect(fake: FakeActions, split: str = "2026-11-18T04:25:19Z"):
    split_dt = datetime.fromisoformat(split.replace("Z", "+00:00"))
    return measure.collect(fake, "scripts-tests.yml", "main", "Scripts Tests (CPU)", 50, split_dt)


def test_split_classifie_les_runs_avant_et_apres():
    fake = FakeActions(
        runs=[_run(1, "2026-11-18T04:16:50Z"), _run(2, "2026-11-18T04:30:00Z")],
        jobs={
            1: [_job("Scripts Tests (CPU)", "2026-11-18T04:16:53Z", "2026-11-18T04:32:17Z")],
            2: [_job("Scripts Tests (CPU)", "2026-11-18T04:30:05Z", "2026-11-18T04:50:00Z")],
        },
    )
    got = _collect(fake)
    assert [m.group for m in got] == ["before", "after"]
    assert got[0].duration_s == 924.0
    assert got[1].duration_s == 1195.0


def test_un_run_cancelled_est_exclu():
    """Un run annule par un push suivant ne mesure aucune duree."""
    fake = FakeActions(
        runs=[_run(1, "2026-11-18T04:16:50Z")],
        jobs={
            1: [
                _job(
                    "Scripts Tests (CPU)",
                    "2026-11-18T04:16:53Z",
                    "2026-11-18T04:20:00Z",
                    conclusion="cancelled",
                )
            ]
        },
    )
    assert _collect(fake) == []


def test_un_job_en_cours_est_exclu():
    """Un job non termine n'a pas de duree : il est ignore, pas compte a zero."""
    fake = FakeActions(
        runs=[_run(1, "2026-11-18T04:25:22Z")],
        jobs={1: [_job("Scripts Tests (CPU)", "2026-11-18T04:25:25Z", None, conclusion=None)]},
    )
    assert _collect(fake) == []


def test_un_autre_job_est_ignore():
    fake = FakeActions(
        runs=[_run(1, "2026-11-18T04:16:50Z")],
        jobs={
            1: [
                _job("ADK runtime contracts (18)", "2026-11-18T04:16:54Z", "2026-11-18T04:18:28Z"),
                _job("Scripts Tests (CPU)", "2026-11-18T04:16:53Z", "2026-11-18T04:32:17Z"),
            ]
        },
    )
    got = _collect(fake)
    assert len(got) == 1
    assert got[0].job == "Scripts Tests (CPU)"


def test_un_job_en_echec_conserve_sa_duree():
    """Un job qui echoue apres N minutes a bien dure N minutes : il compte."""
    fake = FakeActions(
        runs=[_run(1, "2026-11-18T04:16:50Z")],
        jobs={
            1: [
                _job(
                    "Scripts Tests (CPU)",
                    "2026-11-18T04:16:53Z",
                    "2026-11-18T04:43:24Z",
                    conclusion="failure",
                )
            ]
        },
    )
    got = _collect(fake)
    assert len(got) == 1
    assert got[0].conclusion == "failure"
    assert got[0].duration_s == 1591.0


def test_stats_sur_une_liste_vide():
    vide = measure.stats([])
    assert vide["n"] == 0
    assert vide["median_s"] is None


def test_stats_mediane_et_moyenne():
    got = measure.stats([924.0, 933.0, 1108.0, 1121.0])
    assert got["n"] == 4
    assert got["median_s"] == round((933.0 + 1108.0) / 2, 1)
    assert got["mean_s"] == round((924.0 + 933.0 + 1108.0 + 1121.0) / 4, 1)
    assert got["min_s"] == 924.0
    assert got["max_s"] == 1121.0


def test_le_point_de_coupure_est_inclus_du_cote_apres():
    """Un job demarrant exactement a l'instant de coupure compte comme apres."""
    fake = FakeActions(
        runs=[_run(1, "2026-11-18T04:25:19Z")],
        jobs={1: [_job("Scripts Tests (CPU)", "2026-11-18T04:25:19Z", "2026-11-18T04:40:00Z")]},
    )
    got = _collect(fake)
    assert [m.group for m in got] == ["after"]


def test_parse_accepte_le_suffixe_z():
    assert measure._parse("2026-11-18T04:25:19Z") == datetime(
        2026, 11, 18, 4, 25, 19, tzinfo=timezone.utc
    )


def test_le_rapport_repartit_les_durees_par_conclusion():
    """Le rapport expose une entree par couple groupe/conclusion (mutant : le calcul
    des statistiques y etait applique au dictionnaire, pas a la liste)."""
    fake = FakeActions(
        runs=[
            _run(1, "2026-11-18T04:16:50Z"),
            _run(2, "2026-11-18T04:16:50Z"),
            _run(3, "2026-11-18T04:30:00Z"),
        ],
        jobs={
            1: [_job("Scripts Tests (CPU)", "2026-11-18T04:16:53Z", "2026-11-18T04:32:17Z")],
            2: [
                _job(
                    "Scripts Tests (CPU)",
                    "2026-11-18T04:16:53Z",
                    "2026-11-18T04:43:24Z",
                    conclusion="failure",
                )
            ],
            3: [_job("Scripts Tests (CPU)", "2026-11-18T04:32:20Z", "2026-11-18T04:47:03Z")],
        },
    )
    got = measure.collect(fake, "scripts-tests.yml", "main", "Scripts Tests (CPU)", 50,
                          datetime(2026, 11, 18, 4, 25, 19, tzinfo=timezone.utc))
    report = measure.build_report(
        got,
        repo="jsboige/CoursIA",
        workflow="scripts-tests.yml",
        branch="main",
        job="Scripts Tests (CPU)",
        split="2026-11-18T04:25:19Z",
    )
    assert report["before"]["n"] == 2
    assert report["after"]["n"] == 1
    assert report["after"]["median_s"] == 883.0
    assert report["by_conclusion"]["before:success"]["n"] == 1
    assert report["by_conclusion"]["before:failure"]["n"] == 1
    assert report["by_conclusion"]["after:success"]["median_s"] == 883.0
    assert len(report["measurements"]) == 3
