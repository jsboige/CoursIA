"""Tests de la mesure par job de l'inventaire « CI a deux etages » (P0).

L'instrument ne se teste pas en l'executant contre l'API -- ce serait une
mesure, pas un test. Ce qui est teste ici, c'est ce qui **decide** de la
mesure :

1. **L'echantillonnage est borne et deterministe.** Seuls des runs
   *termines* sont eligible : un run en cours n'a pas de `completed_at`, et
   le retenir biaiserait la mesure (attente courte parce qu'il vient de
   demarrer, execution absente). Le plafond par workflow et le plafond
   global sont respectes, et les runs retenus sont les plus recents.
2. **La file et l'execution sont mesurees separement**, et non melangees
   comme la duree du run (`updated_at - run_started_at`) les melangeait.
3. **La part du checkout** vient de l'organe natif
   (`measure_checkout_p90.step_minutes`), pas d'une reimplementation : un
   job sans etape de checkout est compte a part, jamais lu comme une duree
   nulle.
"""

from __future__ import annotations

import sys
from pathlib import Path

CI_DIR = Path(__file__).resolve().parents[1] / "ci"
sys.path.insert(0, str(CI_DIR))

import measure_ci_two_tier as m  # noqa: E402


def _run(run_id: int, path: str, created: str, status: str = "completed") -> dict:
    return {
        "id": run_id,
        "path": path,
        "name": path.split("/")[-1],
        "created_at": created,
        "status": status,
    }


def _job(created: str, started: str, completed: str | None,
         steps: list[dict] | None = None) -> dict:
    return {
        "id": 1,
        "created_at": created,
        "started_at": started,
        "completed_at": completed,
        "steps": steps or [],
    }


def _step(name: str, started: str, completed: str) -> dict:
    return {"name": name, "started_at": started, "completed_at": completed}


# --- L'echantillonnage ------------------------------------------------------


def test_un_run_non_termine_n_est_jamais_retenu() -> None:
    runs = [
        _run(1, ".github/workflows/a.yml", "2026-11-09T10:00:00Z", status="in_progress"),
        _run(2, ".github/workflows/a.yml", "2026-11-09T09:00:00Z"),
    ]
    retenus = m.selectionner_runs(runs, par_workflow=3, plafond=10)
    assert [r["id"] for r in retenus] == [2]


def test_le_plafond_par_workflow_est_respecte() -> None:
    runs = [
        _run(i, ".github/workflows/a.yml", f"2026-11-09T1{i}:00:00Z")
        for i in range(1, 6)
    ]
    retenus = m.selectionner_runs(runs, par_workflow=2, plafond=10)
    assert len(retenus) == 2
    # Les deux plus recents.
    assert {r["id"] for r in retenus} == {4, 5}


def test_le_plafond_global_prime_sur_le_plafond_par_workflow() -> None:
    runs = [
        _run(i, f".github/workflows/w{i}.yml", "2026-11-09T10:00:00Z")
        for i in range(1, 6)
    ]
    retenus = m.selectionner_runs(runs, par_workflow=3, plafond=4)
    assert len(retenus) == 4


def test_un_workflow_sans_run_termine_disparait_de_l_echantillon() -> None:
    runs = [_run(1, ".github/workflows/a.yml", "2026-11-09T10:00:00Z", status="queued")]
    assert m.selectionner_runs(runs, par_workflow=3, plafond=10) == []


# --- La mesure par job ------------------------------------------------------


def test_la_file_et_l_execution_sont_mesurees_separement(monkeypatch) -> None:
    runs = [_run(1, ".github/workflows/a.yml", "2026-11-09T10:00:00Z")]
    jobs = [{
        "jobs": [{
            "id": 7,
            # 10 min de file, 2 min d'execution
            "created_at": "2026-11-09T10:00:00Z",
            "started_at": "2026-11-09T10:10:00Z",
            "completed_at": "2026-11-09T10:12:00Z",
            "steps": [],
        }]
    }]

    def fake_api(path: str, tries: int = 4):
        return jobs[0]

    monkeypatch.setattr(m, "api", fake_api)
    mesure, couverture = m.mesurer_jobs(runs, par_workflow=3, plafond=10)
    assert couverture["runs_inspectes"] == 1
    ligne = mesure["rows"][0]
    assert ligne["attente_med_min"] == 10.0
    assert ligne["exec_med_min"] == 2.0
    # La part de la file dans le total (10 + 2 = 12) vaut 10/12.
    assert ligne["part_attente_dans_total_p90"] == 0.833


def test_un_job_sans_etape_de_checkout_est_compte_a_part(monkeypatch) -> None:
    runs = [_run(1, ".github/workflows/a.yml", "2026-11-09T10:00:00Z")]

    def fake_api(path: str, tries: int = 4):
        return {"jobs": [_job("2026-11-09T10:00:00Z", "2026-11-09T10:01:00Z",
                              "2026-11-09T10:02:00Z", steps=[])]}

    monkeypatch.setattr(m, "api", fake_api)
    mesure, _ = m.mesurer_jobs(runs, par_workflow=3, plafond=10)
    ligne = mesure["rows"][0]
    assert ligne["jobs_sans_etape_checkout"] == 1
    # « aucune etape reconnue » n'est pas « une etape de duree nulle ».
    assert ligne["checkout_med_min"] is None


def test_la_part_du_checkout_vient_de_l_organe_natif(monkeypatch) -> None:
    runs = [_run(1, ".github/workflows/a.yml", "2026-11-09T10:00:00Z")]

    def fake_api(path: str, tries: int = 4):
        return {"jobs": [_job(
            "2026-11-09T10:00:00Z", "2026-11-09T10:00:00Z", "2026-11-09T10:10:00Z",
            steps=[_step("Checkout repository", "2026-11-09T10:00:00Z",
                         "2026-11-09T10:04:00Z")],
        )]}

    monkeypatch.setattr(m, "api", fake_api)
    mesure, _ = m.mesurer_jobs(runs, par_workflow=3, plafond=10)
    ligne = mesure["rows"][0]
    # 4 min de checkout dans 10 min d'execution.
    assert ligne["checkout_med_min"] == 4.0
    assert ligne["part_checkout_dans_exec_p90"] == 0.4


def test_un_job_sans_fin_est_compte_a_part(monkeypatch) -> None:
    runs = [_run(1, ".github/workflows/a.yml", "2026-11-09T10:00:00Z")]

    def fake_api(path: str, tries: int = 4):
        return {"jobs": [_job("2026-11-09T10:00:00Z", "2026-11-09T10:01:00Z", None)]}

    monkeypatch.setattr(m, "api", fake_api)
    mesure, _ = m.mesurer_jobs(runs, par_workflow=3, plafond=10)
    ligne = mesure["rows"][0]
    assert ligne["jobs_sans_fin"] == 1
    assert ligne["exec_med_min"] is None


def test_une_page_de_jobs_illisible_ne_fait_pas_tomber_la_mesure(monkeypatch) -> None:
    runs = [_run(1, ".github/workflows/a.yml", "2026-11-09T10:00:00Z")]

    def fake_api(path: str, tries: int = 4):
        raise RuntimeError("reseau")

    monkeypatch.setattr(m, "api", fake_api)
    mesure, couverture = m.mesurer_jobs(runs, par_workflow=3, plafond=10)
    assert mesure["rows"] == []
    assert couverture["runs_sans_jobs_lisibles"] == 1
