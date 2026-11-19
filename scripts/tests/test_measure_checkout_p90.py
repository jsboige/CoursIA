"""Tests de l'instrument de mesure de la duree du checkout (P1 du plan).

L'instrument ne se teste pas en l'executant contre l'API -- ce serait une
mesure, pas un test. Ce qui est teste ici, c'est ce qui **decide** de la
mesure :

1. **Le filtre de fenetre est reellement applique.** La forme
   `created%3E={since}` se decode en une cle `created>` que l'API ignore :
   l'instrument mesurait alors n'importe quelle fenetre, pendant que son
   rapport annoncait la fenetre demandee. Mesure du 2026-11-09 : 2 500 runs
   non filtres contre 733 filtres sur la meme fenetre de 2 h. Le test
   verifie la **chaine construite**, decodee par le parseur de requete.
2. **L'etape de heal est reconnue**, et pas seulement celle du checkout :
   c'est l'etape que la phase P1 deplace le cout vers, et un instrument qui
   ne la verrait pas lirait ce deplacement comme un gain.
3. **Les fonctions pures** (percentile, minutes, detection d'etape) ont un
   comportement explicite sur les cas limites.
"""

from __future__ import annotations

import sys
import urllib.parse

import pytest
from pathlib import Path

CI_DIR = Path(__file__).resolve().parents[1] / "ci"
sys.path.insert(0, str(CI_DIR))

import measure_checkout_p90 as mcp  # noqa: E402


# --- Le filtre de fenetre ---------------------------------------------------


def test_le_filtre_de_fenetre_est_reellement_applique() -> None:
    url = mcp.runs_url("2026-11-09T20:00:00Z", 1)
    params = urllib.parse.parse_qs(urllib.parse.urlparse(url).query)
    # La cle attendue par l'API Actions est `created`, avec l'operateur `>=`
    # dans la valeur. C'est ce qui rend le filtre operant.
    assert params["created"] == [">=2026-11-09T20:00:00Z"]


def test_la_forme_que_l_api_ignore_n_est_plus_utilisee() -> None:
    # `created%3E=` se decode en une cle `created>` : l'API ignore cette
    # cle, et le filtre ne porte alors sur rien.
    url = mcp.runs_url("2026-11-09T20:00:00Z", 1)
    assert "created%3E=" not in url
    assert "created=%3E%3D" in url


def test_l_url_porte_le_declencheur_la_page_et_la_fenetre() -> None:
    url = mcp.runs_url("2026-11-09T20:00:00Z", 3)
    params = urllib.parse.parse_qs(urllib.parse.urlparse(url).query)
    assert params["event"] == ["pull_request"]
    assert params["page"] == ["3"]
    assert params["per_page"] == ["100"]


# --- Les fonctions pures ----------------------------------------------------


def test_percentile_interpole_sur_une_liste_triee() -> None:
    # La regle de l'instrument est `index = int(fraction * (n - 1))`, donc
    # un p90 sur quatre valeurs est la **troisieme** (index 2), et un median
    # la deuxieme (index 1). Elle n'est pas changee ici : la changer
    # rendrait les mesures anterieures non comparables.
    assert mcp.percentile([1.0, 2.0, 3.0, 4.0], 0.9) == 3.0
    assert mcp.percentile([1.0, 2.0, 3.0, 4.0], 0.5) == 2.0


def test_percentile_ordonne_avant_de_prendre() -> None:
    # Sans tri, l'index 1 de [1, 4, 2, 3] rendrait 4.0 ; avec le tri, il
    # rend 2.0. C'est le tri qui rend la mesure juste.
    assert mcp.percentile([1.0, 4.0, 2.0, 3.0], 0.5) == 2.0


def test_percentile_d_une_liste_vide_vaut_zero() -> None:
    assert mcp.percentile([], 0.9) == 0.0


def test_minutes_calcule_la_duree_entre_deux_horodatages() -> None:
    assert mcp.minutes("2026-11-09T20:00:00Z", "2026-11-09T20:01:30Z") == 1.5


def test_minutes_rend_none_si_la_fin_precede_le_debut() -> None:
    assert mcp.minutes("2026-11-09T20:05:00Z", "2026-11-09T20:00:00Z") is None


def test_minutes_rend_none_sans_horodatage() -> None:
    assert mcp.minutes(None, "2026-11-09T20:00:00Z") is None
    assert mcp.minutes("2026-11-09T20:00:00Z", None) is None


# --- La detection des etapes ------------------------------------------------


def _step(name: str, start: str, end: str) -> dict:
    return {"name": name, "started_at": start, "completed_at": end}


def test_l_etape_de_checkout_est_reconnue() -> None:
    steps = [_step("Checkout repository", "2026-11-09T20:00:00Z", "2026-11-09T20:01:00Z")]
    assert mcp.step_minutes(steps, mcp.CHECKOUT_NAMES) == 1.0


def test_l_etape_de_heal_est_reconnue() -> None:
    steps = [
        _step(
            "Purger un work dir reutilise au graphe incomplet (#15387)",
            "2026-11-09T20:00:00Z",
            "2026-11-09T20:02:00Z",
        )
    ]
    assert mcp.step_minutes(steps, mcp.HEAL_NAMES) == 2.0


def test_le_nom_de_heal_sans_son_numero_d_issue_est_reconnu() -> None:
    # le marqueur est le debut du nom : la queue peut changer sans que la
    # mesure perde son objet.
    steps = [
        _step(
            "Purger un work dir reutilise",
            "2026-11-09T20:00:00Z",
            "2026-11-09T20:02:00Z",
        )
    ]
    assert mcp.step_minutes(steps, mcp.HEAL_NAMES) == 2.0


def test_une_etape_inconnue_rend_none() -> None:
    steps = [_step("Set up Python", "2026-11-09T20:00:00Z", "2026-11-09T20:00:30Z")]
    assert mcp.step_minutes(steps, mcp.CHECKOUT_NAMES) is None
    assert mcp.step_minutes(steps, mcp.HEAL_NAMES) is None


def test_une_liste_d_etapes_vide_rend_none() -> None:
    assert mcp.step_minutes([], mcp.CHECKOUT_NAMES) is None
    assert mcp.step_minutes(None, mcp.HEAL_NAMES) is None

# --- Pagination temporelle -------------------------------------------------


def _fake_actions(runs):
    """API triee de la plus recente a la plus ancienne, plafonnee a 1000."""
    calls = []

    def api(url):
        params = urllib.parse.parse_qs(urllib.parse.urlparse(url).query)
        lo, hi = params["created"][0].split("..")
        page = int(params["page"][0])
        calls.append((lo, hi, page))
        eligible = sorted(
            (r for r in runs if lo <= r["created_at"] <= hi),
            key=lambda r: (r["created_at"], r["id"]), reverse=True,
        )
        capped = eligible[:1000]
        return {"total_count": len(eligible), "workflow_runs": capped[(page - 1) * 100:page * 100]}

    return api, calls


def _run(run_id, second, name="A"):
    from datetime import datetime, timedelta, timezone

    time = datetime(2026, 11, 1, tzinfo=timezone.utc) + timedelta(seconds=second)
    return {"id": run_id, "name": name, "created_at": time.strftime(mcp.FMT)}


def _bounds(last=1499):
    return mcp.ts(_run(0, 0)["created_at"]), mcp.ts(_run(0, last)["created_at"])


def test_1500_runs_sont_collectes_sans_trou_ni_doublon(monkeypatch):
    runs = [_run(i, i) for i in range(1500)]
    api, calls = _fake_actions(runs)
    monkeypatch.setattr(mcp, "gh", api)
    actual, complete = mcp.collect_runs(*_bounds(), 4000)
    assert complete
    assert [r["id"] for r in actual] == list(range(1499, -1, -1))
    assert len(calls) > 10
    assert calls[1][0] == _run(0, 750)["created_at"]
    assert any(lo == _run(0, 0)["created_at"] and hi == _run(0, 749)["created_at"] for lo, hi, _ in calls)


def test_plafond_exact_et_timestamps_identiques(monkeypatch):
    runs = [_run(i, 0) for i in range(1000)]
    api, calls = _fake_actions(runs)
    monkeypatch.setattr(mcp, "gh", api)
    actual, complete = mcp.collect_runs(*_bounds(0), 1000)
    assert complete and len(actual) == 1000
    assert len({r["id"] for r in actual}) == 1000
    assert len(calls) == 10


def test_plafond_indivisible_est_une_erreur(monkeypatch):
    import pytest

    api, _ = _fake_actions([_run(i, 0) for i in range(1001)])
    monkeypatch.setattr(mcp, "gh", api)
    with pytest.raises(RuntimeError, match="meme seconde"):
        mcp.collect_runs(*_bounds(0), 4000)


def test_limite_apres_filtre_workflow_et_temoin_de_troncature(monkeypatch):
    runs = [_run(i, i, "A" if i % 2 else "B") for i in range(1500)]
    api, _ = _fake_actions(runs)
    monkeypatch.setattr(mcp, "gh", api)
    actual, complete = mcp.collect_runs(*_bounds(), 10, "B")
    assert not complete
    assert [r["id"] for r in actual] == list(range(1498, 1478, -2))
    actual, complete = mcp.collect_runs(*_bounds(), 750, "B")
    assert complete and len(actual) == 750


def test_reponse_incomplete_et_erreur_api_ne_sont_pas_masquees(monkeypatch):
    import pytest

    monkeypatch.setattr(mcp, "gh", lambda url: {"total_count": 2, "workflow_runs": [_run(1, 0)]})
    with pytest.raises(RuntimeError, match="nombre de runs incoherent"):
        mcp.collect_runs(*_bounds(0), 5)

    def fail(url):
        raise RuntimeError("API indisponible")

    monkeypatch.setattr(mcp, "gh", fail)
    with pytest.raises(RuntimeError, match="API indisponible"):
        mcp.collect_runs(*_bounds(0), 5)
    with pytest.raises(RuntimeError, match="API indisponible"):
        mcp.collect_jobs(1)


def test_toutes_les_pages_de_jobs_sont_lues(monkeypatch):
    jobs = [{"id": i} for i in range(1, 106)]

    def api(url):
        page = int(urllib.parse.parse_qs(urllib.parse.urlparse(url).query)["page"][0])
        return {"total_count": len(jobs), "jobs": jobs[(page - 1) * 100:page * 100]}

    monkeypatch.setattr(mcp, "gh", api)
    assert mcp.collect_jobs(9) == jobs


def test_rapport_cli_signale_la_limite_et_filtre_avant_le_compte(monkeypatch, capsys):
    import json
    from datetime import datetime, timedelta, timezone

    now = datetime.now(timezone.utc).replace(microsecond=0)
    runs = [
        {"id": i, "name": "cible" if i % 2 else "autre",
         "created_at": (now - timedelta(seconds=i)).strftime(mcp.FMT)}
        for i in range(6)
    ]
    api, _ = _fake_actions(runs)
    job_calls = []

    def dispatch(url):
        if "/jobs?" in url:
            job_calls.append(url)
            return {"total_count": 0, "jobs": []}
        return api(url)

    monkeypatch.setattr(mcp, "gh", dispatch)
    monkeypatch.setattr(sys, "argv", ["measure", "--hours", "1", "--runs", "2", "--workflow", "cible"])
    assert mcp.main() == 0
    report = json.loads(capsys.readouterr().out)
    assert report["window_complete"] is False
    assert report["runs_inspectes"] == 2
    assert report["workflow_filter"] == "cible"
    assert len(job_calls) == 2 and "/runs/1/" in job_calls[0] and "/runs/3/" in job_calls[1]


def test_un_double_run_et_une_page_de_jobs_vide_sont_refuses(monkeypatch):
    import pytest

    monkeypatch.setattr(mcp, "gh", lambda url: {"total_count": 2, "workflow_runs": [_run(1, 0)] * 2})
    with pytest.raises(RuntimeError, match="duplique"):
        mcp.collect_runs(*_bounds(0), 5)
    monkeypatch.setattr(mcp, "gh", lambda url: {"total_count": 1, "jobs": []})
    with pytest.raises(RuntimeError, match="incomplete"):
        mcp.collect_jobs(1)


def test_jobs_dupliques_entre_pages_interrompent_le_rapport(monkeypatch, tmp_path, capsys):
    import pytest
    from datetime import datetime, timezone

    run = {"id": 42, "name": "A", "created_at": datetime.now(timezone.utc).strftime(mcp.FMT)}
    output = tmp_path / "rapport.json"

    def api(url):
        if "/jobs?" not in url:
            return {"total_count": 1, "workflow_runs": [run]}
        page = int(urllib.parse.parse_qs(urllib.parse.urlparse(url).query)["page"][0])
        ids = range(1, 101) if page == 1 else [100]
        return {"total_count": 101, "jobs": [{"id": i} for i in ids]}

    monkeypatch.setattr(mcp, "gh", api)
    monkeypatch.setattr(sys, "argv", ["measure", "--hours", "1", "--out", str(output)])
    with pytest.raises(RuntimeError, match="job duplique"):
        mcp.main()
    assert not output.exists()
    assert not capsys.readouterr().out


@pytest.mark.parametrize("job", [{}, {"id": None}, {"id": "42"}, {"id": True}, {"id": 0}, {"id": -1}, None])
def test_identifiant_de_job_invalide_est_refuse(monkeypatch, job):
    import pytest

    monkeypatch.setattr(mcp, "gh", lambda url: {"total_count": 1, "jobs": [job]})
    with pytest.raises(RuntimeError, match="ID de job invalide"):
        mcp.collect_jobs(42)
