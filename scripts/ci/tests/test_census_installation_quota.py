"""Le census des consommateurs du quota d'installation (#26739, volet B).

Ce fichier verrouille ce qui doit rester vrai, quel que soit le transport :

  - la ligne `api-quota:` est lue comme un compte d'appels **payes** (les 304
    sont gratuits pour GitHub) : un organe qui publie plusieurs lignes prend
    la plus forte (une jambe peut republier son total apres un lot) ;
  - la colonne `appels visibles` compte les appels `gh api` **nommes** dans le
    journal : c'est une borne inferieure (un appel fait par un script Python
    a sortie capturee n'apparait pas), jamais un compte exhaustif ;
  - un passage dont l'organe ne publie pas de ligne `api-quota:` est rendu
    `n.m.` : une valeur inventee serait pire qu'un trou ;
  - le classement se fait sur les appels payes mesures, puis sur le volume de
    passages -- un `n.m.` ne doit pas passer devant un mesure ;
  - le census compte workflow par workflow (`total_count`), pas via le listing
    global : ce dernier est plafonne a 1 000 resultats et perdrait la fenetre ;
  - les journaux ne sont lus que pour les workflows les plus sollicites : un
    census qui lit 60 journaux coute plus de quota qu'il n'en mesure.

Aucun test n'atteint le reseau : le lancement de `gh` est simule.
"""

from __future__ import annotations

import importlib.util
import json
import sys
from datetime import datetime, timezone
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "census_installation_quota.py"
_spec = importlib.util.spec_from_file_location("census_installation_quota", SCRIPT)
mod = importlib.util.module_from_spec(_spec)
sys.modules[_spec.name] = mod
_spec.loader.exec_module(mod)


def test_api_quota_regex_reads_paid_calls():
    log = (
        "[pr-gate] api-quota: 12 gh api call(s), 138 servis en 304\n"
        "api-quota: 14 appel(s) API sur ce passage\n"
        "api-quota: 3 appel(s) REST\n"
        "api-quota: 0 gh api call(s)\n"
    )
    assert mod.API_QUOTA_RE.findall(log) == ["12", "14", "3", "0"]


def test_api_quota_regex_ignores_a_line_without_a_count():
    # une mention qualitative ne doit pas compter comme un appel
    assert mod.API_QUOTA_RE.findall("api-quota: source=app (seau de l'App)") == []


def test_visible_call_regex_counts_named_calls_only():
    log = (
        "##[command]gh api repos/jsboige/CoursIA/actions/runs\n"
        "##[command]gh api --method PATCH repos/x/check-runs/1\n"
        "un script Python appelle gh api en interne (sortie capturee)\n"
    )
    assert len(mod.VISIBLE_CALL_RE.findall(log)) == 2


def test_window_start_is_the_asked_back():
    now = datetime(2026, 11, 25, 12, 0, tzinfo=timezone.utc)
    start = mod.window_start(24, now)
    assert (now - start).total_seconds() == 24 * 3600


def test_fetch_workflows_reads_ids_and_names(monkeypatch):
    payload = {
        "workflows": [
            {"id": 11, "name": "PR gate"},
            {"id": 12, "name": "Sweep"},
        ]
    }
    monkeypatch.setattr(
        mod, "run_gh", lambda args: (0, json.dumps(payload), "")
    )
    assert mod.fetch_workflows("jsboige/CoursIA") == [(11, "PR gate"), (12, "Sweep")]


def test_count_runs_is_zero_on_transport_error(monkeypatch):
    monkeypatch.setattr(mod, "run_gh", lambda args: (1, "", "boom"))
    since = mod.window_start(24)
    assert mod.count_runs("jsboige/CoursIA", 11, since) == 0


def test_count_runs_reads_total_count(monkeypatch):
    monkeypatch.setattr(
        mod, "run_gh", lambda args: (0, json.dumps({"total_count": 327}), "")
    )
    since = mod.window_start(24)
    assert mod.count_runs("jsboige/CoursIA", 11, since) == 327


def test_render_table_marks_unmeasured_and_ranks_measured_first():
    measured = mod.Passage(workflow="Mesure", runs_24h=100, paid_calls=10.0)
    unmeasured = mod.Passage(workflow="Non mesure", runs_24h=900, visible_calls=2.0)
    table = mod.render_table([unmeasured, measured], top=10)
    lines = table.splitlines()
    assert lines[0].startswith("| # | Consommateur |")
    # le passage mesure passe devant, malgre 900 runs du passage non mesure
    assert "| 1 | Mesure |" in lines[2]
    assert "| 2 | Non mesure |" in lines[3]
    # le non mesure affiche n.m. sur les colonnes de compte
    assert "n.m." in lines[3]
    # les appels payes par 24 h valent la moyenne fois le nombre de passages
    assert "| 1 | Mesure | 100 | 10.0 | 1000 |" in lines[2]


def test_measure_passages_samples_only_the_top_workflows(monkeypatch):
    counts = {11: 500, 12: 300, 13: 2}
    logged: list[list[int]] = []

    def fake_count(repo, workflow_id, since):
        return counts.get(workflow_id, 0)

    def fake_ids(repo, workflow_id, since, limit):
        return [workflow_id * 100 + i for i in range(limit)]

    def fake_logs(repo, run_ids):
        logged.append(list(run_ids))
        return ["api-quota: 8 gh api call(s)"] * len(run_ids)

    monkeypatch.setattr(mod, "count_runs", fake_count)
    monkeypatch.setattr(mod, "fetch_run_ids", fake_ids)
    monkeypatch.setattr(mod, "sample_run_logs", fake_logs)
    passages = mod.measure_passages(
        "jsboige/CoursIA",
        [(11, "Gros"), (12, "Moyen"), (13, "Petit")],
        mod.window_start(24),
        sample=2,
        sample_top=2,
    )
    by_name = {p.workflow: p for p in passages}
    assert by_name["Gros"].runs_24h == 500
    assert by_name["Gros"].paid_calls == 8.0
    assert by_name["Gros"].calls_24h == 4000.0
    # le troisieme workflow (hors top-2) n'a pas de journal lu
    assert by_name["Petit"].paid_calls is None
    assert len(logged) == 2


def test_measure_passages_keeps_unmeasured_when_no_quota_line(monkeypatch):
    monkeypatch.setattr(mod, "count_runs", lambda repo, wid, since: 3)
    monkeypatch.setattr(mod, "fetch_run_ids", lambda repo, wid, since, limit: [1])
    monkeypatch.setattr(mod, "sample_run_logs", lambda repo, ids: ["rien ici"])
    passage = mod.measure_passages(
        "jsboige/CoursIA", [(11, "W")], mod.window_start(24), sample=1
    )[0]
    assert passage.paid_calls is None
    assert passage.calls_24h is None


def test_fetch_run_ids_reads_the_recent_runs(monkeypatch):
    payload = {"workflow_runs": [{"id": 501}, {"id": 502}]}
    monkeypatch.setattr(mod, "run_gh", lambda args: (0, json.dumps(payload), ""))
    assert mod.fetch_run_ids(
        "jsboige/CoursIA", 11, mod.window_start(24), 3
    ) == [501, 502]
