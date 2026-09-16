#!/usr/bin/env python3
"""test_check_runner_starvation_cadence.py — cadence servie du starvation advisory.

Couvre la jambe #15332 de check_runner_starvation.py :
  - evaluate_cadence : note systématique (minutes depuis le dernier run
    planifié + intervalle servi précédent)
  - WARNING SCHEDULER MUET seulement au-delà du seuil (pas de rouge sur le
    retard chronique de GitHub)
  - WARNING quand aucun run event=schedule n'est lisible
  - fetch_scheduled_runs : filtrage event=schedule, échec API -> liste vide

Usage :
    pytest tests/test_check_runner_starvation_cadence.py -v
"""

from __future__ import annotations

import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts" / "ci"))

import check_runner_starvation as crs  # noqa: E402

NOW = datetime(2026, 9, 16, 8, 0, tzinfo=timezone.utc)


def _v(**kw) -> object:
    return crs.evaluate_cadence(
        kw.get("scheduled", []),
        kw.get("now", NOW),
        kw.get("declared", 30.0),
        kw.get("warn", 240.0),
    )


def test_note_porte_la_cadence_servie() -> None:
    v = _v(scheduled=[NOW - timedelta(minutes=40), NOW - timedelta(minutes=340)])
    assert v.status == "OK"
    assert len(v.notes) == 1
    assert "40 min depuis le dernier run planifie" in v.notes[0]
    assert "intervalle servi precedent: 300 min" in v.notes[0]
    assert "declare 30 min" in v.notes[0]


def test_pas_de_warning_sur_retard_chronique() -> None:
    # Intervalles servis ~5 h observés à l'ét nominal : sous le seuil de 240 min
    # depuis le DERNIER run, aucune alerte.
    v = _v(scheduled=[NOW - timedelta(minutes=200), NOW - timedelta(minutes=500)])
    assert v.status == "OK"
    assert not v.warnings


def test_warning_scheduler_muet_au_dela_du_seuil() -> None:
    v = _v(scheduled=[NOW - timedelta(minutes=300), NOW - timedelta(minutes=600)])
    assert v.status == "OK"  # warning, pas ERROR
    assert len(v.warnings) == 1
    assert "SCHEDULER MUET" in v.warnings[0]
    assert "300 min" in v.warnings[0]


def test_aucun_run_lisible_donner_warning() -> None:
    v = _v(scheduled=[])
    assert len(v.warnings) == 1
    assert "SCHEDULER MUET" in v.warnings[0]
    assert not v.notes


def test_un_seul_run_visible_note_sans_intervalle() -> None:
    v = _v(scheduled=[NOW - timedelta(minutes=40)])
    assert v.status == "OK"
    assert "un seul run schedule visible" in v.notes[0]


def test_fetch_scheduled_runs_filtre_et_degrade(monkeypatch) -> None:
    # Deux runs rendus par l'API (un schedule, un workflow_run heartbeat) :
    # seules les dates des runs planifies sont retenues, ordre conserve.
    def fake_gh_json(args, token=None):
        if "event=schedule" not in args[0]:
            return {"workflow_runs": []}
        return {
            "workflow_runs": [
                {"created_at": "2026-09-16T06:51:15Z"},
                {"created_at": "2026-09-16T01:28:18Z"},
            ]
        }

    monkeypatch.setattr(crs, "_gh_json", fake_gh_json)
    runs = crs.fetch_scheduled_runs("jsboige/CoursIA", "linux-runner-starvation-advisory.yml")
    assert len(runs) == 2
    assert runs[0] == datetime(2026, 9, 16, 6, 51, 15, tzinfo=timezone.utc)

    # Echec API -> liste vide (l'evaluateur le traduit en warning, pas en crash).
    monkeypatch.setattr(crs, "_gh_json", lambda args, token=None: None)
    assert crs.fetch_scheduled_runs("jsboige/CoursIA", "linux-runner-starvation-advisory.yml") == []
