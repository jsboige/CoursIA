#!/usr/bin/env python3
"""Tests pour releve_git_object_missing.py — issue #27729.

Aucun acces reseau : les fonctions testees sont pures (lecture d'etapes de
job, de signatures d'annotation, et agregation). Les payloads sont les
formes d'API mesurees sur la famille #18312.
"""
from __future__ import annotations

import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "scripts" / "ci"))

from releve_git_object_missing import (
    _borne,
    _tranches,
    agreger,
    franchit_checkout,
    preuve_signature,
    verdict,
)


def _job(conclusion: str = "success", steps: list[dict] | None = None) -> dict:
    return {
        "id": 42,
        "name": "job",
        "conclusion": conclusion,
        "runner_name": "myia-ai-01-wsl-3",
        "steps": steps or [],
    }


def _step(name: str, conclusion: str) -> dict:
    return {"name": name, "conclusion": conclusion}


def test_franchit_checkout_vrai_si_checkout_reussi():
    job = _job(steps=[_step("Checkout PR", "success"), _step("Run tests", "success")])
    assert franchit_checkout(job) is True


def test_franchit_checkout_faux_si_checkout_echoue():
    job = _job("failure", steps=[_step("Checkout PR", "failure")])
    assert franchit_checkout(job) is False


def test_franchit_checkout_faux_si_checkout_skipped():
    job = _job("skipped", steps=[_step("Checkout PR", "skipped")])
    assert franchit_checkout(job) is False


def test_franchit_checkout_faux_sans_etape_checkout():
    assert franchit_checkout(_job(steps=[_step("Run tests", "success")])) is False


def test_signature_promisor():
    annotations = [{"message": "could not fetch abcdef1234 from promisor remote"}]
    assert "promisor remote" in (preuve_signature(_job(), annotations) or "")


def test_signature_index_pack():
    annotations = [{"message": "fetch-pack: invalid index-pack output"}]
    assert "invalid index-pack output" in (preuve_signature(_job(), annotations) or "")


def test_signature_could_not_read():
    annotations = [{"message": "fatal: Could not read 6822b791899cf28b1a52cb7856f9f476d5ae2cc8"}]
    assert "Could not read" in (preuve_signature(_job(), annotations) or "")


def test_signature_exit_128_uniquement_si_les_etapes_echouees_sont_des_checkouts():
    job = _job("failure", steps=[_step("Checkout PR", "failure")])
    annotations = [{"message": "Process completed with exit code 128."}]
    assert "exit code 128" in (preuve_signature(job, annotations) or "")

    job_test = _job("failure", steps=[_step("Checkout PR", "success"), _step("pytest", "failure")])
    assert preuve_signature(job_test, annotations) is None


def test_agregation_compte_executions_et_occurrences():
    analyses = [
        {"job_id": 1, "run_id": 10, "jour": "2026-11-19", "workflow": "w", "runner": "myia-a",
         "conclusion": "success", "self_hosted": True, "franchit_checkout": True, "signature": None},
        {"job_id": 2, "run_id": 10, "jour": "2026-11-19", "workflow": "w", "runner": "myia-b",
         "conclusion": "success", "self_hosted": True, "franchit_checkout": True, "signature": None},
        {"job_id": 3, "run_id": 11, "jour": "2026-11-20", "workflow": "w", "runner": "myia-a",
         "conclusion": "failure", "self_hosted": True, "franchit_checkout": False,
         "signature": "from promisor remote"},
        {"job_id": 4, "run_id": 11, "jour": "2026-11-20", "workflow": "w", "runner": "",
         "conclusion": None, "self_hosted": False, "franchit_checkout": False, "signature": None},
    ]
    releve = agreger(analyses)
    assert releve["jobs"] == 4
    assert releve["executions_reelles"] == 2
    assert releve["executions_self_hosted"] == 2
    assert releve["occurrences"] == 1
    assert releve["par_jour"]["2026-11-19"]["executions"] == 2
    assert releve["par_jour"]["2026-11-20"]["occurrences"] == 1


def test_verdict_exige_le_seuil_d_executions():
    faible = {"occurrences": 0, "executions_reelles": 12, "executions_self_hosted": 12}
    assert verdict(faible, seuil=50)["criter_atteint"] is False

    suffisant = {"occurrences": 0, "executions_reelles": 731, "executions_self_hosted": 120}
    assert verdict(suffisant, seuil=50)["criter_atteint"] is True

    avec_occurrence = {"occurrences": 2, "executions_reelles": 731, "executions_self_hosted": 120}
    assert verdict(avec_occurrence, seuil=50)["criter_atteint"] is False


def test_verdict_refuse_un_acquittement_sur_lecture_incomplete():
    releve = {"occurrences": 0, "executions_reelles": 731, "executions_self_hosted": 120,
              "lectures_en_erreur": 3}
    bilan = verdict(releve, seuil=50)
    assert bilan["criter_atteint"] is False
    assert bilan["lecture_complete"] is False


def test_borne_date_seule_designe_la_journee_entiere():
    debut = _borne("2026-11-19", False)
    fin = _borne("2026-11-19", True)
    assert debut.strftime("%Y-%m-%dT%H:%M:%SZ") == "2026-11-19T00:00:00Z"
    assert fin.strftime("%Y-%m-%dT%H:%M:%SZ") == "2026-11-19T23:59:59Z"


def test_borne_iso_est_lue_telle_quelle():
    assert _borne("2026-11-19T08:30:00Z", False).strftime("%H:%M") == "08:30"


def test_tranches_horaires_couvrent_la_journee():
    tranches = _tranches(_borne("2026-11-19", False), _borne("2026-11-19", True), 60)
    assert len(tranches) == 24
    assert tranches[0][0] == "2026-11-19T00:00:00Z"
    assert tranches[-1][1] == "2026-11-19T23:59:59Z"


def test_tranches_quatre_heures():
    tranches = _tranches(_borne("2026-11-19", False), _borne("2026-11-19", True), 240)
    assert len(tranches) == 6
    assert tranches[1][0] == "2026-11-19T04:00:00Z"
