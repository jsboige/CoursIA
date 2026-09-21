"""Tests check_run_state (#16765) -- fixtures = jambes REELLES du fondateur #16232.

Rollup verbatim de #16232 (gh pr view --json statusCheckRollup, 2026-09-19) :
le rollup rend les TROIS jambes `Always-on guards -- 14 organes, 1 checkout`,
dans l'ordre FAILURE / CANCELLED / SUCCESS -- non chronologique. Un fold
premiere-occurrence retient le FAILURE perime : c'est le defaut mesure par
ai-01. Le fold latest-wins retient le SUCCESS : #16232 est MERGED.
"""
import sys
from pathlib import Path

import pytest

# scripts/ n'est pas un package (pas de __init__.py) et pytest.ini ne met pas
# la racine sur sys.path : preamble obligatoire, meme forme que
# test_check_umbrella_freshness.py (sinon ModuleNotFoundError en CI -- Hermes
# CONCERNS 18/09, run 35404554399).
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from scripts.check_run_state import (  # noqa: E402
    RED, GREEN, fold_latest, main, normalize_leg, render, residual_reds,
)

# --- entrees rollup verbatim (camelCase, ordre EXACT du rollup) ------------
ROLLUP_16232_ALWAYS_ON = [
    {"__typename": "CheckRun", "completedAt": "2026-09-15T02:14:08Z",
     "conclusion": "FAILURE", "workflowName": "Always-on guards",
     "detailsUrl": "https://github.com/jsboige/CoursIA/actions/runs/34920294922/job/104226702528",
     "name": "Always-on guards -- 14 organes, 1 checkout",
     "startedAt": "2026-09-15T02:12:44Z", "status": "COMPLETED"},
    {"__typename": "CheckRun", "completedAt": "2026-09-15T02:12:42Z",
     "conclusion": "CANCELLED", "workflowName": "Always-on guards",
     "detailsUrl": "https://github.com/jsboige/CoursIA/actions/runs/34920294343/job/104226698538",
     "name": "Always-on guards -- 14 organes, 1 checkout",
     "startedAt": "2026-09-15T02:12:41Z", "status": "COMPLETED"},
    {"__typename": "CheckRun", "completedAt": "2026-09-15T02:20:42Z",
     "conclusion": "SUCCESS", "workflowName": "Always-on guards",
     "detailsUrl": "https://github.com/jsboige/CoursIA/actions/runs/34920713078/job/104228010691",
     "name": "Always-on guards -- 14 organes, 1 checkout",
     "startedAt": "2026-09-15T02:19:13Z", "status": "COMPLETED"},
]

# --- memes jambes, forme REST check-runs (snake_case, extraites de
# commits/94e31d7e.../check-runs le 2026-09-19) ------------------------------
REST_16232_ALWAYS_ON = [
    {"name": "Always-on guards -- 14 organes, 1 checkout",
     "conclusion": "cancelled", "started_at": "2026-09-15T02:12:41Z",
     "id": 104226698538, "details_url": "https://github.com/jsboige/CoursIA/actions/runs/34920294343/job/104226698538"},
    {"name": "Always-on guards -- 14 organes, 1 checkout",
     "conclusion": "failure", "started_at": "2026-09-15T02:12:44Z",
     "id": 104226702528, "details_url": "https://github.com/jsboige/CoursIA/actions/runs/34920294922/job/104226702528"},
    {"name": "Always-on guards -- 14 organes, 1 checkout",
     "conclusion": "success", "started_at": "2026-09-15T02:19:13Z",
     "id": 104228010691, "details_url": "https://github.com/jsboige/CoursIA/actions/runs/34920713078/job/104228010691"},
]

AO = "Always-on guards -- 14 organes, 1 checkout"


def test_fondateur_fold_latest_rend_le_succes_pas_le_failure_perime():
    folded = fold_latest(ROLLUP_16232_ALWAYS_ON)
    assert folded[AO]["conclusion"] == "success"
    assert folded[AO]["started_at"] == "2026-09-15T02:19:13Z"


def test_fondateur_fold_naif_premiere_occurrence_prendrait_le_failure():
    """Le piege mesure : le rollup rend le FAILURE en PREMIERE position.
    Un scan premiere-occurrence (le geste naturel sur une liste) retient le
    rouge perime -- preuve que le defect est bien le fold du lecteur."""
    first = {}
    for e in ROLLUP_16232_ALWAYS_ON:
        first.setdefault(e["name"], e)
    assert first[AO]["conclusion"] == "FAILURE"
    # le fold canonique diverge : c'est toute la raison d'etre du helper
    assert fold_latest(ROLLUP_16232_ALWAYS_ON)[AO]["conclusion"] == "success"


def test_parity_rollup_graphql_vs_rest_check_runs():
    """Rollup et /check-runs rendent les memes jambes : le fold doit rendre le
    meme verdict sur les deux formes (preuve sur le fondateur)."""
    assert (fold_latest(ROLLUP_16232_ALWAYS_ON)[AO]["conclusion"]
            == fold_latest(REST_16232_ALWAYS_ON)[AO]["conclusion"] == "success")


def test_normalize_leg_mappe_les_deux_formes():
    assert normalize_leg(ROLLUP_16232_ALWAYS_ON[2])["started_at"] == \
        normalize_leg(REST_16232_ALWAYS_ON[2])["started_at"] == \
        "2026-09-15T02:19:13Z"
    assert normalize_leg(ROLLUP_16232_ALWAYS_ON[2])["name"] == AO


def test_residual_reds_expose_le_rouge_supersede_sans_le_swallow():
    """Contre-preuve #11532 : un rouge ancien sous un vert recent peut TOUJOURS
    bloquer (AND inter-suites, CodeQL default setup). Le helper ne l'efface
    pas : il le rend dans residual_reds -- un latest vert n'est pas une
    preuve de mergeabilite."""
    res = residual_reds(REST_16232_ALWAYS_ON)
    assert len(res) == 1
    assert res[0]["name"] == AO
    assert res[0]["conclusion"] == "failure"
    assert res[0]["started_at"] == "2026-09-15T02:12:44Z"


def test_residual_vide_quand_le_dernier_est_rouge():
    """Rouge recent : PAS de residual (c'est un vrai rouge, latest le porte
    deja -- le classer residual serait le blanchir)."""
    legs = [
        {"name": "X", "conclusion": "success", "started_at": "T1", "id": 1},
        {"name": "X", "conclusion": "failure", "started_at": "T2", "id": 2},
    ]
    assert residual_reds(legs) == []
    assert fold_latest(legs)["X"]["conclusion"] == "failure"


def test_cancel_nest_jamais_un_rouge():
    """Asymetrie documentee (#13156 cancel-storms) : cancelled n'est pas un
    verdict d'echec -- ni dans RED, ni dans latest_reds."""
    assert "cancelled" not in RED and "cancelled" not in GREEN
    legs = ROLLUP_16232_ALWAYS_ON[:2]  # cancelled + failure, pas de vert recent
    state = render("deadbeef", legs)
    assert AO in state["latest_reds"]          # le failure reste un rouge
    legs_cancel_only = [ROLLUP_16232_ALWAYS_ON[1]]
    state2 = render("deadbeef", legs_cancel_only)
    assert state2["latest_reds"] == []         # cancel seul : pas de rouge
    assert state2["residual_reds"] == []


def test_tie_break_id_puis_ordre_quand_started_at_identiques():
    """Clee dedupe_latest : started_at, PUIS id, PUIS index (monotonie
    check-run, #11416)."""
    legs = [
        {"name": "X", "conclusion": "failure", "started_at": "T", "id": 1},
        {"name": "X", "conclusion": "success", "started_at": "T", "id": 2},
    ]
    assert fold_latest(legs)["X"]["conclusion"] == "success"
    legs_sans_id = [
        {"name": "X", "conclusion": "failure", "started_at": "T"},
        {"name": "X", "conclusion": "success", "started_at": "T"},
    ]
    assert fold_latest(legs_sans_id)["X"]["conclusion"] == "success"


def test_main_exit_codes_sans_reseau(monkeypatch, capsys):
    """--sha avec collect moque : 0 = latest tout vert (fondateur), 1 = rouge
    dans la vue latest, 2 = erreur d'instrument."""
    import scripts.check_run_state as m

    monkeypatch.setattr(m, "collect", lambda pr=None, sha=None:
                        ("94e31d7e", REST_16232_ALWAYS_ON))
    assert m.main(["--sha", "94e31d7e"]) == 0
    out = capsys.readouterr().out
    assert "success" in out and "residual_reds" in out

    rouge = [{"name": "Scripts Tests (CPU)", "conclusion": "failure",
              "started_at": "T1", "id": 1}]
    monkeypatch.setattr(m, "collect", lambda pr=None, sha=None: ("ab", rouge))
    assert m.main(["--sha", "ab", "--json"]) == 1
    payload = capsys.readouterr().out
    assert "Scripts Tests (CPU)" in payload

    def boom(pr=None, sha=None):
        raise RuntimeError("gh api ... -> 1: not found")
    monkeypatch.setattr(m, "collect", boom)
    assert m.main(["--sha", "ab"]) == 2
