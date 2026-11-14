#!/usr/bin/env python3
"""Offline tests for scripts/ci/detect_heads_without_ci.py.

The class under test was measured on #26455 (14/11): an `update-branch`
produced a head on which no `pull_request` workflow ran at all -- the only
check came from the review trigger. The merge chain then waited more than two
hours on an empty `gate=`.

What these pin:

1. **A PR whose head carries no `pull_request` run IS named** (positive
   control, the shape of #26455).
2. **A PR whose head carries a `pull_request` run is NOT named** (negative
   control, a healthy PR).
3. **A head younger than the threshold is NOT named** -- the CI has not had
   the time to run yet; naming it would be a false positive.
4. **A CI in flight (`EXPECTED` / `PENDING`) is NOT an absent CI** -- the
   check exists, it is queued.
5. **A workflow elided by `paths:` is not a false positive**: its check still
   carries the `pull_request` event.

Run: python -m pytest scripts/tests/test_detect_heads_without_ci.py
"""
from __future__ import annotations

import importlib.util
from datetime import datetime, timedelta, timezone
from pathlib import Path

import pytest

SCRIPT = Path(__file__).resolve().parent.parent / "ci" / "detect_heads_without_ci.py"


def _load():
    spec = importlib.util.spec_from_file_location("detect_heads_without_ci", SCRIPT)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


dw = _load()

NOW = datetime(2026, 11, 14, 13, 0, 0, tzinfo=timezone.utc)


def _pr(number: int, events, age_min: float = 60.0, states=(),
        mergeable: str = "MERGEABLE", merge_state: str = "CLEAN") -> dict:
    """A PR payload shaped like the GraphQL node."""
    contexts = []
    for event in events:
        contexts.append({"checkSuite": {"workflowRun": {"event": event}}})
    for state in states:
        contexts.append({"state": state})
    head = NOW - timedelta(minutes=age_min)
    return {
        "number": number,
        "title": "PR {}".format(number),
        "headRefOid": "a" * 40,
        "updatedAt": head.isoformat(),
        "mergeable": mergeable,
        "mergeStateStatus": merge_state,
        "commits": {"nodes": [{"commit": {"committedDate": head.isoformat()}}]},
        "statusCheckRollup": {"contexts": {"nodes": contexts}},
    }


def test_positif_une_pr_sans_run_pull_request_est_nommee():
    """Positive control: the shape of #26455 -- only a review-triggered check."""
    prs = [_pr(26455, events=["pull_request_review"], age_min=90.0)]
    named = dw.heads_without_ci(prs, NOW)
    assert [entry["number"] for entry in named] == [26455]
    assert named[0]["age_min"] == pytest.approx(90.0, abs=0.1)


def test_positif_une_pr_sans_aucun_check_est_nommee():
    """The empty form: no check at all on the head."""
    prs = [_pr(26456, events=[], age_min=120.0)]
    named = dw.heads_without_ci(prs, NOW)
    assert [entry["number"] for entry in named] == [26456]
    assert named[0]["checks"] == 0


def test_negatif_une_pr_avec_un_run_pull_request_nest_pas_nommee():
    """Negative control: a healthy PR is left alone."""
    prs = [_pr(26500, events=["pull_request"], age_min=120.0)]
    assert dw.heads_without_ci(prs, NOW) == []


def test_negatif_un_workflow_elague_par_paths_nest_pas_un_faux_positif():
    """A `paths:`-elided workflow still carries the `pull_request` event."""
    prs = [_pr(26501, events=["pull_request_target"], age_min=120.0)]
    assert dw.heads_without_ci(prs, NOW) == []


def test_une_tete_jeune_nest_pas_nommee():
    """The CI has not had the time to run yet."""
    prs = [_pr(26502, events=["pull_request_review"], age_min=2.0)]
    assert dw.heads_without_ci(prs, NOW) == []


def test_une_ci_en_vol_nest_pas_une_ci_absente():
    """A queued or pending check is a CI present, not absent."""
    prs = [_pr(26503, events=[], age_min=120.0, states=["PENDING"])]
    assert dw.heads_without_ci(prs, NOW) == []
    prs = [_pr(26504, events=[], age_min=120.0, states=["EXPECTED"])]
    assert dw.heads_without_ci(prs, NOW) == []


def test_une_date_de_tete_illisible_ne_rend_pas_la_pr_innomable():
    """An unreadable head date is not evidence of an absent CI."""
    pr = _pr(26505, events=["pull_request_review"], age_min=120.0)
    pr["commits"] = {"nodes": []}
    pr["updatedAt"] = ""
    assert dw.heads_without_ci([pr], NOW) == []


def test_le_seuil_est_parametrable():
    prs = [_pr(26506, events=["pull_request_review"], age_min=20.0)]
    assert [e["number"] for e in dw.heads_without_ci(prs, NOW, min_age_min=15.0)] == [26506]
    assert dw.heads_without_ci(prs, NOW, min_age_min=30.0) == []


def test_parse_iso_accepte_le_zulu_et_naive():
    assert dw.parse_iso("2026-11-14T13:00:00Z") == NOW
    naive = dw.parse_iso("2026-11-14T13:00:00")
    assert naive.tzinfo is not None
    assert naive == NOW


def test_le_nom_du_repo_est_valide():
    with pytest.raises(ValueError):
        dw.fetch_open_prs("pas-un-repo")


# --- les deux verdicts (correction de la CR sur #26543) ----------------------
#
# Une tete sans run `pull_request` n'a pas toujours la meme cause : GitHub ne
# lance AUCUN workflow `pull_request` sur une PR qu'il ne peut pas fusionner.
# Mesure du coordinateur (14/11, revue de #26543) : les deux PRs nommees par
# cet organe (#26496, #25144) etaient `mergeable=false`,
# `mergeable_state=dirty` ; fermer puis rouvrir les deux n'a rien relance
# (`actions/runs?head_sha=<tete>` rend 0 apres reouverture). Le geste nomme
# ne repare donc rien sur cette forme.
#
# Un test par verdict, sur la forme mesuree : zero check et `DIRTY`.


def test_verdict_conflit_sur_la_forme_mesuree_zero_check_et_dirty():
    """VERDICT CONFLIT : zero check + `DIRTY` -> le geste est de rafraichir
    la branche, PAS de fermer puis rouvrir."""
    prs = [_pr(26496, events=[], age_min=120.0, mergeable="CONFLICTING",
               merge_state="DIRTY")]
    named = dw.heads_without_ci(prs, NOW)
    assert [entry["number"] for entry in named] == [26496]
    assert named[0]["verdict"] == "conflict"
    assert "rafraichir la branche" in named[0]["repair"]
    # Le geste qui ne repaire rien sur cette forme ne doit pas apparaitre.
    assert "fermer puis rouvrir" not in named[0]["repair"]


def test_verdict_sans_run_sur_une_tete_fusionnable():
    """VERDICT SANS RUN : zero check + tete fusionnable -> fermer puis
    rouvrir (le geste qui relance la CI sans changer la tete)."""
    prs = [_pr(26455, events=["pull_request_review"], age_min=90.0)]
    named = dw.heads_without_ci(prs, NOW)
    assert named[0]["verdict"] == "no_run"
    assert "fermer puis rouvrir" in named[0]["repair"]
    assert "rafraichir la branche" not in named[0]["repair"]


def test_un_conflit_reste_nomme_la_classe_est_reelle():
    """Une PR en conflit est toujours « sans CI » : elle est nommee, avec le
    verdict et le geste qui correspondent."""
    prs = [_pr(25144, events=[], age_min=300.0, mergeable="CONFLICTING",
               merge_state="DIRTY")]
    named = dw.heads_without_ci(prs, NOW)
    assert [entry["number"] for entry in named] == [25144]
    assert named[0]["mergeable"] == "CONFLICTING"
    assert named[0]["mergeStateStatus"] == "DIRTY"


def test_mergeable_inconnu_but_dirty_reste_un_conflit():
    """GitHub repond `UNKNOWN` tant que `mergeable` n'est pas calcule : c'est
    alors `mergeStateStatus` qui porte la reponse."""
    prs = [_pr(26507, events=[], age_min=120.0, mergeable="UNKNOWN",
               merge_state="DIRTY")]
    named = dw.heads_without_ci(prs, NOW)
    assert named[0]["verdict"] == "conflict"


def test_le_verdict_par_defaut_reste_sans_run():
    """Sans champ de fusion lu, le verdict par defaut reste `no_run` : le
    comportement historique, et la forme mesuree de #26455."""
    pr = _pr(26508, events=[], age_min=120.0)
    pr.pop("mergeable")
    pr.pop("mergeStateStatus")
    named = dw.heads_without_ci([pr], NOW)
    assert named[0]["verdict"] == "no_run"
