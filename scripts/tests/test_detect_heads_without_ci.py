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


def _pr(number: int, events, age_min: float = 60.0, states=()) -> dict:
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
