#!/usr/bin/env python3
"""Tests for ``scripts/coordination/recette_due.py`` -- the weekly recette turn.

The organ answers one question per lane: has it served a ``recette`` issue in the
last ``--window-days``? If not, which recette issue goes first? The tests pin:

  * the validator declaration (body line) and the fleet/non-fleet fallback;
  * "ball in the fleet's court" = the validator spoke after the last fleet comment;
  * a claim-only fleet comment is NOT a communication to the validator (#21988,
    voie b): [CLAIMED]/[CLAIMED-AMEND] alone never hands the ball back, a
    delivery or plain-prose answer does;
  * the weekly window (a visit on ANY recette issue counts as the turn);
  * the service order (held by another lane last, ball first, never served next,
    then oldest fleet communication);
  * the rc contract (0 OK/NONE, 1 DUE, 2 organ unreachable -> fail-open).

The live ``gh`` path is replayed in the PR body; these tests never call ``gh``.
Run: python -m pytest scripts/tests/test_recette_due.py
"""
from __future__ import annotations

import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "coordination"))

import recette_due as rd  # noqa: E402

NOW = datetime(2026, 10, 6, 12, 0, tzinfo=timezone.utc)
LANE = "myia-po-2023:CoursIA"
OTHER = "myia-po-2027:CoursIA-2"


def _c(login, created_at, body="note"):
    return {"author": {"login": login}, "createdAt": created_at, "body": body,
            "url": f"https://example.invalid/{login}/{created_at}"}


def _issue(number, comments, body="Recette.\n\nValidateur : @fmomo-ai\n"):
    return {"number": number, "title": f"recette {number}", "body": body, "comments": comments}


def _claim(lane, created_at, marker="CLAIMED"):
    return _c("jsboige", created_at, f"[{marker}] lane {lane} -- tour de recette")


# --- validator declaration and fleet membership ---------------------------------

def test_declared_validator_plain_and_bold():
    assert rd.declared_validator("x\nValidateur : @fmomo-ai\n") == "fmomo-ai"
    assert rd.declared_validator("**Validateur** : @Some-One") == "Some-One"
    assert rd.declared_validator("pas de ligne") is None


def test_fleet_membership():
    assert rd.is_fleet("jsboige") and rd.is_fleet("myia-ai-01")
    assert rd.is_fleet("github-actions[bot]")
    assert rd.is_fleet(None)
    assert not rd.is_fleet("fmomo-ai")


# --- per-issue assessment --------------------------------------------------------

def test_ball_in_fleet_court_when_validator_spoke_last():
    st = rd.assess_issue(_issue(1, [_c("jsboige", "2026-10-01T10:00:00Z"),
                                    _c("fmomo-ai", "2026-10-02T10:00:00Z")]), LANE, NOW)
    assert st["ball_in_fleet_court"] is True
    assert st["validator"] == "fmomo-ai"


def test_ball_with_validator_after_fleet_answer():
    st = rd.assess_issue(_issue(1, [_c("fmomo-ai", "2026-10-01T10:00:00Z"),
                                    _c("jsboige", "2026-10-02T10:00:00Z")]), LANE, NOW)
    assert st["ball_in_fleet_court"] is False


def test_undeclared_validator_falls_back_to_non_fleet_author():
    st = rd.assess_issue(_issue(1, [_c("jsboige", "2026-10-01T10:00:00Z"),
                                    _c("someone", "2026-10-03T10:00:00Z")], body="sans ligne"), LANE, NOW)
    assert st["validator"] is None
    assert st["ball_in_fleet_court"] is True


def test_declared_validator_ignores_other_outsiders():
    st = rd.assess_issue(_issue(1, [_c("jsboige", "2026-10-01T10:00:00Z"),
                                    _c("drive-by", "2026-10-03T10:00:00Z")]), LANE, NOW)
    assert st["ball_in_fleet_court"] is False


def test_lane_visit_read_from_claim_markers():
    st = rd.assess_issue(_issue(1, [_claim(LANE, "2026-10-03T12:00:00Z"),
                                    _claim(LANE, "2026-10-04T12:00:00Z", "DELIVERED")]), LANE, NOW)
    assert st["last_lane_visit"] == "2026-10-04T12:00:00Z"
    assert abs(st["lane_visit_age_days"] - 2.0) < 1e-9


# --- a claim is not a communication to the validator (#21988, voie b) -------------

def test_fleet_claim_without_followup_keeps_ball_in_fleet_court():
    st = rd.assess_issue(_issue(1, [_c("fmomo-ai", "2026-10-01T10:00:00Z"),
                                    _claim(LANE, "2026-10-02T10:00:00Z")]), LANE, NOW)
    assert st["ball_in_fleet_court"] is True
    assert st["last_fleet_comment"] is None


def test_claimed_amend_alone_is_not_a_communication():
    st = rd.assess_issue(_issue(1, [_c("fmomo-ai", "2026-10-01T10:00:00Z"),
                                    _claim(LANE, "2026-09-25T10:00:00Z"),
                                    _claim(LANE, "2026-10-02T10:00:00Z", "CLAIMED-AMEND")]), LANE, NOW)
    assert st["ball_in_fleet_court"] is True
    assert st["last_fleet_comment"] is None


def test_fleet_delivery_returns_the_ball_to_validator():
    st = rd.assess_issue(_issue(1, [_c("fmomo-ai", "2026-10-01T10:00:00Z"),
                                    _claim(LANE, "2026-10-02T10:00:00Z"),
                                    _claim(LANE, "2026-10-03T10:00:00Z", "DELIVERED")]), LANE, NOW)
    assert st["ball_in_fleet_court"] is False
    assert st["last_fleet_comment"] == "2026-10-03T10:00:00Z"


def test_dispatch_comment_claim_plus_delivered_counts_as_communication():
    body = f"[CLAIMED] lane {LANE} -- tour de recette\n[DELIVERED] lane {LANE} -- PR #21279"
    st = rd.assess_issue(_issue(1, [_c("fmomo-ai", "2026-10-01T10:00:00Z"),
                                    _c("jsboige", "2026-10-02T10:00:00Z", body)]), LANE, NOW)
    assert st["ball_in_fleet_court"] is False


def test_cited_claim_marker_in_fence_is_not_an_event():
    # Un claim cite verbatim dans un bloc de code n'enacte rien (clc #12072) :
    # le commentaire reste une communication de flotte ordinaire.
    body = "```text\n[CLAIMED] lane myia-po-2023:CoursIA -- citation\n```\nReponse au validateur."
    st = rd.assess_issue(_issue(1, [_c("fmomo-ai", "2026-10-01T10:00:00Z"),
                                    _c("jsboige", "2026-10-02T10:00:00Z", body)]), LANE, NOW)
    assert st["ball_in_fleet_court"] is False


def test_live_claim_of_other_lane_holds_the_issue():
    st = rd.assess_issue(_issue(1, [_claim(OTHER, "2026-10-06T08:00:00Z")]), LANE, NOW)
    assert st["held_by"] == [OTHER]


def test_stale_claim_of_other_lane_does_not_hold():
    st = rd.assess_issue(_issue(1, [_claim(OTHER, "2026-10-01T08:00:00Z")]), LANE, NOW)
    assert st["held_by"] == []


def test_released_claim_does_not_hold():
    st = rd.assess_issue(_issue(1, [_claim(OTHER, "2026-10-06T08:00:00Z"),
                                    _claim(OTHER, "2026-10-06T09:00:00Z", "RELEASED")]), LANE, NOW)
    assert st["held_by"] == []


# --- decision ----------------------------------------------------------------------

def _states(*issues):
    return [rd.assess_issue(i, LANE, NOW) for i in issues]


def test_none_without_recette_issue():
    assert rd.decide([], 7)["verdict"] == "NONE"


def test_ok_when_any_recette_issue_visited_this_week():
    res = rd.decide(_states(_issue(1, [_claim(LANE, "2026-10-03T12:00:00Z")]),
                            _issue(2, [])), 7)
    assert res["verdict"] == "OK" and res["issue"] == 1


def test_due_when_last_visit_older_than_window():
    res = rd.decide(_states(_issue(1, [_claim(LANE, "2026-09-25T12:00:00Z")])), 7)
    assert res["verdict"] == "DUE" and res["issue"] == 1


def test_due_order_ball_first_then_never_served():
    old_visit = _issue(1, [_claim(LANE, "2026-09-20T12:00:00Z")])
    never = _issue(2, [_c("jsboige", "2026-09-01T00:00:00Z")])
    ball = _issue(3, [_claim(LANE, "2026-09-21T12:00:00Z"), _c("fmomo-ai", "2026-09-22T12:00:00Z")])
    assert rd.decide(_states(old_visit, never, ball), 7)["issue"] == 3
    assert rd.decide(_states(old_visit, never), 7)["issue"] == 2


def test_due_order_oldest_fleet_communication_last_criterion():
    # #21988 : un claim n'est pas une communication -- le critere de recence ne
    # lit que les communications (prose, livraisons). Les deux issues portent un
    # claim de la lane (visite recentes identiques), la prose de flotte tranche.
    a = _issue(1, [_claim(LANE, "2026-09-05T12:00:00Z"), _c("jsboige", "2026-09-20T12:00:00Z")])
    b = _issue(2, [_claim(LANE, "2026-09-05T12:00:00Z"), _c("jsboige", "2026-09-10T12:00:00Z")])
    assert rd.decide(_states(a, b), 7)["issue"] == 2


def test_abandoned_claim_issue_comes_back_into_service():
    # Pathologie #21988 mesuree : un claim pose puis abandonne laissait l'issue
    # en WAITING-VALIDATOR alors que personne n'attend de reponse. Voie b : la
    # balle reste chez la flotte, l'issue redevient servable et passe en tete.
    starved = _issue(2, [_claim(LANE, "2026-09-20T10:00:00Z")])
    pathology = _issue(1, [_c("fmomo-ai", "2026-10-01T10:00:00Z"),
                           _claim(OTHER, "2026-10-02T10:00:00Z")])
    res = rd.decide(_states(starved, pathology), 7)
    assert res["verdict"] == "DUE" and res["issue"] == 1
    assert "balle est chez la flotte" in res["reason"]


def test_held_issue_goes_last():
    held = _issue(1, [_c("fmomo-ai", "2026-10-02T12:00:00Z"), _claim(OTHER, "2026-10-06T08:00:00Z")])
    free = _issue(2, [])
    res = rd.decide(_states(held, free), 7)
    assert res["issue"] == 2


# --- run / main ----------------------------------------------------------------------

def test_run_with_injected_fetchers():
    issues = {7: _issue(7, [_c("fmomo-ai", "2026-09-24T10:00:00Z")])}
    res = rd.run(LANE, 7, NOW, list_issues=lambda: [{"number": 7}], fetch_issue=issues.__getitem__)
    assert res["verdict"] == "DUE" and res["issue"] == 7 and res["lane"] == LANE


def test_main_rc_contract(monkeypatch, capsys):
    monkeypatch.setattr(rd, "run", lambda *a, **k: {"verdict": "DUE", "issue": 7, "reason": "r", "issues": []})
    assert rd.main(["--lane", LANE]) == 1
    monkeypatch.setattr(rd, "run", lambda *a, **k: {"verdict": "OK", "issue": 7, "reason": "r", "issues": []})
    assert rd.main(["--lane", LANE]) == 0

    def boom(*a, **k):
        raise subprocess.CalledProcessError(1, ["gh"])
    monkeypatch.setattr(rd, "run", boom)
    assert rd.main(["--lane", LANE]) == 2
    assert "UNKNOWN" in capsys.readouterr().out
