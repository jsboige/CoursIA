#!/usr/bin/env python3
"""Tests for ``scripts/coordination/belt_queues.py`` -- the central belt draw.

The assignment of issues to lanes is the coordinator's judgment; the organ only
prepares the board and measures afterwards. The tests pin: the family key and the
needs hints shown on the board, the plate measurement (a dispatch claim alone does
not empty a plate, a hand-back or a closed issue does), the board excluding issues
still on a plate, the weekly recette line, and ``record`` refusing an issue given
to two lanes. Never calls ``gh``.
Run: python -m pytest scripts/tests/test_belt_queues.py
"""
from __future__ import annotations

import sys
from datetime import datetime, timezone
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "coordination"))

import belt_queues as bq  # noqa: E402

NOW = datetime(2026, 10, 6, 13, 43, tzinfo=timezone.utc)
A, B = "myia-po-2023:CoursIA", "myia-po-2027:CoursIA-2"


def _pick(n, title="t", body="", labels=None, genre="docs", delivered=None, claimed=None,
          created="2026-09-01T00:00:00Z"):
    return {"number": n, "title": title, "body": body, "labels": labels or [], "genre": genre, "idle": 0,
            "last_delivery_stamp": delivered, "last_claim_stamp": claimed, "created_at": created}


def _payload(n, comments=(), state="OPEN"):
    return {"number": n, "state": state, "comments": list(comments)}


def _mark(lane, at, marker="CLAIMED"):
    return {"author": {"login": "jsboige"}, "createdAt": at, "body": f"[{marker}] lane {lane} -- x", "url": "u"}


# --- board hints ------------------------------------------------------------------

def test_family_prefers_notebook_series_path():
    p = _pick(1, "[Lean] x", "voir MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-7.ipynb")
    assert bq.family_of(p) == "SymbolicAI/Lean"


def test_family_falls_back_to_title_tag_then_label_then_genre():
    assert bq.family_of(_pick(1, "[ICT] Jambe C3")) == "ICT"
    assert bq.family_of(_pick(1, "plain", labels=[{"name": "lean"}])) == "lean"
    assert bq.family_of(_pick(1, "plain", genre="ci")) == "ci"


def test_needs_detects_vision_and_local_vllm():
    assert bq.needs_of(_pick(1, "QA visuel des slides")) == ["vision"]
    assert bq.needs_of(_pick(1, "x", "appel a 192.168.0.47:5002")) == ["vllm-local"]


def test_visit_age_uses_belt_stamps_not_updated_at():
    p = _pick(1, delivered="2026-09-30T13:43:00Z", claimed="2026-10-02T13:43:00Z")
    assert bq.visit_age_days(p, NOW) == 4.0
    assert bq.visit_age_days(_pick(2, created="2026-09-26T13:43:00Z"), NOW) == 10.0


def test_groups_keep_belt_order_of_first_member():
    groups = bq.group_picks([_pick(1, "[X] a"), _pick(2, "[Y] b"), _pick(3, "[X] c")], NOW)
    assert [g["family"] for g in groups] == ["X", "Y"]
    assert [it["number"] for it in groups[0]["items"]] == [1, 3]


# --- plates -----------------------------------------------------------------------

PREV = {"assigned_at": "2026-10-06T09:43:00Z", "lanes": {
    A: {"arc": "X", "queue": [{"number": 10}, {"number": 11}]},
    B: {"arc": "Y", "queue": [{"number": 20}]},
}}


def test_plate_drops_handed_back_and_closed_issues():
    payloads = {10: _payload(10, [_mark(A, "2026-10-06T10:00:00Z"), _mark(A, "2026-10-06T11:00:00Z", "DELIVERED")]),
                11: _payload(11), 20: _payload(20, state="CLOSED")}
    plates = bq.measure_plates(PREV, payloads.__getitem__)
    assert [it["number"] for it in plates[A]["remaining"]] == [11]
    assert plates[B]["remaining"] == []


def test_dispatch_claim_alone_keeps_the_issue_on_the_plate():
    payloads = {10: _payload(10, [_mark(A, "2026-10-06T09:44:00Z")]), 11: _payload(11), 20: _payload(20)}
    plates = bq.measure_plates(PREV, payloads.__getitem__)
    assert [it["number"] for it in plates[A]["remaining"]] == [10, 11]


def test_hand_back_before_the_assignment_does_not_count():
    payloads = {10: _payload(10, [_mark(A, "2026-10-01T10:00:00Z", "RELEASED")]), 11: _payload(11), 20: _payload(20)}
    plates = bq.measure_plates(PREV, payloads.__getitem__)
    assert [it["number"] for it in plates[A]["remaining"]] == [10, 11]


def test_hand_back_by_another_lane_does_not_empty_my_plate():
    payloads = {10: _payload(10, [_mark(B, "2026-10-06T11:00:00Z", "DONE")]), 11: _payload(11), 20: _payload(20)}
    plates = bq.measure_plates(PREV, payloads.__getitem__)
    assert [it["number"] for it in plates[A]["remaining"]] == [10, 11]


def _delivered(lane, at, pr):
    return {"author": {"login": "jsboige"}, "createdAt": at,
            "body": f"[DELIVERED] lane {lane} -- PR #{pr}", "url": "u"}


def test_delivered_with_open_pr_keeps_the_issue_on_the_plate():
    # Meme lecture que recette_due.held_by (reducteur v2, #12386) : la PR est en
    # vol, la lane tient l'issue ; le board ne doit pas la croire rendue.
    payloads = {10: _payload(10, [_mark(A, "2026-10-06T10:00:00Z"), _delivered(A, "2026-10-06T11:00:00Z", 42)]),
                11: _payload(11), 20: _payload(20)}
    plates = bq.measure_plates(PREV, payloads.__getitem__, pr_states={42: "OPEN"})
    assert [it["number"] for it in plates[A]["remaining"]] == [10, 11]


@pytest.mark.parametrize("state", ["MERGED", "CLOSED"])
def test_delivered_with_merged_or_closed_pr_empties_the_plate(state):
    payloads = {10: _payload(10, [_mark(A, "2026-10-06T10:00:00Z"), _delivered(A, "2026-10-06T11:00:00Z", 42)]),
                11: _payload(11), 20: _payload(20)}
    plates = bq.measure_plates(PREV, payloads.__getitem__, pr_states={42: state})
    assert [it["number"] for it in plates[A]["remaining"]] == [11]


def test_reclaim_after_merged_delivery_keeps_the_issue_on_the_plate():
    payloads = {10: _payload(10, [_delivered(A, "2026-10-06T10:00:00Z", 42), _mark(A, "2026-10-06T11:00:00Z")]),
                11: _payload(11), 20: _payload(20)}
    plates = bq.measure_plates(PREV, payloads.__getitem__, pr_states={42: "MERGED"})
    assert [it["number"] for it in plates[A]["remaining"]] == [10, 11]


# --- board ------------------------------------------------------------------------

def test_board_hides_issues_still_on_a_plate_and_reports_recette():
    payloads = {10: _payload(10, [_mark(A, "2026-10-06T10:00:00Z", "DONE")]), 11: _payload(11),
                20: _payload(20, state="CLOSED")}
    belt = {"picks": [_pick(30, "[X] a"), _pick(11, "[X] old"), _pick(31, "[Z] b")]}

    def recette(lane):
        return {"verdict": "DUE", "issue": 17586} if lane == B else {"verdict": "OK", "issue": 17586}
    res = bq.board(belt, [A, B], PREV, NOW, fetch_issue=payloads.__getitem__, recette=recette)
    drawn = [it["number"] for g in res["families"] for it in g["items"]]
    assert drawn == [30, 31]
    assert [it["number"] for it in res["lanes"][A]["remaining"]] == [11]
    assert res["lanes"][B]["recette"]["verdict"] == "DUE"
    text = bq.render_board(res)
    assert "recette DUE #17586" in text and "1/2 rendues" in text


def test_board_without_previous_assignment():
    res = bq.board({"picks": [_pick(1, "[X] a")]}, [A], None, NOW)
    assert res["previous_at"] is None and res["lanes"][A]["assigned"] == 0


# --- record -------------------------------------------------------------------------

def test_record_stamps_and_keeps_order_and_arc():
    belt = {"picks": [_pick(5, "[X] a"), _pick(6, "[X] b")]}
    rec = bq.record({"lanes": {A: {"arc": "X progressif", "queue": [6, 5]}}}, belt, NOW)
    assert rec["assigned_at"] == "2026-10-06T13:43:00Z"
    assert [it["number"] for it in rec["lanes"][A]["queue"]] == [6, 5]
    assert rec["lanes"][A]["queue"][0]["family"] == "X" and rec["lanes"][A]["arc"] == "X progressif"


def test_record_refuses_an_issue_given_to_two_lanes():
    with pytest.raises(ValueError):
        bq.record({"lanes": {A: {"queue": [5]}, B: {"queue": [5]}}}, None, NOW)
