"""#21067 correctif 1 -- plafond de LIVRAISONS par lane et par EPIC.

Le plafond de visites (#22500, `umbrella_visit_cause`) regarde un claim pose
sur l'EPIC ou une sous-issue creee. Il est aveugle a l'enchainement : une lane
qui passe d'un carnet au suivant ne pose ni l'un ni l'autre, et le tapis la
ressert. Ces tests epinglent le predicat qui comble ce trou, et surtout ses
trois faux positifs -- un plafond qui refuse sur une mesure absente est une
famine fabriquee.
"""

from __future__ import annotations

import datetime as dt

import pytest

from scripts.pick_idle_grain import (
    EPIC_LANE_DELIVERY_CAP_DEFAULT,
    epic_lane_delivery_cause,
    epic_lane_delivery_counts,
)

LANE = "myia-po-2024:CoursIA-2"
NOW = dt.datetime(2026, 10, 29, 12, 0, tzinfo=dt.timezone.utc)


def _pr(number: int, lane: str, merged_days_ago: float, cites: str) -> dict:
    merged = NOW - dt.timedelta(days=merged_days_ago)
    body = f"Grain: MED/tooling — lane {lane} — prev: MED/tooling #1\n\n{cites}\n"
    return {"number": number, "body": body,
            "mergedAt": merged.strftime("%Y-%m-%dT%H:%M:%SZ")}


def _umbrella(number: int, labels=None, klass="umbrella") -> dict:
    return {"number": number, "title": "un EPIC", "klass": klass,
            "labels": labels or []}


# --- epic_lane_delivery_counts -------------------------------------------


def test_counts_only_this_lane():
    prs = [
        _pr(1, LANE, 1, "Part of #16334"),
        _pr(2, "myia-po-2023:CoursIA-2", 1, "Part of #16334"),
        _pr(3, LANE, 2, "Closes #16334"),
    ]
    assert epic_lane_delivery_counts(prs, LANE, now=NOW) == {16334: 2}


def test_counts_ignore_prs_outside_window():
    prs = [
        _pr(1, LANE, 1, "Part of #16334"),
        _pr(2, LANE, 30, "Part of #16334"),  # hors fenetre 7 j
    ]
    assert epic_lane_delivery_counts(prs, LANE, now=NOW) == {16334: 1}


def test_counts_ignore_untagged_and_bare_hash():
    prs = [
        {"number": 1, "body": "Part of #16334", "mergedAt": NOW.strftime("%Y-%m-%dT%H:%M:%SZ")},
        _pr(2, LANE, 1, "voir le fil #16334 et la PR #9999"),  # #N nu : pas une citation
    ]
    assert epic_lane_delivery_counts(prs, LANE, now=NOW) == {}


def test_counts_empty_corpus_is_empty_not_error():
    assert epic_lane_delivery_counts(None, LANE, now=NOW) == {}
    assert epic_lane_delivery_counts([], LANE, now=NOW) == {}


# --- epic_lane_delivery_cause --------------------------------------------


def test_cause_fires_at_cap():
    it = _umbrella(16334)
    assert epic_lane_delivery_cause(it, {16334: 2}, 2, LANE) is not None


def test_cause_silent_below_cap():
    it = _umbrella(16334)
    assert epic_lane_delivery_cause(it, {16334: 1}, 2, LANE) is None


def test_cause_cap_zero_disables():
    it = _umbrella(16334)
    assert epic_lane_delivery_cause(it, {16334: 9}, 0, LANE) is None


def test_cause_fails_open_without_measure():
    it = _umbrella(16334)
    assert epic_lane_delivery_cause(it, None, 2, LANE) is None
    assert epic_lane_delivery_cause(it, {}, 2, LANE) is None
    assert epic_lane_delivery_cause(it, {16334: 9}, 2, None) is None


def test_cause_ignores_non_umbrella():
    it = _umbrella(16334, klass="grain")
    assert epic_lane_delivery_cause(it, {16334: 9}, 2, LANE) is None


def test_cause_exempts_consolidation():
    it = _umbrella(20298, labels=[{"name": "consolidation"}])
    assert epic_lane_delivery_cause(it, {20298: 9}, 2, LANE) is None


def test_cause_names_the_lane_and_the_count():
    cause = epic_lane_delivery_cause(_umbrella(16334), {16334: 3}, 2, LANE)
    assert LANE in cause
    assert "#21067" in cause
    assert "3 livraison" in cause


def test_default_cap_is_two():
    # Le cap de veine que les lanes appliquent a la main (variation-protocol).
    assert EPIC_LANE_DELIVERY_CAP_DEFAULT == 2
