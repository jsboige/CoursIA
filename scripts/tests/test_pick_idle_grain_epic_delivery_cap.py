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
import types

import pytest

import scripts.pick_idle_grain as pig
from scripts.pick_idle_grain import (
    EPIC_LANE_DELIVERY_CAP_DEFAULT,
    belt_filter,
    draw_belt,
    epic_delivery_cap_state,
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


def test_one_pr_citing_the_epic_twice_counts_once():
    """UNe livraison = UNe PR, pas une occurrence de citation.

    Regression mesuree (revue NanoClaw sur #23265) : un corps qui cite l'EPIC
    en tete (`Part of #N`) ET en pied (`Closes #N`) comptait 2, donc le
    plafond K=2 refusait la lane apres UNE seule livraison reelle -- une
    famine fabriquee par la mesure elle-meme.
    """
    prs = [_pr(1, LANE, 1, "Part of #16334\n\nCloses #16334")]
    assert epic_lane_delivery_counts(prs, LANE, now=NOW) == {16334: 1}


def test_two_prs_citing_the_epic_each_once_still_count_two():
    """Controle positif : la deduplication porte sur la PR, pas sur l'EPIC."""
    prs = [
        _pr(1, LANE, 1, "Part of #16334"),
        _pr(2, LANE, 1, "Closes #16334"),
    ]
    assert epic_lane_delivery_counts(prs, LANE, now=NOW) == {16334: 2}


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


# --- epic_delivery_cap_state : TROIS etats, pas deux ---------------------


def test_cap_state_measured_zero_is_not_unmeasured():
    """Le defaut que la revue a nomme : une mesure a ZERO n'est pas absente.

    `epic_deliveries == {}` sortait « non mesurees » alors que la lecture
    avait abouti et que la lane n'avait rien livre. Le garde avait tourne ;
    la sortie disait le contraire.
    """
    record = {"lane": LANE, "measured": True, "error": None,
              "truncated": False, "windows": {}, "undated": [],
              "epic_deliveries": {}}
    state, deliveries = epic_delivery_cap_state(record, LANE)
    assert state == "measured"
    assert deliveries == {}


def test_cap_state_measured_with_counts():
    record = {"lane": LANE, "measured": True, "error": None,
              "truncated": False, "windows": {}, "undated": [],
              "epic_deliveries": {16334: 2}}
    assert epic_delivery_cap_state(record, LANE) == ("measured", {16334: 2})


def test_cap_state_unmeasured_on_error():
    """Mesure en echec : le garde reste inactif, et le dit."""
    record = {"lane": LANE, "measured": False, "error": "gh timeout",
              "truncated": False, "windows": {}, "undated": [],
              "epic_deliveries": {}}
    assert epic_delivery_cap_state(record, LANE) == ("unmeasured", {})


def test_cap_state_not_applicable_without_lane():
    """Sans lane, le plafond n'a pas d'objet : il est par lane."""
    record = {"lane": LANE, "measured": True, "error": None,
              "truncated": False, "windows": {}, "undated": [],
              "epic_deliveries": {16334: 9}}
    assert epic_delivery_cap_state(record, None) == ("not-applicable", {})
    assert epic_delivery_cap_state(None, LANE) == ("not-applicable", {})


# --- Cablage : les trois points d'entree de belt_filter ------------------
#
# La revue a releve que le plafond n'etait cable que sur le chemin principal.
# Ces tests epinglent les deux autres : `draw_belt` (modele deterministe) et
# `consume_board` (voie de l'instantane). Sans eux, le cablage serait
# decoratif -- un parametre accepte mais jamais eprouve.


def _args(**over):
    base = {
        "exclude_issue": [], "require_label": [], "exclude_label": [],
        "min_age_days": None, "max_age_days": None,
        "min_idle_days": None, "max_idle_days": None,
        "urns": "grain,umbrella", "grains": 4, "lane": LANE,
        "epic_delivery_cap": 2, "check_claims": True,
    }
    base.update(over)
    return types.SimpleNamespace(**base)


def _belt_item(number, klass="grain"):
    return {"number": number, "klass": klass, "age": 10, "idle": 2,
            "genre": "docs", "labels": [], "title": f"issue #{number}",
            "created_at": "2026-09-01T00:00:00Z",
            "last_delivery_stamp": None}


def test_belt_filter_forwards_the_drops_to_the_caller():
    """La cause doit remonter : un plafond muet se lit comme une famine."""
    drops: list[tuple[dict, str]] = []
    kept = belt_filter([_belt_item(16334, "umbrella"), _belt_item(7)],
                       _args(), epic_deliveries={16334: 2}, drops=drops)
    assert [it["number"] for it in kept] == [7]
    assert [it["number"] for it, _cause in drops] == [16334]


def test_draw_belt_honours_the_cap():
    """Le modele deterministe ne doit pas pouvoir contourner le plafond."""
    drops: list[tuple[dict, str]] = []
    kept = draw_belt([_belt_item(16334, "umbrella"), _belt_item(7)],
                     _args(), epic_deliveries={16334: 2}, drops=drops)
    assert [it["number"] for it in kept] == [7]
    assert [it["number"] for it, _cause in drops] == [16334]


def test_draw_belt_fails_open_without_a_measure():
    kept = draw_belt([_belt_item(16334, "umbrella")], _args())
    assert [it["number"] for it in kept] == [16334]


def test_consume_board_honours_the_cap_on_the_snapshot_path():
    """La voie de l'instantane servait un EPIC deja livre : elle le retire."""
    items = [_belt_item(16334, "umbrella"), _belt_item(7)]
    snap = pig.build_board_snapshot(items, [], lane=LANE,
                                    computed_at="2026-10-29T11:59:00Z",
                                    head=len(items))
    picks, meta = pig.consume_board(snap, _args(), urns={"grain", "umbrella"},
                                    live_check=False,
                                    epic_deliveries={16334: 2})
    assert [it["number"] for it in picks] == [7]
    assert [d["number"] for d in meta["epic_delivery_cap"]["dropped"]] == [16334]
    assert meta["epic_delivery_cap"]["state"] == "measured"


def test_consume_board_declares_an_absent_measure_instead_of_serving_blind():
    """Sans mesure, l'etat est publie -- jamais un silence qui se lit comme un vert.

    Le chemin consommateur ne peut pas payer le corpus de PRs mergees que
    l'acceptance #20053 lui interdit ; il doit donc DIRE qu'il n'a pas evalue
    le plafond, et un appelant qui a la mesure la passe.
    """
    items = [_belt_item(7)]
    snap = pig.build_board_snapshot(items, [], lane=LANE,
                                    computed_at="2026-10-29T11:59:00Z",
                                    head=len(items))
    _picks, meta = pig.consume_board(snap, _args(), urns={"grain"},
                                     live_check=False)
    assert meta["epic_delivery_cap"]["state"] == "unmeasured"
    assert meta["epic_delivery_cap"]["applied"] is False
