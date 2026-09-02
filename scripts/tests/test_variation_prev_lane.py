#!/usr/bin/env python3
"""Unit tests for `prev_lane_mismatches` -- the prev:/lane consistency witness
(#13383).

#10045 blocks a Grain tag whose `lane` is ABSENT. It is structurally blind to
one that is WRONG, and a wrong lane is not cosmetic: `variation_light_cap`
reads that field, so a mis-attributed PR is counted in ANOTHER lane's LIGHT
budget. #13383 measured 8 such PRs in one wave; the one a machine can catch is
#13350, which declared `lane myia-po-2026:CoursIA-2` while chaining `prev:`
onto #13349 -- a PR of po-2027.

The witness is validated BY ITS NEGATIVES, in both directions: neutralising
the predicate (matching lanes) and widening it (unknown prev, absent lane,
self-citation) must all stay silent.

FIXTURE NUMBERS MUST BE REALISTIC. `_PREV_CLAUSE_RE` matches `#(\\d{4,6})`, so
a fixture using `#1`/`#2` makes EVERY assertion of silence pass by chance --
the clause is never parsed at all, and the test proves nothing about lanes.
The first draft of this file did exactly that: eight silences green, and the
one positive red. Each silence below is therefore paired with a MUTATION that
changes only the lane and asserts the witness fires -- the proof that the
silence was about the lane, and not about the regex failing to bite.

Run: `python -m pytest scripts/tests/test_variation_prev_lane.py`
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import variation_light_cap as vlc  # noqa: E402

LANE_A = "myia-po-2024:CoursIA-2"
LANE_B = "myia-po-2027:CoursIA"


def pr(number, lane, prev=None, tier="MED", genre="tooling"):
    """A merged-PR record in the shape `_load` yields."""
    body = f"Grain: {tier}/{genre} -- lane {lane}"
    if prev is not None:
        body += f" -- prev: MED/tooling #{prev}"
    return {"number": number, "body": body, "labels": []}


def numbers(merged):
    return [m["number"] for m in vlc.prev_lane_mismatches(merged)]


# --- positive: the measured #13350 shape ----------------------------------

def test_prev_of_another_lane_is_flagged():
    """#13350: declared po-2026:CoursIA-2, prev chained on a po-2027 PR."""
    merged = [
        pr(13349, "myia-po-2027:CoursIA"),
        pr(13350, "myia-po-2026:CoursIA-2", prev=13349),
    ]
    assert vlc.prev_lane_mismatches(merged) == [{
        "number": 13350,
        "lane": "myia-po-2026:CoursIA-2",
        "prev_number": 13349,
        "prev_lane": "myia-po-2027:CoursIA",
    }]


def test_flags_each_offender_once():
    merged = [
        pr(14100, LANE_B),
        pr(14101, LANE_A, prev=14100),
        pr(14102, "myia-po-2025:CoursIA", prev=14100),
    ]
    assert numbers(merged) == [14101, 14102]


# --- negative control 1: neutralise the predicate (lanes agree) -----------

def test_same_lane_is_silent_and_the_mutation_fires():
    """The nominal chain: a lane's prev is its own previous grain.

    The mutation flips ONLY the cited PR's lane: same numbers, same clause,
    same parse. If the silent case were silent because the regex missed, the
    mutation would be silent too.
    """
    silent = [pr(14110, LANE_A), pr(14111, LANE_A, prev=14110)]
    assert numbers(silent) == []

    mutated = [pr(14110, LANE_B), pr(14111, LANE_A, prev=14110)]
    assert numbers(mutated) == [14111]


def test_no_prev_clause_is_silent_and_the_mutation_fires():
    silent = [pr(14120, LANE_B), pr(14121, LANE_A)]
    assert numbers(silent) == []

    mutated = [pr(14120, LANE_B), pr(14121, LANE_A, prev=14120)]
    assert numbers(mutated) == [14121]


# --- negative control 2: widen it (unknown must not read as mismatched) ---

def test_prev_outside_the_loaded_set_is_silent_and_the_mutation_fires():
    """Another day / another page: the cited lane is UNKNOWN, not different.

    This is the silence that matters most. `gh pr list` pages, so a lane's
    prev usually sits outside the window; treating absence as mismatch would
    fire on nearly every well-formed tag. The mutation adds the cited PR to
    the set -- nothing else changes -- and the witness speaks.
    """
    silent = [pr(14130, LANE_A, prev=14129)]
    assert numbers(silent) == []

    mutated = [pr(14129, LANE_B), pr(14130, LANE_A, prev=14129)]
    assert numbers(mutated) == [14130]


def test_prev_without_lane_is_silent_and_the_mutation_fires():
    """The cited PR carries no lane -- `unattributed()` is what reports it."""
    silent = [
        {"number": 14140, "body": "Grain: MED/tooling (no lane)", "labels": []},
        pr(14141, LANE_A, prev=14140),
    ]
    assert numbers(silent) == []

    mutated = [pr(14140, LANE_B), pr(14141, LANE_A, prev=14140)]
    assert numbers(mutated) == [14141]


def test_citing_pr_without_lane_is_silent_and_the_mutation_fires():
    silent = [
        pr(14150, LANE_B),
        {"number": 14151, "body": "Grain: MED/tooling -- prev: MED/tooling #14150",
         "labels": []},
    ]
    assert numbers(silent) == []

    mutated = [pr(14150, LANE_B), pr(14151, LANE_A, prev=14150)]
    assert numbers(mutated) == [14151]


def test_self_citation_is_silent_and_the_mutation_fires():
    """A tag citing itself is a typo, not a two-lane adjacency claim."""
    silent = [pr(14160, LANE_A, prev=14160)]
    assert numbers(silent) == []

    mutated = [pr(14159, LANE_B), pr(14160, LANE_A, prev=14159)]
    assert numbers(mutated) == [14160]


def test_empty_set_is_silent():
    assert vlc.prev_lane_mismatches([]) == []


# --- the blind spot, pinned so a null result is never read as "tags OK" ----

def test_interior_of_a_mistagged_run_is_invisible():
    """A run of same-wrong-lane PRs chaining onto each other agrees with
    itself: only the pair crossing back into a correct tag shows.

    This is the #13383 shape, measured on real bodies 2026-09-02: after the
    manual pass moved both ends of #13371->#13369 and #13373->#13371 together,
    those pairs became self-consistent and silent, while #13369->#13370 (which
    still crosses into ai-01) stays visible. Pinned here so nobody reads a
    null result as proof the tags are right -- it bounds the damage only.
    """
    merged = [
        pr(14180, LANE_B),                    # correctly tagged, other lane
        pr(14181, LANE_A, prev=14180),        # boundary  -> visible
        pr(14182, LANE_A, prev=14181),        # interior  -> invisible
        pr(14183, LANE_A, prev=14182),        # interior  -> invisible
    ]
    assert numbers(merged) == [14181]


# --- wiring into compute_signals ------------------------------------------

def test_signal_scoped_to_target_lane():
    """The offender declares po-2026; auditing po-2027 must not claim it."""
    merged = [
        pr(13349, "myia-po-2027:CoursIA"),
        pr(13350, "myia-po-2026:CoursIA-2", prev=13349),
    ]

    own = vlc.compute_signals(merged, "myia-po-2026:CoursIA-2")
    assert own["signals"]["PREV-LANE-MISMATCH"] is True
    assert [m["number"] for m in own["prev_lane_mismatches"]] == [13350]

    other = vlc.compute_signals(merged, "myia-po-2027:CoursIA")
    assert other["signals"]["PREV-LANE-MISMATCH"] is False
    assert other["prev_lane_mismatches"] == []


def test_signal_absent_on_a_clean_lane_day():
    merged = [pr(14170, LANE_A), pr(14171, LANE_A, prev=14170)]
    sig = vlc.compute_signals(merged, LANE_A)
    assert sig["signals"]["PREV-LANE-MISMATCH"] is False
