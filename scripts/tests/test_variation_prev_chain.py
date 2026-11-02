#!/usr/bin/env python3
"""Unit tests for `prev_chain_runs` -- the chaining-outside-the-belt axis
(#21067 correctif 2).

A VEIN (the #11343 axis) counts how many merged PRs of a lane cite the same
issue in a day; it is blind to HOW they got there. #21067 measured the other
half: some EPICs absorb dozens of grains from ONE lane because the lane walks
from grain to grain -- each new PR chains `prev:` onto the previous one INSIDE
the same EPIC, and no draw from the belt happened between them. The correctif
2 sends the NEXT grain of such a walk back to the tapis, so the organ must see
the chain itself, not only the vein.

The chain is validated BY ITS NEGATIVES, in both directions: a `prev:` that
cites a PR of ANOTHER issue (legitimate rotation), one that cites a PR with
no readable citation, a fresh draw (no `prev:`), and a different-lane
`prev:` (the #13383 witness, a separate defect) must all BREAK the chain.

FIXTURE NUMBERS MUST BE REALISTIC. `_PREV_CLAUSE_RE` matches `#(\\d{4,6})`:
a fixture using `#1`/`#2` makes every assertion of silence pass by chance --
the clause is never parsed at all. Same discipline as
`test_variation_prev_lane.py`, whose first draft had eight silences green and
the one positive red because of exactly that. Issue citations live in the
SECOND body line: `extract_vein_key` skips the `Grain:` tag line, so a body
whose only citation is the tag makes every vein_key None and the chain
fires never -- the opposite false silence.

Run: `python -m pytest scripts/tests/test_variation_prev_chain.py`
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import variation_light_cap as vlc  # noqa: E402

LANE = "myia-po-2027:CoursIA-2"


def pr(number, issue, prev=None, lane=LANE, genre="tooling"):
    """A merged-PR record: cites `issue` on line 2, chains `prev:` on line 3."""
    body = f"Grain: MED/{genre} -- lane {lane} -- prev: MED/{genre} #{prev}\n" \
        if prev is not None else f"Grain: MED/{genre} -- lane {lane}\n"
    body += f"\nTranche de #{issue}."
    return {"number": number, "body": body, "labels": []}


def chains(merged, **kw):
    return vlc.prev_chain_runs(merged, LANE, **kw)


# --- positive: the #21067 walk ----------------------------------------------

def test_three_grains_same_epic_chain():
    """Two `prev:` links inside one EPIC -> one chain of 3 PRs."""
    merged = [pr(23001, 16334), pr(23002, 16334, prev=23001),
              pr(23003, 16334, prev=23002)]
    assert chains(merged) == [{
        "vein_key": 16334,
        "count": 3,
        "numbers": [23001, 23002, 23003],
        "includes_candidate": False,
    }]


def test_candidate_extends_chain_in_place():
    """The OPEN candidate (not merged) is the third link: the signal fires on
    the PR that extends the walk, not a day later on the next merged grain."""
    merged = [pr(23001, 16334), pr(23002, 16334, prev=23001)]
    candidate = pr(23010, 16334, prev=23002)
    out = vlc.prev_chain_runs(merged, LANE, candidate=candidate)
    assert out == [{
        "vein_key": 16334,
        "count": 3,
        "numbers": [23001, 23002, 23010],
        "includes_candidate": True,
    }]


def test_candidate_of_another_lane_ignored():
    """A candidate whose tag declares another lane is not this organ's grain."""
    merged = [pr(23001, 16334), pr(23002, 16334, prev=23001)]
    candidate = pr(23010, 16334, prev=23002, lane="myia-po-2024:CoursIA")
    assert chains(merged, candidate=candidate) == []


def test_two_links_exactly_at_cap():
    """chain_cap=2 means >= 2 links: two links (3 PRs) trip, one does not."""
    one_link = [pr(23001, 16334), pr(23002, 16334, prev=23001)]
    assert chains(one_link) == []
    three_links = one_link + [pr(23003, 16334, prev=23002),
                              pr(23004, 16334, prev=23003)]
    assert chains(three_links)[0]["count"] == 4


# --- negatives: each silence paired with the mutation that fires it ---------

def test_fresh_draw_breaks_chain():
    """A PR without `prev:` is a belt draw -- the very gesture the correctif
    wants. Mutation: adding the missing link re-forms the chain."""
    merged = [pr(23001, 16334), pr(23002, 16334, prev=23001),
              pr(23003, 16334),  # fresh draw: chain broken
              pr(23004, 16334, prev=23003)]
    assert chains(merged) == []
    # Mutation: chain the draw back onto its predecessor -> 4-grain walk.
    chained = [pr(23001, 16334), pr(23002, 16334, prev=23001),
               pr(23003, 16334, prev=23002), pr(23004, 16334, prev=23003)]
    assert chains(chained)[0]["count"] == 4


def test_rotation_between_epics_breaks_chain():
    """`prev:` citing a PR of a DIFFERENT issue is legitimate variety, not a
    walk. Mutation: point the rotation PR back at the same EPIC -> chain."""
    merged = [pr(23001, 16334), pr(23002, 16334, prev=23001),
              pr(23003, 20403, prev=23002)]  # rotates to another EPIC
    assert chains(merged) == []
    back = [pr(23001, 16334), pr(23002, 16334, prev=23001),
            pr(23003, 16334, prev=23002)]
    assert chains(back)[0]["count"] == 3


def test_uncited_previous_breaks_chain():
    """The cited PR carries no readable issue citation: unknown is not chained.
    The ONLY chain the set can form passes through it. Mutation: give it the
    same citation -> chain. (The first draft of this fixture put the seed
    OUTSIDE the would-be chain — 23002->23001->(absent 23000) leaves the
    two-link chain 23001..23003 intact, so the silence passed for the wrong
    reason and the mutation fired on a chain that never touched the seed.)"""
    uncited = {"number": 23000,
               "body": f"Grain: MED/tooling -- lane {LANE}\n",
               "labels": []}
    merged = [uncited, pr(23001, 16334, prev=23000),
              pr(23002, 16334, prev=23001)]
    assert chains(merged) == []
    # Mutation: the seed now cites 16334 -> the link becomes real, 3-chain.
    seeded = [pr(23000, 16334), pr(23001, 16334, prev=23000),
              pr(23002, 16334, prev=23001)]
    assert chains(seeded)[0]["count"] == 3


def test_prev_outside_loaded_set_breaks_chain():
    """A `prev:` whose number is not in the set is unknown, not chained (the
    link may cross a day/page boundary). The ONLY chain the set can form is
    23003->23004, one link — under the cap. Mutation: include the cited PR."""
    merged = [pr(23003, 16334, prev=22001), pr(23004, 16334, prev=23003)]
    assert chains(merged) == []
    with_seed = [pr(22001, 16334), pr(23003, 16334, prev=22001),
                 pr(23004, 16334, prev=23003)]
    assert chains(with_seed)[0]["count"] == 3


def test_prev_of_another_lane_breaks_chain():
    """A cross-lane `prev:` is the #13383 witness, a DIFFERENT defect: it must
    not fabricate a chain for this lane."""
    merged = [pr(23001, 16334, lane="myia-po-2024:CoursIA"),
              pr(23002, 16334, prev=23001),
              pr(23003, 16334, prev=23002)]
    assert chains(merged) == []


def test_self_citation_is_not_a_link():
    """A tag citing itself is a typo (#13383's own silence), not adjacency."""
    self_cite = {"number": 23001,
                 "body": f"Grain: MED/tooling -- lane {LANE} -- prev: #23001\n"
                         "\nTranche de #16334.",
                 "labels": []}
    merged = [pr(23000, 16334), self_cite, pr(23002, 16334, prev=23001)]
    assert chains(merged) == []


def test_two_chains_reported_separately():
    """Two independent walks on two EPICs each report their own chain."""
    merged = [pr(23001, 16334), pr(23002, 16334, prev=23001),
              pr(23003, 16334, prev=23002),
              pr(23011, 20403), pr(23012, 20403, prev=23011),
              pr(23013, 20403, prev=23012)]
    out = chains(merged)
    assert [c["vein_key"] for c in out] == [16334, 20403]
    assert all(c["count"] == 3 for c in out)


# --- compute_signals wiring --------------------------------------------------

def test_compute_signals_exposes_prev_chain_run():
    merged = [pr(23001, 16334), pr(23002, 16334, prev=23001),
              pr(23003, 16334, prev=23002)]
    sig = vlc.compute_signals(merged, LANE, files_by_pr={})
    assert sig["signals"]["PREV-CHAIN-RUN"] is True
    assert sig["prev_chain_runs"][0]["vein_key"] == 16334


def test_compute_signals_quiet_on_two_independent_draws():
    """The defect the correctif targets is the WALK: two independent draws on
    the same EPIC stay a vein (that axis' business), never a chain."""
    merged = [pr(23001, 16334), pr(23002, 16334)]
    sig = vlc.compute_signals(merged, LANE, files_by_pr={})
    assert sig["signals"]["PREV-CHAIN-RUN"] is False
    assert sig["prev_chain_runs"] == []


def test_check_pr_branch_carries_chain_fields():
    """--check-pr JSON: the chain rides on the candidate, so a non-LIGHT
    candidate that extends a walk still surfaces prev_chain_exceeded."""
    merged = [pr(23001, 16334), pr(23002, 16334, prev=23001)]
    candidate = pr(23010, 16334, prev=23002, genre="lean")  # DEEP candidate
    body = candidate["body"].replace("MED/lean", "DEEP/lean")
    import json
    import tempfile
    with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False,
                                     encoding="utf-8") as fh:
        json.dump(merged, fh)
        replay = fh.name
    rc = vlc.main(["--replay", replay, "--check-pr", "23010",
                   "--body", body, "--no-fetch-files"])
    assert rc == 0
