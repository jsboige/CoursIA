#!/usr/bin/env python3
"""Unit tests for variation_adjacency_guard.py -- the G-VAR-3 organ (#11170).

G-VAR-3 (variation-protocol.md §2) bans two consecutive grains of the same
LIGHT genre for a lane. The acceptance cases come straight from the issue:
#11136 (`LIGHT/docs -- prev: LIGHT/docs 11134`) was MERGED on the night of
2026-08-15/16 with no gate tripping, #11165 (`LIGHT/docs -- prev:
MED/notebook-python`) is the legitimately-different counter-example, and the
first-grain exemption (`prev: none (premier grain)`) must never be flagged.

Run:
    python -m pytest scripts/tests/test_variation_adjacency_guard.py
"""
import sys
from pathlib import Path

# Insert `scripts/` (for grain_tag + variation_light_cap) and `scripts/ci/`
# (for the script under test).
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import variation_adjacency_guard as vag  # noqa: E402

# The two night-of-2026-08-15/16 cases, verbatim tags from issue #11170.
CASE_11136 = "Grain: LIGHT/docs -- lane myia-po-2023:CoursIA -- prev: LIGHT/docs 11134"
CASE_11165 = "Grain: LIGHT/docs -- lane myia-po-2023:CoursIA -- prev: MED/notebook-python"


def test_11136_replay_blocks():
    # The merged-without-question case: same LIGHT genre twice -> BLOCK.
    v = vag.check(CASE_11136)
    assert v["guard_pass"] is False
    assert v["blocking"] is True
    assert v["adjacent"] is True
    assert v["genre"] == "docs"
    assert v["prev_genre"] == "docs"


def test_11165_replay_passes():
    # The legitimately-different case: docs then notebook-python -> PASS.
    v = vag.check(CASE_11165)
    assert v["guard_pass"] is True
    assert v["blocking"] is False
    assert v["adjacent"] is False


def test_blocking_reason_names_genres_and_lane():
    # The issue demands the error message cite BOTH genres and the lane, so
    # the failure is debuggable from the job log alone.
    v = vag.check(CASE_11136)
    assert "docs" in v["reason"]
    assert "myia-po-2023:CoursIA" in v["reason"]
    assert "UN AUTRE genre" in v["reason"]


def test_first_grain_exemption():
    # `prev: none (premier grain)` -> PASS, no predecessor to compare.
    v = vag.check(
        "Grain: LIGHT/docs -- lane myia-po-2023:CoursIA -- prev: none (premier grain)"
    )
    assert v["guard_pass"] is True
    assert v["adjacent"] is False


def test_prev_absent_is_not_reflagged():
    # A missing prev: is covered by the variation-tag-prev-absent label and
    # the tag-required job -- this organ must not double-flag it.
    v = vag.check("Grain: LIGHT/docs -- lane myia-po-2023:CoursIA")
    assert v["guard_pass"] is True
    assert v["adjacent"] is False


def test_no_tag_is_not_reflagged():
    # Missing Grain tag -> covered by check-variation-tag-required.
    v = vag.check("Some body with no Grain tag at all.")
    assert v["guard_pass"] is True
    assert v["adjacent"] is False


def test_different_genres_pass():
    v = vag.check(
        "Grain: MED/genai -- lane myia-po-2023:CoursIA -- prev: MED/guard #11200"
    )
    assert v["guard_pass"] is True
    assert v["adjacent"] is False


def test_deep_med_adjacency_is_advisory():
    # Same DEEP/MED domain-core genre twice: §2 allows it "si chacun est une
    # substance genument distincte" -- label, never block.
    v = vag.check(
        "Grain: DEEP/lean -- lane myia-po-2026:CoursIA -- prev: DEEP/lean #9999"
    )
    assert v["guard_pass"] is True
    assert v["blocking"] is False
    assert v["adjacent"] is True
    assert "advisory" in v["reason"]


def test_every_light_genre_blocks():
    # The full LIGHT set {guard, ledger, docs, readme, test} bans adjacency.
    for genre in ("guard", "ledger", "docs", "readme", "test"):
        v = vag.check(f"Grain: LIGHT/{genre} -- lane x:y -- prev: LIGHT/{genre} #1")
        assert v["guard_pass"] is False, f"{genre} adjacency must block"
        assert v["blocking"] is True


def test_aliases_normalised_before_comparison():
    # `docs-translation` folds to `docs` via the alias table: two grains of
    # the same work under invented labels must still trip the ban (§1).
    v = vag.check(
        "Grain: LIGHT/docs -- lane myia-po-2025:CoursIA-2 -- prev: LIGHT/docs-translation #100"
    )
    assert v["guard_pass"] is False
    assert v["prev_genre"] == "docs"


def test_tier_of_prev_does_not_matter():
    # The ban compares GENRES, not tiers: LIGHT/docs after MED/docs is the
    # same violation (the MED/readme defect case of #10020).
    v = vag.check(
        "Grain: LIGHT/docs -- lane myia-po-2023:CoursIA -- prev: MED/docs #200"
    )
    assert v["guard_pass"] is False
    assert v["blocking"] is True


def test_empty_inputs_pass():
    assert vag.check(None)["guard_pass"] is True
    assert vag.check("")["guard_pass"] is True
