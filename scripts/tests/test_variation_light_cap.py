#!/usr/bin/env python3
"""Unit tests for variation_light_cap.py (G-VAR-2 cap detection, #8964).

Acceptance replay over a live `gh pr list` wave is pasted in the PR body; these
tests pin the PARSING and CAP LOGIC with synthetic cases so the organ does not
silently rot. Run: `python -m pytest scripts/tests/test_variation_light_cap.py`.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import variation_light_cap as vlc  # noqa: E402

# The three body shapes observed in the wild (separator/case-agnostic, #8938).
BODY_EMDASH = "Grain: LIGHT/guard -- lane myia-po-2023:CoursIA\n\nbody"
BODY_HYPHEN_BOLD = "**Grain:** LIGHT/guard - lane myia-ai-01:CoursIA"
BODY_MIDDOT_BOLD_LANE = (
    "**Grain:** LIGHT/refs . **Lane:** myia-po-2024:CoursIA-2 . **See** #1206"
)


def test_parse_emdash_lowercase_lane():
    g = vlc.parse_grain(BODY_EMDASH)
    assert g == {"tier": "LIGHT", "lane": "myia-po-2023:CoursIA"}


def test_parse_hyphen_bold():
    g = vlc.parse_grain(BODY_HYPHEN_BOLD)
    assert g == {"tier": "LIGHT", "lane": "myia-ai-01:CoursIA"}


def test_parse_middot_bold_capital_lane():
    # bold + middot + capital **Lane:** + workspace with a hyphen (CoursIA-2)
    g = vlc.parse_grain(BODY_MIDDOT_BOLD_LANE)
    assert g == {"tier": "LIGHT", "lane": "myia-po-2024:CoursIA-2"}


def test_parse_no_grain_returns_none():
    assert vlc.parse_grain("no tag here") is None


def test_parse_empty_body():
    assert vlc.parse_grain("") is None
    assert vlc.parse_grain(None) is None  # type: ignore[arg-type]


def test_parse_non_light_tier():
    g = vlc.parse_grain("Grain: DEEP/lean -- lane myia-po-2023:CoursIA")
    assert g["tier"] == "DEEP"


def test_parse_grain_without_lane():
    # Tag present but lane missing -> tier read, lane None.
    g = vlc.parse_grain("Grain: LIGHT/guard -- no lane here")
    assert g == {"tier": "LIGHT", "lane": None}


def test_second_light_same_lane_is_cap_reached():
    # CI semantics: the current PR is NOT in the merged set. If the lane
    # already has one merged LIGHT, the current (2nd) is cap-reached.
    prs = [
        {"number": 1, "body": BODY_EMDASH, "mergedAt": "2026-07-30T03:00:00Z"},
    ]
    status = vlc.light_cap_status(prs, "myia-po-2023:CoursIA")
    assert status["cap_reached"] is True
    assert status["consumed_by"]["number"] == 1


def test_no_merged_light_not_cap_reached():
    # No prior merged LIGHT of this lane -> the current PR is the 1st -> OK.
    status = vlc.light_cap_status([], "myia-po-2023:CoursIA")
    assert status["cap_reached"] is False
    assert status["consumed_by"] is None


def test_other_lane_merged_does_not_reach_this_lane():
    # A LIGHT of a DIFFERENT lane already merged does not spend THIS lane's
    # budget (G-VAR-2 is per-lane).
    prs = [
        {"number": 1, "body": BODY_HYPHEN_BOLD, "mergedAt": "2026-07-30T03:00:00Z"},
    ]
    status_ai = vlc.light_cap_status(prs, "myia-ai-01:CoursIA")
    assert status_ai["cap_reached"] is True  # #1 ai-01 merged -> 2nd ai-01 reached
    status_po = vlc.light_cap_status(prs, "myia-po-2023:CoursIA")
    assert status_po["cap_reached"] is False  # 0 po-2023 merged -> 1st OK


def test_non_light_does_not_spend_budget():
    # A DEEP PR of the same lane must not consume the LIGHT budget.
    prs = [
        {"number": 1, "body": "Grain: DEEP/lean -- lane myia-po-2023:CoursIA",
         "mergedAt": "2026-07-30T03:00:00Z"},
    ]
    status = vlc.light_cap_status(prs, "myia-po-2023:CoursIA")
    assert status["cap_reached"] is False


def test_replay_flags_only_second_light_per_lane():
    prs = [
        {"number": 10, "body": BODY_HYPHEN_BOLD, "mergedAt": "2026-07-30T02:54:00Z"},
        {"number": 9, "body": BODY_EMDASH, "mergedAt": "2026-07-30T03:28:00Z"},
        {"number": 13, "body": BODY_MIDDOT_BOLD_LANE, "mergedAt": "2026-07-30T03:47:00Z"},
        {"number": 51, "body": BODY_EMDASH, "mergedAt": "2026-07-30T13:32:00Z"},
    ]
    rows = vlc.replay(prs)
    # #51 is the 2nd po-2023 LIGHT -> the only cap-reached entry.
    flagged = [r for r in rows if r["cap_reached"]]
    assert [r["number"] for r in flagged] == [51]
    assert flagged[0]["consumed_by"] == 9
    ok = {r["number"] for r in rows if not r["cap_reached"]}
    assert ok == {10, 9, 13}


def test_replay_empty():
    assert vlc.replay([]) == []


# --- requalification (#8970): coordinator override of the declared tag -----

# GitHub `--json labels` returns objects {name,...}; label_names must flatten
# BOTH that shape and a bare [str].
def test_label_names_flattens_objects_and_strings():
    assert vlc.label_names({"labels": [{"name": "a", "color": "fff"}, {"name": "b"}]}) == ["a", "b"]
    assert vlc.label_names({"labels": ["a", "b"]}) == ["a", "b"]
    assert vlc.label_names({}) == []
    assert vlc.label_names({"labels": None}) == []


def test_effective_tier_declared_when_no_requal_label():
    # No requalification label -> the declared tier stands.
    assert vlc.effective_tier(BODY_EMDASH, []) == "LIGHT"
    assert vlc.effective_tier("Grain: DEEP/lean -- lane x:y", ["bug"]) == "DEEP"


def test_effective_tier_requal_label_overrides_up():
    # Declared LIGHT, re-qualified MED -> effective MED (spares the budget).
    assert vlc.effective_tier(BODY_EMDASH, ["grain-requalified:MED"]) == "MED"


def test_effective_tier_requal_label_overrides_down():
    # Declared DEEP, re-qualified LIGHT -> effective LIGHT (consumes the budget).
    # This is the symmetric case #8970 requires a test for.
    assert vlc.effective_tier(
        "Grain: DEEP/lean -- lane x:y", ["grain-requalified:LIGHT"]
    ) == "LIGHT"


def test_effective_tier_requal_label_case_insensitive():
    assert vlc.effective_tier(BODY_EMDASH, ["Grain-Requalified:med"]) == "MED"


def test_up_qualification_spare_light_budget():
    # A declared LIGHT re-qualified up to MED does NOT spend the budget ->
    # a NEW LIGHT of the same lane is the 1st -> not cap-reached. (#8930 case.)
    prs_po2023 = [
        {"number": 30, "body": BODY_EMDASH,  # po-2023, declared LIGHT
         "labels": ["grain-requalified:MED"],
         "mergedAt": "2026-07-30T03:00:00Z"},
    ]
    status = vlc.light_cap_status(prs_po2023, "myia-po-2023:CoursIA")
    assert status["cap_reached"] is False  # the only LIGHT was re-qualified up


def test_up_qualification_unflags_in_replay():
    # #8930 acceptance case: declared LIGHT/tooling (po-2024), re-qualified MED,
    # must NOT be flagged in the replay. #8951 (no requal) stays flagged.
    prs = [
        {"number": 9, "body": BODY_EMDASH, "mergedAt": "2026-07-30T03:28:00Z"},
        {"number": 13, "body": BODY_MIDDOT_BOLD_LANE, "mergedAt": "2026-07-30T03:47:00Z"},
        {"number": 51, "body": BODY_EMDASH, "mergedAt": "2026-07-30T13:32:00Z"},
        {"number": 30, "body": BODY_MIDDOT_BOLD_LANE,  # po-2024, declared LIGHT
         "labels": ["grain-requalified:MED"],
         "mergedAt": "2026-07-30T16:03:00Z"},
    ]
    rows = vlc.replay(prs)
    flagged = {r["number"] for r in rows if r["cap_reached"]}
    assert 51 in flagged      # 2nd po-2023 LIGHT, no requal -> flagged
    assert 30 not in flagged  # re-qualified up to MED -> NOT a LIGHT -> unflagged
    assert 30 not in {r["number"] for r in rows}  # not even counted as a LIGHT


def test_down_qualification_feeds_counter_in():
    # Symmetric: a declared DEEP re-qualified DOWN to LIGHT DOES spend the
    # budget -> a later declared LIGHT of the same lane becomes the 2nd.
    prs = [
        {"number": 1, "body": "Grain: DEEP/lean -- lane myia-po-2023:CoursIA",
         "labels": ["grain-requalified:LIGHT"],
         "mergedAt": "2026-07-30T02:00:00Z"},
        {"number": 2, "body": BODY_EMDASH,  # declared LIGHT, same lane
         "mergedAt": "2026-07-30T10:00:00Z"},
    ]
    # #1 is now an effective LIGHT -> a NEW po-2023 LIGHT is cap-reached.
    status = vlc.light_cap_status(prs, "myia-po-2023:CoursIA")
    assert status["cap_reached"] is True
    assert status["consumed_by"]["number"] == 1  # the re-qualified-down PR


def test_replay_down_qualification_makes_later_light_cap_reached():
    prs = [
        {"number": 1, "body": "Grain: DEEP/lean -- lane myia-po-2023:CoursIA",
         "labels": ["grain-requalified:LIGHT"],
         "mergedAt": "2026-07-30T02:00:00Z"},
        {"number": 2, "body": BODY_EMDASH, "mergedAt": "2026-07-30T10:00:00Z"},
    ]
    rows = vlc.replay(prs)
    # both are now effective LIGHT of the same lane -> #2 is the 2nd -> flagged
    flagged = [r for r in rows if r["cap_reached"]]
    assert [r["number"] for r in flagged] == [2]
    assert flagged[0]["consumed_by"] == 1

