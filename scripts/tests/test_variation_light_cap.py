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


# --- re-qualification (#8970) ----------------------------------------------
# Declared LIGHT, coordinator re-qualified MED at merge. The label is the final
# word on the tier; the declared tag stays in the body (author intent preserved).
LABEL_REQUAL_MED = [{"name": "grain-requalified:MED"}]
LABEL_REQUAL_LIGHT = [{"name": "grain-requalified:LIGHT"}]


def test_effective_grain_label_overrides_tier():
    g = vlc.effective_grain({"body": BODY_EMDASH, "labels": LABEL_REQUAL_MED})
    assert g["tier"] == "MED"
    assert g["declared_tier"] == "LIGHT"
    assert g["lane"] == "myia-po-2023:CoursIA"


def test_effective_grain_no_label_keeps_declared():
    g = vlc.effective_grain({"body": BODY_EMDASH})
    assert g["tier"] == "LIGHT"
    assert g["declared_tier"] == "LIGHT"


def test_label_names_accepts_strings_and_dicts():
    # gh yields [{"name": ...}]; synthetic data may carry bare strings.
    assert vlc._label_names({"labels": [{"name": "a"}, {"name": "b"}]}) == ["a", "b"]
    assert vlc._label_names({"labels": ["a", "b"]}) == ["a", "b"]
    assert vlc._label_names({}) == []


def test_requalified_tier_case_insensitive():
    assert vlc._requalified_tier(["grain-requalified:med"]) == "MED"
    assert vlc._requalified_tier(["other", "grain-requalified:LIGHT"]) == "LIGHT"
    assert vlc._requalified_tier([]) is None
    # An unrelated label must not be misread as a re-qualification.
    assert vlc._requalified_tier(["variation-light-cap-reached"]) is None


def test_requalified_med_does_not_spend_budget():
    # #8970: a prior merged declared-LIGHT re-qualified MED is NOT a LIGHT, so it
    # did not spend the budget -> a new LIGHT of the lane is NOT cap-reached.
    prs = [
        {"number": 8930, "body": BODY_EMDASH, "mergedAt": "2026-07-30T10:00:00Z",
         "labels": LABEL_REQUAL_MED},
    ]
    status = vlc.light_cap_status(prs, "myia-po-2023:CoursIA")
    assert status["cap_reached"] is False
    assert status["consumed_by"] is None


def test_requalified_med_spared_in_replay():
    # #8970 acceptance: #8930 (declared LIGHT, re-qualified MED) is effective MED
    # -> it is NOT in the LIGHT replay set, so it is neither flagged nor the
    # budget owner. #8951 is the real 1st (and only) effective LIGHT -> OK.
    prs = [
        {"number": 8930, "body": BODY_EMDASH, "mergedAt": "2026-07-30T10:00:00Z",
         "labels": LABEL_REQUAL_MED},
        {"number": 8951, "body": BODY_EMDASH, "mergedAt": "2026-07-30T13:32:00Z"},
    ]
    rows = vlc.replay(prs)
    assert [r["number"] for r in rows] == [8951]
    assert rows[0]["cap_reached"] is False


def test_no_regression_first_light_per_lane():
    # #8970 acceptance: #8913/#8909/#8910 (1st LIGHT of each lane) stay unflagged
    # beside a re-qualified PR; only #8951 (real 2nd po-2023 LIGHT) is flagged.
    prs = [
        {"number": 8910, "body": BODY_HYPHEN_BOLD, "mergedAt": "2026-07-30T02:54:00Z"},
        {"number": 8909, "body": BODY_EMDASH, "mergedAt": "2026-07-30T03:28:00Z"},
        {"number": 8913, "body": BODY_MIDDOT_BOLD_LANE, "mergedAt": "2026-07-30T03:47:00Z"},
        {"number": 8930, "body": BODY_EMDASH, "mergedAt": "2026-07-30T10:00:00Z",
         "labels": LABEL_REQUAL_MED},
        {"number": 8951, "body": BODY_EMDASH, "mergedAt": "2026-07-30T13:32:00Z"},
    ]
    rows = vlc.replay(prs)
    flagged = [r["number"] for r in rows if r["cap_reached"]]
    assert flagged == [8951]
    assert {r["number"] for r in rows if not r["cap_reached"]} == {8910, 8909, 8913}
    assert 8930 not in {r["number"] for r in rows}  # spared: effective MED


def test_downqualification_light_spends_budget():
    # Symmetric case (#8970): a declared DEEP down-qualified to LIGHT IS an
    # effective LIGHT -> it spends the budget. A later LIGHT is cap-reached.
    prs = [
        {"number": 700, "body": "Grain: DEEP/lean -- lane myia-po-2023:CoursIA",
         "mergedAt": "2026-07-30T08:00:00Z", "labels": LABEL_REQUAL_LIGHT},
    ]
    status = vlc.light_cap_status(prs, "myia-po-2023:CoursIA")
    assert status["cap_reached"] is True
    assert status["consumed_by"]["number"] == 700


def test_downqualification_light_replayed_and_flaggable():
    # A down-qualified LIGHT enters the replay set and can itself be flagged if
    # a same-lane effective LIGHT merged earlier. declared_tier is carried.
    prs = [
        {"number": 9, "body": BODY_EMDASH, "mergedAt": "2026-07-30T03:28:00Z"},
        {"number": 700, "body": "Grain: DEEP/lean -- lane myia-po-2023:CoursIA",
         "mergedAt": "2026-07-30T11:00:00Z", "labels": LABEL_REQUAL_LIGHT},
    ]
    rows = vlc.replay(prs)
    assert [r["number"] for r in rows] == [9, 700]
    flagged = [r for r in rows if r["cap_reached"]]
    assert [r["number"] for r in flagged] == [700]
    assert flagged[0]["consumed_by"] == 9
    assert rows[1]["declared_tier"] == "DEEP"
