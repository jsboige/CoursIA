#!/usr/bin/env python3
"""Unit tests for variation_light_cap.py (G-VAR-2 cap detection, #8964).

Acceptance replay over a live `gh pr list` wave is pasted in the PR body; these
tests pin the PARSING and CAP LOGIC with synthetic cases so the organ does not
silently rot. Run: `python -m pytest scripts/tests/test_variation_light_cap.py`.
"""
import json
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



# --- ratio budget (G-VAR-2 2026-07-31): 1 LIGHT per 3 merged grains ---------

def _pr(n, lane, tier, at, labels=None):
    d = {"number": n, "body": f"Grain: {tier}/x -- lane {lane}", "mergedAt": at}
    if labels is not None:
        d["labels"] = labels
    return d


def test_light_budget_floor_is_one():
    # A low-output lane keeps EXACTLY the old ceiling -- the floor is what
    # makes the ratio a strict relaxation: no lane is worse off than before.
    assert vlc.light_budget(0) == 1
    assert vlc.light_budget(1) == 1
    assert vlc.light_budget(5) == 1


def test_light_budget_grows_per_slice_of_three():
    assert vlc.light_budget(6) == 2
    assert vlc.light_budget(9) == 3
    assert vlc.light_budget(20) == 6  # the 19-merge day + the open candidate


def test_high_output_lane_is_not_capped_at_one():
    # The motivating case: 9 grains merged (7 DEEP + 2 LIGHT). Under the old
    # absolute cap the 2nd LIGHT was flagged; the lane is the OPPOSITE of
    # monoculture, so it must not be.
    lane = "myia-po-2024:CoursIA-2"
    prs = [_pr(i, lane, "DEEP", f"2026-07-31T0{i}:00:00Z") for i in range(1, 8)]
    prs += [_pr(8, lane, "LIGHT", "2026-07-31T08:00:00Z"),
            _pr(9, lane, "LIGHT", "2026-07-31T09:00:00Z")]
    rows = vlc.replay(prs)
    assert {r["number"] for r in rows if r["cap_reached"]} == set()
    assert all(r["budget"] == 3 for r in rows)  # 9 grains // 3


def test_high_output_lane_still_capped_past_budget():
    # The ratio relaxes, it does not disarm: a 4th LIGHT on a 9-grain lane
    # (budget 3) IS flagged. A lane still cannot be majority-LIGHT.
    lane = "myia-po-2024:CoursIA-2"
    prs = [_pr(i, lane, "DEEP", f"2026-07-31T0{i}:00:00Z") for i in range(1, 6)]
    prs += [_pr(6, lane, "LIGHT", "2026-07-31T06:00:00Z"),
            _pr(7, lane, "LIGHT", "2026-07-31T07:00:00Z"),
            _pr(8, lane, "LIGHT", "2026-07-31T08:00:00Z"),
            _pr(9, lane, "LIGHT", "2026-07-31T09:00:00Z")]
    rows = vlc.replay(prs)
    assert {r["number"] for r in rows if r["cap_reached"]} == {9}


# --- labels-file loading (#9971): gh pr view object form vs bare arrays -----

def test_load_labels_file_object_form_gh_pr_view(tmp_path):
    # `gh pr view --json labels` returns the OBJECT {"labels":[{name,...}]}.
    # This is the shape the CI workflow actually writes; the double-wrap bug
    # silently dropped every label, so a requalification was invisible.
    p = tmp_path / "labels.json"
    p.write_text(
        '{"labels": [{"name": "grain-requalified:LIGHT", "color": "fff"}]}',
        encoding="utf-8",
    )
    assert vlc.load_labels_file(p) == ["grain-requalified:LIGHT"]


def test_load_labels_file_bare_array_of_objects(tmp_path):
    # A bare [{name,...}] array -- the shape the old false comment assumed.
    p = tmp_path / "labels.json"
    p.write_text('[{"name": "a"}, {"name": "b"}]', encoding="utf-8")
    assert vlc.load_labels_file(p) == ["a", "b"]


def test_load_labels_file_bare_strings(tmp_path):
    # A bare ["str"] array (a hand-written file).
    p = tmp_path / "labels.json"
    p.write_text('["a", "b"]', encoding="utf-8")
    assert vlc.load_labels_file(p) == ["a", "b"]


def test_load_labels_file_missing_empty_invalid(tmp_path):
    # Missing / empty / invalid-JSON file -> no labels, no crash. The CI
    # workflow always writes valid JSON, but a manual invocation must not fail.
    assert vlc.load_labels_file(tmp_path / "absent.json") == []
    empty = tmp_path / "empty.json"
    empty.write_text("", encoding="utf-8")
    assert vlc.load_labels_file(empty) == []
    bad = tmp_path / "bad.json"
    bad.write_text("{not json", encoding="utf-8")
    assert vlc.load_labels_file(bad) == []


def test_check_pr_labels_file_object_downqualifies_to_light(tmp_path, capsys):
    # Regression for #9971: body declares MED, the CI labels-file is in the
    # OBJECT form `gh pr view` produces and carries grain-requalified:LIGHT.
    # The effective tier must be LIGHT, so the verdict carries lane/budget/spent
    # -- NOT the "reason: not LIGHT (effective MED)" verdict the double-wrap bug
    # produced. Fails on the pre-fix code: the output had no "lane" key.
    lpath = tmp_path / "pr_labels.json"
    lpath.write_text(
        json.dumps({"labels": [{"name": "grain-requalified:LIGHT"}]}),
        encoding="utf-8",
    )
    bpath = tmp_path / "pr_body.txt"
    bpath.write_text(
        "Grain: MED/tooling -- lane myia-po-2023:CoursIA-2\n\nbody",
        encoding="utf-8",
    )
    rpath = tmp_path / "merged.json"
    rpath.write_text("[]", encoding="utf-8")  # no prior merged LIGHT in this lane
    rc = vlc.main([
        "--replay", str(rpath), "--check-pr", "1234",
        "--body-file", str(bpath), "--labels-file", str(lpath),
    ])
    out = json.loads(capsys.readouterr().out)
    assert rc == 0
    # Pre-fix verdict was {"cap_reached": false, "reason": "not LIGHT ..."} with
    # NO "lane" key -> this assertion is what fails before the fix.
    assert out["lane"] == "myia-po-2023:CoursIA-2"
    assert out["cap_reached"] is False  # 1st LIGHT of the lane, within budget


def test_check_pr_requal_deep_exits_light_cap(tmp_path, capsys):
    # Symmetry (#8970): a grain-requalified:DEEP on a body declaring LIGHT
    # lifts it OUT of the LIGHT cap -- the override works both ways. The
    # object-form labels-file must carry that label (would be invisible pre-fix).
    lpath = tmp_path / "pr_labels.json"
    lpath.write_text(
        json.dumps({"labels": [{"name": "grain-requalified:DEEP"}]}),
        encoding="utf-8",
    )
    bpath = tmp_path / "pr_body.txt"
    bpath.write_text(
        "Grain: LIGHT/tooling -- lane myia-po-2023:CoursIA-2",
        encoding="utf-8",
    )
    rpath = tmp_path / "merged.json"
    rpath.write_text("[]", encoding="utf-8")
    rc = vlc.main([
        "--replay", str(rpath), "--check-pr", "1235",
        "--body-file", str(bpath), "--labels-file", str(lpath),
    ])
    out = json.loads(capsys.readouterr().out)
    assert rc == 0
    # Effective DEEP -> never spends the LIGHT budget.
    assert out["reason"].startswith("not LIGHT")
    assert "DEEP" in out["reason"]


def test_denominator_counts_all_tiers_not_just_lights():
    # DEEP/MED grains are what EARN the budget; counting only LIGHTs would
    # make the ratio self-referential (1 LIGHT always allows the next one).
    lane = "myia-po-2023:CoursIA"
    prs = [_pr(i, lane, "DEEP", f"2026-07-31T0{i}:00:00Z") for i in range(1, 7)]
    assert len(vlc.lane_grains(prs, lane)) == 6
    assert len(vlc.lane_lights(prs, lane)) == 0
    # 6 merged + 1 open candidate = 7 -> budget 2, nothing spent -> allowed
    st = vlc.light_cap_status(prs, lane)
    assert st["cap_reached"] is False and st["budget"] == 2 and st["spent"] == 0


def test_status_counts_the_open_candidate_in_denominator():
    # Conservative on purpose: the candidate is itself a grain of the day, so
    # a lane cannot front-load LIGHTs at 02:00 against unproduced throughput.
    lane = "myia-po-2023:CoursIA"
    prs = [_pr(1, lane, "LIGHT", "2026-07-31T02:00:00Z")]
    st = vlc.light_cap_status(prs, lane)
    assert st["lane_grains"] == 2       # 1 merged + the candidate
    assert st["budget"] == 1 and st["spent"] == 1
    assert st["cap_reached"] is True


# --- unassessable vs assessed (#9465): the organ must not report a
# --- measurement it could not take as a passing measurement.

def _check_pr(tmp_path, merged, body, labels=None, capsys=None):
    """Drive main() in --check-pr mode and return its parsed JSON line."""
    import json as _json
    mpath = tmp_path / "merged.json"
    mpath.write_text(_json.dumps(merged), encoding="utf-8")
    bpath = tmp_path / "body.txt"
    bpath.write_text(body, encoding="utf-8")
    argv = ["--replay", str(mpath), "--check-pr", "1", "--body-file", str(bpath)]
    if labels is not None:
        lpath = tmp_path / "labels.json"
        lpath.write_text(_json.dumps(labels), encoding="utf-8")
        argv += ["--labels-file", str(lpath)]
    rc = vlc.main(argv)
    out = capsys.readouterr().out.strip().splitlines()[-1]
    return rc, _json.loads(out)


def test_untagged_body_is_unassessable_not_false(tmp_path, capsys):
    # The defect that made the gate green while blind: an untagged body was
    # reported `cap_reached: false`, i.e. indistinguishable from "assessed and
    # within budget". It must be the third state.
    rc, res = _check_pr(tmp_path, [], "no tag anywhere in this body", capsys=capsys)
    assert rc == 0                       # advisory posture preserved
    assert res["cap_reached"] is None    # NOT False
    assert "unassessable" in res["reason"]


def test_light_without_lane_is_unassessable(tmp_path, capsys):
    # Tier known, but the budget is per-lane: no lane -> no denominator.
    rc, res = _check_pr(tmp_path, [], "Grain: LIGHT/guard -- no lane here", capsys=capsys)
    assert rc == 0
    assert res["cap_reached"] is None
    assert "no lane" in res["reason"]


def test_known_non_light_without_lane_is_assessed_false(tmp_path, capsys):
    # Symmetric guard against over-broadening: a KNOWN MED/DEEP never spends
    # the LIGHT budget, so it is a genuine `false` even with no lane. Only the
    # lane's denominator suffers, which is `unattributed`'s business.
    rc, res = _check_pr(tmp_path, [], "Grain: DEEP/lean -- no lane here", capsys=capsys)
    assert rc == 0
    assert res["cap_reached"] is False
    assert res["reason"] == "not LIGHT (effective DEEP)"


def test_tagged_light_still_assessed_normally(tmp_path, capsys):
    # Non-regression: a fully tagged LIGHT is still assessed, not deflected
    # into the new unassessable branch.
    merged = [{"number": 1, "body": BODY_EMDASH, "mergedAt": "2026-08-05T03:00:00Z"}]
    rc, res = _check_pr(tmp_path, merged, BODY_EMDASH, capsys=capsys)
    assert rc == 0
    assert res["cap_reached"] is True
    assert res["lane"] == "myia-po-2023:CoursIA"


def test_unattributed_lists_untagged_prs():
    prs = [
        {"number": 1, "body": BODY_EMDASH, "mergedAt": "2026-08-05T01:00:00Z"},
        {"number": 2, "body": "ledger stamp, no tag", "mergedAt": "2026-08-05T02:00:00Z"},
        {"number": 3, "body": "", "mergedAt": "2026-08-05T03:00:00Z"},
    ]
    assert [pr["number"] for pr in vlc.unattributed(prs)] == [2, 3]


def test_untagged_day_replays_empty_but_is_not_clean():
    # The c.85 measurement, pinned: 5 ledger stamps merged, zero tags. `replay`
    # is legitimately empty -- the arithmetic is right -- but `unattributed`
    # is what stops that emptiness reading as a clean day.
    prs = [{"number": n, "body": "metadata.cost stamp", "mergedAt": f"2026-08-05T0{n}:00:00Z"}
           for n in range(1, 6)]
    assert vlc.replay(prs) == []
    assert len(vlc.unattributed(prs)) == 5


def test_budget_is_per_lane_not_global():
    # A busy lane's budget must not bleed into a quiet lane's.
    busy, quiet = "myia-po-2024:CoursIA-2", "myia-po-2025:CoursIA"
    prs = [_pr(i, busy, "DEEP", f"2026-07-31T0{i}:00:00Z") for i in range(1, 7)]
    prs += [_pr(7, quiet, "LIGHT", "2026-07-31T07:00:00Z"),
            _pr(8, quiet, "LIGHT", "2026-07-31T08:00:00Z")]
    rows = vlc.replay(prs)
    assert {r["number"] for r in rows if r["cap_reached"]} == {8}  # quiet lane: budget 1


# --- G-VAR-2/3 by GENRE (#10020) --------------------------------------------
#
# The tier is an auto-declaration; the genre is the corroborable axis. Issue
# #10020 §Acceptance requires:
#   1. Replay the 16-grain po-2025:CoursIA-2 day set and signal GENRE-RUN on
#      the 5 readme consecutive (the cap is silent because 0 LIGHT declared).
#   2. >= 2 falsification tests: a lane with varied DEEP/MED genres raises no
#      signal, and a lane with a single LIGHT does not raise CAP-EXCEEDED.
#   3. The four signals are independent (a TIER-INFLATION can trip without
#      GENRE-RUN, and vice versa).
#   4. GENRE-MISMATCH corroboration from diff paths is opt-in via --files;
#      a missing input is not a false positive.
#   5. Aliases normalise (translation -> docs, lean-ci -> guard, etc.).

# Reference day set: po-2025:CoursIA-2 2026-08-08 (16 grains, 0 LIGHT declared,
# 5 readme consecutive, 2 docs, 1 guard via alias). The fixture mirrors the
# dataset verified firsthand via `gh pr list --search 'merged:2026-08-08'`
# on the issue acceptance lane.
_P_2025_C2 = "myia-po-2025:CoursIA-2"


def _tag_pr(n, tier, genre, lane=_P_2025_C2, at=None, labels=None):
    """Helper for #10020 fixtures: build a PR with a fuller Grain tag."""
    if at is None:
        at = f"2026-08-08T{n % 24:02d}:00:00Z"
    body = f"Grain: {tier}/{genre} -- lane {lane} -- prev: MED/x #{n - 1}"
    d = {"number": n, "body": body, "mergedAt": at}
    if labels is not None:
        d["labels"] = labels
    return d


# The 16-grain po-2025:CoursIA-2 2026-08-08 day set. Mirrors the actual
# merged PRs (see acceptance: issue #10020 §Le defaut, mesure). 5 readme
# consecutive (#9960, #9965, #9966, #9969, #9977) all declared MED; the
# TIER-axis is silent, the GENRE-axis must scream.
_PO2025_DAY = [
    _tag_pr(9960, "MED", "readme", at="2026-08-08T07:00:00Z"),
    _tag_pr(9965, "MED", "readme", at="2026-08-08T08:00:00Z"),
    _tag_pr(9966, "MED", "readme", at="2026-08-08T09:00:00Z"),
    _tag_pr(9969, "MED", "readme", at="2026-08-08T10:00:00Z"),
    _tag_pr(9977, "MED", "readme", at="2026-08-08T11:00:00Z"),
    _tag_pr(9985, "DEEP", "notebook-python", at="2026-08-08T12:00:00Z"),
    _tag_pr(9986, "MED", "docs", at="2026-08-08T13:00:00Z"),
    _tag_pr(9987, "MED", "translation", at="2026-08-08T14:00:00Z"),  # alias -> docs
    _tag_pr(9989, "MED", "refactor", at="2026-08-08T15:00:00Z"),
    _tag_pr(9993, "MED", "tooling", at="2026-08-08T16:00:00Z"),
    _tag_pr(9996, "MED", "tooling", at="2026-08-08T17:00:00Z"),
    _tag_pr(9999, "MED", "notebook-python", at="2026-08-08T18:00:00Z"),
    _tag_pr(10004, "MED", "secrets", at="2026-08-08T19:00:00Z"),
    _tag_pr(10008, "MED", "tooling", at="2026-08-08T20:00:00Z"),
    _tag_pr(10010, "MED", "lean-ci", at="2026-08-08T21:00:00Z"),  # alias -> guard
    _tag_pr(10016, "MED", "tooling", at="2026-08-08T22:00:00Z"),
]


def test_canonicalize_genre_aliases():
    # The exact aliases issue #10020 §1 names (and the observed po-2025 ones).
    assert vlc.canonicalize_genre("translation") == "docs"
    assert vlc.canonicalize_genre("docs-translation") == "docs"
    assert vlc.canonicalize_genre("lean-ci") == "guard"
    assert vlc.canonicalize_genre("cjk-ci") == "guard"
    assert vlc.canonicalize_genre("audit-tooling") == "tooling"
    assert vlc.canonicalize_genre("test-coverage") == "test"
    assert vlc.canonicalize_genre("data") == "ledger"
    # No alias -> identity.
    assert vlc.canonicalize_genre("readme") == "readme"
    assert vlc.canonicalize_genre("DOCS") == "DOCS".lower()  # case-insensitive
    # Empty/None -> None.
    assert vlc.canonicalize_genre(None) is None
    assert vlc.canonicalize_genre("") is None
    # Compound form not in the map -> the head is preserved (this is the
    # edge case where the family is genuinely informative; the alias map
    # covers the observed ones, anything else is left alone to be flagged
    # by the broader genre-offlist guard).
    assert vlc.canonicalize_genre("lean-tooling") == "tooling"


def test_light_genres_set_is_locked():
    # The G-VAR-3 lockout genres. Adding a genre here is a deliberate,
    # auditable change to the protocol, not a tunable.
    assert vlc.LIGHT_GENRES == frozenset({"docs", "readme", "guard", "ledger", "test"})


def test_effective_genre_aliases_via_body():
    # The full Pipeline: declared genre -> canonical via parse_grain_tag then
    # canonicalize_genre. Same extraction as the CI guard (shared via #9485).
    body = "Grain: MED/translation -- lane myia-po-2025:CoursIA-2"
    assert vlc.effective_genre(body, []) == "docs"
    body = "Grain: MED/lean-ci -- lane myia-po-2025:CoursIA-2"
    assert vlc.effective_genre(body, []) == "guard"
    # No tag -> None (the smoke test for the unassessable case).
    assert vlc.effective_genre("", []) is None
    assert vlc.effective_genre("no tag", []) is None


def test_lane_genre_tally_po2025_day():
    # 16 grains, 5 readme + 2 docs (9986 + 9987 alias) + 4 tooling +
    # 2 notebook-python + 1 refactor + 1 secrets + 1 guard (10010 alias).
    # light_genre = 5 + 2 + 1 = 8, light_declared = 0, cap = max(1, 16//3) = 5.
    tally = vlc.lane_genre_tally(_PO2025_DAY, _P_2025_C2)
    assert tally["lane_grains"] == 16
    assert tally["light_declared"] == 0
    assert tally["light_genre"] == 8
    assert tally["cap"] == 5
    # The by_genre histogram: readme=5, tooling=4, notebook-python=2,
    # docs=2 (canonical, including 9987 translation), refactor=1, secrets=1,
    # guard=1 (canonical, from 10010 lean-ci).
    assert tally["by_genre"]["readme"] == 5
    assert tally["by_genre"]["tooling"] == 4
    assert tally["by_genre"]["docs"] == 2
    assert tally["by_genre"]["guard"] == 1
    assert tally["by_genre"]["notebook-python"] == 2


def test_genre_runs_po2025_signals_genre_run():
    # The acceptance case: 5 readme consecutive (#9960 -> #9977) AND
    # 2 docs consecutive (#9986, #9987 -- the second via the
    # `translation` -> `docs` alias). The alias normalisation is what
    # made the second run INVISIBLE to the human eye on the day
    # (the alert only mentioned the readme streak); the detector finds
    # BOTH, which is the whole point of the organ -- the human missed
    # the alias-normalised adjacency, the detector cannot.
    runs = vlc.genre_runs(_PO2025_DAY, _P_2025_C2)
    long_runs = [r for r in runs if r["count"] >= 2]
    by_genre = {r["genre"]: r for r in long_runs}
    assert "readme" in by_genre
    assert by_genre["readme"]["count"] == 5
    assert by_genre["readme"]["numbers"] == [9960, 9965, 9966, 9969, 9977]
    assert "docs" in by_genre
    assert by_genre["docs"]["count"] == 2
    assert by_genre["docs"]["numbers"] == [9986, 9987]
    # Total runs (incl. singles): readme (5) + docs (1: 9986) + docs (1: 9987)
    # + refactor skipped + guard (1: 10010). The detector counts a stretch
    # as a single run; the 9986 -> 9987 pair is a single run of length 2.
    assert len(long_runs) == 2


def test_compute_signals_po2025_inflation_and_cap_exceeded():
    # The full panel of signals for the issue's reference case.
    sig = vlc.compute_signals(_PO2025_DAY, _P_2025_C2)
    # light_genre=8 > light_declared=0 + 1 = 1 -> TIER-INFLATION
    assert sig["signals"]["TIER-INFLATION"] is True
    # 5 readme consecutive -> GENRE-RUN
    assert sig["signals"]["GENRE-RUN"] is True
    # light_genre=8 > cap=5 -> CAP-EXCEEDED-BY-GENRE
    assert sig["signals"]["CAP-EXCEEDED-BY-GENRE"] is True
    # No candidate files provided -> GENRE-MISMATCH inactive.
    assert sig["signals"]["GENRE-MISMATCH"] is False
    assert sig["inferred_genre_from_paths"] is None


# --- FALSIFICATION TESTS (issue #10020 §Acceptance, #10016 model) ---------
#
# The detector must stay SILENT in non-monoculture cases. Two cases are
# pinned: (a) varied DEEP/MED genres, (b) a single LIGHT grain (within the
# floor budget).

def test_signal_silence_on_varied_deep_med_lane():
    # 9 grains of varied tiers/genres -- the OPPOSITE of monoculture. No
    # signal should fire. This is the far-from-the-bound case the detector
    # could over-shoot (always emitting TIER-INFLATION whenever any
    # discrepancy exists); it must not.
    lane = "myia-po-2024:CoursIA-2"
    prs = [
        _tag_pr(1, "DEEP", "lean", lane=lane, at="2026-08-08T01:00:00Z"),
        _tag_pr(2, "DEEP", "qc", lane=lane, at="2026-08-08T02:00:00Z"),
        _tag_pr(3, "MED", "notebook-python", lane=lane, at="2026-08-08T03:00:00Z"),
        _tag_pr(4, "MED", "refactor", lane=lane, at="2026-08-08T04:00:00Z"),
        _tag_pr(5, "DEEP", "training", lane=lane, at="2026-08-08T05:00:00Z"),
        _tag_pr(6, "MED", "tooling", lane=lane, at="2026-08-08T06:00:00Z"),
        _tag_pr(7, "DEEP", "genai", lane=lane, at="2026-08-08T07:00:00Z"),
        _tag_pr(8, "MED", "tooling", lane=lane, at="2026-08-08T08:00:00Z"),
        _tag_pr(9, "DEEP", "notebook-dotnet", lane=lane, at="2026-08-08T09:00:00Z"),
    ]
    sig = vlc.compute_signals(prs, lane)
    assert sig["signals"]["TIER-INFLATION"] is False
    assert sig["signals"]["GENRE-RUN"] is False
    assert sig["signals"]["CAP-EXCEEDED-BY-GENRE"] is False
    assert sig["tally"]["light_genre"] == 0  # no LIGHT-genre grains
    assert sig["tally"]["light_declared"] == 0


def test_signal_silence_on_single_light_lane():
    # 1 LIGHT grain (the floor budget): the cap is exactly 1, the budget is
    # NOT exceeded. GENRE-RUN needs >= 2 consecutive. TIER-INFLATION needs
    # > declared + 1 = at least 2 LIGHT-genre with 0 LIGHT-declared. The
    # detector is silent here -- the budget is permissive on purpose, the
    # single-grain case was never the problem.
    lane = "myia-po-2023:CoursIA"
    prs = [_tag_pr(1, "LIGHT", "guard", lane=lane, at="2026-08-08T01:00:00Z")]
    sig = vlc.compute_signals(prs, lane)
    assert sig["signals"]["TIER-INFLATION"] is False  # 1 == 0 + 1 (borderline)
    assert sig["signals"]["GENRE-RUN"] is False
    assert sig["signals"]["CAP-EXCEEDED-BY-GENRE"] is False
    assert sig["tally"]["light_genre"] == 1
    assert sig["tally"]["light_declared"] == 1
    assert sig["tally"]["cap"] == 1


def test_signal_tier_inflation_two_genre_light_no_light_declared():
    # The boundary case: 2 LIGHT-genre grains, 0 LIGHT-declared. The +1
    # tolerance absorbs a single mismatch (the 1 LIGHT-genre from a MED
    # declaration would not be inflation; this is the everyday case).
    # The 2nd mismatch is the line: TIER-INFLATION fires.
    lane = "myia-po-2023:CoursIA"
    prs = [
        _tag_pr(1, "MED", "readme", lane=lane, at="2026-08-08T01:00:00Z"),
        _tag_pr(2, "MED", "docs", lane=lane, at="2026-08-08T02:00:00Z"),
    ]
    sig = vlc.compute_signals(prs, lane)
    assert sig["signals"]["TIER-INFLATION"] is True
    # GENRE-RUN needs >= 2 consecutive SAME genre; readme+docs is not same.
    assert sig["signals"]["GENRE-RUN"] is False
    # 2 LIGHT-genre vs cap=1 -> CAP-EXCEEDED.
    assert sig["signals"]["CAP-EXCEEDED-BY-GENRE"] is True


def test_signal_genre_run_ignores_declared_tier():
    # Two readme consecutive, all DEEP declared. The G-VAR-3 ban by GENRE
    # must fire even though the lane never declared LIGHT (the exact
    # scenario the issue's defect described).
    lane = "myia-po-2023:CoursIA"
    prs = [
        _tag_pr(1, "DEEP", "readme", lane=lane, at="2026-08-08T01:00:00Z"),
        _tag_pr(2, "DEEP", "readme", lane=lane, at="2026-08-08T02:00:00Z"),
    ]
    sig = vlc.compute_signals(prs, lane)
    assert sig["signals"]["GENRE-RUN"] is True
    assert sig["signals"]["TIER-INFLATION"] is True  # 2 LIGHT-genre, 0 LIGHT-declared
    # The runs panel names the actual numbers.
    assert sig["long_runs"][0]["count"] == 2
    assert sig["long_runs"][0]["numbers"] == [1, 2]


def test_signal_genre_mismatch_from_paths(tmp_path, capsys):
    # A PR declared `tooling` whose diff is two README.md files (and
    # nothing else). GENRE-MISMATCH must fire: the inferred genre is
    # `readme`, the declared canonical genre is `tooling`.
    merged_obj = [
        {"number": 1, "body": "Grain: MED/tooling -- lane myia-po-2023:CoursIA",
         "mergedAt": "2026-08-08T01:00:00Z"},
    ]
    mpath = tmp_path / "merged.json"
    mpath.write_text(json.dumps(merged_obj), encoding="utf-8")
    bpath = tmp_path / "body.txt"
    bpath.write_text(
        "Grain: MED/tooling -- lane myia-po-2023:CoursIA", encoding="utf-8"
    )
    rc = vlc.main([
        "--replay", str(mpath), "--genre-signals",
        "--lane", "myia-po-2023:CoursIA",
        "--body-file", str(bpath),
        "--files", "README.md,docs/README.md",
    ])
    out = json.loads(capsys.readouterr().out.strip().splitlines()[-1])
    assert rc == 0
    assert out["signals"]["GENRE-MISMATCH"] is True
    assert out["inferred_genre_from_paths"] == "readme"
    assert out["candidate_genre_canonical"] == "tooling"


def test_signal_genre_mismatch_inactive_without_files(tmp_path, capsys):
    # GENRE-MISMATCH is OPT-IN: a --files argument is the only signal
    # provenance. A missing --files is INACTIVE (no claim), not a false
    # positive.
    merged_obj = [
        {"number": 1, "body": "Grain: MED/tooling -- lane myia-po-2023:CoursIA",
         "mergedAt": "2026-08-08T01:00:00Z"},
    ]
    mpath = tmp_path / "merged.json"
    mpath.write_text(json.dumps(merged_obj), encoding="utf-8")
    bpath = tmp_path / "body.txt"
    bpath.write_text(
        "Grain: MED/tooling -- lane myia-po-2023:CoursIA", encoding="utf-8"
    )
    rc = vlc.main([
        "--replay", str(mpath), "--genre-signals",
        "--lane", "myia-po-2023:CoursIA",
        "--body-file", str(bpath),
    ])
    out = json.loads(capsys.readouterr().out.strip().splitlines()[-1])
    assert rc == 0
    assert out["signals"]["GENRE-MISMATCH"] is False
    assert out["inferred_genre_from_paths"] is None


def test_signal_genre_mismatch_active_for_docs_paths(tmp_path, capsys):
    # Files under docs/ -> inferred `docs` (not `readme`). When the
    # declared canonical genre is also `docs`, no MISMATCH; `tooling`
    # declared against a docs-only diff MISMATCHES.
    merged_obj = [
        {"number": 1, "body": "Grain: MED/tooling -- lane myia-po-2023:CoursIA",
         "mergedAt": "2026-08-08T01:00:00Z"},
    ]
    mpath = tmp_path / "merged.json"
    mpath.write_text(json.dumps(merged_obj), encoding="utf-8")
    bpath = tmp_path / "body.txt"
    bpath.write_text(
        "Grain: MED/tooling -- lane myia-po-2023:CoursIA", encoding="utf-8"
    )
    rc = vlc.main([
        "--replay", str(mpath), "--genre-signals",
        "--lane", "myia-po-2023:CoursIA",
        "--body-file", str(bpath),
        "--files", "docs/reference/x.md,docs/reference/y.md",
    ])
    out = json.loads(capsys.readouterr().out.strip().splitlines()[-1])
    assert rc == 0
    assert out["signals"]["GENRE-MISMATCH"] is True
    assert out["inferred_genre_from_paths"] == "docs"


def test_genre_from_paths_mixed_non_md_is_none():
    # #10102 §Acceptance 1: a non-`*.md` path is an ABSENT signal
    # (input partially-decidable). Returning `tooling` would MISMATCH
    # every honest code-PR declaration (`lean`, `notebook-python`, ...),
    # inverting the rule. Empty list and `None` stay `None`.
    assert vlc._genre_from_paths(["README.md", "scripts/foo.py"]) is None
    assert vlc._genre_from_paths(["scripts/foo.py"]) is None
    assert vlc._genre_from_paths([]) is None
    assert vlc._genre_from_paths(None) is None


def test_genre_from_paths_claude_md_is_docs():
    # #10102 §Acceptance 2: `*.md` under `.claude/` (harness prose: rules
    # + skills) classifies as `docs`, not `readme`. Reproduces #10090,
    # which declared `docs` over `.claude/rules/*.md` and was wrongly
    # flagged MISMATCH by the prior heuristic.
    assert vlc._genre_from_paths([".claude/rules/x.md"]) == "docs"
    assert vlc._genre_from_paths(
        [".claude/rules/a.md", ".claude/skills/skill/SKILL.md"]
    ) == "docs"
    assert vlc._genre_from_paths([".claude/agents/foo.md"]) == "docs"


def test_genre_from_paths_docs_prefix_is_docs():
    # #10102 §Acceptance 1 + #10020 carryover: `docs/**/*.md` -> `docs`.
    assert vlc._genre_from_paths(["docs/reference/x.md"]) == "docs"
    assert vlc._genre_from_paths(
        ["docs/reference/x.md", "docs/genai/y.md"]
    ) == "docs"


def test_genre_from_paths_readme_is_readme():
    # #10102 §Acceptance: `README*.md` (and other `*.md` outside the
    # two namespaces) -> `readme` (catch-all preserves prior behaviour
    # for plain `*.md` files).
    assert vlc._genre_from_paths(["README.md"]) == "readme"
    assert vlc._genre_from_paths(["MyIA.AI.Notebooks/X/README.md"]) == "readme"
    assert vlc._genre_from_paths(["plain.md"]) == "readme"


def test_genre_from_paths_pr_10090_no_longer_mismatch(tmp_path, capsys):
    # #10102 §Acceptance 3: non-regression reproducing #10090.
    # 3 `*.md` (1 under `docs/`, 2 under `.claude/`), declared `docs`
    # -> inferred `docs` -> no MISMATCH. Prior heuristic flagged it.
    merged_obj = [
        {"number": 1, "body": "Grain: MED/docs -- lane myia-po-2023:CoursIA-2",
         "mergedAt": "2026-08-08T01:00:00Z"},
    ]
    mpath = tmp_path / "merged.json"
    mpath.write_text(json.dumps(merged_obj), encoding="utf-8")
    bpath = tmp_path / "body.txt"
    bpath.write_text(
        "Grain: MED/docs -- lane myia-po-2023:CoursIA-2", encoding="utf-8"
    )
    rc = vlc.main([
        "--replay", str(mpath), "--genre-signals",
        "--lane", "myia-po-2023:CoursIA-2",
        "--body-file", str(bpath),
        "--files",
        "docs/reference/x.md,.claude/rules/y.md,.claude/rules/z.md",
    ])
    out = json.loads(capsys.readouterr().out.strip().splitlines()[-1])
    assert rc == 0
    assert out["signals"]["GENRE-MISMATCH"] is False
    assert out["inferred_genre_from_paths"] == "docs"


def test_genre_from_paths_code_pr_no_mismatch_signal(tmp_path, capsys):
    # #10102 §Acceptance 1 + 4: a code PR (declared `tooling`) with a
    # non-md diff no longer emits GENRE-MISMATCH. Prior heuristic
    # flagged it (the bug).
    merged_obj = [
        {"number": 1, "body": "Grain: MED/tooling -- lane myia-po-2023:CoursIA-2",
         "mergedAt": "2026-08-08T01:00:00Z"},
    ]
    mpath = tmp_path / "merged.json"
    mpath.write_text(json.dumps(merged_obj), encoding="utf-8")
    bpath = tmp_path / "body.txt"
    bpath.write_text(
        "Grain: MED/tooling -- lane myia-po-2023:CoursIA-2", encoding="utf-8"
    )
    rc = vlc.main([
        "--replay", str(mpath), "--genre-signals",
        "--lane", "myia-po-2023:CoursIA-2",
        "--body-file", str(bpath),
        "--files", "scripts/variation_light_cap.py,scripts/foo.py",
    ])
    out = json.loads(capsys.readouterr().out.strip().splitlines()[-1])
    assert rc == 0
    assert out["signals"]["GENRE-MISMATCH"] is False
    assert out["inferred_genre_from_paths"] is None


def test_signal_genre_mismatch_inactive_when_no_body(tmp_path, capsys):
    # --genre-signals without a body can still emit TIER-INFLATION /
    # GENRE-RUN / CAP-EXCEEDED-BY-GENRE (those work on the merged set
    # alone), but GENRE-MISMATCH needs a candidate genre -> INACTIVE.
    merged_obj = [
        {"number": 1, "body": "Grain: MED/readme -- lane myia-po-2023:CoursIA",
         "mergedAt": "2026-08-08T01:00:00Z"},
        {"number": 2, "body": "Grain: MED/readme -- lane myia-po-2023:CoursIA",
         "mergedAt": "2026-08-08T02:00:00Z"},
    ]
    mpath = tmp_path / "merged.json"
    mpath.write_text(json.dumps(merged_obj), encoding="utf-8")
    rc = vlc.main([
        "--replay", str(mpath), "--genre-signals",
        "--lane", "myia-po-2023:CoursIA",
        "--files", "README.md",
    ])
    out = json.loads(capsys.readouterr().out.strip().splitlines()[-1])
    assert rc == 0
    assert out["signals"]["GENRE-RUN"] is True
    assert out["signals"]["GENRE-MISMATCH"] is False  # no candidate body
    assert out["candidate_genre_canonical"] is None


def test_genre_signals_requires_lane(tmp_path):
    # --genre-signals without --lane is a usage error -- the lane is the
    # denominator of every tally; without it the panel is undefined.
    import pytest as _pytest
    mpath = tmp_path / "merged.json"
    mpath.write_text("[]", encoding="utf-8")
    with _pytest.raises(SystemExit):
        vlc.main(["--replay", str(mpath), "--genre-signals"])


def test_genre_signals_exit_zero_always(tmp_path, capsys):
    # The advisory posture: exit 0 for ANY signal combination. The
    # coordinator reads the JSON; the consumer is merge-time, not
    # workflow-time. `tee | grep` would have eaten this; the JSON stays
    # intact.
    merged_obj = [
        {"number": 1, "body": "Grain: MED/readme -- lane myia-po-2023:CoursIA",
         "mergedAt": "2026-08-08T01:00:00Z"},
        {"number": 2, "body": "Grain: MED/readme -- lane myia-po-2023:CoursIA",
         "mergedAt": "2026-08-08T02:00:00Z"},
    ]
    mpath = tmp_path / "merged.json"
    mpath.write_text(json.dumps(merged_obj), encoding="utf-8")
    rc = vlc.main([
        "--replay", str(mpath), "--genre-signals",
        "--lane", "myia-po-2023:CoursIA",
    ])
    assert rc == 0


def test_po2025_replay_signals_genre_run_via_cli(tmp_path, capsys):
    # End-to-end acceptance against the CLI: the 16-grain day set
    # produces the four signals via the new --genre-signals mode. The
    # json output is parseable, exit 0, GENRE-RUN True.
    mpath = tmp_path / "merged.json"
    mpath.write_text(json.dumps(_PO2025_DAY), encoding="utf-8")
    rc = vlc.main([
        "--replay", str(mpath), "--genre-signals",
        "--lane", _P_2025_C2,
    ])
    out = json.loads(capsys.readouterr().out.strip().splitlines()[-1])
    assert rc == 0
    assert out["signals"]["GENRE-RUN"] is True
    assert out["signals"]["TIER-INFLATION"] is True
    assert out["signals"]["CAP-EXCEEDED-BY-GENRE"] is True
    # The long_run carries the 5 readme numbers from the issue acceptance.
    assert out["long_runs"][0]["count"] == 5
    assert out["long_runs"][0]["numbers"] == [9960, 9965, 9966, 9969, 9977]
