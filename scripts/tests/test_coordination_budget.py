#!/usr/bin/env python3
"""Unit tests for coordination_budget.py (per-lane Grain budget overview, #9859).

Pins the aggregation, the budget/consumed arithmetic, the anomaly detection
(no tag, lane missing, G-VAR-3 adjacency, idle), and the `--replay` input path
with synthetic bodies. The live `--days` path is exercised in the PR body on
real PRs; these tests never call `gh`. Run: `python -m pytest
scripts/tests/test_coordination_budget.py`.
"""
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import coordination_budget as cb  # noqa: E402


def _pr(number, body, merged_at="2026-08-07T09:00:00Z", labels=None):
    """Build a synthetic merged-PR dict in the `gh --json` shape."""
    return {
        "number": number,
        "title": f"PR #{number}",
        "body": body,
        "mergedAt": merged_at,
        "labels": labels or [],
    }


# tag forms -- canonical, alias genre, lane missing, no tag
BODY_DEEP = "Grain: DEEP/lean -- lane myia-po-2026:CoursIA"
BODY_MED = "Grain: MED/tooling -- lane myia-po-2026:CoursIA"
BODY_LIGHT_TOOLING = "Grain: LIGHT/tooling -- lane myia-po-2026:CoursIA"
BODY_LIGHT_DOCS = "Grain: LIGHT/docs -- lane myia-po-2026:CoursIA"
BODY_ALIAS_GENRE = "Grain: LIGHT/lean-ci -- lane myia-po-2025:CoursIA"
BODY_NO_LANE = "Grain: MED/tooling -- no lane token here"
BODY_NO_TAG = "## Summary\n\njust a body with no grain tag"


# --- aggregation -----------------------------------------------------------


def test_aggregate_counts_by_effective_tier():
    prs = [
        _pr(1, BODY_DEEP),
        _pr(2, BODY_MED),
        _pr(3, BODY_LIGHT_TOOLING),
    ]
    rows = cb.aggregate(prs)
    row = rows["myia-po-2026:CoursIA"]
    assert row["DEEP"] == 1
    assert row["MED"] == 1
    assert row["LIGHT"] == 1
    assert row["total"] == 3


def test_aggregate_light_budget_ratio():
    # 6 grains -> budget max(1, 6//3) = 2
    prs = [_pr(i, BODY_MED) for i in range(1, 7)]
    rows = cb.aggregate(prs)
    assert rows["myia-po-2026:CoursIA"]["budget"] == 2


def test_aggregate_budget_floor_one_for_small_lane():
    # 1-2 grains -> floor of 1
    rows = cb.aggregate([_pr(1, BODY_DEEP)])
    assert rows["myia-po-2026:CoursIA"]["budget"] == 1


def test_aggregate_consumed_tracks_effective_tier():
    # a declared LIGHT re-qualified up to MED does NOT consume the budget (#8970)
    prs = [
        _pr(1, BODY_DEEP),
        _pr(2, BODY_LIGHT_TOOLING, labels=["grain-requalified:MED"]),
        _pr(3, BODY_LIGHT_DOCS),  # genuinely LIGHT -> consumes
    ]
    rows = cb.aggregate(prs)
    row = rows["myia-po-2026:CoursIA"]
    # effective tiers: DEEP, MED (requal), LIGHT -> LIGHT count = 1
    assert row["LIGHT"] == 1
    assert row["MED"] == 1
    assert row["consumed"] == 1


def test_aggregate_separates_lanes():
    prs = [
        _pr(1, BODY_DEEP),
        _pr(2, BODY_ALIAS_GENRE),  # myia-po-2025
    ]
    rows = cb.aggregate(prs)
    assert "myia-po-2026:CoursIA" in rows
    assert "myia-po-2025:CoursIA" in rows


def test_aggregate_skips_untagged_and_no_lane():
    prs = [
        _pr(1, BODY_NO_LANE),  # tag present, lane None
        _pr(2, BODY_NO_TAG),  # no tag
    ]
    rows = cb.aggregate(prs)
    assert rows == {}  # neither attributes to a lane


def test_aggregate_collects_genres():
    prs = [
        _pr(1, BODY_DEEP),  # lean
        _pr(2, BODY_MED),  # tooling
        _pr(3, BODY_ALIAS_GENRE.replace("lean-ci", "qc")),  # myia-po-2025 / qc
    ]
    rows = cb.aggregate(prs)
    assert rows["myia-po-2026:CoursIA"]["genres"] == {"lean", "tooling"}


# --- anomalies -------------------------------------------------------------


def test_anomaly_no_tag_reported():
    prs = [_pr(1, BODY_NO_TAG)]
    anom = cb.detect_anomalies(prs)
    assert len(anom) == 1
    assert "no Grain tag" in anom[0]
    assert "#1" in anom[0]


def test_anomaly_lane_missing_reported():
    prs = [_pr(7, BODY_NO_LANE)]
    anom = cb.detect_anomalies(prs)
    assert any("no lane" in a and "#7" in a for a in anom)


def test_anomaly_same_genre_light_adjacency():
    # two consecutive LIGHT/tooling in the same lane -> G-VAR-3 smell
    prs = [
        _pr(1, BODY_LIGHT_TOOLING, merged_at="2026-08-07T08:00:00Z"),
        _pr(2, BODY_LIGHT_TOOLING, merged_at="2026-08-07T09:00:00Z"),
    ]
    anom = cb.detect_anomalies(prs)
    assert any("G-VAR-3" in a and "tooling" in a for a in anom)


def test_anomaly_distinct_genres_no_adjacency():
    # LIGHT/tooling then LIGHT/docs -> distinct genres, no smell
    prs = [
        _pr(1, BODY_LIGHT_TOOLING, merged_at="2026-08-07T08:00:00Z"),
        _pr(2, BODY_LIGHT_DOCS, merged_at="2026-08-07T09:00:00Z"),
    ]
    anom = cb.detect_anomalies(prs)
    assert not any("G-VAR-3" in a for a in anom)


def test_anomaly_idle_lane_only_with_known_list():
    prs = [_pr(1, BODY_DEEP)]  # only po-2026 produced
    # without a known-lanes list: no idle report (cannot know the canon)
    assert not any("idle" in a for a in cb.detect_anomalies(prs))
    # with a known list including an absent lane: idle reported
    anom = cb.detect_anomalies(
        prs, known_lanes=["myia-po-2026:CoursIA", "myia-po-2024:CoursIA"]
    )
    assert any("idle" in a and "po-2024" in a for a in anom)


def test_no_anomaly_on_clean_window():
    prs = [
        _pr(1, BODY_DEEP),
        _pr(2, BODY_MED),
    ]
    assert cb.detect_anomalies(prs) == []


# --- replay input ----------------------------------------------------------


def test_load_prs_replay_reads_json_array(tmp_path):
    data = [_pr(1, BODY_DEEP), _pr(2, BODY_MED)]
    f = tmp_path / "prs.json"
    f.write_text(json.dumps(data), encoding="utf-8")
    loaded = cb.load_prs_replay(str(f))
    assert len(loaded) == 2
    assert loaded[0]["number"] == 1


def test_replay_end_to_end_via_main(tmp_path, capsys):
    # two lanes, one idle, one lane-missing -> table + anomalies render
    data = [
        _pr(1, BODY_DEEP, merged_at="2026-08-07T08:00:00Z"),
        _pr(2, BODY_MED, merged_at="2026-08-07T08:30:00Z"),
        _pr(3, BODY_NO_LANE),
        _pr(4, BODY_ALIAS_GENRE, merged_at="2026-08-07T09:00:00Z"),
    ]
    f = tmp_path / "prs.json"
    f.write_text(json.dumps(data), encoding="utf-8")
    rc = cb.main(["--replay", str(f)])
    out = capsys.readouterr().out
    assert rc == 0
    assert "Coordination budget" in out
    assert "myia-po-2026:CoursIA" in out
    assert "myia-po-2025:CoursIA" in out
    assert "no lane" in out  # anomaly surfaced
    # numbers are computed, not declared
    assert "| 2 | 1 | 0 |" in out  # po-2026: 1 DEEP + 1 MED, 0 LIGHT


def test_json_mode_emits_machine_readable(tmp_path, capsys):
    data = [_pr(1, BODY_DEEP)]
    f = tmp_path / "prs.json"
    f.write_text(json.dumps(data), encoding="utf-8")
    rc = cb.main(["--replay", str(f), "--json"])
    out = capsys.readouterr().out
    payload = json.loads(out)
    assert rc == 0
    assert "myia-po-2026:CoursIA" in payload["rows"]
    assert payload["rows"]["myia-po-2026:CoursIA"]["DEEP"] == 1
    assert "anomalies" in payload
