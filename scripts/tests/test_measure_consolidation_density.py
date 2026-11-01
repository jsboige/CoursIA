"""Controles de la mesure #16473 acceptance 4, sans reseau."""
from __future__ import annotations

import json
import sys
from datetime import datetime, timezone
from pathlib import Path

import pytest

UTC = timezone.utc

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from coordination.measure_consolidation_density import (
    compare,
    issue_refs,
    main,
    measure_window,
    render_markdown,
)

START = datetime(2026, 9, 10, tzinfo=UTC)
END = datetime(2026, 9, 17, tzinfo=UTC)


def pr(number, body, refs=(1,), merged="2026-09-12T00:00:00Z", labels=None):
    return {
        "number": number,
        "body": body,
        "mergedAt": merged,
        "labels": labels or [],
        "closingIssuesReferences": [
            {"id": f"I_{ref}", "number": ref} for ref in refs
        ],
    }


def issue(number, title="Backtest QC", body="Sharpe et CAGR"):
    return {"number": number, "title": title, "body": body}


def tag(tier="DEEP", genre="lean"):
    return f"Grain: {tier}/{genre} — lane myia-po-2028:CoursIA — prev: LIGHT/docs #1"


def measure(prs, issues=None):
    return measure_window(
        prs,
        {item["number"]: item for item in (issues or [issue(1)])},
        START,
        END,
    )


def test_only_linked_services_enter_density_and_content_partition():
    result = measure([
        pr(10, tag(), refs=(1,)),
        pr(11, tag("DEEP", "guard"), refs=(2,)),
        pr(12, tag("MED", "lean"), refs=(3,)),
        pr(13, tag(), refs=()),
    ], [issue(1), issue(2), issue(3)])
    assert result["services"] == 3
    assert result["deep_content"] == 1
    assert result["deep_content_density"] == pytest.approx(1 / 3)
    assert result["unlinked_prs"] == 1


def test_graphql_reference_shape_is_accepted():
    payload = {"closingIssuesReferences": {"nodes": [{"number": 42, "id": "I_42"}]}}
    assert issue_refs(payload) == [{"number": 42, "id": "I_42"}]


def test_duplicate_issue_is_one_service_at_earliest_merge():
    result = measure([
        pr(10, tag("LIGHT", "docs"), refs=(1,), merged="2026-09-13T00:00:00Z"),
        pr(11, tag(), refs=(1,), merged="2026-09-12T00:00:00Z"),
    ])
    assert result["services"] == 1
    assert result["duplicate_issue_links"] == 1
    assert result["prs_with_closing_link"] == 2
    assert result["unlinked_prs"] == 0
    assert result["deep_content"] == 1
    assert result["service_details"][0]["pr"] == 11


def test_requalified_deep_does_not_inflate_numerator():
    result = measure([
        pr(10, tag(), labels=[{"name": "grain-requalified:LIGHT"}]),
    ])
    assert result["services"] == 1
    assert result["deep_content"] == 0


def test_axes_bc_use_issue_not_pr_prose():
    lean_issue = issue(1, "Mutualiser les lakes Mathlib", "junctions NTFS")
    result = measure([
        pr(10, tag("DEEP", "lean"), refs=(1,)),
        pr(11, tag("DEEP", "lean"), refs=(2,)),
    ], [lean_issue, issue(2, "Backtest QC")])
    assert result["deep_content"] == 2
    assert result["deep_axis_bc"] == 1
    assert result["deep_axis_bc_examples"][0]["issue"] == 1


def test_boundary_is_start_inclusive_end_exclusive():
    result = measure([
        pr(10, tag(), refs=(1,), merged="2026-09-10T00:00:00Z"),
        pr(11, tag(), refs=(2,), merged="2026-09-17T00:00:00Z"),
    ], [issue(1), issue(2)])
    assert result["services"] == 1


def test_missing_issue_metadata_is_visible_not_guessed():
    result = measure_window([pr(10, tag(), refs=(99,))], {}, START, END)
    assert result["missing_issue_metadata"] == [99]
    assert result["deep_content"] == 1
    assert result["deep_axis_bc"] == 0


def test_compare_requires_nonempty_denominators():
    empty = measure([], [])
    full = measure([pr(10, tag())])
    assert compare(empty, full)["verdict"] == "INCONCLUSIVE"
    assert compare(full, empty)["deep_content_delta_points"] is None
    assert compare(full, full)["verdict"] == "NOT_INCREASED"


def test_increase_and_markdown_scope_warning():
    before = measure([pr(10, tag("LIGHT", "docs"))])
    after = measure([pr(11, tag())])
    report = compare(before, after)
    assert report["verdict"] == "INCREASE"
    assert report["deep_content_delta_points"] == pytest.approx(100)
    text = render_markdown(report)
    assert "100.0 %" in text
    assert "pas une causalite" in text
    assert "See/Part of" in text


def test_replay_and_outputs(tmp_path):
    replay = tmp_path / "fixture.json"
    replay.write_text(json.dumps({
        "before": [pr(10, tag("LIGHT", "docs"))],
        "after": [pr(11, tag(), merged="2026-09-20T00:00:00Z")],
        "issues": [issue(1)],
    }), encoding="utf-8")
    json_out = tmp_path / "result.json"
    assert main(["--replay", str(replay), "--json-out", str(json_out)]) == 0
    result = json.loads(json_out.read_text(encoding="utf-8"))
    assert result["verdict"] == "INCREASE"
    assert result["after"]["services"] == 1
