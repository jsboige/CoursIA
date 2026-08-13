#!/usr/bin/env python3
"""Unit tests for the pure classification core of candidate_delivered.py (#10466).

The ``classify`` and ``is_epic`` functions are network-free; ``main`` (the gh
wiring) is exercised end-to-end in CI dry-runs, not here. These fixtures encode
the verdicts measured firsthand on the #10466 sample:

  - #10403 : delivered by #10405/#10410, last comment before merge -> candidate
  - #1454  : EPIC ("[EPIC]" title) even though it has recent merges -> excluded
  - active : a comment lands AFTER the latest merge -> active (label retracted)
  - no_delivery : no merged PR references the issue -> no_delivery
  - label-EPIC : label "EPIC" (no "epic" in title) -> excluded
"""

import sys
import os

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from candidate_delivered import classify, is_epic, _parse_cross_ref_events  # noqa: E402


def _issue(title="x", labels=None, created_at="2026-08-01T00:00:00Z", comments=None):
    return {
        "title": title,
        "labels": labels or [],
        "created_at": created_at,
        "comments": [{"created_at": c} for c in (comments or [])],
    }


def test_candidate_delivered_silent_after_merge():
    # Mirrors #10403: claims at 02:56, delivery merges at 06:40, silence after.
    issue = _issue(title="5 guards 2-point diff", comments=["2026-08-11T02:56:16Z"])
    refs = [
        {"pr_number": 10405, "merged_at": "2026-08-11T04:25:17Z"},
        {"pr_number": 10410, "merged_at": "2026-08-11T06:40:37Z"},
    ]
    verdict, _ = classify(issue, refs)
    assert verdict == "candidate"


def test_epic_by_title_excluded_even_with_recent_merge():
    # Mirrors #1454: "[EPIC]" title, latest merge 2026-08-11T20:00 (after last
    # comment 08-10) -- the activity check alone would WRONGLY flag it. The
    # title exclusion must fire first.
    issue = _issue(title="[EPIC] Training & Post-Training", comments=["2026-08-10T09:04:34Z"])
    refs = [{"pr_number": 9999, "merged_at": "2026-08-11T20:00:20Z"}]
    verdict, _ = classify(issue, refs)
    assert verdict == "epic"


def test_epic_by_label_excluded():
    # #10355 / #4362 carry an "EPIC" label with no "epic" in the title.
    issue = _issue(title="fallacy detection via FT", labels=["EPIC", "enhancement"])
    refs = [{"pr_number": 1, "merged_at": "2026-08-11T10:00:00Z"}]
    verdict, _ = classify(issue, refs)
    assert verdict == "epic"


def test_active_when_comment_after_merge():
    # A worker re-engages the issue after delivery -> active, label retracted.
    issue = _issue(title="some defect", comments=["2026-08-11T12:00:00Z"])
    refs = [{"pr_number": 1, "merged_at": "2026-08-11T10:00:00Z"}]
    verdict, why = classify(issue, refs)
    assert verdict == "active"
    assert "active after merge" in why


def test_no_delivery_when_no_merged_ref():
    issue = _issue(title="fresh idea", comments=[])
    refs = [{"pr_number": 1, "merged_at": None}]  # open PR, not merged
    verdict, _ = classify(issue, refs)
    assert verdict == "no_delivery"


def test_candidate_when_comment_equals_merge_time():
    # Boundary: equal timestamps lean to candidate (strict > for active).
    issue = _issue(title="x", comments=["2026-08-11T10:00:00Z"])
    refs = [{"pr_number": 1, "merged_at": "2026-08-11T10:00:00Z"}]
    verdict, _ = classify(issue, refs)
    assert verdict == "candidate"


def test_candidate_uses_creation_when_no_comments():
    # No comments at all: issue created_at is the activity floor.
    issue = _issue(title="x", created_at="2026-08-01T00:00:00Z", comments=[])
    refs = [{"pr_number": 1, "merged_at": "2026-08-10T00:00:00Z"}]
    verdict, _ = classify(issue, refs)
    assert verdict == "candidate"


def test_is_epic_case_insensitive():
    assert is_epic("[EPIC] foo", [])
    assert is_epic("epic: bar", [])
    assert is_epic("x", ["Epic"])
    assert is_epic("x", ["enhancement", "epic-foo"])
    assert not is_epic("a defect", ["bug"])
    assert not is_epic("Epictetus notebook", [])  # substring inside a word -- accepted trade-off


def _xref_event(src_number, merged_at=None, is_pr=True):
    """Build one raw GitHub ``cross-referenced`` timeline event (shape from #10403)."""
    issue = {"number": src_number}
    if is_pr:
        issue["pull_request"] = ({"merged_at": merged_at} if merged_at else {})
    return {"event": "cross-referenced", "source": {"issue": issue}}


def test_parse_cross_ref_events_merged_prs_captured():
    # Mirrors #10403 timeline (measured firsthand): 5 cross-refs, 4 merged.
    events = [
        _xref_event(10397, is_pr=False),                       # an issue, not a PR
        _xref_event(10405, merged_at="2026-08-11T04:25:17Z"),  # merged PR
        _xref_event(10410, merged_at="2026-08-11T06:40:37Z"),  # merged PR
        _xref_event(10466),                                    # open PR, not merged
        _xref_event(10507, merged_at="2026-08-11T22:51:43Z"),  # merged PR
    ]
    refs = _parse_cross_ref_events(events)
    assert len(refs) == 5  # all cross-refs kept; classify filters by merged_at
    merged = [r for r in refs if r["merged_at"]]
    assert len(merged) == 3
    assert {r["pr_number"] for r in merged} == {10405, 10410, 10507}
    # The non-PR issue ref carries merged_at=None (classify ignores it).
    issue_ref = next(r for r in refs if r["pr_number"] == 10397)
    assert issue_ref["merged_at"] is None


def test_parse_cross_ref_events_feeds_classify_candidate():
    # End-to-end: the parsed refs drive classify() to the right verdict.
    events = [_xref_event(10410, merged_at="2026-08-11T06:40:37Z")]
    refs = _parse_cross_ref_events(events)
    issue = _issue(title="5 guards 2-point diff", comments=["2026-08-11T02:56:16Z"])
    verdict, _ = classify(issue, refs)
    assert verdict == "candidate"


def test_parse_cross_ref_events_empty_when_no_source_number():
    # Defensive: malformed event with no source.issue.number is dropped, not crashed.
    events = [{"event": "cross-referenced", "source": {"issue": {}}}]
    assert _parse_cross_ref_events(events) == []
    assert _parse_cross_ref_events(None) == []


if __name__ == "__main__":
    import pytest
    sys.exit(pytest.main([__file__, "-v"]))
