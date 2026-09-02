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

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from candidate_delivered import (  # noqa: E402
    classify,
    is_epic,
    human_retraction,
    _is_bot,
    _parse_cross_ref_events,
    _parse_label_events,
)


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
    # closed-unmerged PR = abandoned lane, no work in flight
    refs = [{"pr_number": 1, "merged_at": None, "is_pr": True, "state": "closed"}]
    verdict, _ = classify(issue, refs)
    assert verdict == "no_delivery"


def test_in_flight_when_open_pr_references_after_merges():
    # Mirrors #10984 (#11100): open PR #10986 references the issue BESIDES six
    # merged PRs -- a multi-phase rollout. Old heuristic: candidate (wrong).
    issue = _issue(title="rollout phase 7 of N", comments=["2026-08-10T09:00:00Z"])
    refs = [
        {"pr_number": 10995, "merged_at": "2026-08-14T23:18:16Z", "is_pr": True, "state": "closed"},
        {"pr_number": 10986, "merged_at": None, "is_pr": True, "state": "open"},
        {"pr_number": 11048, "merged_at": "2026-08-15T13:41:32Z", "is_pr": True, "state": "closed"},
    ]
    verdict, why = classify(issue, refs)
    assert verdict == "in_flight"
    assert "#10986" in why


def test_in_flight_even_without_any_merge():
    # Only an open PR (no merge yet): the issue is being worked on right now.
    issue = _issue(title="fresh idea", comments=[])
    refs = [{"pr_number": 1, "merged_at": None, "is_pr": True, "state": "open"}]
    verdict, _ = classify(issue, refs)
    assert verdict == "in_flight"


def test_open_issue_mention_is_not_in_flight():
    # A non-PR issue citing this one carries state "open" too -- must NOT
    # trigger in_flight (only PR refs count as work in flight).
    issue = _issue(title="x", comments=[])
    refs = [
        {"pr_number": 10397, "merged_at": None, "is_pr": False, "state": "open"},
        {"pr_number": 1, "merged_at": "2026-08-11T06:40:37Z", "is_pr": True, "state": "closed"},
    ]
    verdict, _ = classify(issue, refs)
    assert verdict == "candidate"


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


def _xref_event(src_number, merged_at=None, is_pr=True, state=None):
    """Build one raw GitHub ``cross-referenced`` timeline event (shape from #10403
    and #10984: source.issue carries `state`; `pull_request` present iff PR)."""
    issue = {"number": src_number, "state": state}
    if is_pr:
        issue["pull_request"] = ({"merged_at": merged_at} if merged_at else {})
    return {"event": "cross-referenced", "source": {"issue": issue}}


def test_parse_cross_ref_events_merged_prs_captured():
    # Mirrors #10403 timeline (measured firsthand): 5 cross-refs, 4 merged.
    events = [
        _xref_event(10397, is_pr=False, state="open"),                       # an issue, not a PR
        _xref_event(10405, merged_at="2026-08-11T04:25:17Z", state="closed"),  # merged PR
        _xref_event(10410, merged_at="2026-08-11T06:40:37Z", state="closed"),  # merged PR
        _xref_event(10466, state="open"),                                     # open PR, not merged
        _xref_event(10507, merged_at="2026-08-11T22:51:43Z", state="closed"),  # merged PR
    ]
    refs = _parse_cross_ref_events(events)
    assert len(refs) == 5  # all cross-refs kept; classify filters by merged_at
    merged = [r for r in refs if r["merged_at"]]
    assert len(merged) == 3
    assert {r["pr_number"] for r in merged} == {10405, 10410, 10507}
    # The non-PR issue ref carries merged_at=None (classify ignores it)...
    issue_ref = next(r for r in refs if r["pr_number"] == 10397)
    assert issue_ref["merged_at"] is None and issue_ref["is_pr"] is False
    # ...and an open PR ref is marked is_pr + state open (drives in_flight).
    open_ref = next(r for r in refs if r["pr_number"] == 10466)
    assert open_ref["is_pr"] is True and open_ref["state"] == "open"


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




# ---------------------------------------------------------------------------
# #14307 -- a human retraction is a verdict, and it sticks.
#
# These fixtures are written to be validated by their FALSE NEGATIVES, not by
# their hits: the two that matter are the ones a naive "was it ever unlabeled?"
# predicate gets wrong in silence -- a bot self-retraction (which must stay
# revisable) and a human who re-poses the label (which must hand control back).
# ---------------------------------------------------------------------------

def _lab(event, actor, created_at):
    return {"event": event, "actor": actor, "created_at": created_at}


# The shape measured on #10038 / #11601 / #10475: bot poses, human removes with
# a written verdict, a later merge cites the issue, bot poses again.
_BOT = "github-actions[bot]"
_DELIVERED_SILENT = [{"pr_number": 13939, "merged_at": "2026-09-02T08:51:58Z"}]


def test_human_retraction_sticks_over_a_later_merge():
    # Without the memory this is a textbook "candidate": merged PR, no comment
    # after it. #10038 went round this loop three times.
    issue = _issue(title="i18n notebooks : T4 renderer + CI autonome")
    events = [
        _lab("labeled", _BOT, "2026-08-30T06:01:00Z"),
        _lab("unlabeled", "jsboige", "2026-08-31T05:25:49Z"),
        _lab("labeled", _BOT, "2026-09-02T10:28:58Z"),
    ]
    verdict, why = classify(issue, _DELIVERED_SILENT, events)
    assert verdict == "retracted"
    assert "jsboige" in why and "2026-08-31" in why


def test_bot_self_retraction_does_not_stick():
    # FALSE NEGATIVE #1. The sweep retracts its own label when an issue becomes
    # active or in_flight (#11100). That is hysteresis, not a verdict: the next
    # run must be free to re-pose. Measured on #12100, #11985, #12389.
    issue = _issue(title="ordinary leaf issue")
    events = [
        _lab("labeled", _BOT, "2026-08-23T07:10:00Z"),
        _lab("unlabeled", _BOT, "2026-09-01T06:10:00Z"),
    ]
    assert classify(issue, _DELIVERED_SILENT, events)[0] == "candidate"


def test_human_relabel_hands_control_back():
    # FALSE NEGATIVE #2. The escape hatch: a human who re-poses the label by
    # hand makes their own `labeled` the latest human event, so the sweep
    # resumes normal service instead of being locked out forever.
    issue = _issue(title="ordinary leaf issue")
    events = [
        _lab("labeled", _BOT, "2026-08-13T06:10:00Z"),
        _lab("unlabeled", "jsboige", "2026-08-16T08:36:00Z"),
        _lab("labeled", "jsboige", "2026-08-20T09:00:00Z"),
    ]
    assert classify(issue, _DELIVERED_SILENT, events)[0] == "candidate"


def test_worker_login_counts_as_human():
    # Retractions come from lane logins too (#13107 was retracted by
    # myia-po-2023). Only a "...[bot]" suffix marks a non-verdict.
    issue = _issue(title="ordinary leaf issue")
    events = [_lab("unlabeled", "myia-po-2023", "2026-08-30T19:41:00Z")]
    assert classify(issue, _DELIVERED_SILENT, events)[0] == "retracted"


def test_no_label_events_is_unaffected():
    # Backward compatibility: the parameter defaults to None ("not consulted"),
    # and an empty history is not a retraction.
    issue = _issue(title="ordinary leaf issue")
    assert classify(issue, _DELIVERED_SILENT)[0] == "candidate"
    assert classify(issue, _DELIVERED_SILENT, [])[0] == "candidate"
    assert classify(issue, _DELIVERED_SILENT, None)[0] == "candidate"


def test_retraction_pre_empts_in_flight():
    # Precedence: a standing human verdict is not evidence about delivery, so
    # it is answered before the reference heuristics. Both paths yield "no
    # label", but the printed verdict must name the human decision.
    issue = _issue(title="ordinary leaf issue")
    refs = [{"pr_number": 999, "merged_at": None, "is_pr": True, "state": "open"}]
    events = [_lab("unlabeled", "jsboige", "2026-08-31T05:25:49Z")]
    assert classify(issue, refs, events)[0] == "retracted"


def test_epic_still_wins_over_retraction():
    # An EPIC is a structural exclusion, unaffected by label history.
    issue = _issue(title="[EPIC] rollout multi-phase")
    events = [_lab("unlabeled", "jsboige", "2026-08-31T05:25:49Z")]
    assert classify(issue, _DELIVERED_SILENT, events)[0] == "epic"


def test_unknown_actor_is_treated_as_human():
    # Fail towards preserving a verdict: an unreadable actor must not silently
    # downgrade a removal into revisable hysteresis.
    issue = _issue(title="ordinary leaf issue")
    events = [_lab("unlabeled", "", "2026-08-31T05:25:49Z")]
    assert classify(issue, _DELIVERED_SILENT, events)[0] == "retracted"


def test_is_bot_recognises_app_logins():
    assert _is_bot("github-actions[bot]")
    assert _is_bot("dependabot[bot]")
    assert not _is_bot("jsboige")
    assert not _is_bot("myia-po-2023")
    assert not _is_bot("")


def test_human_retraction_orders_by_timestamp_not_position():
    # The timeline arrives chronologically, but the predicate must not depend
    # on it: order the human events by their own timestamps.
    out_of_order = [
        _lab("labeled", "jsboige", "2026-08-20T09:00:00Z"),
        _lab("unlabeled", "jsboige", "2026-08-16T08:36:00Z"),
    ]
    assert human_retraction(out_of_order) is None
    assert human_retraction([]) is None
    assert human_retraction(None) is None


def test_parse_label_events_filters_other_labels_and_events():
    raw = [
        {"event": "labeled", "label": {"name": "candidate-delivered"},
         "actor": {"login": _BOT}, "created_at": "2026-08-30T06:01:00Z"},
        {"event": "unlabeled", "label": {"name": "base-stale-14d"},
         "actor": {"login": "jsboige"}, "created_at": "2026-08-30T07:00:00Z"},
        {"event": "cross-referenced", "created_at": "2026-08-30T08:00:00Z"},
        {"event": "labeled", "actor": {"login": _BOT},
         "created_at": "2026-08-30T09:00:00Z"},  # no label payload -> dropped
        {"event": "unlabeled", "label": {"name": "candidate-delivered"},
         "actor": None, "created_at": "2026-08-31T05:25:49Z"},
    ]
    got = _parse_label_events(raw, "candidate-delivered")
    assert [(e["event"], e["actor"]) for e in got] == [
        ("labeled", _BOT), ("unlabeled", "")]
    assert _parse_label_events([], "candidate-delivered") == []
    assert _parse_label_events(None, "candidate-delivered") == []


def test_parse_label_events_feeds_classify_retracted():
    # End-to-end over the pure pair, as _parse_cross_ref_events is tested above:
    # a raw timeline slice reproduces the #10038 verdict without any network.
    raw = [
        {"event": "labeled", "label": {"name": "candidate-delivered"},
         "actor": {"login": _BOT}, "created_at": "2026-08-30T06:01:00Z"},
        {"event": "unlabeled", "label": {"name": "candidate-delivered"},
         "actor": {"login": "jsboige"}, "created_at": "2026-08-31T05:25:49Z"},
        {"event": "labeled", "label": {"name": "candidate-delivered"},
         "actor": {"login": _BOT}, "created_at": "2026-09-02T10:28:58Z"},
    ]
    events = _parse_label_events(raw, "candidate-delivered")
    verdict, _ = classify(_issue(), _DELIVERED_SILENT, events)
    assert verdict == "retracted"


if __name__ == "__main__":
    import pytest
    sys.exit(pytest.main([__file__, "-v"]))
