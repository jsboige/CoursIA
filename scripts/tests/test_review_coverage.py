#!/usr/bin/env python3
"""Unit tests for the pure classification core of review_coverage.py (#11232).

The ``classify`` function is network-free; ``main`` (the gh wiring) is
exercised end-to-end in CI dry-runs, not here. These fixtures encode the
verdicts measured firsthand on the #11232 sample (2026-08-16):

  - #11132 : 1041 additions, 0 reviews -> flag
  - #11210 : 883 additions, 0 reviews -> flag
  - #11217 : 318 additions, 2 reviews (Hermes + ai-01) -> clear
  - #11048 : 425 additions, 1 review (Hermes) -> clear
  - young PR : < threshold AND 0 reviews -> clear
  - draft PR : any size, 0 reviews -> skip_draft
  - base=branch PR : any size, 0 reviews -> skip_base
  - bot review : 1 review from clusterManager-Myia -> clear (the defect
    is the absence, not the absence of a human)

The bot review is important: a check that excluded bot reviews would
itself be the defect (it would re-create the hole it claims to fill, just
on a narrower surface).
"""

import sys
import os

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from review_coverage import classify  # noqa: E402


def _pr(additions: int, reviews: int | None = 0, *,
        is_draft: bool = False, base: str = "main") -> dict:
    """Build a PR fixture shaped like ``gh pr view --json`` output."""
    return {
        "number": 99999,
        "title": "test",
        "isDraft": is_draft,
        "baseRefName": base,
        "additions": additions,
        "reviews": [{"author": {"login": "x"}, "state": "APPROVED"}] * (reviews or 0),
    }


def test_large_no_review_flags():
    """#11132 1041 additions, 0 reviews -> flag (the headline case)."""
    assert classify(_pr(1041, 0)) == "flag"


def test_large_no_review_flags_883():
    """#11210 883 additions, 0 reviews -> flag."""
    assert classify(_pr(883, 0)) == "flag"


def test_medium_with_2_reviews_clears():
    """#11217 318 additions, 2 reviews -> clear (Hermes + ai-01)."""
    assert classify(_pr(318, 2)) == "clear"


def test_medium_with_1_review_clears():
    """#11048 425 additions, 1 review (Hermes) -> clear."""
    assert classify(_pr(425, 1)) == "clear"


def test_below_threshold_with_no_review_clears():
    """Young PR below threshold: 100 additions, 0 reviews -> clear.

    The signal is large-no-review, not just no-review. Otherwise the
    organ would label every fresh PR the moment it opens, defeating the
    purpose (the dashboard label would be a rediscovery of the PR list).
    """
    assert classify(_pr(100, 0)) == "clear"


def test_draft_large_no_review_skips():
    """Draft PR: 9999 additions, 0 reviews -> skip_draft, NOT flag.

    Draft PRs are by design unready for review; flagging them would mix
    two signals (coverage hole + "not ready") and produce noise.
    """
    assert classify(_pr(9999, 0, is_draft=True)) == "skip_draft"


def test_non_main_base_skips():
    """base != main: 9999 additions, 0 reviews -> skip_base.

    A PR targeting a feature branch has a different review audience
    (the branch owner / co-workers, not the cross-lane coordinator).
    The label is a current-state signal of the main-track coverage hole.
    """
    assert classify(_pr(9999, 0, base="feature/x")) == "skip_base"


def test_threshold_default_is_300():
    """The default threshold of 300 is the per-issue-body rationale.

    300 is just above the +318 LOC of #11217 (Hermes triggered) and
    well below #11132 / #11210. Documented in
    docs/reference/review-coverage-threshold.md.
    """
    from review_coverage import THRESHOLD_DEFAULT
    assert THRESHOLD_DEFAULT == 300


def test_exact_threshold_with_no_review_flags():
    """Edge case: PR at exactly the threshold, no review -> flag.

    ``additions >= threshold`` semantics: 300 with threshold 300 is in
    scope. Off-by-one here would be a silent scanner that misses the
    exact-threshold case.
    """
    assert classify(_pr(300, 0)) == "flag"


def test_exact_threshold_with_review_clears():
    """Edge case: PR at exactly the threshold, has review -> clear."""
    assert classify(_pr(300, 1)) == "clear"


def test_bot_review_clears():
    """A bot review alone counts (the defect is the ABSENCE, not the
    absence of a human).

    If we excluded bot reviews, the organ would re-create the hole it
    claims to fill, just on a narrower surface.
    """
    pr = _pr(1000, 0)
    pr["reviews"] = [{"author": {"login": "clusterManager-Myia"}, "state": "COMMENTED"}]
    assert classify(pr) == "clear"


def test_legacy_classification_unknown_field_is_robust():
    """Missing fields default to safe values (no crash).

    Real `gh pr view` payloads occasionally drop fields; the classifier
    must not raise on missing keys, or the cron would hard-fail.
    """
    minimal = {"number": 1}
    assert classify(minimal) in {"clear", "skip_draft", "skip_base", "flag"}
    # Specific check: no `additions` key + no `reviews` key = below threshold
    # + no reviews = clear (a no-op pass), not flag.
    assert classify(minimal) == "clear"


if __name__ == "__main__":
    test_large_no_review_flags()
    test_large_no_review_flags_883()
    test_medium_with_2_reviews_clears()
    test_medium_with_1_review_clears()
    test_below_threshold_with_no_review_clears()
    test_draft_large_no_review_skips()
    test_non_main_base_skips()
    test_threshold_default_is_300()
    test_exact_threshold_with_no_review_flags()
    test_exact_threshold_with_review_clears()
    test_bot_review_clears()
    test_legacy_classification_unknown_field_is_robust()
    print("All tests passed")
