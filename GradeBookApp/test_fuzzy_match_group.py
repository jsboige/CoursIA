"""Tests for GradeBookApp/gradebook.py::fuzzy_match_group.

Guards its heavy deps (pandas/rapidfuzz/...) via ``pytest.importorskip`` so the
suite skips cleanly in CI (no GradeBookApp Python env) but runs on any machine
that has the grading-engine deps installed.

Covers the regression fixed alongside this test: commit 3a612f85c wired a
configurable ``group_match_threshold`` and a 3-arg call site (gradebook.py
l.1137) but never updated ``fuzzy_match_group``'s signature -- so the 3-arg
call raised ``TypeError`` and the threshold was dead config. The fix restores
the author's documented intent via a backward-compatible ``threshold=90``
default.
"""
import os
import sys

import pytest

# Make ``gradebook`` (sibling file) importable regardless of invocation cwd,
# since the repo root pytest.ini uses ``--import-mode importlib`` and does not
# put GradeBookApp/ on sys.path.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

pd = pytest.importorskip("pandas")
pytest.importorskip("rapidfuzz")

from gradebook import fuzzy_match_group  # noqa: E402  (after importorskip guards)


def test_three_arg_call_no_longer_crashes():
    """Regression: l.1137 passes 3 args; the old 2-param signature raised TypeError."""
    # Exact pair -> Cas 1 -> True, at any threshold. Point: 3-arg call must be callable.
    assert fuzzy_match_group("projet alpha", "projet alpha", 90) is True
    assert fuzzy_match_group("projet alpha", "projet alpha", 100) is True


def test_threshold_governs_cas2_borderline():
    """Cas 2 admission follows the configurable threshold, not a hardcoded 90.
    Derives the assertion from the actual fuzz ratio (no brittle magic number)."""
    from rapidfuzz import fuzz

    a = "projet machine learning"
    b = "projet machine learnig"  # 1-char typo -> ratio < 100, reaches Cas 2
    ratio = fuzz.ratio(a, b)
    assert ratio < 100, "fixture must not be exact (would short-circuit at Cas 1)"
    assert 50 < ratio < 100, f"fixture ratio {ratio} outside the expected band"
    # Admitted at/under the measured ratio, rejected strictly above it.
    assert fuzzy_match_group(a, b, threshold=int(ratio)) is True
    assert fuzzy_match_group(a, b, threshold=100) is False


def test_two_arg_backward_compat_default_90():
    """Existing 2-arg callers (l.742, l.853) keep the historical default-90 behavior."""
    a = "projet machine learning"
    b = "projet machine learnig"
    assert fuzzy_match_group(a, b) == fuzzy_match_group(a, b, 90)


def test_cas0_distinct_group_codes_never_match():
    """Cas 0 dominates: distinct leading codes must not match, even at a low threshold."""
    assert fuzzy_match_group("a1 - projet", "a2 - projet", threshold=10) is False
    # Same code matches regardless of a strict threshold.
    assert fuzzy_match_group("a1 - projet", "a1 - projet", threshold=100) is True
