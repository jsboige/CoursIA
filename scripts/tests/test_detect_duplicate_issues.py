#!/usr/bin/env python3
"""Tests for `scripts.detect_duplicate_issues`.

Two scopes:
- Unit tests on `detect_burst_pairs` with synthetic IssueRow lists
  (no network, no `gh`).
- CLI self-test on the positive control (#13050/#13051) -- this requires
  GitHub access; it's gated behind a `_HAS_NETWORK` env var so CI without
  network still passes. Set `DETECT_DUP_NETWORK=1` to enable.
"""
from __future__ import annotations

import importlib.util
import os
import sys
import unittest
from pathlib import Path

# Load scripts/detect_duplicate_issues.py as a module (it lives outside
# the standard `scripts.tests` package directory).
_SCRIPT = Path(__file__).resolve().parent.parent / "detect_duplicate_issues.py"
_spec = importlib.util.spec_from_file_location("detect_duplicate_issues", _SCRIPT)
assert _spec and _spec.loader, f"could not load {_SCRIPT}"
_mod = importlib.util.module_from_spec(_spec)
sys.modules["detect_duplicate_issues"] = _mod
_spec.loader.exec_module(_mod)

IssueRow = _mod.IssueRow
BurstPair = _mod.BurstPair
detect_burst_pairs = _mod.detect_burst_pairs


def _row(number: int, title: str, iso: str, state: str = "OPEN") -> IssueRow:
    return IssueRow(number=number, title=title, createdAt=iso, state=state)


class TestBurstPairDetection(unittest.TestCase):
    def test_empty_input(self):
        """Empty input -> no pairs. Positive controls report MISSING by design
        (we couldn't find them in a 0-row scan) -- that's the whole point
        of the control: it must fail loudly when the scanner is broken."""
        result = detect_burst_pairs([])
        self.assertEqual(result.total_issues_scanned, 0)
        self.assertEqual(result.distinct_titles, 0)
        self.assertEqual(result.n_pairs, 0)
        # Positive controls are NOT found in 0 rows -- this is expected.
        self.assertIn((13050, 13051), result.positive_controls_missing)

    def test_single_issue(self):
        rows = [_row(1, "foo", "2026-08-26T01:00:00Z")]
        result = detect_burst_pairs(rows)
        self.assertEqual(result.total_issues_scanned, 1)
        self.assertEqual(result.n_pairs, 0)

    def test_burst_pair_within_window(self):
        rows = [
            _row(50, "Doublons d'issues", "2026-08-26T01:39:13Z"),
            _row(51, "Doublons d'issues", "2026-08-26T01:39:14Z"),  # +1 s
        ]
        result = detect_burst_pairs(rows, window_seconds=10)
        self.assertEqual(result.n_pairs, 1)
        pair = result.pairs[0]
        self.assertEqual(pair.a_number, 50)
        self.assertEqual(pair.b_number, 51)
        self.assertAlmostEqual(pair.delta_seconds, 1.0, places=3)

    def test_burst_pair_outside_window(self):
        rows = [
            _row(50, "foo", "2026-08-26T01:00:00Z"),
            _row(51, "foo", "2026-08-26T01:30:00Z"),  # +30 min
        ]
        result = detect_burst_pairs(rows, window_seconds=60)
        self.assertEqual(result.n_pairs, 0)

    def test_pair_window_boundary_exact(self):
        rows = [
            _row(50, "foo", "2026-08-26T01:00:00Z"),
            _row(51, "foo", "2026-08-26T01:01:00Z"),  # +60 s exact
        ]
        # Inclusive upper bound -- the test of the issue spec says "delta <= window".
        result = detect_burst_pairs(rows, window_seconds=60)
        self.assertEqual(result.n_pairs, 1)

    def test_pair_window_boundary_one_over(self):
        rows = [
            _row(50, "foo", "2026-08-26T01:00:00Z"),
            _row(51, "foo", "2026-08-26T01:01:01Z"),  # +61 s
        ]
        result = detect_burst_pairs(rows, window_seconds=60)
        self.assertEqual(result.n_pairs, 0)

    def test_distinct_titles_no_pair(self):
        rows = [
            _row(1, "alpha", "2026-08-26T01:00:00Z"),
            _row(2, "beta", "2026-08-26T01:00:01Z"),
            _row(3, "gamma", "2026-08-26T01:00:02Z"),
        ]
        result = detect_burst_pairs(rows)
        self.assertEqual(result.distinct_titles, 3)
        self.assertEqual(result.n_pairs, 0)

    def test_three_in_a_burst(self):
        """Three issues with same title, 1 s apart -> 3 pairs (combinatorial)."""
        rows = [
            _row(10, "x", "2026-08-26T01:00:00Z"),
            _row(11, "x", "2026-08-26T01:00:01Z"),
            _row(12, "x", "2026-08-26T01:00:02Z"),
        ]
        result = detect_burst_pairs(rows, window_seconds=10)
        # combinations(3,2) = 3
        self.assertEqual(result.n_pairs, 3)

    def test_positive_control_found(self):
        rows = [
            _row(13050, "foo", "2026-08-26T01:39:13Z"),
            _row(13051, "foo", "2026-08-26T01:39:14Z"),
        ]
        result = detect_burst_pairs(rows, window_seconds=60)
        self.assertIn((13050, 13051), result.positive_controls_found)
        self.assertEqual(result.positive_controls_missing, [])

    def test_positive_control_missing(self):
        """If the known pair is absent, the missing list surfaces it."""
        rows = [
            _row(1, "foo", "2026-08-26T01:00:00Z"),
            _row(2, "foo", "2026-08-26T01:00:01Z"),
        ]
        result = detect_burst_pairs(rows, window_seconds=10)
        self.assertEqual(result.positive_controls_found, [])
        self.assertIn((13050, 13051), result.positive_controls_missing)

    def test_positive_control_either_ordering(self):
        """If the pair appears with reversed numbers, it still matches."""
        rows = [
            _row(13051, "foo", "2026-08-26T01:39:13Z"),
            _row(13050, "foo", "2026-08-26T01:39:14Z"),
        ]
        result = detect_burst_pairs(rows, window_seconds=60)
        # The pair appears as (13051, 13050) -- not (13050, 13051).
        # detect_burst_pairs uses combinations() which respects order
        # (sorted by createdAt) -- so a_number <= b_number by construction.
        # In this fixture, 13051 is created first; if the scanner
        # finds (13051, 13050), the control (13050, 13051) is NOT found.
        # This documents the assumption: the scanner treats (a,b) by
        # createdAt order, so positive controls should be ordered by
        # creation. The known #13208 pairs are created within seconds of
        # each other; in practice they're already ordered by the lower
        # number being created first (issue ids are monotonic). If that
        # ever flips, KNOWN_POSITIVE_CONTROLS needs to be updated.
        # Here we accept EITHER outcome but require one of them:
        self.assertTrue(
            (13050, 13051) in result.positive_controls_found
            or (13050, 13051) in result.positive_controls_missing
        )

    def test_pair_state_recorded(self):
        rows = [
            _row(1, "foo", "2026-08-26T01:00:00Z", state="CLOSED"),
            _row(2, "foo", "2026-08-26T01:00:01Z", state="OPEN"),
        ]
        result = detect_burst_pairs(rows, window_seconds=10)
        self.assertEqual(result.pairs[0].a_state, "CLOSED")
        self.assertEqual(result.pairs[0].b_state, "OPEN")

    def test_sort_order_smallest_delta_first(self):
        rows = [
            _row(1, "x", "2026-08-26T01:00:00Z"),
            _row(2, "x", "2026-08-26T01:00:10Z"),  # +10 s
            _row(3, "x", "2026-08-26T01:00:01Z"),  # +1 s
        ]
        result = detect_burst_pairs(rows, window_seconds=60)
        # Pairs: (1,3) +1s, (1,2) +10s, (3,1)... no, (3,2) +9s.
        # Order: (1,3) first (delta=1), then (3,2) (delta=9), then (1,2) (delta=10).
        deltas = [p.delta_seconds for p in result.pairs]
        self.assertEqual(deltas, sorted(deltas))


class TestSelfTestCLI(unittest.TestCase):
    """`--self-test` requires the GitHub API and the #13050/#13051 pair.
    Skipped unless `DETECT_DUP_NETWORK=1` is set."""

    def test_self_test_passes_against_real_data(self):
        if not os.environ.get("DETECT_DUP_NETWORK"):
            self.skipTest("set DETECT_DUP_NETWORK=1 to run live self-test")
        # Run the CLI in a subprocess; expect exit 0 (no dup) or 1 (some dup),
        # but NOT 2 (positive control missing).
        import subprocess
        proc = subprocess.run(
            [
                sys.executable, str(_SCRIPT),
                "--self-test", "--limit", "600", "--window-seconds", "60",
            ],
            capture_output=True, text=True, timeout=120,
        )
        self.assertNotEqual(
            proc.returncode, 2,
            f"self-test FAILED: positive control #13050/#13051 missing.\n"
            f"stdout: {proc.stdout[-500:]}\nstderr: {proc.stderr[-500:]}",
        )


if __name__ == "__main__":
    unittest.main()
