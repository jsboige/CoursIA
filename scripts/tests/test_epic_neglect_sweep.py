#!/usr/bin/env python3
"""Tests for `scripts.epic_neglect_sweep` (issue #13653).

The measuring core and the report builder are PURE (no network, no `gh`);
only the wiring (`list_open_epics`, `list_recent_merged_prs`,
`upsert_sweep_comment`) touches GitHub -- exercised by the live dry run, not
here. The acceptance criteria of #13653 are encoded as controls: the
neglected are named and sorted, a cited EPIC never appears, the vintage is
written, and the limitations are stated.
"""
from __future__ import annotations

import importlib.util
import sys
import unittest
from datetime import datetime, timedelta, timezone
from pathlib import Path

_SCRIPT = Path(__file__).resolve().parent.parent / "epic_neglect_sweep.py"
_spec = importlib.util.spec_from_file_location("epic_neglect_sweep", _SCRIPT)
assert _spec and _spec.loader, f"could not load {_SCRIPT}"
_mod = importlib.util.module_from_spec(_spec)
sys.modules["epic_neglect_sweep"] = _mod
_spec.loader.exec_module(_mod)

Epic = _mod.Epic
MergedPr = _mod.MergedPr
measure_neglect = _mod.measure_neglect
build_report = _mod.build_report

NOW = datetime(2026, 8, 30, 12, 0, tzinfo=timezone.utc)


def _epic(number, title="EPIC", *, inact_d=0.0, age_d=1.0) -> Epic:
    return Epic(
        number=number,
        title=title,
        created_at=NOW - timedelta(days=age_d),
        updated_at=NOW - timedelta(days=inact_d),
    )


class TestMeasureNeglect(unittest.TestCase):
    def test_empty_pool_all_neglected(self):
        rows, n_cited, window = measure_neglect(
            [_epic(1), _epic(2)], [], NOW)
        self.assertEqual(len(rows), 2)
        self.assertEqual(n_cited, 0)
        self.assertIsNone(window)

    def test_cited_epic_excluded(self):
        """Acceptance (positive control): an EPIC touched by a merged PR in
        the window does NOT appear -- otherwise the report is indistinguish-
        able from one listing everything."""
        rows, n_cited, _ = measure_neglect(
            [_epic(1), _epic(2)],
            [MergedPr(10, "feat(#2): x", "Closes #2", NOW - timedelta(hours=1))],
            NOW,
        )
        self.assertEqual([r.epic.number for r in rows], [1])
        self.assertEqual(n_cited, 1)

    def test_sorted_by_inact_desc(self):
        """Acceptance: sorted by neglect (inact) descending."""
        rows, _, _ = measure_neglect(
            [_epic(1, inact_d=0.5), _epic(2, inact_d=4.0), _epic(3, inact_d=2.0)],
            [], NOW,
        )
        self.assertEqual([r.epic.number for r in rows], [2, 3, 1])

    def test_citation_reads_title_and_body(self):
        pr = MergedPr(10, "feat(#7): t", "See #8 also", NOW)
        self.assertEqual(pr.cited_issues(), {7, 8})

    def test_window_is_real_span_of_fetch(self):
        """Acceptance: the window is measured, not assumed."""
        merged = [
            MergedPr(1, "a", "", NOW - timedelta(hours=50)),
            MergedPr(2, "b", "", NOW - timedelta(hours=2)),
            MergedPr(3, "c", "", NOW - timedelta(hours=25)),
        ]
        _, _, window = measure_neglect([_epic(1)], merged, NOW)
        self.assertEqual(window[0], NOW - timedelta(hours=50))
        self.assertEqual(window[1], NOW - timedelta(hours=2))

    def test_inact_and_age_computed(self):
        rows, _, _ = measure_neglect(
            [_epic(1, inact_d=3.0, age_d=15.0)], [], NOW)
        self.assertAlmostEqual(rows[0].inact_days, 3.0)
        self.assertAlmostEqual(rows[0].age_days, 15.0)

    def test_deterministic_tiebreak_by_number(self):
        rows, _, _ = measure_neglect(
            [_epic(9, inact_d=2.0), _epic(2, inact_d=2.0)], [], NOW)
        self.assertEqual([r.epic.number for r in rows], [2, 9])


class TestBuildReport(unittest.TestCase):
    def _rows(self):
        return measure_neglect(
            [_epic(1, "Meta-EPIC", inact_d=5.0, age_d=10.0),
             _epic(2, "Pages", inact_d=4.0, age_d=15.0),
             _epic(3, "citee", inact_d=1.0)],
            [MergedPr(10, "feat(#3): x", "", NOW - timedelta(hours=3))],
            NOW,
        )

    def test_report_carries_vintage(self):
        """Acceptance: window + measurement date WRITTEN -- a ranking without
        a vintage reads as current."""
        rows, n_cited, window = self._rows()
        report = build_report(rows, 3, n_cited, window, NOW, 1)
        self.assertIn("Fenetre de citation : 1 PR(s) mergee(s)", report)
        self.assertIn("2026-08-30T12:00Z", report)
        self.assertIn("->", report)

    def test_report_states_limitations(self):
        """Acceptance: the report says what it does NOT measure."""
        rows, n_cited, window = self._rows()
        report = build_report(rows, 3, n_cited, window, NOW, 1)
        self.assertIn("ouverte non mergee", report)
        self.assertIn("autre numero", report)
        self.assertIn("pas une tendance", report)

    def test_report_names_neglected_with_inact_and_age(self):
        rows, n_cited, window = self._rows()
        report = build_report(rows, 3, n_cited, window, NOW, 1)
        self.assertIn("#1 — Meta-EPIC", report)
        self.assertIn("5.0 j", report)
        self.assertIn("15 j", report)
        self.assertNotIn("#3", report.split("Ce que ce compte")[0].replace(
            "#13653", ""))  # cited EPIC not in the table

    def test_report_counts_summary(self):
        rows, n_cited, window = self._rows()
        report = build_report(rows, 3, n_cited, window, NOW, 1)
        self.assertIn("2/3 EPIC(s) ouverte(s)", report)
        self.assertIn("1 citee(s)", report)

    def test_empty_case_written(self):
        """A mute sweep is indistinguishable from a dead one (#13086)."""
        report = build_report([], 3, 3,
                              (NOW - timedelta(hours=48), NOW), NOW, 5)
        self.assertIn("Aucune EPIC delaissee", report)

    def test_marker_framed(self):
        rows, n_cited, window = self._rows()
        report = build_report(rows, 3, n_cited, window, NOW, 1)
        self.assertTrue(report.startswith(_mod.SWEEP_MARKER_START))
        self.assertTrue(report.rstrip().endswith(_mod.SWEEP_MARKER_END))
        self.assertIn("Cf #13653", report)


class TestGhRowExtraction(unittest.TestCase):
    def test_epic_from_gh_dict(self):
        e = Epic.from_gh_dict({
            "number": 42,
            "title": " Some EPIC ",
            "createdAt": "2026-08-01T10:00:00Z",
            "updatedAt": "2026-08-28T10:00:00Z",
            "labels": [{"name": "EPIC"}],
        })
        self.assertEqual(e.number, 42)
        self.assertEqual(e.title, "Some EPIC")
        self.assertEqual(e.updated_at.year, 2026)
        self.assertIsNotNone(e.updated_at.tzinfo)

    def test_merged_pr_from_gh_dict(self):
        p = MergedPr.from_gh_dict({
            "number": 7, "title": "t #9", "body": "Closes #9",
            "mergedAt": "2026-08-30T08:00:00Z",
        })
        self.assertEqual(p.cited_issues(), {9})

    def test_parse_iso_handles_z(self):
        d = _mod._parse_iso("2026-08-30T08:00:00Z")
        self.assertEqual(d.hour, 8)
        self.assertIsNotNone(d.tzinfo)


if __name__ == "__main__":
    unittest.main()
