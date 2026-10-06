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
import io
import json
import sys
import unittest
from contextlib import redirect_stderr
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


class TestEpicRecognition(unittest.TestCase):
    """#18203 geste 2: an EPIC is recognized by label OR title prefix.

    On `main`, recognition reads the label only, so an EPIC titled `[EPIC] x`
    without the label is invisible to the sweep -- it can fall behind with no
    report ever naming it. These controls fail on `main` (`is_epic` does not
    exist there) and pass on this branch.
    """

    def test_label_recognized(self):
        self.assertTrue(_mod.is_epic(
            {"title": "Tirage des grains", "labels": [{"name": "EPIC"}]}))

    def test_title_prefix_recognized_without_label(self):
        self.assertTrue(_mod.is_epic(
            {"title": "[EPIC] Tirage des grains", "labels": []}))

    def test_title_prefix_case_insensitive(self):
        self.assertTrue(_mod.is_epic(
            {"title": "[epic] lowercase prefix", "labels": []}))

    def test_title_prefix_after_leading_space(self):
        self.assertTrue(_mod.is_epic(
            {"title": "  [EPIC] padded prefix", "labels": []}))

    def test_plain_issue_not_epic(self):
        self.assertFalse(_mod.is_epic(
            {"title": "Bug report", "labels": [{"name": "bug"}]}))

    def test_mid_title_mention_not_epic(self):
        """Prefix, not substring: a note MENTIONING [EPIC] is not one."""
        self.assertFalse(_mod.is_epic(
            {"title": "Note about [EPIC] conventions", "labels": []}))

    def test_no_title_no_labels_not_epic(self):
        self.assertFalse(_mod.is_epic({"title": None, "labels": None}))

    def test_both_channels_coexist_dedup(self):
        """Label AND prefix on the same issue: still one EPIC (bool predicate,
        no double count -- the dedup happens because recognition is a filter
        over the issue list, not a union of two lists)."""
        d = {"title": "[EPIC] double convention", "labels": [{"name": "EPIC"}]}
        self.assertTrue(_mod.is_epic(d))


# --- #19211 : le 404 du PATCH, et une panne d'ecriture qui se voit -------------
#
# Le rapport n'etait plus publie depuis 35 jours sous un run quotidien VERT.
# Cause mesuree : `gh issue view --json comments` rend l'id de NOEUD GraphQL,
# alors que `repos/{repo}/issues/comments/{id}` attend l'id NUMERIQUE. Le
# commentaire de #13653 porte `created_at == updated_at`, donc le PATCH n'avait
# jamais abouti. Les controles ci-dessous epinglent (1) la FORME de l'id lu,
# (2) la pagination, (3) le fait qu'une panne PERSISTANTE rougit.

_REAL_RUN = _mod.subprocess.run
_REAL_NOW = _mod._now
_REAL_EPICS = _mod.list_open_epics
_REAL_MERGED = _mod.list_recent_merged_prs
_NODE_ID = "IC_kwDOH2Odns8AAAABRmTerA"
_DB_ID = 5475983020
_MARKER_BODY = f"{_mod.SWEEP_MARKER_START}\nrapport\n{_mod.SWEEP_MARKER_END}"
_AGED = datetime(2026, 9, 1, 8, 47, 16, tzinfo=timezone.utc)
_FIXED_NOW = datetime(2026, 10, 5, 12, 0, tzinfo=timezone.utc)


class _Completed:
    def __init__(self, payload, rc=0, err=""):
        self.stdout = payload if isinstance(payload, str) else json.dumps(payload)
        self.stderr = err
        self.returncode = rc


def _comment(updated_at=None, body=_MARKER_BODY, cid=_DB_ID):
    row = {"id": cid, "body": body}
    if updated_at is not None:
        row["updated_at"] = updated_at.strftime("%Y-%m-%dT%H:%M:%SZ")
    return row


class _FakeGh:
    """`subprocess.run` remplace : dispatch sur la commande, journalise les argv."""

    def __init__(self, page, *, patch_rc=0, patch_err=""):
        self.page = page
        self.patch_rc = patch_rc
        self.patch_err = patch_err
        self.calls: list[list[str]] = []

    def __call__(self, cmd, **kw):
        self.calls.append(list(cmd))
        if "--method" in cmd:
            return _Completed({"id": _DB_ID}, rc=self.patch_rc, err=self.patch_err)
        return _Completed(self.page)

    def write_urls(self) -> list[str]:
        return [
            a for c in self.calls if "--method" in c
            for a in c if a.startswith("repos/")
        ]


class TestFindSweepCommentUsesRestIds(unittest.TestCase):
    """#19211 : l'id qui part dans l'URL doit etre NUMERIQUE."""

    def _install(self, fake):
        _mod.subprocess.run = fake
        self.addCleanup(setattr, _mod.subprocess, "run", _REAL_RUN)

    def test_lookup_asks_the_rest_endpoint_not_the_graphql_one(self):
        fake = _FakeGh([[_comment(_AGED)]])
        self._install(fake)
        _mod._find_sweep_comment("o/r", 13653)
        self.assertEqual(len(fake.calls), 1, fake.calls)
        argv = fake.calls[0]
        self.assertIn("api", argv)
        self.assertIn("repos/o/r/issues/13653/comments?per_page=100", argv)
        # Controle NEGATIF : la forme d'avant, qui rendait un id de noeud.
        joined = " ".join(argv)
        self.assertNotIn("issue view", joined)
        self.assertNotIn("--json comments", joined)

    def test_found_id_is_numeric_not_the_graphql_node_id(self):
        self._install(_FakeGh([[_comment(_AGED)]]))
        found = _mod._find_sweep_comment("o/r", 13653)
        self.assertIsNotNone(found)
        self.assertEqual(str(found["id"]), str(_DB_ID))
        self.assertNotEqual(str(found["id"]), _NODE_ID)

    def test_marker_on_a_later_page_is_still_found(self):
        """Sinon l'organe conclut « absent » et POSTE un doublon a chaque tir."""
        self._install(_FakeGh([[{"id": 1, "body": "bruit"}], [_comment(_AGED)]]))
        found = _mod._find_sweep_comment("o/r", 13653)
        self.assertIsNotNone(found)
        self.assertEqual(str(found["id"]), str(_DB_ID))

    def test_patch_url_carries_the_numeric_id(self):
        """Le temoin du 404 : c'est l'URL qui repondait `Not Found`."""
        fake = _FakeGh([[_comment(_AGED)]])
        self._install(fake)
        _mod.upsert_sweep_comment("o/r", 13653, "nouveau rapport")
        self.assertEqual(fake.write_urls(), [f"repos/o/r/issues/comments/{_DB_ID}"])

    def test_a_body_without_marker_takes_the_post_branch(self):
        """Controle de bord : pas de marqueur -> POST, jamais un PATCH a vide."""
        fake = _FakeGh([[{"id": 9, "body": "un autre commentaire"}]])
        self._install(fake)
        _mod.upsert_sweep_comment("o/r", 13653, "rapport")
        self.assertEqual(fake.write_urls(), [])


class TestPersistentWriteFailureIsVisible(unittest.TestCase):
    """#19211 acceptance 3 : une panne d'ecriture PERSISTANTE n'est plus
    indistinguishable d'un run sain."""

    def _install(self, fake):
        _mod.subprocess.run = fake
        self.addCleanup(setattr, _mod.subprocess, "run", _REAL_RUN)

    def _stderr(self, fn):
        buf = io.StringIO()
        with redirect_stderr(buf):
            rc = fn()
        return rc, buf.getvalue()

    def test_persistent_failure_reds_and_names_the_breakage(self):
        aged = _FIXED_NOW - timedelta(days=34)  # #13653 : 35 jours de silence
        self._install(_FakeGh([[_comment(aged)]]))
        rc, err = self._stderr(
            lambda: _mod.write_failure_exit_code("o/r", 13653, _FIXED_NOW))
        self.assertEqual(rc, 2, err)
        self.assertIn("::error::", err)
        self.assertIn("13653", err)

    def test_transient_failure_stays_green_and_warns(self):
        fresh = _FIXED_NOW - timedelta(hours=1)
        self._install(_FakeGh([[_comment(fresh)]]))
        rc, err = self._stderr(
            lambda: _mod.write_failure_exit_code("o/r", 13653, _FIXED_NOW))
        self.assertEqual(rc, 0, err)
        self.assertIn("::warning::", err)
        self.assertNotIn("::error::", err)

    def test_cli_exits_2_when_a_persistent_write_failure_occurred(self):
        """De bout en bout : le PATCH echoue et le rendez-vous est fige."""
        aged = _FIXED_NOW - timedelta(days=34)
        fake = _FakeGh([[_comment(aged)]], patch_rc=1,
                       patch_err="gh: Not Found (HTTP 404)")
        self._install(fake)
        _mod.list_open_epics = lambda repo: []
        _mod.list_recent_merged_prs = lambda repo, limit: []
        _mod._now = lambda: _FIXED_NOW
        self.addCleanup(setattr, _mod, "_now", _REAL_NOW)
        self.addCleanup(setattr, _mod, "list_open_epics", _REAL_EPICS)
        self.addCleanup(setattr, _mod, "list_recent_merged_prs", _REAL_MERGED)
        rc, err = self._stderr(
            lambda: _mod._cli(["--repo", "o/r", "--apply-comment", "13653"]))
        self.assertEqual(rc, 2, err)
        self.assertIn("::error::", err)


if __name__ == "__main__":
    unittest.main()
