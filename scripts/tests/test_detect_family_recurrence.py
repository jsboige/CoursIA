#!/usr/bin/env python3
"""Tests for `scripts.detect_family_recurrence`.

Two scopes:
- Unit tests on `detect` with synthetic `Issue` lists (no network, no `gh`).
- CLI self-test on the positive control (#24294 -> #24268) -- the control
  needs GitHub access to be poured into the lot, so it is gated behind a
  `_HAS_NETWORK` env var (same convention as
  `scripts/tests/test_detect_duplicate_issues.py`): set
  `DETECT_FAMILY_NETWORK=1` to enable.

The negative controls matter as much as the positive one: the detector must
NOT group issues that merely share a series (66 open issues cite
``SymbolicAI``), and must NOT group issues that cite a script which is not an
organ of this repository.
"""
from __future__ import annotations

import importlib.util
import contextlib
import io
import json
import os
import sys
import tempfile
import unittest
from pathlib import Path

_SCRIPT = Path(__file__).resolve().parent.parent / "detect_family_recurrence.py"
_spec = importlib.util.spec_from_file_location("detect_family_recurrence", _SCRIPT)
assert _spec and _spec.loader, f"could not load {_SCRIPT}"
_mod = importlib.util.module_from_spec(_spec)
sys.modules["detect_family_recurrence"] = _mod
_spec.loader.exec_module(_mod)

Issue = _mod.Issue
detect = _mod.detect
title_skeleton = _mod.title_skeleton
organ_inventory = _mod.organ_inventory
family_table = _mod.family_table
delivered_candidates = _mod.delivered_candidates
main = _mod.main
KNOWN_POSITIVE_CONTROL = _mod.KNOWN_POSITIVE_CONTROL

# A fixed "now" so the window tests do not depend on the wall clock.
NOW = _mod.datetime(2026, 11, 4, 12, 0, tzinfo=_mod.timezone.utc)


def _issue(number: int, title: str, body: str = "", created: str = "2026-11-02T10:00:00Z",
           labels: list | None = None) -> Issue:
    return Issue(number=number, title=title, body=body, createdAt=created,
                 labels=list(labels or []))


class TestFamilyKeys(unittest.TestCase):
    def test_series_alone_is_not_a_family(self):
        """Two issues of the SAME series, about DIFFERENT organs, are not a family.

        This is the noise control: 66 open issues cite ``SymbolicAI``; grouping
        them would call the whole series a family.
        """
        issues = [
            _issue(1, "Un carnet de SymbolicAI", body="MyIA.AI.Notebooks/SymbolicAI/Lean/x.ipynb"),
            _issue(2, "Un autre carnet de SymbolicAI", body="MyIA.AI.Notebooks/SymbolicAI/GameTheory/y.ipynb"),
        ]
        organs = {"check_a.py", "check_b.py"}
        self.assertEqual(detect(issues, organs, now=NOW), [])

    def test_script_outside_the_repo_is_not_an_organ(self):
        """A ``*.py`` that does not exist under ``scripts/`` is not a family key."""
        issues = [
            _issue(1, "life.py plante", body="voir life.py"),
            _issue(2, "life.py : second cas", body="life.py encore"),
        ]
        self.assertEqual(detect(issues, {"check_a.py"}, now=NOW), [])

    def test_title_gabarit_families(self):
        """Same gabarit of title -> same family, even without an organ."""
        issues = [
            _issue(10, "Fix(lean,#21001): le lac ne compile pas"),
            _issue(11, "Fix(lean,#21002): le lac ne compile pas"),
        ]
        result = detect(issues, set(), now=NOW)
        self.assertEqual(len(result), 1)
        self.assertEqual(result[0].issue, 11)
        self.assertEqual(result[0].host, 10)
        self.assertEqual(result[0].signal, "title")

    def test_audit_partitions_are_not_proposed_for_fold_back(self):
        """The partitions of one audit are NOT a family to fold back.

        #17073 carries dozens of partitions; they are the LIVING STRUCTURE of
        the campaign (the maintainer's directive of 2026-11-01 makes them the
        pool), not duplicates of each other. The detector must leave them
        alone.
        """
        issues = [
            _issue(300, "[Audit #17073] Serie Lean — partition Hermes",
                   body="travail de la partition", created="2026-11-02T10:00:00Z"),
            _issue(301, "[Audit #17073] Serie Lean — partition Loki",
                   body="travail de la partition", created="2026-11-03T10:00:00Z"),
        ]
        self.assertEqual(detect(issues, set(), now=NOW), [])

    def test_audit_partitions_with_the_SAME_label_are_not_a_family(self):
        """The property, not the spelling: two partitions of the same label.

        21 of the 29 open partitions carry the label ``partition Hermes``;
        the exclusion must be by MARKER, not by the accident of the title
        template (the old test only checked ``Hermes`` != ``Loki``).
        """
        issues = [
            _issue(300, "[Audit #17073] Serie Lean — partition Hermes",
                   body="travail de la partition", created="2026-11-02T10:00:00Z"),
            _issue(301, "[Audit #17073] Serie Lean — partition Hermes",
                   body="travail de la partition", created="2026-11-03T10:00:00Z"),
            _issue(302, "[Audit #17107] Serie Lean — partition Hermes",
                   body="autre partition, meme libelle", created="2026-11-03T10:00:00Z"),
        ]
        self.assertEqual(detect(issues, set(), now=NOW), [])

    def test_an_issue_declaring_another_parent_is_to_arbitrer(self):
        """A declared filiation is not a violation: it is reported apart.

        Folding an issue that declares ``Part of #N`` into another host would
        DESTROY that filiation -- the organ must say ``a_arbitrer``.
        """
        issues = [
            _issue(100, "check_a.py : le cas de reference", body="check_a.py",
                   created="2026-10-30T10:00:00Z"),
            _issue(101, "check_a.py : faux positif", body="check_a.py\n\nPart of #102",
                   created="2026-11-02T10:00:00Z"),
            _issue(102, "une autre issue ouverte, sans famille", body="rien ici",
                   created="2026-10-30T10:00:00Z"),
        ]
        result = detect(issues, {"check_a.py"}, window_days=14, now=NOW)
        self.assertEqual(len(result), 1)
        self.assertEqual(result[0].declared_parent, 102)
        self.assertEqual(result[0].confidence, "a_arbitrer")
        # un parent declare QUI EST l'hote n'est pas une divergence : c'est
        # la filiation CONFIRMEE, ni violation ni arbitrage (review 17:24Z).
        issues[1].body = "check_a.py\n\nPart of #100"
        result = detect(issues, {"check_a.py"}, window_days=14, now=NOW)
        self.assertEqual(result[0].confidence, "filiation_confirmee")

    def test_a_declared_parent_equal_to_the_host_is_a_confirmed_filiation(self):
        """The third state: the declared filiation IS the proposed host.

        Before it existed, the line was counted as a ``forte`` violation --
        and that label MOVED when a third-party issue was closed (#22827
        closed on 2026-11-04T16:51Z made #24610 a violation precisely
        because its declared parent had become the proposed host). A verdict
        that depends on the calendar is not a verdict: the state is now
        neutral by construction.
        """
        issues = [
            _issue(100, "check_a.py : le cas de reference", body="check_a.py",
                   created="2026-10-30T10:00:00Z"),
            _issue(101, "check_a.py : faux positif", body="check_a.py\n\nPart of #100",
                   created="2026-11-02T10:00:00Z"),
        ]
        result = detect(issues, {"check_a.py"}, window_days=14, now=NOW)
        self.assertEqual(len(result), 1)
        self.assertEqual(result[0].host, 100)
        self.assertEqual(result[0].declared_parent, 100)
        self.assertEqual(result[0].confidence, "filiation_confirmee")
        # and it is not a violation: the four classes are disjoint
        self.assertNotIn(result[0].confidence, {"forte", "a_arbitrer"})

    def test_a_declared_parent_protects_even_when_closed(self):
        """A declared filiation protects, even if the parent is closed.

        The two parents the review cited (#11435, #15369) are CLOSED: the
        organ must not count those recurrences as violations -- the verdict
        there is a human arbitration.
        """
        issues = [
            _issue(100, "check_a.py : le cas de reference", body="check_a.py",
                   created="2026-10-30T10:00:00Z"),
            _issue(101, "check_a.py : faux positif", body="check_a.py\n\nPart of #999",
                   created="2026-11-02T10:00:00Z"),
        ]
        result = detect(issues, {"check_a.py"}, window_days=14, now=NOW)
        self.assertEqual(result[0].declared_parent, 999)
        self.assertEqual(result[0].confidence, "a_arbitrer")

    def test_an_issue_without_a_declared_parent_stays_a_violation(self):
        """No declared parent = the issue is the orphan the rule targets."""
        issues = [
            _issue(100, "check_a.py : le cas de reference", body="check_a.py",
                   created="2026-10-30T10:00:00Z"),
            _issue(101, "check_a.py : faux positif", body="check_a.py",
                   created="2026-11-02T10:00:00Z"),
        ]
        result = detect(issues, {"check_a.py"}, window_days=14, now=NOW)
        self.assertEqual(result[0].confidence, "forte")

    def test_a_truncated_pool_is_reported_as_incomplete(self):
        """A pool that leaves issues out must not read as the population."""
        dropped, complete = _mod._pool_status(400, 596)
        self.assertEqual(dropped, 196)
        self.assertFalse(complete)
        dropped, complete = _mod._pool_status(596, 596)
        self.assertEqual(dropped, 0)
        self.assertTrue(complete)
        self.assertEqual(_mod._pool_status(10, None), (None, None))

    def test_unrelated_issues_are_not_a_family(self):
        issues = [
            _issue(1, "Un probleme de physique"),
            _issue(2, "Un autre probleme de physique"),
        ]
        self.assertEqual(detect(issues, {"check_a.py"}, now=NOW), [])


class TestHostSelection(unittest.TestCase):
    def test_host_is_the_issue_about_the_organ(self):
        """The host is the issue whose TITLE names the organ, not the oldest."""
        issues = [
            _issue(100, "check_a.py : faux positif sur les valeurs FR",
                   body="check_a.py", created="2026-10-20T10:00:00Z"),
            _issue(200, "Un carnet cite check_a.py", body="check_a.py",
                   created="2026-11-02T10:00:00Z"),
        ]
        result = detect(issues, {"check_a.py"}, now=NOW)
        self.assertEqual(len(result), 1)
        self.assertEqual(result[0].host, 100)
        self.assertEqual(result[0].confidence, "forte")

    def test_weak_confidence_when_the_host_only_cites_the_organ(self):
        """When NO issue of the group names the organ in its TITLE, the group
        only shares a citation: the report says ``faible`` -- a candidate to
        triage, not a fold-back to perform."""
        issues = [
            _issue(100, "Un vieux probleme", body="on y parle de check_a.py",
                   created="2026-10-20T10:00:00Z"),
            _issue(200, "Un probleme plus recent", body="check_a.py",
                   created="2026-11-02T10:00:00Z"),
        ]
        result = detect(issues, {"check_a.py"}, now=NOW)
        self.assertEqual(len(result), 1)
        self.assertEqual(result[0].host, 100)
        self.assertEqual(result[0].confidence, "faible")

    def test_an_epic_that_cites_an_organ_is_not_its_host(self):
        """An EPIC that merely CITES an organ is not the family of the issues
        about that organ: the issue whose TITLE names the organ is the host."""
        issues = [
            _issue(100, "[EPIC] Un grand projet", body="on y parle de check_a.py",
                   created="2026-10-01T10:00:00Z"),
            _issue(200, "check_a.py : faux positif", body="check_a.py",
                   created="2026-10-30T10:00:00Z"),
            _issue(300, "Un cas recent du meme organe", body="check_a.py",
                   created="2026-11-02T10:00:00Z"),
        ]
        result = detect(issues, {"check_a.py"}, now=NOW)
        self.assertEqual(len(result), 1)
        self.assertEqual(result[0].host, 200)
        # The recurrence only CITES the organ in its body -> candidate, not
        # an obvious fold-back.
        self.assertEqual(result[0].confidence, "faible")

    def test_forte_when_the_recurrence_names_the_organ_too(self):
        issues = [
            _issue(200, "check_a.py : faux positif", body="check_a.py",
                   created="2026-10-30T10:00:00Z"),
            _issue(300, "check_a.py : un second faux positif", body="check_a.py",
                   created="2026-11-02T10:00:00Z"),
        ]
        result = detect(issues, {"check_a.py"}, now=NOW)
        self.assertEqual(len(result), 1)
        self.assertEqual(result[0].confidence, "forte")

    def test_an_audit_partition_is_neither_member_nor_host(self):
        """A partition is excluded BEFORE any key is produced, on both routes.

        Excluding only the ``title:`` route left the partitions as hosts of
        the ``organ:`` families they cite: measured on the real pool, 6
        recurrences proposed to fold real work into ``#17793`` and 2 into
        ``#24103``, and a partition that enumerates its brothers could take
        the host role away from the real carrier of the family.
        """
        issues = [
            _issue(300, "[Audit #17073] Serie Lean — partition Hermes",
                   body="check_a.py", created="2026-10-05T10:00:00Z"),
            _issue(301, "[Audit #17073] Serie Lean — partition Loki",
                   body="check_a.py", created="2026-11-02T10:00:00Z"),
        ]
        self.assertEqual(detect(issues, {"check_a.py"}, now=NOW), [])
        self.assertEqual(family_table(issues, {"check_a.py"}), [])

    def test_a_partition_cannot_steal_the_host_role_from_the_real_carrier(self):
        """The partition loses the host role; the issue that NAMES the organ
        keeps it."""
        issues = [
            _issue(100, "check_a.py : le cas de reference", body="check_a.py",
                   created="2026-10-05T10:00:00Z"),
            _issue(300, "[Audit #17073] Serie Lean — partition Hermes",
                   body="check_a.py #100 #101", created="2026-10-06T10:00:00Z"),
            _issue(101, "check_a.py : faux positif", body="check_a.py",
                   created="2026-11-02T10:00:00Z"),
        ]
        result = detect(issues, {"check_a.py"}, now=NOW)
        self.assertEqual(len(result), 1)
        self.assertEqual(result[0].issue, 101)
        self.assertEqual(result[0].host, 100)


class TestPartition(unittest.TestCase):
    """The families must be a PARTITION of the pool, not a cover.

    Measured on the real pool (2026-11-04): an issue citing several organs
    landed in several families at once, and the "host" of a family could be an
    unrelated issue -- an Origami notebook issue became the host of a
    nav-chain family. The consolidation table was then unusable as a plan.
    """

    def test_an_issue_belongs_to_exactly_one_family(self):
        issues = [
            _issue(100, "check_a.py : le cas de reference", body="check_a.py"),
            _issue(101, "check_b.py : un autre organe", body="check_b.py"),
            _issue(102, "check_a.py et check_b.py dans le meme corps",
                   body="check_a.py check_b.py"),
        ]
        table = family_table(issues, {"check_a.py", "check_b.py"})
        seen = []
        for row in table:
            seen.extend(m["issue"] for m in row["members"])
            seen.append(row["host"])
        self.assertEqual(sorted(seen), [100, 101, 102],
                         "chaque issue doit apparaitre dans une seule famille")
        self.assertEqual(len(seen), len(set(seen)),
                         "aucune issue ne doit apparaitre deux fois")

    def test_a_delivered_issue_is_not_a_family_member(self):
        """``candidate-delivered`` = the work is done, the issue awaits a closure.

        Folding it into another issue would destroy the delivery proof: it is
        a closure candidate, not a duplication.
        """
        issues = [
            _issue(100, "check_a.py : le cas de reference", body="check_a.py"),
            _issue(101, "check_a.py : deja livre", body="check_a.py",
                   labels=["candidate-delivered"]),
        ]
        table = family_table(issues, {"check_a.py"})
        members = [m["issue"] for row in table for m in row["members"]]
        self.assertNotIn(101, members)
        delivered = delivered_candidates(issues)
        self.assertEqual([d["issue"] for d in delivered], [101])


class TestWindow(unittest.TestCase):
    def test_two_old_issues_are_not_a_recurrence(self):
        """Only RECENT issues are reported as recurrences."""
        issues = [
            _issue(1, "check_a.py : le cas de reference", body="check_a.py",
                   created="2026-09-01T10:00:00Z"),
            _issue(2, "check_a.py : faux positif", body="check_a.py",
                   created="2026-09-02T10:00:00Z"),
        ]
        self.assertEqual(detect(issues, {"check_a.py"}, window_days=14, now=NOW), [])

    def test_recent_issue_folds_into_the_older_family(self):
        """The HOST may be old -- it is the RECURRENCE that must be recent."""
        issues = [
            _issue(1, "check_a.py : le cas de reference", body="check_a.py",
                   created="2026-10-30T10:00:00Z"),
            _issue(2, "check_a.py : faux positif", body="check_a.py",
                   created="2026-11-02T10:00:00Z"),
        ]
        result = detect(issues, {"check_a.py"}, window_days=14, now=NOW)
        self.assertEqual(len(result), 1)
        self.assertEqual((result[0].issue, result[0].host), (2, 1))


class TestPositiveControl(unittest.TestCase):
    """The measured control of the pool c2767, reproduced offline.

    #24294 is a small local finding on ``scan_d5_prose_outputs_alignment.py``
    discovered while fixing #24268 -- the family issue of the same organ.
    """

    def _pool(self):
        return [
            _issue(24268, "scan_d5_prose_outputs_alignment.py : une estampille de build graphviz "
                          "est prise pour une valeur pedagogique (faux positif)",
                   body="Sans parent : defaut d'un organe de controle.",
                   created="2026-11-02T17:23:20Z"),
            _issue(24294, "scan_d5_prose_outputs_alignment.py : une valeur au format FR dans une "
                          "expression n'entre pas dans l'enumeration de la prose (faux positif residuel)",
                   body="Sans parent : defaut d'un organe de controle, decouvert en corrigeant #24268.",
                   created="2026-11-02T19:42:41Z"),
        ]

    def test_control_pair_is_detected(self):
        organs = organ_inventory()
        self.assertIn("scan_d5_prose_outputs_alignment.py", organs,
                      "l'organe de controle a disparu du depot : le controle est perime")
        result = detect(self._pool(), organs, now=NOW)
        self.assertEqual(len(result), 1)
        self.assertEqual(result[0].issue, KNOWN_POSITIVE_CONTROL["recurrence"])
        self.assertEqual(result[0].host, KNOWN_POSITIVE_CONTROL["host"])

    def test_cli_self_test_exit_2_when_the_control_is_absent(self):
        """A pool without the control MUST make the CLI exit 2.

        Otherwise "0 recurrence" and "detector mute" are indistinguishable --
        the very failure mode the positive control exists for.
        """
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "pool.json"
            path.write_text(json.dumps([
                {"number": 1, "title": "check_a.py : cas isole", "body": "check_a.py",
                 "createdAt": "2026-11-02T10:00:00Z", "labels": []},
            ]), encoding="utf-8")
            rc = main(["--from-file", str(path), "--self-test", "--json"])
        self.assertEqual(rc, 2)


class TestPoolVisibility(unittest.TestCase):
    """The pool status must be visible in EVERY mode (review du 17:24Z, §3).

    The body of the PR copies its table from the ``--json`` output -- the
    very mode where a silent truncation was the most dangerous: the WARN was
    under ``if not args.json``, so it fired in the human mode and not in the
    one the published numbers are taken from.
    """

    def _pool(self):
        return [_issue(i, f"check_a.py : cas {i}", body="check_a.py",
                       created="2026-10-30T10:00:00Z") for i in range(1, 4)]

    def _run(self, total, argv):
        old_list, old_total = _mod._gh_issue_list, _mod._open_issue_total
        _mod._gh_issue_list = lambda repo, limit: self._pool()
        _mod._open_issue_total = lambda repo: total
        err, out = io.StringIO(), io.StringIO()
        try:
            with contextlib.redirect_stderr(err), contextlib.redirect_stdout(out):
                rc = main(argv)
        finally:
            _mod._gh_issue_list, _mod._open_issue_total = old_list, old_total
        return rc, out.getvalue(), err.getvalue()

    def test_a_truncated_pool_warns_on_stderr_in_json_mode(self):
        rc, out, err = self._run(596, ["--limit", "400", "--json"])
        self.assertIn("pool tronque", err)
        self.assertIn('"dropped": 593', out)
        self.assertIn('"pool_complete": false', out)
        self.assertNotIn("pool tronque", out,
                         "le WARN est sur stderr : stdout reste du JSON pur")

    def test_an_unknown_total_warns_instead_of_reading_as_the_population(self):
        """``search/issues`` en echec : le total est inconnu, donc la limite
        de repli (1000) peut avoir tronque le pool sans que rien le dise."""
        rc, out, err = self._run(None, ["--json"])
        self.assertIn("INCONNU", err)
        self.assertIn('"n_open_total": null', out)

    def test_a_complete_pool_does_not_warn(self):
        rc, out, err = self._run(3, ["--json"])
        self.assertNotIn("pool tronque", err)
        self.assertNotIn("INCONNU", err)
        self.assertIn('"pool_complete": true', out)


class TestLiveControl(unittest.TestCase):
    """Live CLI self-test -- needs GitHub access."""

    def test_cli_self_test_against_real_data(self):
        if not os.environ.get("DETECT_FAMILY_NETWORK"):
            self.skipTest("DETECT_FAMILY_NETWORK absent : test live ignore")
        rc = main(["--self-test", "--json", "--limit", "400"])
        self.assertEqual(rc, 0, "le controle positif doit etre trouve")


if __name__ == "__main__":
    unittest.main()
