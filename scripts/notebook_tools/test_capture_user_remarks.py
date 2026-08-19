#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Tests unitaires de capture_user_remarks.py (Epic #11259 T3).

Invariants :
- fidélité verbatim : le body de l'issue cite la remarque à l'identique
  (espaces, accents, multi-lignes) — jamais reformulée ;
- une remarque unitaire = une issue ;
- rattachement mécanique : UNIQUE / AMBIGUOUS / NONE, jamais deviné ;
- dry-run par défaut : --create absent => aucun appel gh ;
- --create : exactement un `gh issue create` par remarque.
"""

from __future__ import annotations

import tempfile
import unittest
import unittest.mock as mock
from pathlib import Path

import capture_user_remarks as cur


class SplitRemarks(unittest.TestCase):
    def test_separator_blocks(self):
        text = "première remarque\nsuite de la première\n---\ndeuxième"
        self.assertEqual(cur.split_remarks(text),
                         ["première remarque\nsuite de la première", "deuxième"])

    def test_line_mode_without_separator(self):
        text = "remarque A\n\nremarque B\n"
        self.assertEqual(cur.split_remarks(text), ["remarque A", "remarque B"])

    def test_empty_input(self):
        self.assertEqual(cur.split_remarks("   \n  \n"), [])

    def test_multiline_block_kept_whole(self):
        text = "titre\n détail indenté\n---\nautre"
        blocks = cur.split_remarks(text)
        self.assertEqual(len(blocks), 2)
        self.assertIn("détail indenté", blocks[0])


class Normalize(unittest.TestCase):
    def test_accents_and_separators_folded(self):
        self.assertEqual(cur._normalize("GénAI_Téxte 04"), "genai-texte-04")

    def test_prefix_semantics(self):
        # « QC-Py-02 » cite 3 tokens consécutifs du stem complet
        stem = cur._tokens("QC-Py-02-Platform-Fundamentals")
        remark = cur._tokens("voir QC-Py-02 c'est confus")
        self.assertEqual(cur._longest_segment_cited(stem, remark), 3)

    def test_short_prefix_not_significant(self):
        stem = cur._tokens("QC-Py-02-Platform-Fundamentals")
        remark = cur._tokens("les notebooks QC-Py en général")
        # « QC-Py » = 2 tokens seulement, mais non discriminant : dominé par
        # les préfixes plus longs ; seul en lice il reste retenu (k=2 >= 2)
        self.assertEqual(cur._longest_segment_cited(stem, remark), 2)

    def test_mid_segment_cited(self):
        # « Toulmin_Model » cite le segment médian de « Argument_Analysis_Toulmin_Model »
        stem = cur._tokens("Argument_Analysis_Toulmin_Model")
        remark = cur._tokens("Dans Toulmin_Model il manque une interprétation")
        self.assertEqual(cur._longest_segment_cited(stem, remark), 2)

    def test_single_generic_token_not_significant(self):
        # « model » seul (1 token) : la fonction le mesure, mais le filtre
        # de significativité (k >= 2) dans resolve_notebooks doit rendre NONE
        idx = ["SymbolicAI/Argument_Analysis/Argument_Analysis_Toulmin_Model.ipynb"]
        status, hits = cur.resolve_notebooks("le model est cassé", idx)
        self.assertEqual(status, "NONE")
        self.assertEqual(hits, [])


class ResolveNotebooks(unittest.TestCase):
    def setUp(self):
        self.index = [
            "QuantConnect/Python/QC-Py-02-Platform-Fundamentals.ipynb",
            "QuantConnect/Python/QC-Py-20-Bitcoin-Strategy.ipynb",
            "GenAI/Image/01-Foundation/01-1-OpenAI-DALL-E-3.ipynb",
        ]

    def test_unique_prefix_match(self):
        status, hits = cur.resolve_notebooks(
            "le QC-Py-02 est confus sur les registres", self.index)
        self.assertEqual(status, "UNIQUE")
        self.assertEqual(hits, [self.index[0]])

    def test_ambiguous_when_multiple_hits(self):
        status, hits = cur.resolve_notebooks(
            "QC-Py-02 et QC-Py-20 ont le même défaut", self.index)
        self.assertEqual(status, "AMBIGUOUS")
        self.assertEqual(len(hits), 2)

    def test_none_when_no_reference(self):
        status, hits = cur.resolve_notebooks(
            "le titre de la série est trompeur", self.index)
        self.assertEqual(status, "NONE")
        self.assertEqual(hits, [])

    def test_short_stems_ignored(self):
        # un stem < 6 caractères normalisés ne doit pas rapprocher le bruit
        idx = ["GenAI/a-b.ipynb"]
        status, _ = cur.resolve_notebooks("a-b", idx)
        self.assertEqual(status, "NONE")


class BuildIssue(unittest.TestCase):
    def test_verbatim_citation_preserved(self):
        remark = "la cellule 12  est confuse\net l'accent « é » manque"
        issue = cur.build_issue(remark, "UNIQUE",
                                ["GenAI/Image/01-Foundation/x.ipynb"],
                                captured_on="2026-08-16")
        for line in remark.splitlines():
            self.assertIn(f"> {line}", issue["body"])
        self.assertIn("[User remark] la cellule 12", issue["title"])

    def test_title_truncated_at_60(self):
        long_remark = "x" * 100
        issue = cur.build_issue(long_remark, "NONE", [])
        self.assertLessEqual(len(issue["title"]), 60 + len("[User remark] "))
        self.assertTrue(issue["title"].endswith("..."))

    def test_unique_attaches_scope(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            scope = base / "scope.md"
            scope.write_text(
                "# s\n\n## Strate A — proposés\n\n- [ ] `GenAI/x.ipynb`\n",
                encoding="utf-8")
            with mock.patch.object(cur, "SCOPE_FILE", scope), \
                 mock.patch.object(cur, "_scope_of", lambda rel: "A"):
                issue = cur.build_issue("voir GenAI/x", "UNIQUE", ["GenAI/x.ipynb"])
        self.assertIn("`GenAI/x.ipynb` — strate A", issue["body"])

    def test_ambiguous_lists_candidates_not_guess(self):
        issue = cur.build_issue("les deux", "AMBIGUOUS", ["a/X.ipynb", "b/Y.ipynb"])
        self.assertIn("AMBIGU", issue["body"])
        self.assertIn("`a/X.ipynb`", issue["body"])
        self.assertIn("l'agent tranche", issue["body"])

    def test_no_interpretation_in_citation_zone(self):
        issue = cur.build_issue("remarque pure", "NONE", [])
        # le squelette d'acceptance existe mais est marqué à instruire
        self.assertIn("À instruire par l'agent", issue["body"])


class DryRunDefault(unittest.TestCase):
    def test_no_gh_call_without_create(self):
        with mock.patch.object(cur, "build_index", return_value=[]), \
             mock.patch.object(cur, "create_issue") as ci, \
             mock.patch("sys.stdin", new=mock.Mock(read=lambda: "remarque\n")):
            rc = cur.main([])
        ci.assert_not_called()
        self.assertEqual(rc, 0)

    def test_create_calls_gh_once_per_remark(self):
        remarks = "remarque une\n---\nremarque deux\n"
        ok_result = (True, "https://github.com/jsboige/CoursIA/issues/1")
        with tempfile.NamedTemporaryFile("w", suffix=".txt", delete=False,
                                         encoding="utf-8") as fh:
            fh.write(remarks)
            path = fh.name
        try:
            # l'appel DOIT rester dans le contexte du mock : hors contexte, le
            # vrai create_issue s'exécuterait (gh réel)
            with mock.patch.object(cur, "build_index", return_value=[]), \
                 mock.patch.object(cur, "create_issue",
                                   return_value=ok_result) as ci:
                rc = cur.main(["--create", path])
                self.assertEqual(ci.call_count, 2)
                self.assertEqual(rc, 0)
        finally:
            Path(path).unlink()


if __name__ == "__main__":
    unittest.main()
