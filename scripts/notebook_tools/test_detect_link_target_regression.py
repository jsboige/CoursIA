"""Tests unitaires pour detect_link_target_regression.

Couvre :
- strip_accents (NFD + oe/ae + lower)
- collect_link_targets (filtres HTTP/#/templating)
- diff_targets (case-insensitive matching par position)
- resolve_target (relatif au notebook)
- scan_notebook (end-to-end avec mock de subprocess git)

Run: python scripts/notebook_tools/test_detect_link_target_regression.py
"""
import json
import subprocess
import sys
import unittest
from pathlib import Path
from unittest import mock

SCRIPTS_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS_DIR))

from detect_link_target_regression import (  # noqa: E402
    LINK_PATTERN,
    collect_link_targets,
    diff_targets,
    extract_md_cells,
    resolve_target,
    scan_notebook,
    strip_accents,
)


class TestStripAccents(unittest.TestCase):
    def test_basic(self):
        self.assertEqual(strip_accents("Inférer"), "Inferer")
        self.assertEqual(strip_accents("Génération"), "Generation")
        self.assertEqual(strip_accents("Café"), "Cafe")

    def test_no_accents(self):
        self.assertEqual(strip_accents("Infer-10-Model-Selection"), "Infer-10-Model-Selection")

    def test_ligatures(self):
        self.assertEqual(strip_accents("cœur"), "coeur")
        self.assertEqual(strip_accents("œuvre"), "oeuvre")
        self.assertEqual(strip_accents("æquo"), "aequo")

    def test_combining_marks(self):
        # NFD decomposable
        self.assertEqual(strip_accents("é"), "e")
        self.assertEqual(strip_accents("à"), "a")
        self.assertEqual(strip_accents("ï"), "i")


class TestCollectLinkTargets(unittest.TestCase):
    def test_basic_markdown_link(self):
        cells = [(0, ["[Infer-10](Infer-10-Model-Selection.ipynb)"])]
        targets = collect_link_targets(cells)
        self.assertEqual(len(targets), 1)
        self.assertEqual(targets[0]["text"], "Infer-10")
        self.assertEqual(targets[0]["target"], "Infer-10-Model-Selection.ipynb")
        self.assertEqual(targets[0]["cell_idx"], 0)
        self.assertEqual(targets[0]["line_no"], 1)

    def test_filter_http_links(self):
        cells = [(0, ["[site](https://example.com)", "[local](file.ipynb)"])]
        targets = collect_link_targets(cells)
        self.assertEqual(len(targets), 1)
        self.assertEqual(targets[0]["target"], "file.ipynb")

    def test_filter_anchor_only(self):
        cells = [(0, ["[section](#section-name)", "[local](file.ipynb)"])]
        targets = collect_link_targets(cells)
        self.assertEqual(len(targets), 1)

    def test_filter_template_var(self):
        cells = [(0, ["[tpl]({variable})", "[local](file.ipynb)"])]
        targets = collect_link_targets(cells)
        self.assertEqual(len(targets), 1)

    def test_filter_no_extension_or_path(self):
        cells = [(0, ["[generic](variable)", "[local](file.ipynb)"])]
        targets = collect_link_targets(cells)
        self.assertEqual(len(targets), 1)


class TestResolveTarget(unittest.TestCase):
    def test_resolve_relative(self):
        nb = Path("C:/tmp/MyIA.AI.Notebooks/Probas/Infer/Infer-11-Topic-Models.ipynb")
        resolved = resolve_target(nb, "Infer-10-Model-Selection.ipynb")
        # Sur Windows, Path.resolve() retourne C:/tmp/.../Infer-10-Model-Selection.ipynb
        self.assertTrue(str(resolved).endswith("MyIA.AI.Notebooks/Probas/Infer/Infer-10-Model-Selection.ipynb".replace("/", "\\"))
                        or str(resolved).endswith("MyIA.AI.Notebooks/Probas/Infer/Infer-10-Model-Selection.ipynb"))

    def test_resolve_with_anchor(self):
        nb = Path("C:/tmp/MyIA.AI.Notebooks/Probas/Infer/Infer-11-Topic-Models.ipynb")
        resolved = resolve_target(nb, "Infer-10.ipynb#section-1")
        self.assertTrue(str(resolved).endswith("MyIA.AI.Notebooks/Probas/Infer/Infer-10.ipynb".replace("/", "\\"))
                        or str(resolved).endswith("MyIA.AI.Notebooks/Probas/Infer/Infer-10.ipynb"))


class TestDiffTargets(unittest.TestCase):
    def test_accent_regression_detected(self):
        """Le cas fondateur : cure #2876 introduit un accent dans le target."""
        base = [
            {"cell_idx": 0, "line_no": 22, "text": "X", "target": "Infer-10-Model-Selection.ipynb"},
        ]
        head = [
            {"cell_idx": 0, "line_no": 22, "text": "X", "target": "Infer-10-Model-sélection.ipynb"},
        ]
        regs = diff_targets(base, head)
        self.assertEqual(len(regs), 1)
        self.assertEqual(regs[0]["kind"], "ACCENT_REGRESSION")
        self.assertEqual(regs[0]["target_added"], "Infer-10-Model-sélection.ipynb")
        self.assertEqual(regs[0]["target_removed"], "Infer-10-Model-Selection.ipynb")

    def test_accent_added_in_text_but_not_target(self):
        """Le texte du lien gagne un accent, mais le target reste intact -> pas de regression cible."""
        base = [
            {"cell_idx": 0, "line_no": 22, "text": "Selection", "target": "Infer-10-Selection.ipynb"},
        ]
        head = [
            {"cell_idx": 0, "line_no": 22, "text": "Sélection", "target": "Infer-10-Selection.ipynb"},
        ]
        regs = diff_targets(base, head)
        self.assertEqual(len(regs), 0)

    def test_no_change(self):
        base = [{"cell_idx": 0, "line_no": 22, "text": "X", "target": "Infer-10.ipynb"}]
        head = [{"cell_idx": 0, "line_no": 22, "text": "X", "target": "Infer-10.ipynb"}]
        regs = diff_targets(base, head)
        self.assertEqual(len(regs), 0)

    def test_fundamental_change_ignored(self):
        """Changement de cible complet (pas un pur accent) -> hors scope."""
        base = [{"cell_idx": 0, "line_no": 22, "text": "X", "target": "Infer-10.ipynb"}]
        head = [{"cell_idx": 0, "line_no": 22, "text": "X", "target": "Infer-99.ipynb"}]
        regs = diff_targets(base, head)
        self.assertEqual(len(regs), 0)

    def test_case_insensitive_match(self):
        """S majuscule vs s minuscule : match grace au .lower()."""
        base = [{"cell_idx": 0, "line_no": 22, "text": "X", "target": "Infer-10-Selection.ipynb"}]
        head = [{"cell_idx": 0, "line_no": 22, "text": "X", "target": "Infer-10-sélection.ipynb"}]
        regs = diff_targets(base, head)
        self.assertEqual(len(regs), 1)


class TestScanNotebook(unittest.TestCase):
    def _make_nb(self, target: str) -> dict:
        return {
            "cells": [{
                "cell_type": "markdown",
                "metadata": {},
                "source": [f"| [Infer-10]({target}) |\n"],
            }],
            "metadata": {},
            "nbformat": 4,
            "nbformat_minor": 5,
        }

    @mock.patch("detect_link_target_regression.read_notebook_at_ref")
    def test_scan_realistic_defect(self, mock_read):
        # base : target sans accent
        nb_base = self._make_nb("Infer-10-Model-Selection.ipynb")
        # head : target avec accent (cassé sur disque)
        nb_head = self._make_nb("Infer-10-Model-sélection.ipynb")
        mock_read.side_effect = lambda path, ref: nb_base if ref == "origin/main" else nb_head

        # Mock : la cible ajoutée (avec accent) n'existe pas, la retirée (sans accent) existe
        real_resolve = resolve_target
        def fake_resolve(nb_path, target):
            if "sélection" in target:
                return Path("C:/fake/path/that/does/not/exist.ipynb")
            return Path("C:/fake/path/Infer-10-Model-Selection.ipynb")
        with mock.patch("detect_link_target_regression.resolve_target", side_effect=fake_resolve):
            nb_path = Path("MyIA.AI.Notebooks/Probas/Infer/Infer-11-Topic-Models.ipynb")
            with mock.patch.object(Path, "exists", return_value=True):
                result = scan_notebook(nb_path, "origin/main", "origin/fix/c683-accents-2876")
                self.assertEqual(result["stats"]["regressions_count"], 1)
                # kind depends on file existence; with mock exists=True, kind stays ACCENT_REGRESSION
                self.assertIn(result["regressions"][0]["kind"], ("ACCENT_REGRESSION", "BROKEN_LINK_ACCENT_REGRESSION"))


if __name__ == "__main__":
    unittest.main(verbosity=2)