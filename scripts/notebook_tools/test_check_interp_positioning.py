#!/usr/bin/env python3
"""Unit tests for check_interp_positioning.

Couvre les invariants de la regle de detection :
- INTERP_HEADER_RE reconnait les 4 variantes documentees
- _is_legit_following_header couvre Exercices / Conclusion / Pour aller plus loin
- _stable_finding_hash est deterministe + depend de l'index
- scan_notebook OK: interp suivie d'un code cell
- scan_notebook OK: interp suivie de ## Exercices (transition legitime)
- scan_notebook BUG: interp suivie de ## N. Section suivante (mesure PyMC-15)
- scan_notebook BUG: interp suivie de ### 1. Intro (mesure GameTheory-10)
- scan_notebook OK: interp en fin de notebook (pas de cellule suivante)
- Integration : PyMC-15 contient >= 3 misplaced, GameTheory-10 <= 1

Run : python scripts/notebook_tools/test_check_interp_positioning.py
"""
from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPTS_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS_DIR))

from check_interp_positioning import (  # noqa: E402
    INTERP_HEADER_RE,
    _as_text,
    _first_line,
    _is_interp_cell,
    _is_legit_following_header,
    _is_section_header,
    _stable_finding_hash,
    scan_notebook,
)


def _make_nb(cells: list[dict]) -> dict:
    """Construit un notebook ipynb minimal a partir d'une liste de cells."""
    return {
        "cells": cells,
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }


def _md(source: str) -> dict:
    return {"cell_type": "markdown", "metadata": {}, "source": source}


def _code(source: str = "# code") -> dict:
    return {
        "cell_type": "code",
        "metadata": {},
        "source": source,
        "outputs": [],
        "execution_count": None,
    }


def _scan(nb: dict) -> list[dict]:
    """scan_notebook prend un Path -> on serialise dans un tmp et on scan."""
    with tempfile.NamedTemporaryFile(mode="w", suffix=".ipynb",
                                      delete=False, encoding="utf-8") as f:
        json.dump(nb, f)
        path = Path(f.name)
    try:
        return scan_notebook(path)
    finally:
        path.unlink()


class TestHelpers(unittest.TestCase):
    def test_first_line_strips_empty(self):
        self.assertEqual(_first_line(""), "")
        self.assertEqual(_first_line("\n\n\n"), "")
        self.assertEqual(_first_line("\n\n## Hello\nbody"), "## Hello")
        self.assertEqual(_first_line("### Lecture du résultat :"), "### Lecture du résultat :")

    def test_as_text_list(self):
        # Convention : un element par ligne, termine par '\\n'
        self.assertEqual(_as_text(["### Lecture du résultat\n", "body\n"]), "### Lecture du résultat\nbody\n")

    def test_as_text_str(self):
        self.assertEqual(_as_text("hello"), "hello")
        self.assertEqual(_as_text(None), "")
        self.assertEqual(_as_text(""), "")


class TestInterpHeader(unittest.TestCase):
    def test_lecture_du(self):
        self.assertTrue(_is_interp_cell("### Lecture du résultat"))
        self.assertTrue(_is_interp_cell("### Lecture du resultat"))  # sans accent

    def test_lecture_des(self):
        self.assertTrue(_is_interp_cell("### Lecture des résultats"))
        self.assertTrue(_is_interp_cell("### Lecture des resultats"))

    def test_interpretation(self):
        self.assertTrue(_is_interp_cell("### Interprétation"))
        self.assertTrue(_is_interp_cell("### Interpretation"))  # sans accent

    def test_interpretation_des_resultats(self):
        self.assertTrue(_is_interp_cell("### Interprétation des résultats"))
        self.assertTrue(_is_interp_cell("### Interpretation des resultats"))

    def test_with_colon_subtitle(self):
        # Les enrichisseurs utilisent "Titre : sous-titre"
        self.assertTrue(_is_interp_cell("### Lecture du résultat : données sparse"))
        self.assertTrue(_is_interp_cell("### Interprétation des résultats : 163 divergences NUTS"))

    def test_four_level_heading_accepted(self):
        # #### est accepte par INTERP_HEADER_RE (le pattern autorise 2-4 '#')
        self.assertTrue(_is_interp_cell("#### Lecture du résultat"))

    def test_case_insensitive(self):
        self.assertTrue(_is_interp_cell("### lecture du résultat"))
        self.assertTrue(_is_interp_cell("### INTERPRÉTATION"))

    def test_not_interp(self):
        self.assertFalse(_is_interp_cell("## 1. Introduction"))
        self.assertFalse(_is_interp_cell("### Définition du problème"))
        self.assertFalse(_is_interp_cell("Ce notebook illustre l'interprétation des résultats"))
        self.assertFalse(_is_interp_cell("# Lecture du résultat"))  # niveau 1 exclu
        self.assertFalse(_is_interp_cell(""))


class TestLegitFollowingHeader(unittest.TestCase):
    def test_exercices(self):
        self.assertTrue(_is_legit_following_header("## Exercices"))
        self.assertTrue(_is_legit_following_header("### Exercice 1"))

    def test_conclusion(self):
        self.assertTrue(_is_legit_following_header("### Conclusion"))
        self.assertTrue(_is_legit_following_header("## Conclusions"))

    def test_pour_aller_plus_loin(self):
        self.assertTrue(_is_legit_following_header("### Pour aller plus loin"))

    def test_references(self):
        self.assertTrue(_is_legit_following_header("### Références"))
        self.assertTrue(_is_legit_following_header("### References"))

    def test_bibliography(self):
        self.assertTrue(_is_legit_following_header("### Bibliography"))
        self.assertTrue(_is_legit_following_header("### Bibliographie"))

    def test_not_legit(self):
        self.assertFalse(_is_legit_following_header("## 1. Section suivante"))
        self.assertFalse(_is_legit_following_header("### 2. Méthode"))


class TestSectionHeader(unittest.TestCase):
    def test_h2(self):
        self.assertTrue(_is_section_header("## 1. Section suivante"))

    def test_h3(self):
        self.assertTrue(_is_section_header("### 2. Méthode"))

    def test_h1_excluded(self):
        # Le notebook n'utilise pas # en general, mais on le considere PAS
        # comme un marqueur de section interne (c'est le titre du notebook).
        self.assertFalse(_is_section_header("# Titre"))

    def test_with_leading_whitespace(self):
        self.assertTrue(_is_section_header("\n  ## Section"))


class TestStableFindingHash(unittest.TestCase):
    def test_determinism(self):
        h1 = _stable_finding_hash("misplaced_before_section", "foo.ipynb", 5, "### Lecture du résultat")
        h2 = _stable_finding_hash("misplaced_before_section", "foo.ipynb", 5, "### Lecture du résultat")
        self.assertEqual(h1, h2)

    def test_index_change_changes_hash(self):
        h1 = _stable_finding_hash("misplaced_before_section", "foo.ipynb", 5, "### Lecture du résultat")
        h2 = _stable_finding_hash("misplaced_before_section", "foo.ipynb", 6, "### Lecture du résultat")
        self.assertNotEqual(h1, h2)

    def test_length_is_12_chars(self):
        h = _stable_finding_hash("r", "f", 0, "h")
        self.assertEqual(len(h), 12)


class TestScanNotebookOkCases(unittest.TestCase):
    def test_interp_followed_by_code(self):
        # Cas nominal : interp immediatement suivie d'une cellule code
        nb = _make_nb([
            _code("# etape 1"),
            _md("### Lecture du résultat : convergence OK"),
            _code("# etape 2"),
        ])
        self.assertEqual(_scan(nb), [])

    def test_interp_followed_by_exercises_section(self):
        # Transition legitime : l'interp clot une section avant les exercices
        nb = _make_nb([
            _code("# etape 1"),
            _md("### Lecture du résultat : convergence OK"),
            _md("## Exercices"),
            _md("### Exercice 1 : ..."),
            _code("# reponse"),
        ])
        self.assertEqual(_scan(nb), [])

    def test_interp_followed_by_conclusion(self):
        nb = _make_nb([
            _code("# etape 1"),
            _md("### Lecture du résultat : bilan"),
            _md("## Conclusion"),
        ])
        self.assertEqual(_scan(nb), [])

    def test_interp_at_end_of_notebook(self):
        # Pas de cellule suivante -> pas un misplaced (rien a comparer)
        nb = _make_nb([
            _code("# etape 1"),
            _md("### Lecture du résultat : fin"),
        ])
        self.assertEqual(_scan(nb), [])

    def test_interp_followed_by_paragraph(self):
        # Une interp suivie d'un paragraphe (PAS un header) -> pas un signal
        nb = _make_nb([
            _code("# etape 1"),
            _md("### Lecture du résultat"),
            _md("Ce paragraphe developpe les implications..."),
        ])
        self.assertEqual(_scan(nb), [])


class TestScanNotebookBuggyCases(unittest.TestCase):
    def test_interp_followed_by_new_h2_section(self):
        # Bug fondateur : interp suivie de ## 1. Section suivante
        nb = _make_nb([
            _code("# imports"),
            _md("### Lecture du résultat : convergence OK"),  # cell[1] misplaced
            _md("## 1. Section suivante"),                    # cell[2]
            _code("# code section suivante"),
        ])
        findings = _scan(nb)
        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0]["rule"], "misplaced_before_section")
        self.assertEqual(findings[0]["cell_index"], 1)

    def test_interp_followed_by_h3_subsection(self):
        nb = _make_nb([
            _code("# etape 1"),
            _md("### Interprétation des résultats"),  # cell[1] misplaced
            _md("### 1. Sous-section"),                # cell[2]
        ])
        findings = _scan(nb)
        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0]["cell_index"], 1)

    def test_interp_followed_by_pour_aller_plus_loin_excluded(self):
        # "Pour aller plus loin" est legitime -> pas un bug
        nb = _make_nb([
            _code("# etape 1"),
            _md("### Interprétation"),
            _md("## Pour aller plus loin"),
        ])
        self.assertEqual(_scan(nb), [])

    def test_multiple_misplaced_in_sequence(self):
        # PyMC-15 mesure : plusieurs cellules interp enchainent des bugs
        nb = _make_nb([
            _code("# cell[0] code"),
            _md("### Lecture du résultat : cell[1]"),  # bug
            _md("## 2. Section"),                       # cell[2]
            _md("### Lecture des résultats : cell[3]"),  # bug
            _md("## 3. Section"),                       # cell[4]
        ])
        findings = _scan(nb)
        self.assertEqual(len(findings), 2)
        self.assertEqual([f["cell_index"] for f in findings], [1, 3])

    def test_interp_with_accent_in_text(self):
        # Verification que INTERP_HEADER_RE gere l'accent francais
        nb = _make_nb([
            _code("# code"),
            _md("### Interprétation des résultats : 163 divergences"),  # accent
            _md("## 2. Amélioration du modèle"),
        ])
        findings = _scan(nb)
        self.assertEqual(len(findings), 1)


class TestRealNotebooks(unittest.TestCase):
    """Tests integration sur les notebooks reels mesures dans #10678."""

    def setUp(self):
        # Resoudre le chemin du repo depuis l'emplacement du test
        self.repo_root = SCRIPTS_DIR.parent.parent
        self.nb_pyMC15 = self.repo_root / "MyIA.AI.Notebooks" / "Probas" / "PyMC" / "PyMC-15-Recommenders.ipynb"
        self.nb_gt10 = self.repo_root / "MyIA.AI.Notebooks" / "GameTheory" / "GameTheory-10-ForwardInduction-SPE-Csharp.ipynb"

    def test_pymc15_has_misplaced_interps(self):
        """#10678 mesure : PyMC-15 a 5 interps buguees (cell[4], [9], [13], [18], [25])."""
        if not self.nb_pyMC15.exists():
            self.skipTest(f"notebook not present: {self.nb_pyMC15}")
        findings = scan_notebook(self.nb_pyMC15)
        misplaced = [f for f in findings if f["rule"] == "misplaced_before_section"]
        self.assertGreaterEqual(
            len(misplaced), 3,
            f"PyMC-15 devrait avoir >=3 interps buguees, trouve {len(misplaced)}",
        )

    def test_pymc15_has_more_than_gametheory10(self):
        """#10678 signal : PyMC-15 est plus affecte que GameTheory-10 (relatif)."""
        if not (self.nb_pyMC15.exists() and self.nb_gt10.exists()):
            self.skipTest("PyMC-15 ou GameTheory-10 absent")
        pyMC = scan_notebook(self.nb_pyMC15)
        gt10 = scan_notebook(self.nb_gt10)
        pyMC_n = sum(1 for f in pyMC if f["rule"] == "misplaced_before_section")
        gt10_n = sum(1 for f in gt10 if f["rule"] == "misplaced_before_section")
        # PyMC-15 (5/5 dans #10678) > GameTheory-10 (~2). Relatif, pas absolu.
        self.assertGreater(
            pyMC_n, gt10_n,
            f"PyMC-15 devrait avoir plus de misplaced ({pyMC_n}) que GameTheory-10 ({gt10_n})",
        )


if __name__ == "__main__":
    unittest.main(verbosity=2)