#!/usr/bin/env python3
"""Unit tests for check_interp_positioning.

Couvre les invariants de la regle de detection :
- INTERP_HEADER_RE reconnait les 4 variantes documentees
- _is_legit_following_header couvre Exercices / Conclusion / Pour aller plus loin,
  numerotes (`## 7. Exercices`) comme non numerotes
- _is_anchored_to_code : code avant l'interp dans sa section => pas un defaut
- _stable_finding_hash est deterministe + depend de l'index
- scan_notebook OK: interp suivie d'un code cell
- scan_notebook OK: interp suivie de ## Exercices (transition legitime)
- scan_notebook OK: code -> interp -> ## N. Section suivante (placement CANONIQUE)
- scan_notebook BUG: interp parachutee entre deux headers, sans code dans sa section
- scan_notebook OK: interp en fin de notebook (pas de cellule suivante)
- Integration : 3 pins de non-regression FP (GameTheory-16, Aspire-01, Z3-09,
  les notebooks que le gate a fait echouer a tort) + 1 pin de detection reelle
  (PyMC-15 cell#9)

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
    _is_section_boundary,
    _is_section_header,
    _stable_finding_hash,
    _top_level,
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

    def test_numbered_prefix_accepted(self):
        # Forme DOMINANTE dans CoursIA. Sans le prefixe optionnel dans la
        # whitelist, `## 7. Exercices` etait signale comme defaut (FP mesure
        # sur GameTheory-16 cell#46, run CI 31769853464).
        self.assertTrue(_is_legit_following_header("## 7. Exercices"))
        self.assertTrue(_is_legit_following_header("### 4.2 Conclusion"))
        self.assertTrue(_is_legit_following_header("## 8. Pour aller plus loin"))
        self.assertTrue(_is_legit_following_header("### 9. Références"))

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


class TestTopLevelAndBoundary(unittest.TestCase):
    """Niveau structurel relatif du notebook (correctif #10910).

    La condition 4 arrete la remontee sur un header de niveau `<=` au niveau
    structurel du notebook (`_top_level`), PAS sur tout `###` : un sous-header
    plus profond que la structure appartient a la MEME section.
    """

    def test_top_level_h2_notebook(self):
        cells = [
            _md("## 1. Section"),
            _md("### 1.1 Sous-section"),
            _md("### 1.2 Sous-section"),
        ]
        self.assertEqual(_top_level(cells), 2)

    def test_top_level_h3_only_notebook(self):
        # Notebook entierement en ### (cas QC-Py-08 / #10785) : le niveau
        # structurel est 3, pas 2 -- sinon le guard serait desarme.
        cells = [
            _md("### 1. Section"),
            _md("### 1.1 Sous-section"),
            _md("### 2. Section"),
        ]
        self.assertEqual(_top_level(cells), 3)

    def test_top_level_default_when_no_header(self):
        cells = [_md("paragraphe"), _md("liste")]
        self.assertEqual(_top_level(cells), 2)

    def test_top_level_ignores_code_and_plain_md(self):
        cells = [_code("# code"), _md("## 1. Section"), _md("texte libre")]
        self.assertEqual(_top_level(cells), 2)

    def test_boundary_stops_on_top_level(self):
        self.assertTrue(_is_section_boundary("## 1. Section", top=2))
        self.assertTrue(_is_section_boundary("### 1. Section", top=3))

    def test_boundary_ignores_deeper_than_top(self):
        # Dans un notebook structure en ##, un ### n'est PAS une frontiere.
        self.assertFalse(_is_section_boundary("### 1.1 Sous-section", top=2))

    def test_boundary_rejects_non_header(self):
        self.assertFalse(_is_section_boundary("paragraphe", top=2))
        self.assertFalse(_is_section_boundary("# Titre", top=2))


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

    def test_interp_anchored_across_sibling_subheader(self):
        """Acceptance 2(a) : code -> ### sous-header -> interp -> ## header.

        Cas de 03-Voting-Methods cell#4..7 (#10910) : le sous-header `###`
        entre le code et l'interp est DANS la meme section (notebook structure
        en `##`) -- la remontee de la condition 4 doit le traverser et
        atteindre le code, donc ABSOUDRE l'interp.
        """
        nb = _make_nb([
            _md("## 1. Methode de vote"),                 # cell[0]
            _code("# duels pairwise"),                    # cell[1]
            _md("### Cycle de Condorcet"),                # cell[2] sous-header frere
            _md("### Interprétation : majorite intransitive"),  # cell[3]
            _md("## 2. Gagnant de Condorcet"),            # cell[4]
        ])
        self.assertEqual(_scan(nb), [])


class TestScanNotebookBuggyCases(unittest.TestCase):
    """Le defaut vise : une interp PARACHUTEE entre deux headers.

    Forme caracteristique -- il n'y a AUCUNE cellule code entre le header qui
    ouvre la section et l'interp, donc l'interp n'a rien a interpreter la ou
    elle se trouve :

        ## 1. Section
        [prose eventuelle]
        ### Lecture du resultat : ...   <- parachutee, aucun code au-dessus
        ## 2. Section suivante

    A ne PAS confondre avec `code -> interp -> header suivant`, qui est le
    placement CANONIQUE (cf TestScanNotebookOkCases + condition 4).
    """

    def test_interp_parachuted_before_new_h2_section(self):
        nb = _make_nb([
            _md("## 1. Section"),
            _md("### Lecture du résultat : convergence OK"),  # cell[1] misplaced
            _md("## 2. Section suivante"),                    # cell[2]
            _code("# code section suivante"),
        ])
        findings = _scan(nb)
        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0]["rule"], "misplaced_before_section")
        self.assertEqual(findings[0]["cell_index"], 1)

    def test_interp_parachuted_before_h3_subsection(self):
        nb = _make_nb([
            _md("## 1. Section"),
            _md("### Interprétation des résultats"),  # cell[1] misplaced
            _md("### 1. Sous-section"),                # cell[2]
        ])
        findings = _scan(nb)
        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0]["cell_index"], 1)

    def test_interp_parachuted_in_h3_only_notebook(self):
        """Acceptance 2(d) : notebook SANS aucun `##` (100% `###`).

        Cas QC-Py-08 / #10785 : le niveau structurel est 3, donc `###` EST la
        frontiere. Code -> ### orphelin -> interp -> ### : la remontee
        s'arrete sur le ### orphelin avant le code -> toujours flagge.
        """
        nb = _make_nb([
            _md("### 1. Section"),                       # cell[0] top=3
            _code("# code de la section"),               # cell[1]
            _md("### bloc orphelin"),                    # cell[2] frontiere
            _md("### Interprétation des données"),       # cell[3] misplaced
            _md("### 2. Section suivante"),              # cell[4]
        ])
        findings = _scan(nb)
        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0]["cell_index"], 3)

    def test_interp_followed_by_pour_aller_plus_loin_excluded(self):
        # "Pour aller plus loin" est legitime -> pas un bug
        nb = _make_nb([
            _md("## 1. Section"),
            _md("### Interprétation"),
            _md("## Pour aller plus loin"),
        ])
        self.assertEqual(_scan(nb), [])

    def test_multiple_misplaced_in_sequence(self):
        # Deux interps parachutees d'affilee, chacune ouvrant sa section
        nb = _make_nb([
            _md("## 1. Section"),                        # cell[0]
            _md("### Lecture du résultat : cell[1]"),    # bug
            _md("## 2. Section"),                        # cell[2]
            _md("### Lecture des résultats : cell[3]"),  # bug
            _md("## 3. Section"),                        # cell[4]
        ])
        findings = _scan(nb)
        self.assertEqual(len(findings), 2)
        self.assertEqual([f["cell_index"] for f in findings], [1, 3])

    def test_interp_with_accent_in_text(self):
        # Verification que INTERP_HEADER_RE gere l'accent francais
        nb = _make_nb([
            _md("## 1. Section"),
            _md("### Interprétation des résultats : 163 divergences"),  # accent
            _md("## 2. Amélioration du modèle"),
        ])
        findings = _scan(nb)
        self.assertEqual(len(findings), 1)

    def test_code_in_section_disarms_the_finding(self):
        """Meme sequence que ci-dessus + une cellule code dans la section.

        C'est la ligne de partage de la condition 4 : le seul ajout d'un code
        cell entre le header et l'interp fait passer le verdict de misplaced a
        correctement ancre.
        """
        nb = _make_nb([
            _md("## 1. Section"),
            _code("# ce code produit l'output commente juste apres"),
            _md("### Lecture du résultat : convergence OK"),
            _md("## 2. Section suivante"),
        ])
        self.assertEqual(_scan(nb), [])


class TestRealNotebooks(unittest.TestCase):
    """Integration sur des notebooks reels -- pins de non-regression c.95.

    Les 3 premiers pins sont les notebooks que le gate a REELLEMENT fait
    echouer (run 31769853464, PR #10856, 2026-08-14) : trois interps
    correctement ancrees a un code cell, signalees a tort, bloquant toute PR
    de contenu notebook. Ils doivent rester a 0.

    Le 4e pin (PyMC-15 cell#9) prouve que le detecteur n'est pas devenu
    aveugle : ce notebook garde son defaut reel -- deux cellules interp
    consecutives, la seconde n'ayant aucun code dans sa section.
    """

    def setUp(self):
        self.repo_root = SCRIPTS_DIR.parent.parent

    def _misplaced(self, relpath: str) -> list[dict] | None:
        nb = self.repo_root / relpath
        if not nb.exists():
            return None
        return [f for f in scan_notebook(nb) if f["rule"] == "misplaced_before_section"]

    def test_gametheory16_numbered_exercices_is_not_a_finding(self):
        """`## 7. Exercices` est une transition legitime -- le prefixe numerote aussi."""
        found = self._misplaced("MyIA.AI.Notebooks/GameTheory/GameTheory-16-MechanismDesign.ipynb")
        if found is None:
            self.skipTest("GameTheory-16 absent")
        self.assertEqual(found, [], f"FP c.95 reintroduit : {found}")

    def test_aspire01_interps_anchored_to_code_are_not_findings(self):
        """cell#12 (code a 3 outputs) et cell#17 (7 outputs) : ancrees, donc OK."""
        found = self._misplaced("MyIA.AI.Notebooks/GenAI/Aspire/01-Aspire-Orchestration-GenAi.ipynb")
        if found is None:
            self.skipTest("Aspire-01 absent")
        self.assertEqual(found, [], f"FP c.95 reintroduit : {found}")

    def test_z3_meal_planner_interp_anchored_to_code_is_not_a_finding(self):
        """cell#18 suit un code a 5 outputs -- placement canonique."""
        found = self._misplaced(
            "MyIA.AI.Notebooks/SymbolicAI/SMT/Z3-Linq2Z3/09_Meal_Planner_Convergence_Scale.ipynb"
        )
        if found is None:
            self.skipTest("Z3-09 absent")
        self.assertEqual(found, [], f"FP c.95 reintroduit : {found}")

    def test_pymc15_repaired_is_clean(self):
        """PyMC-15 a ete repare sur main (#10687 + #10876) : 0 finding.

        Le pin de detection reelle de c.95 (cell#9) est obsolete -- le
        notebook a depuis ete reordonne. La non-cecite du detecteur est
        couverte par les cas synthetiques (parachute entre deux headers) et
        par les findings live de la baseline.
        """
        found = self._misplaced("MyIA.AI.Notebooks/Probas/PyMC/PyMC-15-Recommenders.ipynb")
        if found is None:
            self.skipTest("PyMC-15 absent")
        self.assertEqual(found, [], "PyMC-15 ne doit plus avoir de finding (repare c.96)")


if __name__ == "__main__":
    unittest.main(verbosity=2)