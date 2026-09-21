#!/usr/bin/env python3
"""Unit tests for repair_morpho -- organe canonique de correction morphologique.

Couvre :
- is_prouve_legitimate : auxiliaire 2+ chars (Tell c.1315-L12 fondateur)
- is_donne_legitimate : locution etant donne / tant donne (Tell c.1317-L7 ★★★★ fondateur)
- _scan_cell_source : detection des formes accentuees fautives (REACCENT upstream)
- repair_notebook : list-edit preservant source[] (Tell c.1343-L1 ★★★★★ fondateur)
- repair_notebook : byte-identique newline terminal (Tell c.1331-L5 ★★★★ fondateur)
- controle positif : notebook contamine (REACCENT upstream fautif) -- il doit
  detecter et reparer les occurrences fautives, laisser les participes
  legitimes (apres auxiliaire) et les locutions (etant donne).
- dry_run : mesure l'impact sans toucher au disque (Tell c.1340-L3 ★★★ fondateur)

Run : python scripts/notebook_tools/test_repair_morpho.py
"""
from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPTS_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS_DIR))

from repair_morpho import (  # noqa: E402
    MorphoFinding,
    MorphoReport,
    _normalize,
    _scan_cell_source,
    is_donne_legitimate,
    is_prouve_legitimate,
    repair_notebook,
    scan_notebook,
)


# --- Helpers de fabrication de notebooks -------------------------------------


def _make_nb(cells: list) -> dict:
    return {
        "cells": cells,
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }


def _md_str(text: str) -> dict:
    """Cellule markdown avec source = string (pas list)."""
    return {"cell_type": "markdown", "metadata": {}, "source": text}


def _md_list(items: list) -> dict:
    """Cellule markdown avec source = list (chaque item sauf dernier termine par \n)."""
    return {"cell_type": "markdown", "metadata": {}, "source": items}


def _code(text: str = "# code") -> dict:
    return {"cell_type": "code", "metadata": {}, "source": text}


def _write_nb(nb: dict, path: Path) -> None:
    """Ecrit un notebook byte-identique (Tell c.1331-L5 ★★★★ fondateur)."""
    raw = json.dumps(nb, ensure_ascii=False, indent=1).encode("utf-8")
    path.write_bytes(raw)


# --- Tests invariants de detection ------------------------------------------


class TestAuxiliaires(unittest.TestCase):
    """Verifie les discriminants morphologiques (auxiliaires, locutions)."""

    def test_est_prouve_legitime(self):
        """apres 'est' (auxiliaire 3e pers. etre), prouve est legitime."""
        self.assertTrue(is_prouve_legitimate("Le theoreme est "))

    def test_ete_prouve_legitime(self):
        """apres 'ete' (participe passe etre), prouve est legitime."""
        self.assertTrue(is_prouve_legitimate("Cela a ete "))

    def test_le_prouve_fautif(self):
        """apres 'le' (article), prouve est faute (verbe 3e pers.)."""
        self.assertFalse(is_prouve_legitimate("Tao le "))

    def test_on_prouve_fautif(self):
        """apres 'on' (pronom), prouve est faute."""
        self.assertFalse(is_prouve_legitimate("on "))

    def test_se_prouve_toujours_fautif(self):
        """cf Tell c.1315-L15 ★★★ fondateur : 'se prouve' toujours fautif."""
        self.assertFalse(is_prouve_legitimate("se "))

    def test_a_1char_ambigu(self):
        """'a' (1 char) est ambigu avec article -- on l'exige pas comme auxiliaire."""
        # 'Cela a prouve' : 'a' est auxiliaire mais 1 char -> exclu (Tell c.1315-L16)
        # Mais en realite 'a' est l'auxiliaire 3e pers. avoir, et 'a prouve' est legitime.
        # On documente l'invariant : on accepte PAS 'a' 1 char pour eviter le bruit.
        # Comportement actuel : False (exclu volontairement).
        self.assertFalse(is_prouve_legitimate("Cela a "))

    def test_etant_donne_legitime(self):
        """'etant donne' = locution figee, donne est legitime."""
        self.assertTrue(is_donne_legitimate(
            "Etant donne les contraintes, le probleme est complexe. On "))

    def test_tant_donne_avec_intercalation(self):
        """'tant donne' avec mots intercalés OK (Tell c.1317-L7 ★★★★ fondateur)."""
        self.assertTrue(is_donne_legitimate(
            "Pour un theoreme qui est tant donne, le cluster "))

    def test_sup_donne_fautif(self):
        """apres 'Le sup', donne est faute (verbe 3e pers.)."""
        self.assertFalse(is_donne_legitimate("Le sup "))

    def test_cluster_donne_fautif(self):
        """apres 'le cluster', donne est faute."""
        self.assertFalse(is_donne_legitimate("le cluster "))


# --- Tests de scan d'une cellule ---------------------------------------------


class TestScanCellSource(unittest.TestCase):
    """Le scanner detecte les formes ACCENTUEES fautives (REACCENT upstream)."""

    def test_prouve_legitime_apres_est_non_signale(self):
        """'il est prouve' (legitime) -> 0 finding."""
        findings = _scan_cell_source(0, "Le theoreme est prouve dans le manuel.")
        self.assertEqual(findings, [])

    def test_prouve_fautif_signale(self):
        """'Tao le prouve' (fautif : verbe 3e pers. accentue par REACCENT upstream) -> 1 finding prouve."""
        findings = _scan_cell_source(0, "Tao le prouvé en passant par le lemme 4.")
        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0].word, "prouvé")
        self.assertEqual(findings[0].suggested, "prouve")

    def test_donne_dans_locution_non_signale(self):
        """'etant donne que...' -> 0 finding."""
        findings = _scan_cell_source(0, "Etant donne que le probleme est complexe, on propose X.")
        self.assertEqual(findings, [])

    def test_donne_fautif_signale(self):
        """'Le sup donné le x' (defaut REACCENT upstream : verbe 3e pers. accentue) -> 1 finding donné."""
        findings = _scan_cell_source(0, "Le sup donné le x voulu par le theoreme.")
        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0].word, "donné")
        self.assertEqual(findings[0].suggested, "donne")

    def test_decide_jamais_signale(self):
        """Invariant map REACCENT upstream : 'decide' ne doit JAMAIS etre signale."""
        findings = _scan_cell_source(0, "Si vous etes un agent qui decide du mode.")
        self.assertEqual(findings, [])

    def test_multiples_occurrences(self):
        """3 'prouve' fautifs (defaut REACCENT upstream) + 1 legitime = 3 findings."""
        text = (
            "Tao les prouvé. "
            "Le theoreme est prouvé par Tao. "  # legitime (apres auxiliaire 'est')
            "Tao le prouvé. "
            "on prouvé qu'un algorithme."
        )
        findings = _scan_cell_source(0, text)
        self.assertEqual(len(findings), 3)
        self.assertEqual(findings[0].word, "prouvé")


# --- Tests de repair (list-edit + byte-identique) ---------------------------


class TestRepairByteIdentique(unittest.TestCase):
    """Le repair preserve source[] (list-edit) + newline terminal (Tell c.1331-L5)."""

    def test_list_edit_preserve_structure(self):
        """Modifier un item ne doit pas re-serialiser toute la liste."""
        # Source = list de 3 items
        cell = _md_list([
            "Ligne 1 avec prouvé fautif.\n",
            "Ligne 2 avec donné fautif.\n",
            "Ligne 3 sans faute.",
        ])
        # Faire le repair directement (sans passer par la fonction complete)
        from repair_morpho import repair_notebook
        with tempfile.TemporaryDirectory() as tmpdir:
            path = Path(tmpdir) / "test.ipynb"
            _write_nb(_make_nb([cell]), path)
            r = repair_notebook(path, dry_run=False)
            # Au moins 2 cells modifiees (mais c'est 1 cellule avec 2 corrections)
            self.assertEqual(r.cells_modified, 1)
            # Verifier que la liste a toujours 3 items (list-edit preserve)
            nb = json.loads(path.read_bytes().decode("utf-8"))
            src = nb["cells"][0]["source"]
            self.assertIsInstance(src, list)
            self.assertEqual(len(src), 3)
            # Le \n final de chaque item sauf le dernier est preserve
            self.assertTrue(src[0].endswith("\n"))
            self.assertTrue(src[1].endswith("\n"))
            self.assertFalse(src[2].endswith("\n"))

    def test_newline_terminal_preserve_avec_final(self):
        """Notebook termine par \\n -> repair preserve."""
        cell = _md_list(["Tao le prouvé.\n"])
        from repair_morpho import repair_notebook
        with tempfile.TemporaryDirectory() as tmpdir:
            path = Path(tmpdir) / "test.ipynb"
            raw = json.dumps(_make_nb([cell]), ensure_ascii=False, indent=1).encode("utf-8") + b"\n"
            path.write_bytes(raw)
            self.assertTrue(path.read_bytes().endswith(b"\n"))
            r = repair_notebook(path, dry_run=False)
            self.assertGreater(r.cells_modified, 0)
            self.assertTrue(path.read_bytes().endswith(b"\n"),
                            "newline terminal perdu apres repair")

    def test_newline_terminal_preserve_sans_final(self):
        """Notebook SANS \\n final -> repair preserve (pas d'ajout)."""
        cell = _md_list(["Tao le prouvé.\n"])
        from repair_morpho import repair_notebook
        with tempfile.TemporaryDirectory() as tmpdir:
            path = Path(tmpdir) / "test.ipynb"
            raw = json.dumps(_make_nb([cell]), ensure_ascii=False, indent=1).encode("utf-8")
            path.write_bytes(raw)
            self.assertFalse(path.read_bytes().endswith(b"\n"))
            r = repair_notebook(path, dry_run=False)
            self.assertGreater(r.cells_modified, 0)
            self.assertFalse(path.read_bytes().endswith(b"\n"),
                             "newline terminal ajoute la ou il n'y en avait pas")

    def test_dry_run_ne_touche_pas_le_disque(self):
        """dry_run=True doit mesurer sans modifier (Tell c.1340-L3 ★★★ fondateur)."""
        cell = _md_list(["Tao le prouvé.\n"])
        from repair_morpho import scan_notebook
        with tempfile.TemporaryDirectory() as tmpdir:
            path = Path(tmpdir) / "test.ipynb"
            _write_nb(_make_nb([cell]), path)
            sha_before = path.read_bytes()
            r = scan_notebook(path)
            self.assertTrue(r.dry_run)
            self.assertGreater(len(r.findings), 0)
            self.assertEqual(r.cells_modified, 0)
            self.assertEqual(path.read_bytes(), sha_before,
                             "dry_run a modifie le fichier !")


# --- Controle positif : notebook contamine (defaut REACCENT upstream) -------


class TestControlePositifReaccentUpstream:
    """Controle positif : un notebook contamine par REACCENT upstream fautif
    doit etre detecte + repare, avec preservation des formes legitimes."""

    def test_notebook_contamine(self):
        # Construit un notebook avec un melange de fautes upstream (formes accentuees
        # ajoutées par REACCENT fautif) et de formes legitimes -- comme une
        # contamination REACCENT reelle sur Lean-*.
        cell = _md_str(
            "Tao le prouvé en passant. "                    # prouvé fautif (verbe)
            "Le theoreme localement prouvé est interessant. "  # prouvé discutable (adverbe)
            "Le resultat est prouvé par une machine. "        # prouvé legitime (auxiliaire)
            "Etant donné les contraintes, on propose X. "     # donné legitime (locution)
            "Le sup donné le x. "                             # donné fautif (verbe)
            "Si vous décidez du mode : "                      # décide legitime (verbe)
            "on décide alors de proceder.\n"                  # décide fautif (verbe)
        )
        with tempfile.TemporaryDirectory() as tmpdir:
            path = Path(tmpdir) / "contamine.ipynb"
            _write_nb(_make_nb([cell]), path)
            # Scan : on doit trouver au moins les fautes evidentes
            report = scan_notebook(path)
            words_found = {f.word for f in report.findings}
            self.assertIn("prouvé", words_found,
                          "le prouvé fautif (verbe 3e pers.) doit etre signale")
            self.assertIn("donné", words_found,
                          "le sup donné fautif doit etre signale")
            # 'décide' ne doit JAMAIS etre signale (invariant map upstream)
            self.assertNotIn("décide", words_found,
                             "décide ne doit jamais etre signale (map upstream)")

            # Repair : on verifie que les corrections sont appliquees
            r = repair_notebook(path, dry_run=False)
            self.assertGreater(r.cells_modified, 0)
            repaired = path.read_bytes().decode("utf-8")
            # 'le prouvé en passant' doit devenir 'le prouve en passant' (sans accent)
            self.assertIn("Tao le prouve en passant", repaired,
                          "'le prouvé' doit etre corrige (accent retire)")
            # 'est prouvé par' doit etre preserve
            self.assertIn("est prouvé par", repaired,
                          "'est prouvé' legitime doit etre preserve")
            # 'Etant donné' doit etre preserve
            self.assertIn("Etant donné", repaired,
                          "locution 'etant donné' doit etre preservee")
            # 'Le sup donné' doit etre corrige -> 'Le sup donne'
            self.assertIn("Le sup donne", repaired,
                          "'Le sup donné' doit etre corrige (accent retire)")


# --- Integration : notebook reel --------------------------------------------


class TestIntegrationLean19:
    """Integration : Lean-19 post-REPAIR-5 doit montrer un residu fautif."""

    def test_lean19_residu(self):
        """Lean-19 actuel (post-REPAIR-5 #16993 merge) contient 1 résidu fautif."""
        from repair_morpho import scan_notebook
        nb_path = Path("MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-19-Analysis-I-Tao-Workflow.ipynb")
        if not nb_path.exists():
            self.skipTest(f"{nb_path} introuvable (worktree ?)")
        report = scan_notebook(nb_path)
        # Au moins 1 résidu fautif (le REPAIR-5 a rate 'localement prouve')
        words_found = {f.word for f in report.findings}
        # Soit 'prouve' fautif soit donne fautif (residuel)
        self.assertGreater(len(report.findings), 0,
                           "Lean-19 doit avoir au moins 1 résidu fautif post-REPAIR-5")


if __name__ == "__main__":
    unittest.main(verbosity=2)
