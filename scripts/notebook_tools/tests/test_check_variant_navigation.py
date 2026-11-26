#!/usr/bin/env python3
"""Tests unitaires de check_variant_navigation.

Couvre les controles demandes par l'EPIC #28763 (premiere tranche) :
« Tester aussi une variante absente et une reference cassee », plus la
derivation du type de correspondance et les cas de non-concordance
(type annonce != type deduit, noyau annonce != kernelspec reel).

Fixture : un mini-depot temporaire avec
  - un registre (une paire attestee, une paire non attestee) ;
  - deux repertoires de variantes (Infer / PyMC) ;
  - un README de navigation qui annonce les paires ;
  - des carnets dont l'en-tete porte le bloc canonique « Variante jumelle ».

Run : python scripts/notebook_tools/tests/test_check_variant_navigation.py
"""
from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPTS_DIR = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SCRIPTS_DIR))

from check_variant_navigation import (  # noqa: E402
    TYPE_COMPLEMENT,
    TYPE_EQUIVALENCE,
    TYPE_PROGRESSION,
    derive_correspondence,
    notion_key,
    verify,
)

FAMILY = "Probas/Infer.NET-PyMC"
PY_DIR = "MyIA.AI.Notebooks/Probas/PyMC"
CS_DIR = "MyIA.AI.Notebooks/Probas/Infer"

PY_NOTEBOOK = f"{PY_DIR}/PyMC-01-Setup.ipynb"
CS_NOTEBOOK = f"{CS_DIR}/Infer-01-Setup.ipynb"

ENTRY = f"""- name: Probas-1 Setup
  family: {FAMILY}
  python: {PY_NOTEBOOK}
  csharp: {CS_NOTEBOOK}
  parity_level: native-both
  bridge_verdict: SOTA-OK
  known_differences:
  - "Moteurs d inference distincts."
"""

AUDIT = """- index: 0001
  date: 2026-11-26
  lane: myia-po-2026:CoursIA-2
  verdict: attested
"""


def _nb(source: str = "# carnet", kernel: str = "python3") -> dict:
    return {
        "cells": [{"cell_type": "markdown", "metadata": {}, "source": source}],
        "metadata": {"kernelspec": {"name": kernel}},
        "nbformat": 4,
        "nbformat_minor": 5,
    }


def _write_nb(path: Path, nb: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(nb, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")


class VariantNavigationFixture(unittest.TestCase):
    """Mini-depot : une paire attestee + une variante orpheline."""

    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.root = Path(self._tmp.name)
        self.registry = self.root / "registry"
        (self.registry / "probas-1-setup").mkdir(parents=True)
        (self.registry / "probas-1-setup.yaml").write_text(ENTRY, encoding="utf-8")
        (self.registry / "probas-1-setup" / "0001-audit.yaml").write_text(AUDIT, encoding="utf-8")

        # Cote Python : en-tete canonique pointant vers le jumeau C#.
        _write_nb(
            self.root / PY_NOTEBOOK,
            _nb(
                "# PyMC-01\n\n**Variante jumelle** : [Infer-01-Setup](../Infer/Infer-01-Setup.ipynb)"
                f" — correspondance : {TYPE_EQUIVALENCE} · noyau : `python3` (PyMC)\n"
            ),
        )
        # Cote C# : en-tete canonique vers le jumeau Python, noyau .net-csharp.
        _write_nb(
            self.root / CS_NOTEBOOK,
            _nb(
                "# Infer-01\n\n**Variante jumelle** : [PyMC-01-Setup](../PyMC/PyMC-01-Setup.ipynb)"
                f" — correspondance : {TYPE_EQUIVALENCE} · noyau : `.net-csharp` (Infer.NET)\n",
                kernel=".net-csharp",
            ),
        )
        # Variante orpheline : la notion 02 n'existe que cote Python.
        _write_nb(self.root / PY_DIR / "PyMC-02-Orpheline.ipynb", _nb("# PyMC-02\n"))

        # Surface de navigation : la ligne 01 annonce la paire, la ligne 02 une paire
        # qui n'est PAS attustee au registre.
        readme = self.root / "MyIA.AI.Notebooks/Probas/README.md"
        readme.parent.mkdir(parents=True, exist_ok=True)
        readme.write_text(
            "# Probas\n\n"
            "| 01 | [C#](Infer/Infer-01-Setup.ipynb) · [Python](PyMC/PyMC-01-Setup.ipynb) |\n"
            "| 02 | [C#](Infer/Infer-02-Non-Attestee.ipynb) · "
            "[Python](PyMC/PyMC-02-Non-Attestee.ipynb) |\n",
            encoding="utf-8",
        )
        self.surfaces = ("MyIA.AI.Notebooks/Probas/README.md",)

    def tearDown(self) -> None:
        self._tmp.cleanup()

    def _verify(self):
        findings, stats, _ = verify(
            self.root, self.registry, (FAMILY,), self.surfaces, ()
        )
        return findings, stats

    def _kinds(self, findings, kind):
        return [f for f in findings if f["kind"] == kind]


class TestVarianteAbsente(VariantNavigationFixture):
    def test_variante_absente_nommee(self):
        findings, _ = self._verify()
        absents = self._kinds(findings, "MISSING_VARIANT")
        self.assertTrue(absents, "la variante orpheline doit etre signalee")
        detail = " ".join(f["detail"] for f in absents)
        self.assertIn("02-Orpheline", detail)

    def test_variante_absente_est_advisory(self):
        """Une asymetrie de repertoire ne doit pas bloquer : elle se nomme."""
        findings, _ = self._verify()
        for f in findings:
            if f["kind"] == "MISSING_VARIANT":
                self.assertNotIn(f["kind"], ("BROKEN_LINK", "UNATTESTED_PAIR"))

    def test_equivalence_non_attestee_est_bloquante(self):
        """La ligne 02 annonce une paire absente du registre : finding bloquant."""
        findings, _ = self._verify()
        non_attestees = self._kinds(findings, "UNATTESTED_PAIR")
        self.assertTrue(non_attestees)
        detail = " ".join(f["detail"] for f in non_attestees)
        self.assertIn("Infer-02-Non-Attestee.ipynb", detail)

    def test_paire_attestee_ne_produit_pas_finding(self):
        findings, stats = self._verify()
        bloquants = [f for f in findings if f["kind"] != "MISSING_VARIANT"]
        self.assertEqual(
            [],
            [f for f in bloquants if "01-Setup" in f["detail"]],
            f"la paire attestee ne doit rien produire : {bloquants}",
        )
        self.assertGreaterEqual(stats["pairs_attested"], 1)


class TestReferenceCassee(VariantNavigationFixture):
    def test_lien_casse_dans_un_en_tete(self):
        py = self.root / PY_NOTEBOOK
        _write_nb(
            py,
            _nb(
                "# PyMC-01\n\n**Variante jumelle** : [Infer-01-Setup](../Infer/Infer-01-Inconnu.ipynb)"
                f" — correspondance : {TYPE_EQUIVALENCE} · noyau : `python3`\n"
            ),
        )
        findings, _ = self._verify()
        casses = self._kinds(findings, "BROKEN_LINK")
        self.assertTrue(casses, "un lien casse doit etre signale")
        self.assertIn("Infer-01-Inconnu", " ".join(f["detail"] for f in casses))


class TestNonConcordances(VariantNavigationFixture):
    def test_type_annonce_contredit_par_le_registre(self):
        """Le carnet annonce une equivalence la ou le registre n'atteste qu'une surface."""
        _write_nb(
            self.root / CS_NOTEBOOK,
            _nb(
                "# Infer-01\n\n**Variante jumelle** : [PyMC-01-Setup](../PyMC/PyMC-01-Setup.ipynb)"
                f" — correspondance : {TYPE_EQUIVALENCE} · noyau : `.net-csharp`\n",
                kernel=".net-csharp",
            ),
        )
        (self.registry / "probas-1-setup.yaml").write_text(
            ENTRY.replace("parity_level: native-both", "parity_level: surface"),
            encoding="utf-8",
        )
        findings, _ = self._verify()
        mm = self._kinds(findings, "TYPE_MISMATCH")
        self.assertTrue(mm, "le type annonce doit etre confronte au registre")
        self.assertIn(TYPE_PROGRESSION, " ".join(f["detail"] for f in mm))

    def test_noyau_annonce_contredit_par_le_kernelspec(self):
        py = self.root / PY_NOTEBOOK
        _write_nb(
            py,
            _nb(
                "# PyMC-01\n\n**Variante jumelle** : [Infer-01-Setup](../Infer/Infer-01-Setup.ipynb)"
                f" — correspondance : {TYPE_EQUIVALENCE} · noyau : `.net-csharp`\n",
                kernel="python3",
            ),
        )
        findings, _ = self._verify()
        km = self._kinds(findings, "KERNEL_MISMATCH")
        self.assertTrue(km, "un noyau annonce faux doit etre signale")
        self.assertIn("python3", " ".join(f["detail"] for f in km))


class TestDerivationDuType(unittest.TestCase):
    def test_equivalence_verifiee(self):
        entry = {
            "parity_level": "native-both",
            "bridge_verdict": "SOTA-OK",
            "python": "a.ipynb",
            "csharp": "b.ipynb",
            "audits": [{"index": "0001"}],
        }
        self.assertEqual(TYPE_EQUIVALENCE, derive_correspondence(entry))

    def test_meme_progression(self):
        entry = {
            "parity_level": "surface",
            "bridge_verdict": "SOTA-OK",
            "python": "a.ipynb",
            "csharp": "b.ipynb",
            "audits": [{"index": "0001"}],
        }
        self.assertEqual(TYPE_PROGRESSION, derive_correspondence(entry))

    def test_complement_quand_un_seul_cote(self):
        entry = {"parity_level": "native-both", "bridge_verdict": "SOTA-OK", "python": "a.ipynb"}
        self.assertEqual(TYPE_COMPLEMENT, derive_correspondence(entry))

    def test_indetermine_sans_audit(self):
        """Sans enregistrement d'audit, aucune equivalence ne peut etre annoncee."""
        entry = {
            "parity_level": "native-both",
            "bridge_verdict": "SOTA-OK",
            "python": "a.ipynb",
            "csharp": "b.ipynb",
        }
        self.assertIsNone(derive_correspondence(entry))


class TestCleDeNotion(unittest.TestCase):
    def test_cle_commune_aux_deux_cotes(self):
        dirs = (PY_DIR, CS_DIR)
        self.assertEqual(
            notion_key(PY_NOTEBOOK, dirs), notion_key(CS_NOTEBOOK, dirs)
        )

    def test_cle_distincte_pour_des_notions_differentes(self):
        dirs = (PY_DIR, CS_DIR)
        self.assertNotEqual(
            notion_key(f"{PY_DIR}/PyMC-01-Setup.ipynb", dirs),
            notion_key(f"{CS_DIR}/Infer-02-Gaussian-Mixtures.ipynb", dirs),
        )


if __name__ == "__main__":
    unittest.main(verbosity=2)
