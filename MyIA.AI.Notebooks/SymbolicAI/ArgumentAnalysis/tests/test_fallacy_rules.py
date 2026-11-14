"""Tests de structure de l'organe fallacy_rules (purs, sans spaCy).

Lance : python tests/test_fallacy_rules.py  (depuis le dossier de la serie).
La validation EXECUTEE des motifs spaCy (detect_fallacies sur exemples
français) vit dans le notebook de la serie, commite avec ses outputs.
"""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import fallacy_rules as fr


class TestComptesMesures(unittest.TestCase):
    """Comptes recomptés — alignés sur la consolidation du cœur (13 motifs)."""

    def test_13_motifs_sophismes(self):
        self.assertEqual(fr.rule_counts()["fallacy_motifs"], 13)

    def test_5_cles_5_familles(self):
        counts = fr.rule_counts()
        self.assertEqual(counts["rule_keys"], 5)
        self.assertEqual(counts["families"], 5)

    def test_mining_2_claims_2_premisses(self):
        counts = fr.rule_counts()
        self.assertEqual(counts["claim_motifs"], 2)
        self.assertEqual(counts["premise_motifs"], 2)

    def test_4_gabarits_de_justification(self):
        self.assertEqual(fr.rule_counts()["justification_templates"], 4)


class TestStructure(unittest.TestCase):
    def test_aucune_spec_op_seule(self):
        # Divergence conservee : toute spec nue {"OP": ...} est normalisee.
        self.assertEqual(fr.validate_patterns(), [])

    def test_chaque_motif_porte_une_etiquette(self):
        for key, motifs in fr.FALLACY_RULES.items():
            for motif in motifs:
                self.assertIn("PATTERN", motif)
                self.assertIn("FALLACY_TYPE", motif)
                self.assertTrue(motif["PATTERN"])

    def test_etiquettes_coherentes_avec_familles(self):
        for family, keys in fr.FAMILY_KEYS.items():
            label_attendu = fr.FALLACY_LABELS[family]
            for key in keys:
                for motif in fr.FALLACY_RULES[key]:
                    self.assertEqual(motif["FALLACY_TYPE"], label_attendu)

    def test_index_familles_couvre_toutes_les_cles(self):
        toutes = {k for keys in fr.FAMILY_KEYS.values() for k in keys}
        self.assertEqual(toutes, set(fr.FALLACY_RULES.keys()))

    def test_cles_non_accentuees_comme_le_coeur(self):
        # Re-fondation : les cles portent le nom du coeur, sans accents.
        toutes = set(fr.FALLACY_RULES.keys()) | {k for keys in fr.FAMILY_KEYS.values() for k in keys}
        for cle in toutes:
            self.assertEqual(cle, cle.encode("ascii", "ignore").decode(), f"cle accentuee: {cle}")


class TestReparationsG4(unittest.TestCase):
    """G4 (#1186) : les deux motifs que le coeur a restaures en les corrigeant."""

    def test_ad_hominem_a_le_slot_de_ponctuation(self):
        motif = fr.FALLACY_RULES["AD_HOMINEM_DIRECT"][2]["PATTERN"]
        ponctuations = [s for s in motif if s.get("IS_PUNCT") is True]
        self.assertEqual(len(ponctuations), 1)
        self.assertEqual(ponctuations[0].get("OP"), "?")

    def test_generalisation_sans_slot_noun_surnumeraire(self):
        motif = fr.FALLACY_RULES["GENERALISATION_HATIVE"][1]["PATTERN"]
        # "exemples" est le NOUN : aucun slot NOUN autonome ne doit preceder.
        self.assertEqual(motif[-1], {"LOWER": "exemples"})
        self.assertNotIn({"POS": "NOUN"}, motif)

    def test_autorite_est_une_cle_unique(self):
        self.assertIn("ARGUMENT_AUTORITE", fr.FALLACY_RULES)
        self.assertNotIn("ARGUMENT_D_AUTORITE_GENERAL", fr.FALLACY_RULES)
        self.assertEqual(len(fr.FALLACY_RULES["ARGUMENT_AUTORITE"]), 2)


class TestJustificationsG5(unittest.TestCase):
    """G5 (#1186) : justification par famille, fail-loud (#1019)."""

    # Le coeur porte 4 gabarits, herites du projet etudiant, dont la
    # taxonomie nommait 4 familles. Deux familles de cet organe n'y ont pas
    # de gabarit : la resolution rend None (fail-loud #1019), jamais une
    # justification generique fabriquee.
    FAMILLES_SANS_GABARIT = {"PENTE_GLISSANTE", "APPEL_A_LA_TRADITION"}

    def test_resolution_par_famille(self):
        couvertes = []
        for famille, label in fr.FALLACY_LABELS.items():
            justification = fr.justify_fallacy(label)
            if famille in self.FAMILLES_SANS_GABARIT:
                self.assertIsNone(justification, famille)
            else:
                self.assertIsNotNone(justification, famille)
                couvertes.append(famille)
        self.assertEqual(len(couvertes), 3)

    def test_fail_loud_sur_famille_inconnue(self):
        self.assertIsNone(fr.justify_fallacy("Sophisme imaginaire"))
        self.assertIsNone(fr.justify_fallacy(""))

    def test_resolution_par_sous_chaine_non_symbolique(self):
        # Un etage non symbolique peut rendre une etiquette d'une autre
        # taxonomie : la resolution par sous-chaine la couvre.
        self.assertIsNotNone(fr.justify_fallacy("Appel à l'émotion"))


class TestJoker(unittest.TestCase):
    def test_wildcard_semantique_inchangee(self):
        spec = fr._wildcard("+")
        self.assertEqual(spec["OP"], "+")
        self.assertIn("TEXT", spec)


if __name__ == "__main__":
    unittest.main(verbosity=2)