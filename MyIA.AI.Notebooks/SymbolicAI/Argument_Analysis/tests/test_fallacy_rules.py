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
    """Comptes recomptes sur le source (divergence 3 documentee)."""

    def test_15_motifs_sophismes(self):
        self.assertEqual(fr.rule_counts()["fallacy_motifs"], 15)

    def test_6_cles_5_familles(self):
        counts = fr.rule_counts()
        self.assertEqual(counts["rule_keys"], 6)
        self.assertEqual(counts["families"], 5)

    def test_mining_2_claims_3_premisses(self):
        counts = fr.rule_counts()
        self.assertEqual(counts["claim_motifs"], 2)
        self.assertEqual(counts["premise_motifs"], 3)


class TestStructure(unittest.TestCase):
    def test_aucune_spec_op_seule(self):
        # Divergence 2 : toute spec nue {"OP": ...} doit etre normalisee.
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


class TestJoker(unittest.TestCase):
    def test_wildcard_semantique_inchangee(self):
        spec = fr._wildcard("+")
        self.assertEqual(spec["OP"], "+")
        self.assertIn("TEXT", spec)


if __name__ == "__main__":
    unittest.main(verbosity=2)
