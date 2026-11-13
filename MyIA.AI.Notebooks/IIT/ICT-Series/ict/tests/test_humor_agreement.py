# -*- coding: utf-8 -*-
"""Tests de l'instrument d'accord inter-annotateurs (residue #20301).

Le module `ict/humor_agreement.py` mesure l'accord et le cout d'une campagne
d'annotation deja produite ; il ne produit aucune annotation. Les tests
verifient donc le calcul (kappa, marges, confusion), le cout en tokens, la ligne
de base du hasard (temoin negatif) et la lecture/ecriture JSONL.
"""

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from ict.humor_agreement import (
    agreement_report,
    chance_kappa_distribution,
    cohen_kappa,
    group_by_annotator,
    interpret_kappa,
    pairwise_agreement,
    read_annotations_jsonl,
    token_cost,
    write_annotations_jsonl,
)


class TestCohenKappa(unittest.TestCase):
    def test_accord_parfait(self):
        labels = [0, 1, 2, 0, 1, 2]
        summary = cohen_kappa(labels, list(labels))
        self.assertAlmostEqual(summary["kappa"], 1.0, places=12)
        self.assertAlmostEqual(summary["observed_agreement"], 1.0, places=12)
        self.assertEqual(summary["n"], 6)

    def test_accord_au_hasard(self):
        # marges identiques (0.5 / 0.5), accord observe 0.5 -> kappa nul
        summary = cohen_kappa([0, 0, 1, 1], [0, 1, 0, 1])
        self.assertAlmostEqual(summary["kappa"], 0.0, places=12)
        self.assertAlmostEqual(summary["expected_agreement"], 0.5, places=12)

    def test_desaccord_systematique(self):
        summary = cohen_kappa([0, 1, 0, 1, 0, 1], [1, 0, 1, 0, 1, 0])
        self.assertAlmostEqual(summary["kappa"], -1.0, places=12)

    def test_marges_degenerees_kappa_indefini(self):
        summary = cohen_kappa([0, 0], [0, 0])
        self.assertIsNone(summary["kappa"])
        self.assertIsNotNone(summary["undefined_reason"])
        self.assertIn("indefini", summary["interpretation"])

    def test_longueurs_differentes_refusees(self):
        with self.assertRaises(ValueError):
            cohen_kappa([0, 1], [0])

    def test_series_vides_refusees(self):
        with self.assertRaises(ValueError):
            cohen_kappa([], [])

    def test_etiquette_hors_categories_refusee(self):
        with self.assertRaises(ValueError):
            cohen_kappa([0, 1], [0, 1], categories=[0])

    def test_matrice_de_confusion(self):
        summary = cohen_kappa([0, 0, 1, 1], [0, 1, 1, 1])
        self.assertEqual(summary["confusion"][0][0], 1)
        self.assertEqual(summary["confusion"][0][1], 1)
        self.assertEqual(summary["confusion"][1][1], 2)
        self.assertEqual(summary["confusion"][1][0], 0)

    def test_multi_categories(self):
        a = ["pun", "topical", "sociale", "pun", "sociale", "topical"]
        b = ["pun", "topical", "sociale", "pun", "pun", "topical"]
        summary = cohen_kappa(a, b)
        self.assertEqual(summary["categories"], ["pun", "sociale", "topical"])
        self.assertAlmostEqual(summary["observed_agreement"], 5 / 6, places=12)
        self.assertGreater(summary["kappa"], 0.0)


class TestInterpretation(unittest.TestCase):
    def test_bandes(self):
        self.assertIn("pauvre", interpret_kappa(-0.5))
        self.assertIn("faible", interpret_kappa(0.1))
        self.assertIn("modere", interpret_kappa(0.3))
        self.assertIn("substantiel", interpret_kappa(0.5))
        self.assertIn("fort", interpret_kappa(0.7))
        self.assertIn("presque parfait", interpret_kappa(0.9))

    def test_kappa_indefini_signale(self):
        self.assertIn("indefini", interpret_kappa(None))


class TestGrouping(unittest.TestCase):
    def test_annotateur_unique_par_item(self):
        records = [
            {"id": "i1", "annotator": "A", "label": "humour"},
            {"id": "i1", "annotator": "A", "label": "non-humour"},
        ]
        with self.assertRaises(ValueError):
            group_by_annotator(records)

    def test_annotateurs_differents_autorises(self):
        records = [
            {"id": "i1", "annotator": "A", "label": "humour"},
            {"id": "i1", "annotator": "B", "label": "humour"},
        ]
        grouped = group_by_annotator(records)
        self.assertEqual(set(grouped), {"A", "B"})


class TestPairwise(unittest.TestCase):
    def setUp(self):
        self.records = [
            {"id": "i1", "annotator": "A", "label": 1},
            {"id": "i2", "annotator": "A", "label": 0},
            {"id": "i3", "annotator": "A", "label": 1},
            {"id": "i1", "annotator": "B", "label": 1},
            {"id": "i2", "annotator": "B", "label": 0},
            {"id": "i3", "annotator": "B", "label": 0},
        ]

    def test_paire_unique(self):
        pairwise = pairwise_agreement(self.records)
        self.assertEqual(list(pairwise), ["A vs B"])
        self.assertEqual(pairwise["A vs B"]["n"], 3)
        self.assertAlmostEqual(pairwise["A vs B"]["observed_agreement"], 2 / 3, places=12)

    def test_aucun_item_partage(self):
        records = [
            {"id": "i1", "annotator": "A", "label": 1},
            {"id": "i9", "annotator": "B", "label": 0},
        ]
        pairwise = pairwise_agreement(records)
        self.assertEqual(pairwise["A vs B"]["n"], 0)
        self.assertIsNone(pairwise["A vs B"]["kappa"])


class TestTokenCost(unittest.TestCase):
    def test_agregat_par_annotateur(self):
        records = [
            {"id": "i1", "annotator": "A", "label": 1, "prompt_tokens": 100, "completion_tokens": 10},
            {"id": "i2", "annotator": "A", "label": 0, "prompt_tokens": 200, "completion_tokens": 20},
            {"id": "i1", "annotator": "B", "label": 1, "prompt_tokens": 50, "completion_tokens": 5},
        ]
        cost = token_cost(records)
        self.assertEqual(cost["per_annotator"]["A"]["total_tokens"], 330)
        self.assertEqual(cost["per_annotator"]["B"]["total_tokens"], 55)
        self.assertEqual(cost["total_tokens"], 385)
        self.assertEqual(cost["total_items"], 3)
        self.assertAlmostEqual(cost["per_annotator"]["A"]["mean_total_tokens_per_item"], 165.0)

    def test_champs_tokens_absents_toleres(self):
        cost = token_cost([{"id": "i1", "annotator": "A", "label": 1}])
        self.assertEqual(cost["total_tokens"], 0)


class TestChanceBaseline(unittest.TestCase):
    def test_permutation_ne_produit_pas_d_accord(self):
        a = [0] * 10 + [1] * 10
        b = [0] * 5 + [1] * 15
        baseline = chance_kappa_distribution(a, b, n_draws=200, seed=42)
        self.assertEqual(len(baseline["values"]), 200)
        self.assertLess(baseline["p95"], 0.5)
        # un accord parfait depasse la bande du hasard
        self.assertGreater(1.0, baseline["p95"])

    def test_longueurs_differentes_refusees(self):
        with self.assertRaises(ValueError):
            chance_kappa_distribution([0, 1], [0])


class TestReport(unittest.TestCase):
    def test_rapport_complet(self):
        records = [
            {"id": "i1", "annotator": "A", "label": 1, "prompt_tokens": 10, "completion_tokens": 1},
            {"id": "i2", "annotator": "A", "label": 0, "prompt_tokens": 10, "completion_tokens": 1},
            {"id": "i1", "annotator": "B", "label": 1, "prompt_tokens": 20, "completion_tokens": 2},
            {"id": "i2", "annotator": "B", "label": 1, "prompt_tokens": 20, "completion_tokens": 2},
        ]
        report = agreement_report(records, reference={"i1": 1, "i2": 0})
        self.assertEqual(report["annotators"], ["A", "B"])
        self.assertEqual(report["n_items"], 2)
        self.assertEqual(report["n_records"], 4)
        self.assertIn("A vs B", report["pairwise"])
        self.assertIn("A vs reference", report["vs_reference"])
        self.assertEqual(report["vs_reference"]["A vs reference"]["n"], 2)
        self.assertEqual(report["token_cost"]["total_tokens"], 66)


class TestJsonl(unittest.TestCase):
    def test_aller_retour(self):
        records = [
            {"id": "i1", "annotator": "A", "label": "humour", "prompt_tokens": 3},
            {"id": "i2", "annotator": "A", "label": "non-humour"},
        ]
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "annotations.jsonl"
            written = write_annotations_jsonl(path, records)
            self.assertEqual(written, 2)
            read_back = read_annotations_jsonl(path)
        self.assertEqual(read_back, records)

    def test_champ_manquant_refuse(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "annotations.jsonl"
            path.write_text('{"id": "i1", "annotator": "A"}\n', encoding="utf-8")
            with self.assertRaises(ValueError):
                read_annotations_jsonl(path)


if __name__ == "__main__":
    unittest.main()
