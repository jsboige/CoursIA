#!/usr/bin/env python3
"""Test de non-regression — protocole d'ecoute MOS et agregateur P.808.

Le carnet `04-7-TTS-Voice-Benchmark.ipynb` livre une **rubrique** et une
grille **vide** : il dit quoi noter, il ne dit pas comment conduire la seance
ni comment agreger les notes. L'organe `mos_protocol.py` remplit ce trou.

Ce test verrouille les trois proprietes qui font la valeur de l'organe :

1. **la rubrique est lue, pas reecrite** — les criteres viennent du carnet
   `04-7` (source de verite unique) ;
2. **le protocole est reproductible** — meme graine, meme ordre de
   presentation ; l'ordre change avec la graine ;
3. **l'agregateur rejette l'auditeur aberrant et le dit** — un auditeur
   franchement aberrant est ecarte, un auditeur razonable ne l'est pas, et le
   MOS recalcule sur les auditeurs restants est exact.

Dépendances : numpy + scipy (pas de bibliotheque audio : le protocole est
independant du signal).
"""
from __future__ import annotations

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from mos_protocol import (  # noqa: E402
    P808_RATIO,
    P808_SIGMA,
    MosReport,
    Rubric,
    RubricError,
    aggregate_mos,
    build_trial_list,
    format_report,
    load_grid_items,
    load_rubric,
    rating_sheet,
)

EXPECTED_CRITERIA = (
    "naturalite",
    "francais",
    "intelligibilite",
    "expressivite",
    "fidelite",
)


def _records(rubric: Rubric, judge_bias: dict[str, float], base_by_item: dict[str, float]):
    """Campagne synthetique : note = base(item) + biais(auditeur)."""
    out = []
    for judge_id, bias in judge_bias.items():
        for item_id, base in base_by_item.items():
            out.append(
                {
                    "item_id": item_id,
                    "judge_id": judge_id,
                    "scores": {c: base + bias for c in rubric.criteria},
                }
            )
    return out


class TestRubric(unittest.TestCase):
    """La rubrique est lue dans le carnet de reference."""

    def test_criteria_read_from_reference_notebook(self):
        rubric = load_rubric()
        self.assertEqual(rubric.criteria, EXPECTED_CRITERIA)
        self.assertEqual(rubric.scale, (1, 5))
        self.assertIn("04-7-TTS-Voice-Benchmark.ipynb", rubric.source)

    def test_missing_notebook_is_a_clear_error(self):
        with self.assertRaises(RubricError):
            load_rubric(notebook_path="MyIA.AI.Notebooks/GenAI/Audio/04-Applications/does-not-exist.ipynb")


class TestGridItems(unittest.TestCase):
    """Les essais de la seance sont lus depuis la grille de reference."""

    def test_items_come_from_the_reference_grid(self):
        items = load_grid_items()
        self.assertEqual(len(items), 9)
        for item in items:
            self.assertTrue(item["id"])
            self.assertTrue(item["label"])

    def test_ids_are_unique_and_stable(self):
        ids = [item["id"] for item in load_grid_items()]
        self.assertEqual(len(ids), len(set(ids)))
        self.assertEqual(ids, [item["id"] for item in load_grid_items()])


class TestTrialList(unittest.TestCase):
    """La liste d'essais est randomisee et reproductible."""

    def _items(self, n=6):
        return [{"id": f"e{i}", "label": f"essai {i}"} for i in range(n)]

    def test_same_seed_same_order(self):
        items = self._items()
        first = build_trial_list(items, seed=42)
        second = build_trial_list(items, seed=42)
        self.assertEqual(
            [i["id"] for i in first], [i["id"] for i in second]
        )

    def test_order_is_a_permutation(self):
        items = self._items()
        ordered = [i["id"] for i in build_trial_list(items, seed=1)]
        self.assertEqual(sorted(ordered), sorted(i["id"] for i in items))

    def test_seed_changes_order(self):
        items = self._items(8)
        orders = {
            tuple(i["id"] for i in build_trial_list(items, seed=seed)) for seed in range(8)
        }
        self.assertGreater(len(orders), 1)

    def test_anchors_are_flagged_and_items_are_copies(self):
        items = self._items()
        trial = build_trial_list(items, seed=3, anchor_ids=["e2"])
        anchored = [i for i in trial if i["is_anchor"]]
        self.assertEqual([i["id"] for i in anchored], ["e2"])
        # la source n'est pas mutee
        self.assertNotIn("presentation_order", items[0])

    def test_presentation_order_is_one_based(self):
        trial = build_trial_list(self._items(), seed=0)
        self.assertEqual(
            sorted(i["presentation_order"] for i in trial), list(range(1, len(trial) + 1))
        )


class TestRatingSheet(unittest.TestCase):
    """La fiche de notation est pre-remplie au schema de la rubrique."""

    def test_one_row_per_item_with_empty_criteria(self):
        rubric = load_rubric()
        trial = build_trial_list(
            [{"id": "a", "label": "A"}, {"id": "b", "label": "B"}], seed=1
        )
        sheet = rating_sheet(trial, rubric)
        self.assertEqual(len(sheet), 2)
        for row in sheet:
            for criterion in rubric.criteria:
                self.assertIn(criterion, row)
                self.assertIsNone(row[criterion])


class TestAggregation(unittest.TestCase):
    """L'agregateur produit un MOS exact, un IC, et rejette l'aberrant."""

    def setUp(self):
        self.rubric = load_rubric()

    def test_mos_is_exact_on_a_uniform_campaign(self):
        base = {"A": 4.0, "B": 3.0, "C": 2.0}
        records = _records(self.rubric, {"j1": 0.0, "j2": 0.0}, base)
        report = aggregate_mos(records, rubric=self.rubric)
        self.assertAlmostEqual(report.mos, 3.0, places=6)
        self.assertEqual(report.n_items, 3)
        self.assertEqual(report.n_judges, 2)
        self.assertEqual(report.rejected_judges, [])

    def test_confidence_interval_brackets_the_mos(self):
        base = {"A": 4.0, "B": 3.0, "C": 2.0, "D": 5.0}
        records = _records(self.rubric, {"j1": 0.0, "j2": 0.3, "j3": -0.2}, base)
        report = aggregate_mos(records, rubric=self.rubric)
        self.assertLessEqual(report.ci_low, report.mos)
        self.assertGreaterEqual(report.ci_high, report.mos)
        self.assertGreater(report.ci_high, report.ci_low)

    def test_uniform_campaign_has_a_degenerate_interval(self):
        base = {"A": 4.0, "B": 4.0, "C": 4.0}
        records = _records(self.rubric, {"j1": 0.0, "j2": 0.0}, base)
        report = aggregate_mos(records, rubric=self.rubric)
        self.assertAlmostEqual(report.ci_low, report.ci_high, places=9)

    def test_aberrant_judge_is_rejected_and_named(self):
        base = {"A": 4.0, "B": 4.0, "C": 4.0, "D": 4.0}
        # jury de 6 auditeurs raisonnables + 1 aberrant : la regle P.808
        # (ecart >= 2 sigma ET moyenne < 0,85 x MOS) ne peut pas se declencher
        # sur un panel trop petit, l'ecart-type etant alors gonfle par
        # l'aberrant lui-meme.
        judge_bias = {
            "j1": 0.0,
            "j2": 0.06,
            "j3": -0.06,
            "j4": 0.05,
            "j5": -0.05,
            "j6": 0.0,
            "outlier": -2.5,
        }
        records = _records(self.rubric, judge_bias, base)
        report = aggregate_mos(records, rubric=self.rubric)
        self.assertIn("outlier", report.rejected_judges)
        self.assertEqual(report.n_judges, 6)
        # le MOS recalcule sur les auditeurs restants est celui du consensus
        self.assertAlmostEqual(report.mos, 4.0, places=6)

    def test_reasonable_judge_is_not_rejected(self):
        base = {"A": 4.0, "B": 4.0, "C": 4.0, "D": 4.0}
        judge_bias = {"j1": 0.0, "j2": 0.2, "j3": -0.2, "j4": 0.1}
        records = _records(self.rubric, judge_bias, base)
        report = aggregate_mos(records, rubric=self.rubric)
        self.assertEqual(report.rejected_judges, [])

    def test_rejection_can_be_disabled(self):
        base = {"A": 4.0, "B": 4.0, "C": 4.0, "D": 4.0}
        records = _records(self.rubric, {"j1": 0.0, "j2": 0.0, "outlier": -2.5}, base)
        report = aggregate_mos(records, rubric=self.rubric, reject_outliers=False)
        self.assertEqual(report.rejected_judges, [])
        self.assertEqual(report.n_judges, 3)

    def test_missing_note_is_refused(self):
        records = [
            {
                "item_id": "A",
                "judge_id": "j1",
                "scores": {c: 4.0 for c in self.rubric.criteria[:-1]}
                | {self.rubric.criteria[-1]: None},
            }
        ]
        with self.assertRaises(ValueError):
            aggregate_mos(records, rubric=self.rubric)

    def test_report_is_readable(self):
        base = {"A": 4.0, "B": 3.0}
        records = _records(self.rubric, {"j1": 0.0, "j2": 0.1}, base)
        text = format_report(aggregate_mos(records, rubric=self.rubric))
        self.assertIn("MOS global", text)
        self.assertIn("IC 95 %", text)
        self.assertIn("A", text)


class TestP808Constants(unittest.TestCase):
    """Les constantes de rejet sont celles de la regle citee."""

    def test_constants(self):
        self.assertEqual(P808_SIGMA, 2.0)
        self.assertEqual(P808_RATIO, 0.85)


if __name__ == "__main__":
    unittest.main()
