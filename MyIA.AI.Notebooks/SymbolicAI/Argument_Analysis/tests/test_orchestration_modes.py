# -*- coding: utf-8 -*-
"""Tests de l'organe orchestration_modes (distillation sas EPITA, EPIC #4960).

Fige les comportements mesures du carnet source : registres d'arret,
asymetrie d'axes, regle de calibration et sa limite mesuree.
"""

import unittest

from orchestration_modes import (
    DEPTH_PARITY,
    RUNS,
    ModeRun,
    budget_dependence,
    depth_families,
    depth_family,
    depth_parity_verdict,
    derive_calibrated_budget,
    project_full_duration,
    termination_registers,
    verdict_text,
)

UNDER = RUNS["under_budget"]
CALIBRATED = RUNS["calibrated"]


class TestBancSas(unittest.TestCase):
    """Les donnees embarquees reproduisent le banc du carnet source."""

    def test_sept_modes_par_run(self):
        self.assertEqual(len(UNDER), 7)
        self.assertEqual(len(CALIBRATED), 7)

    def test_memes_modes_aux_deux_budgets(self):
        self.assertEqual({r.mode for r in UNDER}, {r.mode for r in CALIBRATED})

    def test_modes_couverts_par_depth_parity(self):
        """Coherence croisee : le dataset et la table structurelle parlent des memes modes."""
        self.assertEqual({r.mode for r in UNDER}, {r.mode for r in DEPTH_PARITY})


class TestRegistresArret(unittest.TestCase):
    """Les trois registres disent trois choses differentes — et divergent."""

    def test_quatre_tues_au_sous_budget(self):
        self.assertEqual(sum(r.terminated_by_budget for r in UNDER), 4)

    def test_zero_tue_au_calibre(self):
        self.assertEqual(sum(r.terminated_by_budget for r in CALIBRATED), 0)

    def test_mode_tue_meme_si_duree_presque_normale(self):
        # conversational court jusqu'a son plafond INTERNE (180 s) sans etre
        # tue par le filet : ce n'est pas le harnais qui l'arrete.
        conv = next(r for r in UNDER if r.mode == "conversational")
        self.assertFalse(conv.terminated_by_budget)
        self.assertTrue(conv.success)

    def test_succes_partiel_auto_declare(self):
        # Registre 2 contre registre 3 : hierarchique_delegation calibre
        # declare succes avec 3 phases sur 5 — satisfait d'un travail partiel.
        hd = next(r for r in CALIBRATED if r.mode == "hierarchical_delegation")
        self.assertTrue(hd.success)
        self.assertEqual(hd.phases_completed, 3)
        self.assertEqual(hd.phases_total, 5)
        self.assertEqual(verdict_text(hd), "mode satisfait d'un travail partiel")

    def test_verdict_tue_avant_tout(self):
        # Ordre des tests : le filet prime la declaration du mode.
        tue_en_declquant = ModeRun(
            mode="x", success=True, duration_seconds=10.0,
            phases_completed=1, phases_total=9, terminated_by_budget=True)
        self.assertEqual(verdict_text(tue_en_declquant), "tue par le filet du harnais")

    def test_verdict_complet_au_calibre(self):
        ps = next(r for r in CALIBRATED if r.mode == "pipeline_standard")
        self.assertEqual(verdict_text(ps), "phases completes, mode satisfait")

    def test_registres_explicites(self):
        ps = next(r for r in UNDER if r.mode == "pipeline_standard")
        regs = termination_registers(ps)
        self.assertIs(regs["harnais (filet)"], True)
        self.assertIs(regs["mode (declaration)"], False)
        self.assertEqual(regs["realite (phases)"], "6/15")


class TestDepthParity(unittest.TestCase):
    """Sept modes, trois familles d'axes — l'asymetrie documentee."""

    def test_trois_familles(self):
        self.assertEqual(depth_families(DEPTH_PARITY), {
            "breadth", "delegation", "dialogue-depth"})

    def test_famille_retire_la_parenthese(self):
        hd = next(r for r in DEPTH_PARITY if r.mode == "hierarchical_delegation")
        self.assertEqual(depth_family(hd), "delegation")
        cd = next(r for r in DEPTH_PARITY if r.mode == "conversation_deterministic")
        self.assertEqual(depth_family(cd), "dialogue-depth")

    def test_phases_mesurees_dag(self):
        counts = {r.mode: r.depth_count for r in DEPTH_PARITY}
        self.assertEqual(counts["pipeline_light"], 3)
        self.assertEqual(counts["pipeline_standard"], 15)
        self.assertEqual(counts["pipeline_full"], 17)

    def test_plage_delegation_degeneree_conservee(self):
        """Divergence 3 : 4-4 est une distribution mesuree, pas un entier."""
        hd = next(r for r in DEPTH_PARITY if r.mode == "hierarchical_delegation")
        self.assertIsNotNone(hd.measured_range)
        self.assertIn("4-4", hd.measured_range)
        self.assertIn("n=3", hd.measured_range)

    def test_verdict_derive_comptes(self):
        """Anti-#1019 : les comptes du verdict derivent de la table, pas d'un litteral."""
        v = depth_parity_verdict(DEPTH_PARITY)
        self.assertIn("7 modes", v)
        self.assertIn("3 axes", v)

    def test_verdict_derive_suit_une_table_tronquee(self):
        sous = DEPTH_PARITY[:3]  # les trois pipelines : une seule famille
        v = depth_parity_verdict(sous)
        self.assertIn("3 modes", v)
        self.assertIn("1 axe", v)


class TestCalibration(unittest.TestCase):
    """La regle de calibration ET sa limite mesuree."""

    def test_projection_lineaire(self):
        ps = next(r for r in UNDER if r.mode == "pipeline_standard")
        # 180.01 * 15 / 6 = 450.025
        self.assertAlmostEqual(project_full_duration(ps), 450.025, places=2)

    def test_projection_sans_phase_faite(self):
        rien = ModeRun(
            mode="x", success=False, duration_seconds=12.0,
            phases_completed=0, phases_total=4, terminated_by_budget=True)
        self.assertIsNone(project_full_duration(rien))

    def test_derivation_naive_rend_1081(self):
        # Limite mesuree : la derivation naive (projection max * 1,2) rend
        # 1081 s ; le run calibre reel a suffi a 600 s — surestimation x1,8.
        self.assertEqual(derive_calibrated_budget(UNDER), 1081)

    def test_derivation_sans_tue(self):
        self.assertIsNone(derive_calibrated_budget(CALIBRATED))

    def test_phases_ratio(self):
        ps = next(r for r in UNDER if r.mode == "pipeline_standard")
        self.assertAlmostEqual(ps.phases_ratio, 0.4, places=6)


class TestContrasteBudget(unittest.TestCase):
    """Le contraste des deux runs prouve l'artefact du budget."""

    def test_filet_bascule_pour_les_quatre_tues(self):
        out = budget_dependence(UNDER, CALIBRATED)
        self.assertEqual(sum(d["filet_bascule"] for d in out), 4)

    def test_conversational_ne_bascule_pas(self):
        # Plafond interne : son verdict ne doit pas au filet du harnais.
        out = {d["mode"]: d for d in budget_dependence(UNDER, CALIBRATED)}
        self.assertFalse(out["conversational"]["filet_bascule"])
        self.assertIn("travail partiel", out["conversational"]["verdict_calibre"])

    def test_facteur_cent_entre_extremes(self):
        # conversation_deterministic (0,06 s) vs pipeline_full (448 s) :
        # comparer leurs durees n'a pas de sens — le notebook source l'enseigne.
        durs = {r.mode: r.duration_seconds for r in CALIBRATED}
        self.assertGreater(durs["pipeline_full"] / durs["conversation_deterministic"], 100)


class TestStructure(unittest.TestCase):
    """Proprietes structurelles du port."""

    def test_mode_run_frozen(self):
        ps = UNDER[0]
        with self.assertRaises(Exception):
            ps.mode = "autre"

    def test_chaque_record_porte_son_perimetre(self):
        for r in UNDER + CALIBRATED:
            self.assertTrue(r.scope_of_work)


if __name__ == "__main__":
    unittest.main(verbosity=2)
