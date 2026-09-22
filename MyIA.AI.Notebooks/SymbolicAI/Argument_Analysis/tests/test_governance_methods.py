# -*- coding: utf-8 -*-
"""Tests de structure de governance_methods.py — purs, sans execution de vote aleatoire.

Fige les comptes distilles (7 methodes, 6 scenarios) et les proprietes
structurelles du port. La validation executee vit dans le notebook committé
(avec outputs), pas ici.
"""

import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import governance_methods as g


class TestComptesMesures(unittest.TestCase):
    """Fige l'inventaire de la distillation."""

    def test_sept_methodes(self):
        self.assertEqual(g.method_counts()["methods"], 7)

    def test_cles_methodes(self):
        self.assertEqual(
            g.method_counts()["method_keys"],
            ["borda", "byzantine", "condorcet", "majority", "plurality", "quadratic", "raft"],
        )

    def test_six_scenarios(self):
        self.assertEqual(g.method_counts()["scenarios"], 6)
        self.assertEqual(
            g.method_counts()["scenario_names"],
            ["byzantine_noise", "cyclic_majority", "dictatorship",
             "project_funding", "spoiler_candidate", "strategic_bloc"],
        )


class TestStructure(unittest.TestCase):
    """Proprietes structurelles du port."""

    def test_chaque_scenario_trois_champs(self):
        for name, sc in g.SCENARIOS.items():
            self.assertIn("description", sc, name)
            self.assertIn("options", sc, name)
            self.assertIn("agents", sc, name)

    def test_preferences_dans_options(self):
        for name, sc in g.SCENARIOS.items():
            for _, _, prefs in sc["agents"]:
                for p in prefs:
                    self.assertIn(p, sc["options"], f"{name}: {p}")

    def test_personnalites_connues(self):
        for name, sc in g.SCENARIOS.items():
            for _, perso, _ in sc["agents"]:
                self.assertIn(perso, {"stubborn", "flexible", "strategic", "random"}, name)

    def test_plurality_meme_resultat_que_majority(self):
        # Port fidele : le source definit plurality comme simple rappel de majority.
        agents = g.build_agents("dictatorship")
        opts = g.SCENARIOS["dictatorship"]["options"]
        self.assertEqual(
            g.plurality_voting(agents, opts, None, None),
            g.majority_voting(agents, opts, None, None),
        )

    def test_determinisme_seed(self):
        agents = g.build_agents("byzantine_noise")
        opts = g.SCENARIOS["byzantine_noise"]["options"]
        w1 = g.simulate_vote(agents, opts, "byzantine", seed=42)["winner"]
        agents = g.build_agents("byzantine_noise")
        w2 = g.simulate_vote(agents, opts, "byzantine", seed=42)["winner"]
        self.assertEqual(w1, w2)


class TestVotesDeterministes(unittest.TestCase):
    """Votes sans aleatoire (personnalites non random) : resultats calculables a la main."""

    def test_majorite_bloc_strategique(self):
        agents = g.build_agents("strategic_bloc")
        w = g.majority_voting(agents, ["A", "B", "C"])
        self.assertEqual(w, "A")  # 3 votes A contre 1 B, 1 C

    def test_borda_spoiler_elit_centre(self):
        # G1[A,B,C] G2[C,G,D]... Borda cumule les seconds rangs : Centre gagne.
        agents = g.build_agents("spoiler_candidate")
        w = g.borda_count(agents, g.SCENARIOS["spoiler_candidate"]["options"])
        self.assertEqual(w, "Centre")

    def test_majorite_spoiler_elit_gauche(self):
        agents = g.build_agents("spoiler_candidate")
        w = g.majority_voting(agents, g.SCENARIOS["spoiler_candidate"]["options"])
        self.assertEqual(w, "Gauche")

    def test_condorcet_cycle_repli_borda(self):
        # Cycle A>B>C>A : aucun vainqueur de Condorcet, repli Borda (egalite A=B=C=3).
        agents = g.build_agents("cyclic_majority")
        opts = g.SCENARIOS["cyclic_majority"]["options"]
        w = g.condorcet_method(agents, opts)
        # Borda rend 3=3=3, max() prend la premiere cle (A) — documenté divergence 6.
        self.assertEqual(w, "A")

    def test_gini_borne(self):
        self.assertEqual(g.gini([1, 1, 1, 1]), 0.0)
        # Un seul detenteur parmi n : Gini tend vers (n-1)/n, ici 0.75.
        self.assertAlmostEqual(g.gini([0, 0, 0, 10]), 0.75, delta=1e-6)

    def test_shapley_symetrie(self):
        # Deux agents interchangeables => valeurs de Shapley egales.
        vals = g.shapley_value(["X", "Y"], lambda s: 1.0 if len(s) >= 1 else 0.0)
        self.assertAlmostEqual(vals["X"], vals["Y"])

    def test_detect_conflicts_paires(self):
        c = g.detect_conflicts({"a": "A", "b": "B", "c": "A"})
        self.assertEqual(len(c), 2)  # (a,b) et (b,c)

    def test_manipulation_strategique_change_les_votes(self):
        agents = g.build_agents("spoiler_candidate")
        copies = g.apply_manipulation(agents, "strategic")
        votes_avant = [a.decide(["Gauche", "Centre", "Droite"]) for a in agents]
        votes_apres = [a.decide(["Gauche", "Centre", "Droite"]) for a in copies]
        self.assertNotEqual(votes_avant, votes_apres)


if __name__ == "__main__":
    unittest.main(verbosity=2)
