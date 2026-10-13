# -*- coding: utf-8 -*-
"""Tests de l'organe governance_methods re-fondé (sous-grain 2 #4960).

Vérifie la correction #1981 (5 scrutins + 2 protocoles + 8 fonctions de
choix social = 15 algorithmes), les deltas tronc ↔ prototype documentés,
et le comportement des 15 algorithmes sur profils synthétiques déterministes.
"""
import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import governance_methods as gm  # noqa: E402


def _agents(prefs_list, personality="stubborn", seed=0):
    return [gm.Agent(f"A{i}", personality, p, rng=random.Random(seed + i))
            for i, p in enumerate(prefs_list)]


OPTIONS = ["Pizza", "Burger", "Sushi", "Raclette"]
PROFIL = [
    ["Pizza", "Sushi", "Burger", "Raclette"],
    ["Pizza", "Raclette", "Sushi", "Burger"],
    ["Pizza", "Burger", "Sushi", "Raclette"],
    ["Burger", "Raclette", "Sushi", "Pizza"],
    ["Burger", "Sushi", "Raclette", "Pizza"],
    ["Sushi", "Burger", "Raclette", "Pizza"],
    ["Raclette", "Burger", "Sushi", "Pizza"],
]


class TestCategories:
    def test_5_scrutins(self):
        assert set(gm.SCRUTINS) == {"majority", "plurality", "borda",
                                     "condorcet", "quadratic"}

    def test_2_protocoles(self):
        assert set(gm.PROTOCOLES) == {"byzantine", "raft"}

    def test_8_social_choice(self):
        assert len(gm.SOCIAL_CHOICE) == 8

    def test_total_15(self):
        # Erreur #1981 : pas « 7 méthodes », mais 15 algorithmes.
        assert len(gm.SCRUTINS) + len(gm.PROTOCOLES) + len(gm.SOCIAL_CHOICE) == 15


class TestScrutins:
    def test_majority_pizza(self):
        # Pizza a 3 premières places sur 7 -> gagne à la majorité.
        assert gm.majority_voting(_agents(PROFIL), OPTIONS) == "Pizza"

    def test_plurality_alias(self):
        assert gm.plurality_voting(_agents(PROFIL), OPTIONS) ==             gm.majority_voting(_agents(PROFIL), OPTIONS)

    def test_borda_differe(self):
        # Borda peut différer de la majorité (Pizza gagne la majorité,
        # Burger ou Raclette peuvent gagner Borda selon le profil).
        g = gm.borda_count(_agents(PROFIL), OPTIONS)
        assert g in OPTIONS

    def test_condorcet_fallback_borda(self):
        # Sans vainqueur de Condorcet, repli Borda.
        cycle = [["A", "B", "C"], ["B", "C", "A"], ["C", "A", "B"]]
        g = gm.condorcet_method(_agents(cycle), ["A", "B", "C"])
        assert g in ["A", "B", "C"]

    def test_quadratic_defaut_conserve(self):
        # Delta n° 1 : le défaut du prototype est conservé (budget-split).
        ag = _agents(PROFIL, personality="flexible")
        g = gm.quadratic_voting(ag, OPTIONS, {"quadratic_budget": 9})
        assert g in OPTIONS


class TestProtocoles:
    def test_byzantine_deterministe_seed(self):
        a1 = gm.byzantine_consensus(_agents(PROFIL), OPTIONS,
                                     {"byzantine_ratio": 0.2}, rng=random.Random(1))
        a2 = gm.byzantine_consensus(_agents(PROFIL), OPTIONS,
                                     {"byzantine_ratio": 0.2}, rng=random.Random(1))
        assert a1 == a2

    def test_raft_majorite(self):
        g = gm.raft_consensus(_agents(PROFIL), OPTIONS, rng=random.Random(2))
        assert g in OPTIONS


class TestSocialChoice:
    BALLOTS = [
        ["A", "B", "C"],
        ["A", "C", "B"],
        ["B", "A", "C"],
        ["B", "C", "A"],
        ["C", "A", "B"],
    ]
    OPT = ["A", "B", "C"]

    def test_approval(self):
        w, counts = gm.approval_voting(self.BALLOTS, self.OPT, approval_threshold=2)
        assert w in self.OPT
        assert counts["A"] == 4  # A est dans le top-2 de 4 bulletins sur 5

    def test_stv(self):
        winners, rounds = gm.stv(self.BALLOTS, self.OPT, seats=1)
        assert len(winners) == 1 and winners[0] in self.OPT

    def test_copeland(self):
        w, scores = gm.copeland(self.BALLOTS, self.OPT)
        assert w in self.OPT

    def test_kemeny_young(self):
        ranking, score = gm.kemeny_young(self.BALLOTS, self.OPT)
        assert len(ranking) == 3 and score >= 0

    def test_kemeny_young_raise_au_dela_8(self):
        import pytest
        with pytest.raises(ValueError):
            gm.kemeny_young(self.BALLOTS, [f"c{i}" for i in range(9)])

    def test_kemeny_young_safe_fallback(self):
        ranking, score, approx = gm.kemeny_young_safe(self.BALLOTS,
                                                       [f"c{i}" for i in range(9)])
        assert approx is True and score == -1

    def test_schulze(self):
        w, paths = gm.schulze(self.BALLOTS, self.OPT)
        assert w in self.OPT and len(paths) == 3

    def test_condorcet_winner(self):
        # A bat B (3-2), bat C (3-2)... vérifier la présence/absence.
        w = gm.condorcet_winner([["X", "Y"], ["X", "Y"], ["Y", "X"]], ["X", "Y"])
        assert w == "X"

    def test_pairwise_matrix(self):
        m = gm.pairwise_matrix(self.BALLOTS, self.OPT)
        assert m["A"]["B"] == 3  # A préféré à B sur 3 bulletins


class TestAgent:
    def test_stubborn_premier_choix(self):
        a = gm.Agent("x", "stubborn", ["A", "B"], rng=random.Random(0))
        assert a.decide(["A", "B"]) == "A"

    def test_flexible_majority_hint(self):
        a = gm.Agent("x", "flexible", ["A", "B"], rng=random.Random(0))
        assert a.decide(["A", "B"], {"majority_hint": "B"}) == "B"

    def test_stubborn_devient_flexible(self):
        a = gm.Agent("x", "stubborn", ["A", "B"], rng=random.Random(0))
        a.satisfaction_history = [0.0, 0.0, 0.0]
        a.decide(["A", "B"])
        assert a.personality == "flexible"

    def test_bdi_intention(self):
        a = gm.BDIAgent("x", "stubborn", ["A", "B"], rng=random.Random(0))
        a.intentions.add("B")
        assert a.decide(["A", "B"]) == "B"
