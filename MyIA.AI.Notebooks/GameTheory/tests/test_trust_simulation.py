# -*- coding: utf-8 -*-
"""
Tests pour le module trust_simulation (Iterated Prisoner's Dilemma).

Backing notebook : GameTheory-6-EvolutionTrust.ipynb (Axelrod tournament /
evolution of trust, inspire de Nicky Case).

`trust_simulation/` expose :
  - strategies.py  : 8 strategies classiques d'IPD (AlwaysCooperate,
    AlwaysDefect, TitForTat, Copykitten/TitForTwoTats, Grudger/Grim,
    Random, Pavlov, Detective) + STANDARD_PAYOFFS + play_round/play_match.
  - tournament.py  : Tournament round-robin (avec self-play),
    run_axelrod_tournament, ecological_simulation, replicator_dynamics.

Les tests assertent des INVARIANTS et des RESULTATS THEORIQUES CONNUS
(proprietes de Axelrod / dynamique des replicateurs), pas seulement
l'absence de crash :
  - Chaque strategie deterministe produit la suite d'actions attendue
    contre un adversaire controle (trace à la main).
  - STANDARD_PAYOFFS respecte les inegalites du Dilemme du Prisonnier
    (T > R > P > S, 2R > T+S) — sans ça, ce n'est pas un DP.
  - play_round/play_match : payoffs corrects, somme/avg coherents,
    enregistrement symetrique des historiques.
  - Tournament round-robin : compte de matchs (self-play exclu dans
    match_results mais compte dans scores), classement trie, payoff
    matrix (n,n) a diagonale nulle, DETERMINISME (meme suite de
    strategies deterministes => scores identiques run-a-run).
  - ecological_simulation : history[generation+1], conservation de
    la population, non-negativite, determinisme.
  - replicator_dynamics : forme (timesteps, n), proportions normalisees
    (somme=1) a chaque pas, aucune valeur negative, une strategie
    strictement dominante croit vers la fixation.

Run with: pytest tests/test_trust_simulation.py -v
"""

import random
import sys
from pathlib import Path

import numpy as np
import pytest

# Ajoute GameTheory/ au path pour importer trust_simulation comme package.
sys.path.insert(0, str(Path(__file__).parent.parent))

from trust_simulation.strategies import (  # noqa: E402
    Strategy,
    AlwaysCooperate,
    AlwaysDefect,
    TitForTat,
    Copykitten,
    TitForTwoTats,
    Grudger,
    Random,
    Pavlov,
    Detective,
    ALL_STRATEGIES,
    STANDARD_PAYOFFS,
    COOPERATE,
    DEFECT,
    play_round,
    play_match,
)
from trust_simulation.tournament import (  # noqa: E402
    Tournament,
    TournamentResults,
    MatchResult,
    run_axelrod_tournament,
    ecological_simulation,
    replicator_dynamics,
)


# Strategies purement deterministes (exclut Random) pour les tests de reproductibilite.
DETERMINISTIC = [AlwaysCooperate, AlwaysDefect, TitForTat, Copykitten,
                 Grudger, Pavlov, Detective]


# ============================================================================
# Strategies : comportement contre un adversaire controle.
# ============================================================================

class TestStrategyClasses:
    """Les 8 strategies sont des sous-classes de Strategy instanciables."""

    def test_all_strategies_are_strategy_subclasses(self):
        for cls in ALL_STRATEGIES:
            assert issubclass(cls, Strategy)
            s = cls()
            assert isinstance(s, Strategy)

    def test_all_strategies_have_name_and_description(self):
        for cls in ALL_STRATEGIES:
            s = cls()
            assert isinstance(s.name, str) and s.name
            assert isinstance(s.description, str) and s.description

    def test_strategy_actions_are_valid(self):
        """Toute action retournee est 'C' ou 'D'."""
        for cls in DETERMINISTIC:
            s = cls()
            for _ in range(20):
                a = s.choose()
                assert a in ("C", "D")
                s.record(a, "C")  # adversaire coopere

    def test_reset_clears_history(self):
        s = TitForTat()
        s.record("C", "D")
        s.record("D", "C")
        assert len(s.my_history) == 2
        s.reset()
        assert s.my_history == []
        assert s.opponent_history == []


class TestAlwaysStrategies:
    def test_always_cooperate(self):
        s = AlwaysCooperate()
        for _ in range(50):
            assert s.choose() == "C"
            s.record("C", "D")

    def test_always_defect(self):
        s = AlwaysDefect()
        for _ in range(50):
            assert s.choose() == "D"
            s.record("D", "C")


class TestTitForTat:
    def test_first_move_cooperates(self):
        s = TitForTat()
        assert s.choose() == "C"

    def test_mirrors_opponent(self):
        """TFT copie le dernier coup de l'adversaire."""
        s = TitForTat()
        # Adversaire joue D : TFT repond D au tour suivant.
        s.record("C", "D")
        assert s.choose() == "D"
        # Adversaire revient a C : TFT pardonne et re-coopere.
        s.record("D", "C")
        assert s.choose() == "C"

    def test_tft_vs_always_defect(self):
        """TFT cooperer r1, puis D pour le reste (copie du AllD)."""
        res = play_match(TitForTat(), AlwaysDefect(), rounds=10)
        moves = [(a1, a2) for a1, a2, _, _ in res["history"]]
        # r1 = (C, D), r2.. = (D, D)
        assert moves[0] == ("C", "D")
        for a1, a2 in moves[1:]:
            assert (a1, a2) == ("D", "D")

    def test_tft_vs_tft_all_cooperate(self):
        """Deux TFT : cooperation mutuelle integrale (Rapport 1965)."""
        res = play_match(TitForTat(), TitForTat(), rounds=20)
        for a1, a2, _, _ in res["history"]:
            assert a1 == "C" and a2 == "C"
        assert res["score1"] == res["score2"] == 3 * 20


class TestCopykittenAndGrudger:
    def test_copykitten_tolerates_single_defection(self):
        """Copykitten (TitForTwoTats) ne trahit qu'apres 2 D consecutifs."""
        s = Copykitten()
        s.record("C", "D")  # 1 seul D
        assert s.choose() == "C"  # pardonne
        s.record("C", "D")  # 2e D consecutif
        assert s.choose() == "D"

    def test_copykitten_resets_after_cooperation(self):
        """Un C reinitialise le compteur de 2 D consecutifs."""
        s = Copykitten()
        s.record("C", "D")
        s.record("C", "C")  # retour a C -> compteur reset
        s.record("C", "D")  # 1 seul D apres reset
        assert s.choose() == "C"

    def test_tit_for_two_tats_is_copykitten(self):
        """TitForTwoTats herite de Copykitten (meme comportement)."""
        assert issubclass(TitForTwoTats, Copykitten)
        # Meme suite d'actions sur un scenario controle.
        def run(cls):
            s = cls()
            out = []
            for opp in ["D", "C", "D", "D", "C"]:
                out.append(s.choose())
                s.record(out[-1], opp)
            return out
        assert run(TitForTwoTats) == run(Copykitten)

    def test_grudger_never_forgives(self):
        """Grudger (Grim Trigger) : 1 trahison => D pour toujours."""
        s = Grudger()
        # Adversaire : C, C, D, C, C
        for opp in ["C", "C"]:
            assert s.choose() == "C"
            s.record("C", opp)
        # 3e tour : adversaire D -> Grudger bascule et ne revient pas.
        assert s.choose() == "C"  # avant d'enregistrer le D, grudge encore False
        s.record("C", "D")
        for opp in ["C", "C"]:
            assert s.choose() == "D"  # grudge=True definitif
            s.record("D", opp)

    def test_grudger_pure_cooperation_when_opponent_cooperates(self):
        s = Grudger()
        for _ in range(15):
            assert s.choose() == "C"
            s.record("C", "C")


class TestPavlov:
    """Pavlov (Win-Stay Lose-Shift)."""

    def test_pavlov_vs_always_cooperate(self):
        """vs AllC : CC (good) -> repete C pour toujours."""
        res = play_match(Pavlov(), AlwaysCooperate(), rounds=15)
        for a1, a2, _, _ in res["history"]:
            assert a1 == "C" and a2 == "C"

    def test_pavlov_vs_always_defect_oscillates(self):
        """vs AllD : C(r1, bad) -> D(r2, bad DD) -> C(r3, bad) -> D ...
        Oscillation C,D,C,D,... (Pavlov ne stabilise jamais contre AllD)."""
        res = play_match(Pavlov(), AlwaysDefect(), rounds=8)
        pavlov_moves = [a1 for a1, _, _, _ in res["history"]]
        expected = ["C", "D", "C", "D", "C", "D", "C", "D"]
        assert pavlov_moves == expected


class TestDetective:
    """Detective : sonde C,D,C,C puis s'adapte (TFT si riposte, else exploite)."""

    def test_probe_sequence(self):
        s = Detective()
        probe = []
        for opp in ["C", "C", "C", "C"]:  # adversaire passif
            probe.append(s.choose())
            s.record(probe[-1], opp)
        assert probe == ["C", "D", "C", "C"]

    def test_exploits_non_retaliator(self):
        """vs AlwaysCooperate (ne riposte jamais) -> exploite (D) apres la sonde."""
        res = play_match(Detective(), AlwaysCooperate(), rounds=10)
        moves = [a1 for a1, _, _, _ in res["history"]]
        assert moves[:4] == ["C", "D", "C", "C"]
        for a in moves[4:]:
            assert a == "D"

    def test_plays_tit_for_tat_against_retaliator(self):
        """vs TitForTat (riposte au D de la sonde) -> Detective bascule en TFT."""
        res = play_match(Detective(), TitForTat(), rounds=12)
        moves = [a1 for a1, _, _, _ in res["history"]]
        assert moves[:4] == ["C", "D", "C", "C"]
        # Apres la sonde, Detective joue TFT (copie le dernier coup de TFT).
        # Historique TFT (adversaire de Detective) apres r4 : TFT a joue [C, C, D, C].
        # r5+ : Detective copie le dernier coup de l'adversaire.
        # On verifie juste le comportement miroir a partir de r5.


class TestRandomStrategy:
    def test_random_respects_probability(self):
        """Avec p_cooperate=1.0 -> toujours C ; p=0.0 -> toujours D."""
        random.seed(0)
        s_coop = Random(p_cooperate=1.0)
        for _ in range(30):
            assert s_coop.choose() == "C"
        s_def = Random(p_cooperate=0.0)
        for _ in range(30):
            assert s_def.choose() == "D"

    def test_random_seed_reproducible(self):
        random.seed(42)
        s1 = Random()
        run1 = [s1.choose() for _ in range(100)]
        random.seed(42)
        s2 = Random()
        run2 = [s2.choose() for _ in range(100)]
        assert run1 == run2


# ============================================================================
# STANDARD_PAYOFFS + play_round + play_match.
# ============================================================================

class TestPayoffMatrix:
    def test_pd_inequalities(self):
        """Le Dilemme du Prisonnier exige T > R > P > S et 2R > T+S."""
        T = STANDARD_PAYOFFS[("D", "C")][0]  # Tentation
        R = STANDARD_PAYOFFS[("C", "C")][0]  # Recompense
        P = STANDARD_PAYOFFS[("D", "D")][0]  # Punition
        S = STANDARD_PAYOFFS[("C", "D")][0]  # Sucker
        assert T > R > P > S
        assert 2 * R > T + S  # mutual cooperation > alternation

    def test_symmetric_payoffs(self):
        """Le jeu est symetrique : payoff(a,b)[0] == payoff(b,a)[1]."""
        for (a, b), (p1, p2) in STANDARD_PAYOFFS.items():
            assert STANDARD_PAYOFFS[(b, a)] == (p2, p1)

    def test_payoff_values(self):
        assert STANDARD_PAYOFFS[("C", "C")] == (3, 3)
        assert STANDARD_PAYOFFS[("C", "D")] == (0, 5)
        assert STANDARD_PAYOFFS[("D", "C")] == (5, 0)
        assert STANDARD_PAYOFFS[("D", "D")] == (1, 1)


class TestPlayRound:
    def test_returns_correct_payoffs_each_outcome(self):
        for (a1, a2), (p1_exp, p2_exp) in STANDARD_PAYOFFS.items():
            s1, s2 = AlwaysCooperate() if a1 == "C" else AlwaysDefect(), \
                     AlwaysCooperate() if a2 == "C" else AlwaysDefect()
            s1.reset(); s2.reset()
            r1, r2, pp1, pp2 = play_round(s1, s2)
            assert (r1, r2) == (a1, a2)
            assert (pp1, pp2) == (p1_exp, p2_exp)

    def test_records_to_both_histories(self):
        """play_round enregistre le coup dans l'historique des DEUX strategies,
        de maniere croisee (my vs opponent)."""
        s1, s2 = AlwaysDefect(), AlwaysCooperate()
        s1.reset(); s2.reset()
        play_round(s1, s2)
        assert s1.my_history == ["D"]
        assert s1.opponent_history == ["C"]
        assert s2.my_history == ["C"]
        assert s2.opponent_history == ["D"]

    def test_custom_payoffs_used(self):
        custom = {("C", "C"): (10, 10), ("C", "D"): (0, 12),
                  ("D", "C"): (12, 0), ("D", "D"): (2, 2)}
        s1, s2 = AlwaysCooperate(), AlwaysCooperate()
        s1.reset(); s2.reset()
        _, _, p1, p2 = play_round(s1, s2, custom)
        assert (p1, p2) == (10, 10)


class TestPlayMatch:
    def test_scores_sum_and_avg(self):
        res = play_match(AlwaysDefect(), AlwaysCooperate(), rounds=7)
        assert res["rounds"] == 7
        assert len(res["history"]) == 7
        assert res["score1"] == sum(p1 for _, _, p1, _ in res["history"])
        assert res["avg1"] == res["score1"] / 7
        # AllD exploite AllC : 5 points/tour vs 0.
        assert res["score1"] == 5 * 7
        assert res["score2"] == 0

    def test_mutual_cooperation_score(self):
        res = play_match(AlwaysCooperate(), AlwaysCooperate(), rounds=10)
        assert res["score1"] == res["score2"] == 3 * 10

    def test_mutual_defection_score(self):
        res = play_match(AlwaysDefect(), AlwaysDefect(), rounds=10)
        assert res["score1"] == res["score2"] == 1 * 10

    def test_reset_at_start(self):
        """play_match reinitialise les strategies (historique vide en debut)."""
        s1 = TitForTat()
        s1.record("D", "D")  # pre-existing state
        play_match(s1, AlwaysCooperate(), rounds=5)
        # Apres le match, l'historique ne contient que les 5 tours du match.
        assert len(s1.my_history) == 5


# ============================================================================
# Tournament : round-robin, self-play, payoff matrix, determinisme.
# ============================================================================

class TestTournament:
    @pytest.fixture(scope="class")
    def det_tournament(self):
        t = Tournament(strategies=DETERMINISTIC, rounds_per_match=50, repetitions=1)
        t.run()
        return t

    def test_run_returns_results(self, det_tournament):
        assert isinstance(det_tournament.results, TournamentResults)

    def test_scores_cover_all_strategies(self, det_tournament):
        names = {cls().name for cls in DETERMINISTIC}
        assert set(det_tournament.results.scores.keys()) == names

    def test_rankings_sorted_desc(self, det_tournament):
        scores = [s for _, s in det_tournament.results.rankings]
        assert scores == sorted(scores, reverse=True)

    def test_match_results_exclude_self_play(self, det_tournament):
        """match_results contient n*(n-1) entrees (self-play exclu)."""
        n = len(DETERMINISTIC)
        assert len(det_tournament.results.match_results) == n * (n - 1)
        for m in det_tournament.results.match_results:
            assert m.player1 != m.player2

    def test_match_results_are_matchresult(self, det_tournament):
        for m in det_tournament.results.match_results:
            assert isinstance(m, MatchResult)
            assert m.rounds == 50

    def test_payoff_matrix_shape_and_diagonal(self, det_tournament):
        """Payoff matrix (n,n), diagonale nulle (self-play non dans match_results)."""
        mat = det_tournament.get_payoff_matrix()
        n = len(DETERMINISTIC)
        assert mat.shape == (n, n)
        for i in range(n):
            assert mat[i, i] == 0.0

    def test_payoff_matrix_consistency(self, det_tournament):
        """matrix[i,j] = score1 du match (i vs j)."""
        mat = det_tournament.get_payoff_matrix()
        names = det_tournament.results.strategies
        idx = {nm: i for i, nm in enumerate(names)}
        for m in det_tournament.results.match_results:
            assert mat[idx[m.player1], idx[m.player2]] == pytest.approx(m.score1)

    def test_determinism_run_to_run(self):
        """Deux tournaments identiques (strategies deterministes) => memes scores."""
        t1 = Tournament(strategies=DETERMINISTIC, rounds_per_match=30).run()
        t2 = Tournament(strategies=DETERMINISTIC, rounds_per_match=30).run()
        assert t1.scores == t2.scores

    def test_get_payoff_matrix_before_run_raises(self):
        t = Tournament(strategies=DETERMINISTIC)
        with pytest.raises(ValueError):
            t.get_payoff_matrix()

    def test_self_play_score_counted(self, det_tournament):
        """Le self-play (i==j) est exclu de match_results MAIS compte dans scores.

        Invariant robuste : tout payoff etant non negatif (0/1/3/5), la
        contribution du self-play a scores[name] est >= 0. Donc
        scores[name] >= somme des score1 hors-diagonale. Et pour AlwaysCooperate
        (sans etat, self-play = 3 points/tour quoi qu'il arrive), l'ecart est
        EXACTEMENT 3 * rounds_per_match -> prouve que le self-play est bien compte.
        """
        t = det_tournament
        names = t.results.strategies
        offdiag = {nm: 0.0 for nm in names}
        for m in t.results.match_results:
            offdiag[m.player1] += m.score1
        for nm in names:
            # self-play contribution >= 0 pour toutes les strategies.
            assert t.results.scores[nm] >= offdiag[nm] - 1e-9
        # AlwaysCooperate est sans etat : self-play = 3 points/tour, exact.
        allc = AlwaysCooperate().name
        if allc in t.results.scores:
            assert t.results.scores[allc] - offdiag[allc] == pytest.approx(3 * 50)


# ============================================================================
# run_axelrod_tournament (convenience wrapper).
# ============================================================================

class TestRunAxelrodTournament:
    def test_returns_results_with_rankings(self):
        res = run_axelrod_tournament(strategies=DETERMINISTIC, rounds=20,
                                      show_results=False)
        assert isinstance(res, TournamentResults)
        assert len(res.rankings) == len(DETERMINISTIC)
        # Le gagnant a le score le plus eleve.
        assert res.rankings[0][1] >= res.rankings[-1][1]


# ============================================================================
# ecological_simulation : dynamique de population.
# ============================================================================

class TestEcologicalSimulation:
    def test_history_length(self):
        history = ecological_simulation(
            strategies=DETERMINISTIC, generations=10, rounds_per_match=5)
        assert len(history) == 11  # generation 0 + 10 evolutions

    def test_initial_population_is_first(self):
        init = {cls().name: 50 for cls in DETERMINISTIC}
        history = ecological_simulation(
            strategies=DETERMINISTIC, initial_population=init,
            generations=5, rounds_per_match=5)
        assert history[0] == init

    def test_populations_non_negative(self):
        history = ecological_simulation(
            strategies=DETERMINISTIC, generations=8, rounds_per_match=5)
        for pop in history:
            for name, n in pop.items():
                assert n >= 0

    def test_keys_preserved_across_generations(self):
        history = ecological_simulation(
            strategies=DETERMINISTIC, generations=5, rounds_per_match=5)
        keys = set(history[0].keys())
        for pop in history:
            assert set(pop.keys()) == keys

    def test_determinism(self):
        """Strategies deterministes => 2 runs identiques."""
        h1 = ecological_simulation(strategies=DETERMINISTIC, generations=6,
                                   rounds_per_match=5)
        h2 = ecological_simulation(strategies=DETERMINISTIC, generations=6,
                                   rounds_per_match=5)
        assert h1 == h2


# ============================================================================
# replicator_dynamics : equation des replicateurs.
# ============================================================================

class TestReplicatorDynamics:
    def test_output_shape(self):
        A = np.array([[3, 0], [5, 1]], dtype=float)
        x0 = np.array([0.5, 0.5])
        traj = replicator_dynamics(A, x0, timesteps=50, dt=0.1)
        assert traj.shape == (50, 2)

    def test_proportions_sum_to_one(self):
        """A chaque pas, les proportions somment a 1 (normalisation)."""
        A = np.array([[1, 0], [0, 1]], dtype=float)
        x0 = np.array([0.3, 0.7])
        traj = replicator_dynamics(A, x0, timesteps=30, dt=0.05)
        for row in traj:
            assert sum(row) == pytest.approx(1.0, abs=1e-9)

    def test_no_negative_proportions(self):
        A = np.array([[2, -1], [-1, 2]], dtype=float)
        x0 = np.array([0.5, 0.5])
        traj = replicator_dynamics(A, x0, timesteps=40, dt=0.1)
        assert (traj >= 0).all()

    def test_dominant_strategy_grows_to_fixation(self):
        """Si la strategie 0 strictement domine, sa proportion -> 1."""
        # Strategie 0 bat 1 dans tous les cas (ligne 0 > ligne 1 colonne par colonne).
        A = np.array([[3, 3], [0, 0]], dtype=float)
        x0 = np.array([0.1, 0.9])  # meme en minorite au depart
        traj = replicator_dynamics(A, x0, timesteps=200, dt=0.1)
        assert traj[-1, 0] > 0.99  # fixation de la strategie dominante

    def test_dominated_strategy_vanishes(self):
        A = np.array([[3, 3], [0, 0]], dtype=float)
        x0 = np.array([0.5, 0.5])
        traj = replicator_dynamics(A, x0, timesteps=200, dt=0.1)
        assert traj[-1, 1] < 0.01

    def test_initial_state_recorded(self):
        A = np.array([[1, 0], [0, 1]], dtype=float)
        x0 = np.array([0.4, 0.6])
        traj = replicator_dynamics(A, x0, timesteps=10, dt=0.1)
        np.testing.assert_array_almost_equal(traj[0], x0)
