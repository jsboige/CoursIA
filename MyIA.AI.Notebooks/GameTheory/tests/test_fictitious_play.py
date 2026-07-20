# -*- coding: utf-8 -*-
"""
Tests pour ``FictitiousPlay`` (game_theory_utils.py) — algorithme de jeu
apprentissage (Brown 1949 / Robinson 1951) pour jeux matriciels zero-sum.

Chaque joueur joue la meilleure reponse a la distribution empirique de
l'adversaire (best-response to empirical play). La classe est le companion
du notebook GameTheory-17-MultiAgent-RL.ipynb.

Avant le garde d'entree ``iterations <= 0``, ``train(iterations)`` faisait
``for _ in range(iterations)`` : un compte <= 0 produit une boucle VIDE, donc
un **no-op silencieux** — l'appelant croit que l'apprentissage a tourne alors
que la strategie moyenne reste inchangee (uniforme Laplace). FictitiousPlay
etait l'INCOHERENT de la famille des learners : ``kuhn_poker_cfr.train``
(#7489) et ``shapley_value_monte_carlo`` n_samples (#7481) rejettent deja
``<= 0`` via ``ValueError``. Ces tests pinent le garde nouvellement ajoute.

Non-vacuous : sur le module non-patche, ``train(0)`` et ``train(-5)`` ne
levent RIEN (boucle vide) ; sur le module patche, ils levent ``ValueError``.

Run with: pytest tests/test_fictitious_play.py -v
"""

import sys
from pathlib import Path

import numpy as np
import pytest

# Ajoute GameTheory/ au path (meme convention que test_kuhn_poker_cfr /
# test_strategies).
sys.path.insert(0, str(Path(__file__).parent.parent))

from game_theory_utils import FictitiousPlay, create_rps_matrix  # noqa: E402


# ----------------------------------------------------------------------------
# Fixtures.
# ----------------------------------------------------------------------------

@pytest.fixture
def rps():
    """Un jeu Pierre-Papier-Ciseaux (zero-sum, equilibrable)."""
    return FictitiousPlay(create_rps_matrix())


# ----------------------------------------------------------------------------
# Garde d'entree : iterations <= 0 (le fix, non-vacuous).
# ----------------------------------------------------------------------------

class TestTrainIterationsGuard:
    """train(iterations) doit rejeter les comptes degeneres au lieu de
    silencieusement ne rien faire (boucle vide = strategie inchangee)."""

    def test_zero_iterations_raises(self, rps):
        """iterations=0 -> range(0) = boucle vide -> NO-OP silencieux avant le
        garde. Non-vacuous : non-patche ne leve rien ; patche leve ValueError."""
        with pytest.raises(ValueError, match="iterations must be positive"):
            rps.train(0)

    def test_negative_iterations_raises(self, rps):
        """iterations<0 -> range(-5) = boucle vide -> NO-OP silencieux (compte
        absurde). Non-vacuous : non-patche ne leve rien ; patche leve ValueError."""
        with pytest.raises(ValueError, match="iterations must be positive"):
            rps.train(-5)

    def test_negative_iterations_message_carries_value(self, rps):
        """Le message d'erreur embarque la valeur recue (diagnostic, pas juste
        'must be positive')."""
        try:
            rps.train(-42)
        except ValueError as e:
            assert "-42" in str(e)
        else:
            pytest.fail("ValueError expected for iterations=-42")


# ----------------------------------------------------------------------------
# Happy path : train>0 mute reellement la strategie (anti-regression du garde).
# ----------------------------------------------------------------------------

class TestTrainHappyPath:
    """Le garde ne doit PAS casser le chemin nominal : train(positive) tourne
    reellement et fait evoluer les comptes d'actions."""

    def test_train_positive_runs_and_mutates(self, rps):
        """Apres train(50), les comptes d'actions ont augmente (l'apprentissage
        a reellement tourne) — pin que le garde n'a pas court-circuite train."""
        before_p1 = rps.counts_p1.sum()
        rps.train(50)
        after_p1 = rps.counts_p1.sum()
        assert after_p1 == before_p1 + 50  # 50 increments de step()

    def test_train_one_runs_without_error(self, rps):
        """iterations=1 (limite valide) tourne exactement un step."""
        before = rps.counts_p1.sum()
        rps.train(1)
        assert rps.counts_p1.sum() == before + 1

    def test_average_strategy_remains_distribution_after_train(self, rps):
        """Apres entrainement, get_average_strategy est toujours une distribution
        de probabilite valide (somme a 1) — le garde n'a pas corrompu l'etat."""
        rps.train(100)
        for player in (0, 1):
            strat = rps.get_average_strategy(player)
            assert strat.shape == (3,)
            assert np.isclose(strat.sum(), 1.0)
            assert (strat >= 0).all()


# ----------------------------------------------------------------------------
# Etat initial (Laplace uniforme) — invariant de __init__.
# ----------------------------------------------------------------------------

class TestInitialState:
    """__init__ part d'un prior uniforme (smoothing de Laplace, compte=1 par
    action). Pin que l'etat initial est une distribution valide avant tout train."""

    def test_initial_strategy_is_uniform(self, rps):
        """Avant tout train(), la strategie moyenne est uniforme (Laplace)."""
        for player in (0, 1):
            strat = rps.get_average_strategy(player)
            assert np.allclose(strat, np.ones(3) / 3)

    def test_initial_counts_all_ones(self, rps):
        """Les comptes d'actions partent a 1 (smoothing de Laplace)."""
        assert np.all(rps.counts_p1 == 1)
        assert np.all(rps.counts_p2 == 1)
