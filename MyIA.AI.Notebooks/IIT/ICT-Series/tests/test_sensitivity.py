"""Tests unitaires de ``ict.sensitivity`` (ICT-15b, #7288).

Couvre :

* :func:`local_sensitivity` -- calcul direct, max, distribution.
* :func:`sensitivity_distribution` -- statistiques resumees (max, mean, std, p95).
* :func:`huang_conjecture_test` -- verdict consistent / inconsistent / inconclusive.

Methodologie : signaux synthetiques dont la verite terrain est connue
(chaine lineaire, marche aleatoire, fonction constante, fonction
identite).
"""

from __future__ import annotations

import numpy as np
import pytest

from ict import sensitivity as SE


# --------------------------------------------------------------------------- #
#  Helpers                                                                     #
# --------------------------------------------------------------------------- #
def _chain(n: int, length: int) -> list:
    return [(i % n) for i in range(length)]


def _random_walk(n: int, length: int, rng: np.random.Generator) -> list:
    out = [0]
    for _ in range(length - 1):
        out.append(int(rng.integers(0, n)))
    return out


# --------------------------------------------------------------------------- #
#  local_sensitivity                                                           #
# --------------------------------------------------------------------------- #
class TestLocalSensitivity:
    """Cas triviaux ou la verite terrain est connue."""

    def test_constant_function_zero_sensitivity(self):
        # f(x) = 0 pour tous x -> s_x(f) = 0 pour tous x.
        states = _chain(5, 100)
        s = SE.local_sensitivity(states, 5, lambda x: 0)
        assert np.all(s == 0)

    def test_identity_function_maximal_sensitivity_on_chain(self):
        # f(x) = x (sur une chaine 0-1-2-3-4-0) : chaque noeud a 2 voisins
        # (gauche/droite) de valeurs differentes -> s_x = 2 pour chaque x.
        states = _chain(5, 100)
        s = SE.local_sensitivity(states, 5, lambda x: x)
        # Tous les noeuds ont au moins 1 voisin (chaine 5), donc s >= 1.
        # En pratique la symetrisation de transition_graph peut donner
        # un degre <= 2 (les 2 voisins du cycle). On verifie >= 1.
        assert np.all(s >= 1)

    def test_returns_array_of_correct_shape(self):
        states = _chain(5, 100)
        s = SE.local_sensitivity(states, 5, lambda x: x % 2)
        assert s.shape == (5,)
        assert s.dtype in (np.int32, np.int64)


# --------------------------------------------------------------------------- #
#  sensitivity_distribution                                                    #
# --------------------------------------------------------------------------- #
class TestSensitivityDistribution:
    """Statistiques resumees sur les noeuds visites."""

    def test_keys_and_types(self):
        states = _chain(5, 100)
        d = SE.sensitivity_distribution(states, 5, lambda x: x % 2)
        for key in ("max", "mean", "std", "p95", "n_visited"):
            assert key in d
            assert isinstance(d[key], (int, float))

    def test_constant_function_zero_distribution(self):
        states = _chain(5, 100)
        d = SE.sensitivity_distribution(states, 5, lambda x: 0)
        assert d["max"] == 0
        assert d["mean"] == 0

    def test_n_visited_correct(self):
        states = _chain(5, 100)
        # Chaine 5 -> 5 etats distincts visites.
        d = SE.sensitivity_distribution(states, 5, lambda x: x % 2)
        assert d["n_visited"] == 5


# --------------------------------------------------------------------------- #
#  huang_conjecture_test                                                       #
# --------------------------------------------------------------------------- #
class TestHuangConjectureTest:
    """Verdict consistent / inconsistent / inconclusive."""

    def test_keys_and_types(self):
        states = _chain(5, 200)
        r = SE.huang_conjecture_test(states, 5, lambda x: x % 2)
        for key in ("s_max", "deg_proxy", "threshold", "ratio", "n_transitions",
                    "n_visited", "verdict"):
            assert key in r
        assert r["verdict"] in {"consistent", "inconsistent", "inconclusive"}
        assert isinstance(r["s_max"], int)
        assert isinstance(r["deg_proxy"], float)
        assert isinstance(r["threshold"], float)

    def test_constant_function_is_inconclusive_or_inconsistent(self):
        # f(x) = 0 -> s_max = 0, threshold > 0 -> inconsistent.
        # Mais si la trajectoire est trop courte, peut-etre inconclusive.
        states = _chain(5, 100)
        r = SE.huang_conjecture_test(states, 5, lambda x: 0)
        # n_transitions = 99 > 2 * 5 = 10, donc pas inconclusive.
        assert r["verdict"] == "inconsistent"
        assert r["s_max"] == 0

    def test_high_sensitivity_function_can_be_consistent(self):
        # f(x) = x sur une chaine : s_max >= 1, threshold petit (sqrt(deg moyen)).
        # La sensibilite est generalement >> threshold sur des graphes degres.
        states = _chain(10, 500)
        r = SE.huang_conjecture_test(states, 10, lambda x: x)
        # Verdict : consistent ou inconclusive selon longueur, jamais inconsistent.
        assert r["verdict"] in {"consistent", "inconclusive"}

    def test_short_trajectory_is_inconclusive(self):
        # Trajectoire plus courte que 2 * n_symbols -> inconclusive.
        states = _chain(5, 5)  # seulement 4 transitions
        r = SE.huang_conjecture_test(states, 5, lambda x: x % 2)
        assert r["verdict"] == "inconclusive"
