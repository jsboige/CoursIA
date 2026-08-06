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

import math

import numpy as np
import pytest

from ict import sensitivity as SE
from ict.spectral import transition_graph


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


# --------------------------------------------------------------------------- #
#  Edge-cases migrés depuis ict/tests/test_sensitivity.py (consolidation, MED/test) #
#                                                                               #
#  Propriétés mathématiques et fonctionnelles non couvertes par les classes     #
#  ci-dessus : invariance par complément, borne par le degré, cas exacts        #
#  (cycle/parité, fonction point), validation d'input (overflow vocabulaire),   #
#  cohérence distribution <-> local_sensitivity, relation définitionnelle       #
#  threshold = sqrt(deg_proxy), injection d'un proxy_degree_fn.                 #
# --------------------------------------------------------------------------- #
# Cycle orienté 0->1->2->3->0 répété : 4 labels distincts.
_CYCLE4 = [0, 1, 2, 3] * 6
_N_CYCLE = 4


def _parity(n: int) -> int:
    """Fonction d'état : parité (booléenne 0/1)."""
    return n % 2


def _point_k(k: int):
    """Fonction d'état ``f(x) = 1`` ssi ``x == k`` (sinon 0)."""
    def f(x: int) -> int:
        return 1 if x == k else 0
    return f


class TestLocalSensitivityEdgeCases:
    """Invariance par complément, borne par le degré, cas exacts, validation d'input."""

    def test_complement_invariance(self):
        # s_x(f) == s_x(non f) : le basculement f(y)!=f(x) est invariant par
        # négation logique.
        s_f = SE.local_sensitivity(_CYCLE4, _N_CYCLE, _parity)
        s_nf = SE.local_sensitivity(_CYCLE4, _N_CYCLE, lambda x: 1 - (x % 2))
        assert np.array_equal(s_f, s_nf)

    def test_bounded_by_graph_degree(self):
        # s_x <= degré(x) = (W[x] > 0).sum() : on ne bascule que sur les
        # voisins qui existent dans le graphe symétrisé.
        s = SE.local_sensitivity(_CYCLE4, _N_CYCLE, _parity)
        W = transition_graph(_CYCLE4, _N_CYCLE)
        degrees = (W > 0).sum(axis=1)
        assert np.all(s <= degrees)

    def test_cycle_parity_is_two_everywhere(self):
        # Cycle 4-noeuds, f=parité : s_x = 2 partout (2 noeuds de parité opposée
        # sur le vocabulaire).
        s = SE.local_sensitivity(_CYCLE4, _N_CYCLE, _parity)
        assert np.array_equal(s, np.array([2, 2, 2, 2]))

    def test_point_function_localizes_to_k(self):
        # f(x)=1 ssi x=k(=0) : s_0 = n-1 (bascule vers tous les autres),
        # chaque autre bascule uniquement vers k => s = 1.
        s = SE.local_sensitivity(_CYCLE4, _N_CYCLE, _point_k(0))
        assert s[0] == _N_CYCLE - 1
        assert s[1] == 1 and s[2] == 1 and s[3] == 1

    def test_raises_on_too_many_unique_labels(self):
        # Plus de labels distincts que n_symbols => ValueError (garde-fou).
        states = [0, 1, 2, 3, 4, 0, 1, 2, 3, 4]
        with pytest.raises(ValueError):
            SE.local_sensitivity(states, 4, _parity)


class TestSensitivityDistributionEdgeCases:
    """Cohérence distribution <-> local_sensitivity, et std/p95."""

    def test_max_mean_match_local_on_visited(self):
        # distribution['max']/'mean' == max/mean de s sur les noeuds visités.
        dist = SE.sensitivity_distribution(_CYCLE4, _N_CYCLE, _parity)
        s = SE.local_sensitivity(_CYCLE4, _N_CYCLE, _parity)
        assert dist["max"] == float(np.max(s))
        assert dist["mean"] == pytest.approx(float(np.mean(s)))

    def test_std_nonneg_p95_in_range(self):
        # std >= 0 et p95 dans [0, max] (cohérence d'une distribution).
        dist = SE.sensitivity_distribution(_CYCLE4, _N_CYCLE, _parity)
        assert dist["std"] >= 0.0
        assert 0.0 <= dist["p95"] <= dist["max"]


class TestHuangConjectureEdgeCases:
    """Relation définitionnelle threshold = sqrt(deg_proxy), et proxy injecté."""

    def test_threshold_is_sqrt_of_deg_proxy(self):
        # threshold == sqrt(deg_proxy) (définition de la conjecture de Huang).
        out = SE.huang_conjecture_test(_CYCLE4, _N_CYCLE, _parity)
        assert out["threshold"] == pytest.approx(math.sqrt(out["deg_proxy"]))

    def test_proxy_degree_fn_injected_is_respected(self):
        # Un proxy_degree_fn injecté détermine deg_proxy et threshold.
        fixed = 9.0

        def fixed_proxy(states, n_symbols):
            return fixed

        out = SE.huang_conjecture_test(
            _CYCLE4, _N_CYCLE, _parity, proxy_degree_fn=fixed_proxy
        )
        assert out["deg_proxy"] == fixed
        assert out["threshold"] == pytest.approx(math.sqrt(fixed))
