"""Tests de ``ict.time_arrow`` : matrice de transition, stationnaire,
production d'entropie (Schnakenberg).

Couvre notamment le **bug fix ICT-19** (Epic #4588) : la version precedente de
``entropy_production`` annulait a 0 les transitions strictement irreversibles
(``real_zeros``), ecrasant a tort la contribution des cycles diriges. Ces tests
verrouillent le comportement corrige : un cycle dirige DOIT donner sigma > 0.

Numpy + pytest. Le module ne depend que de numpy.
"""

import os
import sys

import numpy as np
import pytest

_HERE = os.path.dirname(os.path.abspath(__file__))
_PARENT = os.path.dirname(_HERE)
if _PARENT not in sys.path:
    sys.path.insert(0, _PARENT)

from ict import time_arrow  # noqa: E402


def _stationary_power(P, n_iter=20000):
    """Stationnaire par iteration de puissance (reference independante)."""
    P = np.asarray(P, dtype=float)
    n = P.shape[0]
    pi = np.ones(n) / n
    for _ in range(n_iter):
        pi = pi @ P
        pi = pi / pi.sum()
    return pi


# --------------------------------------------------------------------------- #
#  transition_matrix
# --------------------------------------------------------------------------- #

def test_transition_matrix_rows_sum_to_one():
    states = [0, 1, 0, 1, 0, 2, 0]
    P = time_arrow.transition_matrix(states, n_symbols=3)
    np.testing.assert_allclose(P.sum(axis=1), np.ones(3), atol=1e-9)


def test_transition_matrix_counts_pairs():
    # 0->1, 1->0, 0->1, 1->0, 0->2, 2->0  => depuis 0 : {1:2, 2:1}, depuis 1: {0:2}
    states = [0, 1, 0, 1, 0, 2, 0]
    P = time_arrow.transition_matrix(states, n_symbols=3, laplace_smoothing=0.0)
    # depuis 0 : 2 vers 1, 1 vers 2 (+ self 0 non observe)
    assert P[0, 1] == pytest.approx(2 / 3, abs=1e-6)
    assert P[0, 2] == pytest.approx(1 / 3, abs=1e-6)
    assert P[1, 0] == pytest.approx(1.0, abs=1e-6)


def test_transition_matrix_deterministic_cycle():
    """Un cycle deterministe 0->1->2->0 donne P[i,(i+1)%3]=1."""
    states = [i % 3 for i in range(300)]
    P = time_arrow.transition_matrix(states, n_symbols=3, laplace_smoothing=0.0)
    for i in range(3):
        assert P[i, (i + 1) % 3] == pytest.approx(1.0, abs=1e-6)


# --------------------------------------------------------------------------- #
#  stationary_distribution
# --------------------------------------------------------------------------- #

def test_stationary_uniform_for_doubly_stochastic():
    P = np.array([[0.5, 0.25, 0.25],
                  [0.25, 0.5, 0.25],
                  [0.25, 0.25, 0.5]])
    pi = time_arrow.stationary_distribution(P)
    np.testing.assert_allclose(pi, np.ones(3) / 3, atol=1e-6)


def test_stationary_matches_power_iteration():
    P = np.array([[0.1, 0.9, 0.0],
                  [0.0, 0.2, 0.8],
                  [0.3, 0.0, 0.7]])
    pi = time_arrow.stationary_distribution(P)
    pi_ref = _stationary_power(P)
    np.testing.assert_allclose(pi, pi_ref, atol=1e-6)


# --------------------------------------------------------------------------- #
#  entropy_production -- bug fix ICT-19 (cycles diriges)
# --------------------------------------------------------------------------- #

def test_entropy_production_zero_for_detailed_balance():
    """Une chaine reversible (detailed balance) donne sigma = 0."""
    P = np.array([[0.5, 0.25, 0.25],
                  [0.25, 0.5, 0.25],
                  [0.25, 0.25, 0.5]])
    pi = time_arrow.stationary_distribution(P)
    sigma = time_arrow.entropy_production(P, pi)
    assert sigma == pytest.approx(0.0, abs=1e-9)


def test_entropy_production_positive_for_directed_cycle():
    """BUG FIX ICT-19 : un cycle dirige (P[j,i]=0) DOIT donner sigma > 0.

    La version precedente annulait cette contribution a 0 (``real_zeros``),
    contredisant la thermo de base : un cycle dirige brise la reversibilite.
    """
    P = np.array([
        [0.1, 0.9, 0.0, 0.0],
        [0.0, 0.1, 0.9, 0.0],
        [0.0, 0.0, 0.1, 0.9],
        [0.9, 0.0, 0.0, 0.1],
    ])
    pi = time_arrow.stationary_distribution(P)
    sigma = time_arrow.entropy_production(P, pi)
    assert sigma > 0.5, (
        f"un cycle dirige doit donner sigma > 0 (irreversibilite), obtenu {sigma}"
    )


def test_entropy_production_positive_for_regularized_cycle():
    """Cycle dirige regularise (eps reverse) : sigma > 0, ordre coherent."""
    eps = 1e-3
    P = np.array([
        [0.1, 0.9 - eps, 0.0, eps],
        [eps, 0.1, 0.9 - eps, 0.0],
        [0.0, eps, 0.1, 0.9 - eps],
        [0.9 - eps, 0.0, eps, 0.1],
    ])
    pi = time_arrow.stationary_distribution(P)
    sigma = time_arrow.entropy_production(P, pi)
    assert sigma > 1.0, f"cycle regularise doit donner sigma > 1, obtenu {sigma}"


def test_entropy_production_directed_beats_reversible():
    """Le cycle dirige est strictement plus irreversible que le reversible."""
    P_rev = np.array([[0.5, 0.25, 0.25],
                      [0.25, 0.5, 0.25],
                      [0.25, 0.25, 0.5]])
    P_cycle = np.array([
        [0.1, 0.9, 0.0, 0.0],
        [0.0, 0.1, 0.9, 0.0],
        [0.0, 0.0, 0.1, 0.9],
        [0.9, 0.0, 0.0, 0.1],
    ])
    s_rev = time_arrow.entropy_production(P_rev, time_arrow.stationary_distribution(P_rev))
    s_cyc = time_arrow.entropy_production(P_cycle, time_arrow.stationary_distribution(P_cycle))
    assert s_cyc > s_rev


def test_entropy_production_bounded_biased_walk_low():
    """Une marche biaisee BORNEE (reflexion aux bords) est quasi-reversible :
    sigma faible (detailed balance approximatif). C'est le substrat S5a d'ICT-18
    -- le fix ne doit PAS le changer (tous flux > 0 via Laplace). Anti-regression."""
    P = np.zeros((5, 5))
    P[0, 0] = 0.3; P[0, 1] = 0.7
    P[4, 4] = 0.3; P[4, 3] = 0.7
    for i in range(1, 4):
        P[i, i - 1] = 0.2; P[i, i] = 0.1; P[i, i + 1] = 0.7
    pi = time_arrow.stationary_distribution(P)
    sigma = time_arrow.entropy_production(P, pi)
    # Marche bornee = quasi reversible (concentration au bord droit mais
    # detailed balance approximatif). sigma doit rester petit (< 0.5).
    assert sigma < 0.5, f"marche bornee devrait rester quasi-reversible, sigma={sigma}"


def test_entropy_production_nonnegative():
    """sigma >= 0 toujours (inegalite de Jensen)."""
    rng = np.random.default_rng(0)
    for _ in range(10):
        P = rng.random((4, 4)) + 0.01
        P = P / P.sum(axis=1, keepdims=True)
        pi = time_arrow.stationary_distribution(P)
        sigma = time_arrow.entropy_production(P, pi)
        assert sigma >= -1e-9
