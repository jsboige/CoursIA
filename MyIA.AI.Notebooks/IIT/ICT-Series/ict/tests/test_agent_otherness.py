"""Tests du module :mod:`ict.agent_otherness` (strate 6, Epic #4588, issue #7291).

Chaque test valide une propriete falsifiable d'un candidat mesure d'alterite
agentique. Pattern herite de ``test_reversibility_budget.py`` : bootstrap
``sys.path`` module-level, sans fixtures, tolerances commentees.
"""

from __future__ import annotations

import os
import sys

import numpy as np
import pytest

_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

from ict import agent_otherness as ao  # noqa: E402


# --------------------------------------------------------------------------- #
#  Candidat 1 -- setpoint_diversity                                            #
# --------------------------------------------------------------------------- #


def test_setpoint_diversity_monoculture_is_zero():
    """Une monoculture parfaite (setpoints identiques) a une diversite nulle."""
    sp = np.zeros((5, 3))
    assert ao.setpoint_diversity(sp) == pytest.approx(0.0, abs=1e-12)


def test_setpoint_diversity_pairwise_mean_matches_manual():
    """La distance euclidienne moyenne coincide avec le calcul manuel."""
    sp = np.array([[0.0, 0.0], [3.0, 4.0]])  # distance 5, moyenne sur 1 couple = 5
    assert ao.setpoint_diversity(sp, metric="pairwise_mean") == pytest.approx(5.0)


def test_setpoint_diversity_entropy_zero_for_identical_points():
    """L'entropie d'une monoculture quantifiee est nulle."""
    sp = np.ones((6, 2))
    assert ao.setpoint_diversity(sp, metric="entropy") == pytest.approx(0.0, abs=1e-12)


def test_setpoint_diversity_entropy_grows_with_spread():
    """Des setpoints bien separes donnent une entropie superieure a une monoculture."""
    monoculture = np.ones((9, 2))
    spread = np.array(
        [[float(i), float(j)] for i in range(3) for j in range(3)]
    )
    assert ao.setpoint_diversity(spread, metric="entropy") > ao.setpoint_diversity(
        monoculture, metric="entropy"
    )


def test_setpoint_diversity_rejects_bad_shape():
    with pytest.raises(ValueError):
        ao.setpoint_diversity(np.zeros(5))


def test_setpoint_diversity_rejects_bad_metric():
    with pytest.raises(ValueError):
        ao.setpoint_diversity(np.zeros((3, 2)), metric="bogus")


# --------------------------------------------------------------------------- #
#  Candidat 2 -- policy_mutual_information                                     #
# --------------------------------------------------------------------------- #


def test_mi_independent_policies_is_zero():
    """Deux politiques independantes -> MI nulle."""
    # lignes et colonnes factorisables (independance)
    jc = np.outer(np.array([10, 20, 30]), np.array([5, 15, 30]))
    assert ao.policy_mutual_information(jc) == pytest.approx(0.0, abs=1e-9)


def test_mi_identical_policies_is_positive():
    """Deux politiques identiques (diagonale jointe) -> MI strictement positive."""
    jc = np.diag(np.array([10.0, 10.0, 10.0]))
    mi = ao.policy_mutual_information(jc)
    assert mi > 0.0


def test_mi_empty_counts_is_zero():
    assert ao.policy_mutual_information(np.zeros((3, 3))) == 0.0


def test_mi_rejects_bad_shape():
    with pytest.raises(ValueError):
        ao.policy_mutual_information(np.zeros(5))


# --------------------------------------------------------------------------- #
#  Candidat 3 -- occupied_basin_count                                          #
# --------------------------------------------------------------------------- #


def test_basin_count_single_cluster_is_one():
    """Une trajectoire cantonnee a un amas dense -> 1 bassin."""
    rng = np.random.default_rng(0)
    traj = rng.normal(loc=0.0, scale=0.05, size=(40, 2))
    assert ao.occupied_basin_count(traj, n_neighbors=5) == 1


def test_basin_count_two_well_separated_clusters_is_two():
    """Deux amas bien separes -> 2 bassins (alterite structurelle preservee)."""
    rng = np.random.default_rng(1)
    cluster_a = rng.normal(loc=[0.0, 0.0], scale=0.05, size=(25, 2))
    cluster_b = rng.normal(loc=[10.0, 10.0], scale=0.05, size=(25, 2))
    traj = np.vstack([cluster_a, cluster_b])
    assert ao.occupied_basin_count(traj, n_neighbors=5) == 2


def test_basin_count_single_point_is_one():
    assert ao.occupied_basin_count(np.array([[1.0, 2.0]])) == 1


def test_basin_count_rejects_bad_shape():
    with pytest.raises(ValueError):
        ao.occupied_basin_count(np.zeros(5))
