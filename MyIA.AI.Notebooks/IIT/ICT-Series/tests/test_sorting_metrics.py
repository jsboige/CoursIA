"""Tests de couverture complete du module ``ict.sorting_metrics`` (stdlib only, pytest).

Les quelques assertions sur les metriques presentes dans ``test_self_sorting.py``
restaient incidentes (elles validaient surtout le modele self-sorting). Ce fichier
prend en charge la couverture *dediee* du module de metriques de morphogenese
minimale : ordre (inversions, sortedness, erreur de monotonie, deplacement
restant), courbes de trajectoire, delai de gratification, agregation par algotype
et temps de recuperation -- avec leurs cas limites (n < 2, doublons, repulsion,
non-recuperation). Cf. Epic #4588 (composant ``tests/test_sorting_metrics.py``).
"""

import os
import sys

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ict import sorting_metrics as m  # noqa: E402


# --------------------------------------------------------------------- inversions
def test_inversion_count_sorted_and_reversed():
    assert m.inversion_count([]) == 0
    assert m.inversion_count([7]) == 0
    assert m.inversion_count([0, 1, 2, 3]) == 0
    assert m.inversion_count([3, 2, 1, 0]) == 6  # toutes les paires sont inversees


def test_inversion_count_with_duplicates():
    # les egalites ne comptent pas (condition stricte values[i] > values[j])
    assert m.inversion_count([1, 1, 1]) == 0
    assert m.inversion_count([2, 2, 1]) == 2  # (0,2) et (1,2)


def test_max_inversions_matches_reversed():
    for n in (0, 1, 2, 4, 7):
        reversed_list = list(range(n, 0, -1))
        assert m.max_inversions(n) == m.inversion_count(reversed_list)


# --------------------------------------------------------------------- sortedness
def test_sortedness_bounds():
    assert m.sortedness([0, 1, 2, 3]) == 1.0
    assert m.sortedness([3, 2, 1, 0]) == 0.0
    partial = m.sortedness([0, 2, 1, 3])  # une seule inversion sur 6 possibles
    assert 0.0 < partial < 1.0
    assert partial == pytest.approx(1.0 - 1 / 6)


def test_sortedness_short_inputs_are_perfect():
    # convention du module : n < 2 -> deja trie
    assert m.sortedness([]) == 1.0
    assert m.sortedness([42]) == 1.0


# -------------------------------------------------------------- monotonicity_error
def test_monotonicity_error_bounds():
    assert m.monotonicity_error([0, 1, 2, 3]) == 0.0
    assert m.monotonicity_error([3, 2, 1, 0]) == 1.0
    assert m.monotonicity_error([]) == 0.0
    assert m.monotonicity_error([42]) == 0.0


def test_monotonicity_is_local_not_global():
    # mesure *locale* (paires adjacentes) distincte de la mesure globale (inversions) :
    # ici une seule descente adjacente alors que plusieurs inversions globales existent
    values = [1, 3, 2, 4]
    assert m.monotonicity_error(values) == pytest.approx(1 / 3)  # une descente sur 3 paires
    assert m.inversion_count(values) == 1


# -------------------------------------------------------------- distance_to_target
def test_distance_to_target_zero_when_sorted():
    assert m.distance_to_target([1, 2, 3, 4]) == 0
    assert m.distance_to_target([4, 3, 2, 1]) > 0


def test_distance_to_target_explicit_value():
    # [4,3,2,1] vers sorted [1,2,3,4] : deplacements |0-3|+|1-2|+|2-1|+|3-0| = 8
    assert m.distance_to_target([4, 3, 2, 1]) == 8


def test_distance_to_target_stable_for_duplicates():
    # branche d'appariement stable des rangs en presence de doublons
    # [2,1,2,1] vers [1,1,2,2] : 2->slot2, 1->slot0, 2->slot3, 1->slot1 = 2+1+1+2 = 6
    assert m.distance_to_target([2, 1, 2, 1]) == 6
    # cible explicite egale a l'entree -> aucun deplacement
    assert m.distance_to_target([5, 5, 1], target=[5, 5, 1]) == 0


# ------------------------------------------------------------------------- courbes
def test_curves_apply_scalar_pointwise_and_preserve_length():
    trajectory = [[3, 2, 1, 0], [2, 3, 0, 1], [0, 1, 2, 3]]
    s_curve = m.sortedness_curve(trajectory)
    mono_curve = m.monotonicity_curve(trajectory)
    inv_curve = m.inversions_curve(trajectory)
    assert len(s_curve) == len(mono_curve) == len(inv_curve) == len(trajectory)
    assert s_curve == [m.sortedness(v) for v in trajectory]
    assert mono_curve == [m.monotonicity_error(v) for v in trajectory]
    assert inv_curve == [m.inversion_count(v) for v in trajectory]
    # la trajectoire se termine triee
    assert s_curve[-1] == 1.0 and inv_curve[-1] == 0


# ------------------------------------------------------- delayed_gratification_events
def test_delayed_gratification_counts_only_strict_rises():
    assert m.delayed_gratification_events([0.9, 0.6, 0.4, 0.2]) == 0  # monotone decroissant
    assert m.delayed_gratification_events([0.5, 0.6, 0.4, 0.7]) == 2  # deux remontees
    assert m.delayed_gratification_events([0.5, 0.5, 0.5]) == 0  # egalite non comptee
    assert m.delayed_gratification_events([0.5]) == 0  # pas de transition


# ----------------------------------------------------------------- aggregation_index
def test_aggregation_index_clustered_vs_alternating():
    clustered = ["bubble", "bubble", "bubble", "insertion", "insertion", "insertion"]
    alternating = ["bubble", "insertion"] * 3
    assert m.aggregation_index(clustered) > 0.0  # regroupement du kin
    assert m.aggregation_index(alternating) < 0.0  # repulsion (mieux melange que l'aleatoire)
    assert m.aggregation_index(clustered) > m.aggregation_index(alternating)


def test_aggregation_index_degenerate_cases():
    assert m.aggregation_index([]) == 0.0
    assert m.aggregation_index(["bubble"]) == 0.0
    # un seul algotype : expected == 1.0 -> division protegee -> 0.0
    assert m.aggregation_index(["bubble", "bubble", "bubble"]) == 0.0


def test_aggregation_curve_pointwise():
    trajectory = [["a", "b", "a", "b"], ["a", "a", "b", "b"]]
    assert m.aggregation_curve(trajectory) == [m.aggregation_index(a) for a in trajectory]


# --------------------------------------------------------------------- recovery_time
def test_recovery_time_basic():
    # revient au niveau d'avant perturbation (curve[1]=1.0) au pas 5 -> 5-2 = 3
    curve = [1.0, 1.0, 0.4, 0.6, 0.9, 1.0]
    assert m.recovery_time(curve, perturbation_step=2) == 3


def test_recovery_time_immediate():
    # des le pas de perturbation, le niveau anterieur est deja atteint -> 0
    assert m.recovery_time([0.8, 0.9], perturbation_step=1) == 0


def test_recovery_time_never_recovers_returns_none():
    assert m.recovery_time([1.0, 0.5, 0.4, 0.3], perturbation_step=1) is None


def test_recovery_time_out_of_range_returns_none():
    curve = [1.0, 0.4, 0.9]
    assert m.recovery_time(curve, perturbation_step=0) is None
    assert m.recovery_time(curve, perturbation_step=len(curve)) is None
