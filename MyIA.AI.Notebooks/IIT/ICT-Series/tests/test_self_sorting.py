"""Tests du modele self-sorting et des metriques ICT (stdlib only, pytest)."""

import os
import sys

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ict.self_sorting import SelfSortingArray  # noqa: E402
from ict import sorting_metrics as m  # noqa: E402


def test_homogeneous_bubble_converges():
    arr = SelfSortingArray([5, 3, 8, 1, 9, 2, 7, 4, 6, 0], seed=1)
    arr.run()
    assert arr.values == sorted(arr.values)
    assert not arr.has_move()


def test_homogeneous_insertion_converges():
    vals = [5, 3, 8, 1, 9, 2, 7, 4, 6, 0]
    arr = SelfSortingArray(vals, algotypes=["insertion"] * len(vals), seed=2)
    arr.run()
    assert arr.values == sorted(vals)


def test_chimeric_converges():
    vals = [9, 2, 6, 1, 8, 3, 7, 0, 5, 4]
    algos = ["bubble", "insertion"] * 5
    arr = SelfSortingArray(vals, algotypes=algos, seed=3)
    arr.run()
    assert arr.values == sorted(vals)


def test_sortedness_monotone_in_inversions():
    assert m.sortedness([0, 1, 2, 3]) == 1.0
    assert m.sortedness([3, 2, 1, 0]) == 0.0
    assert m.inversion_count([3, 2, 1, 0]) == 6


def test_distance_to_target_zero_when_sorted():
    assert m.distance_to_target([1, 2, 3, 4]) == 0
    assert m.distance_to_target([4, 3, 2, 1]) > 0


def test_aggregation_index_clustered_vs_random():
    clustered = ["bubble", "bubble", "bubble", "insertion", "insertion", "insertion"]
    alternating = ["bubble", "insertion"] * 3
    assert m.aggregation_index(clustered) > m.aggregation_index(alternating)


def test_frozen_passive_is_carried():
    # mode passif (defaut) : la cellule gelee est un passager, deplace par sa voisine saine
    arr = SelfSortingArray([9, 0], algotypes=["bubble", "bubble"], frozen=[False, True], seed=0)
    arr.run()
    assert arr.values == [0, 9]  # robustesse : le systeme trie malgre la cellule cassee


def test_frozen_obstacle_is_wall():
    # mode obstacle : la cellule gelee est infranchissable
    arr = SelfSortingArray(
        [9, 0], algotypes=["bubble", "bubble"], frozen=[False, True], seed=0, frozen_mode="obstacle"
    )
    arr.run()
    assert arr.values == [9, 0]  # 9 ne peut pas traverser le mur -> reste non trie


def test_robustness_passive_beats_obstacle():
    import random as _r

    vals = _r.Random(0).sample(range(20), 20)
    fz = [i % 4 == 0 for i in range(20)]  # 25% gelees
    passive = SelfSortingArray(vals, frozen=fz, seed=1, frozen_mode="passive").run(record=False)
    obstacle = SelfSortingArray(vals, frozen=fz, seed=1, frozen_mode="obstacle").run(record=False)
    assert m.sortedness(passive.values) >= m.sortedness(obstacle.values)


def test_recovery_time_basic():
    curve = [1.0, 1.0, 0.4, 0.6, 0.9, 1.0]
    assert m.recovery_time(curve, perturbation_step=2) == 3
