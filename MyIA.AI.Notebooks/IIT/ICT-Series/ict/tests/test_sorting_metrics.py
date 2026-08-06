"""Tests du module :mod:`ict.sorting_metrics` (ICT self-sorting, Epic #4588).

Chaque test valide un invariant falsifiable des metriques de morphogenese
des self-sorting arrays (Zhang, Goldstein & Levin 2025) : relations entre
``inversion_count`` et ``max_inversions`` (triangulaire), bornes de
``sortedness`` dans [0, 1], mesure locale vs globale (``monotonicity_error``
peut croitre quand les inversions decroissent), appariement stable des
doublons dans ``distance_to_target``, signe et bornes de
``aggregation_index`` (agregation vs repulsion vs cas degeneres), et les
contracteurs de trajectoire (``recovery_time``, courbes).

Pattern herite de ``test_reversibility_budget.py`` : bootstrap ``sys.path``
module-level, sans fixtures, chaque assertion documentee. Le module est
autonome (stdlib only) -- aucune dependance numpy ni reseau.
"""

from __future__ import annotations

import os
import sys

import pytest

_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

from ict import sorting_metrics as sm  # noqa: E402


# --------------------------------------------------------------------------- #
#  invariants globaux : inversion_count <-> max_inversions                     #
# --------------------------------------------------------------------------- #


def test_inversion_count_canonical_values():
    """Cas canoniques : trie = 0, [3,1,2] = 2, trie inverse = max."""
    assert sm.inversion_count([1, 2, 3, 4]) == 0
    # Paires (i<j) en descente pour [3,1,2] : (3,1) et (3,2) -> 2.
    assert sm.inversion_count([3, 1, 2]) == 2
    # Sequence strictement decroissante = toutes les paires en descente.
    assert sm.inversion_count([4, 3, 2, 1]) == 6


def test_max_inversions_is_triangular_and_reached_by_reversed():
    """max_inversions(n) = n*(n-1)/2 (triangulaire), atteint par l'inverse."""
    for n in range(0, 8):
        assert sm.max_inversions(n) == n * (n - 1) // 2
    reversed_n = list(range(7, 0, -1))  # [7,6,...,1]
    assert sm.inversion_count(reversed_n) == sm.max_inversions(len(reversed_n))


# --------------------------------------------------------------------------- #
#  sortedness : borne [0, 1], extremes, relation avec inversion_count          #
# --------------------------------------------------------------------------- #


def test_sortedness_extremes_and_bounds():
    """sortedness trie = 1.0, inverse = 0.0, vide/single = 1.0, toujours dans [0,1]."""
    assert sm.sortedness([1, 2, 3]) == 1.0
    assert sm.sortedness([3, 2, 1]) == 0.0
    assert sm.sortedness([]) == 1.0
    assert sm.sortedness([42]) == 1.0
    # Un cas general reste dans [0, 1].
    for values in ([3, 1, 4, 1, 5, 9, 2, 6], [5, 4, 3, 2, 1], [1, 1, 1]):
        s = sm.sortedness(values)
        assert 0.0 <= s <= 1.0


def test_sortedness_matches_inversion_formula():
    """sortedness([1,3,2]) = 1 - 1/3 = 2/3 (1 inversion sur max(3)=3)."""
    # max_inversions(3) = 3 ; inversion_count([1,3,2]) = 1 (paire (3,2)).
    assert sm.sortedness([1, 3, 2]) == pytest.approx(2.0 / 3.0)


# --------------------------------------------------------------------------- #
#  monotonicity_error : mesure LOCALE, independante des inversions globales    #
# --------------------------------------------------------------------------- #


def test_monotonicity_error_local_measure():
    """trie = 0.0, [3,2,1] = 1.0 (toutes adjacentes descendent), [1,3,2,4] = 1/3."""
    assert sm.monotonicity_error([1, 2, 3, 4]) == 0.0
    # Les deux paires adjacentes (3,2) et (2,1) descendent -> 2/2 = 1.0.
    assert sm.monotonicity_error([3, 2, 1]) == 1.0
    assert sm.monotonicity_error([]) == 0.0
    assert sm.monotonicity_error([7]) == 0.0
    # Une seule descente locale sur 3 paires -> 1/3.
    assert sm.monotonicity_error([1, 3, 2, 4]) == pytest.approx(1.0 / 3.0)


def test_monotonicity_error_local_diverges_from_global_inversions():
    """La mesure LOCALE peut diverger de la mesure GLOBALE.

    C'est le signature documente d'un 'sacrifice local au service du progres
    global' : deux configurations a meme nombre d'inversions (global) peuvent
    avoir des erreurs de monotonie (locale) differentes, parce que
    ``monotonicity_error`` ne compte que les descentes ADJACENTES.
      [2,1,4,3] : inversions (2,1),(4,3) = 2 ; monotonie 2 descentes / 3 = 0.667
      [3,1,2,4] : inversions (3,1),(3,2) = 2 ; monotonie 1 descente  / 3 = 0.333
    Meme inversion_count (2), monotonicity_error different (0.667 vs 0.333) :
    aucune des deux metriques ne determine l'autre.
    """
    a = [2, 1, 4, 3]
    b = [3, 1, 2, 4]
    assert sm.inversion_count(a) == sm.inversion_count(b) == 2
    assert sm.monotonicity_error(a) == pytest.approx(2.0 / 3.0)
    assert sm.monotonicity_error(b) == pytest.approx(1.0 / 3.0)
    assert sm.monotonicity_error(a) > sm.monotonicity_error(b)


# --------------------------------------------------------------------------- #
#  distance_to_target : zero si trie, appariement stable des doublons          #
# --------------------------------------------------------------------------- #


def test_distance_to_target_sorted_is_zero():
    """Deja trie -> 0 ; target explicite == values -> 0 ; inverse [3,2,1] = 4."""
    assert sm.distance_to_target([1, 2, 3, 4]) == 0
    assert sm.distance_to_target([5, 3, 8], target=[5, 3, 8]) == 0
    # [3,2,1] vs cible [1,2,3] : |0-2| + |1-1| + |2-0| = 4.
    assert sm.distance_to_target([3, 2, 1]) == 4


def test_distance_to_target_duplicates_greedy_stable_matching():
    """Les doublons sont apparies par slots stables, en ordre de parcours.

    L'appariement est GREEDY : chaque valeur consomme le prochain slot libre
    de sa cible, dans l'ordre du parcours (first-come first-slot). Ce n'est PAS
    un appariement de cout minimal : deux permutations du meme multi-ensemble
    peuvent donc donner des distances differentes.

    [2,1,2,1] vs cible triee [1,1,2,2] :
      idx0 val2 -> slot 2 (1er slot de 2)    |0-2| = 2
      idx1 val1 -> slot 0 (1er slot de 1)    |1-0| = 1
      idx2 val2 -> slot 3 (2e slot de 2)     |2-3| = 1
      idx3 val1 -> slot 1 (2e slot de 1)     |3-1| = 2   total = 6
    [1,2,1,2] (meme multi-ensemble, ordre different) :
      idx0 val1 -> slot 0                    |0-0| = 0
      idx1 val2 -> slot 2                    |1-2| = 1
      idx2 val1 -> slot 1                    |2-1| = 1
      idx3 val2 -> slot 3                    |3-3| = 0   total = 2
    """
    assert sm.distance_to_target([2, 1, 2, 1]) == 6
    assert sm.distance_to_target([1, 2, 1, 2]) == 2
    # L'asymetrie (6 != 2) confirme que l'appariement est scan-order-dependent :
    # un appariement de cout minimal aurait donne 2 pour les deux.
    assert sm.distance_to_target([2, 1, 2, 1]) > sm.distance_to_target([1, 2, 1, 2])


# --------------------------------------------------------------------------- #
#  aggregation_index : agregation > 0, repulsion < 0, cas degeneres = 0        #
# --------------------------------------------------------------------------- #


def test_aggregation_index_clustered_vs_alternating():
    """Clusterise [1,1,2,2] > 0 ; alterne [1,2,1,2] < 0 ; n<2 = 0.0."""
    # Clusterise : observed 2/3, expected 1/3 -> (2/3-1/3)/(2/3) = 0.5.
    assert sm.aggregation_index([1, 1, 2, 2]) == pytest.approx(0.5)
    # Alterne : observed 0/3, expected 1/3 -> (0-1/3)/(2/3) = -0.5.
    assert sm.aggregation_index([1, 2, 1, 2]) == pytest.approx(-0.5)
    # L'indice agrege > 0 et le repulsif < 0 (contracteur de signe).
    assert sm.aggregation_index([1, 1, 2, 2]) > 0.0
    assert sm.aggregation_index([1, 2, 1, 2]) < 0.0
    # Cas trop courts -> 0.0 par garde.
    assert sm.aggregation_index([5]) == 0.0
    assert sm.aggregation_index([]) == 0.0


def test_aggregation_index_all_same_degenerate_returns_zero():
    """Un canal uniforme [5,5,5,5] -> 0.0 (garde anti-division-par-zero).

    Le cas totalement homogene rend attendu == 1.0 (toutes paires adjacentes
    de meme type), le denominateur ``1 - expected`` s'annule alors. Le module
    choisit de retourner 0.0 (indiscernable du neutre) plutot que de diviser
    par zero -- invariant defensif a verrouiller.
    """
    assert sm.aggregation_index([5, 5, 5, 5]) == 0.0


# --------------------------------------------------------------------------- #
#  delayed_gratification_events : compte les degradations d'une courbe          #
# --------------------------------------------------------------------------- #


def test_delayed_gratification_events_counts_increases():
    """Monotone decroissant -> 0 ; [1,2,3] -> 2 ; [3,1,2] -> 1 ; court -> 0."""
    assert sm.delayed_gratification_events([5, 4, 3, 2, 1]) == 0
    assert sm.delayed_gratification_events([1, 2, 3]) == 2
    # 3->1 (descend), 1->2 (remonte) : une seule degradation locale.
    assert sm.delayed_gratification_events([3, 1, 2]) == 1
    assert sm.delayed_gratification_events([]) == 0
    assert sm.delayed_gratification_events([9]) == 0


# --------------------------------------------------------------------------- #
#  recovery_time : None hors-domaine / jamais atteint, sinon le delai exact    #
# --------------------------------------------------------------------------- #


def test_recovery_time_none_cases():
    """perturbation_step hors-domaine -> None ; jamais recouvre -> None."""
    # Hors-domaine (<=0 ou >= len).
    curve = [1.0, 0.9, 0.5, 0.3]
    assert sm.recovery_time(curve, perturbation_step=0) is None
    assert sm.recovery_time(curve, perturbation_step=-1) is None
    assert sm.recovery_time(curve, perturbation_step=len(curve)) is None
    # Jamais recouvre le niveau d'avant : baseline = curve[1] = 0.9, or la suite
    # (0.5, 0.3) ne rejoint jamais >= 0.9 - tol.
    assert sm.recovery_time(curve, perturbation_step=2) is None


def test_recovery_time_returns_exact_step_count():
    """Retourne le nombre exact de pas pour revenir au niveau d'avant."""
    # baseline = curve[1] = 0.4 ; au t=3, curve[3]=0.4 >= 0.4 - tol -> delai = 1.
    curve = [1.0, 0.4, 0.1, 0.4, 0.9]
    assert sm.recovery_time(curve, perturbation_step=2) == 1
    # Au t=4 on depasse largement, mais le premier retour est deja a t=3.
    # Cas ou le retour se fait au pas suivant uniquement :
    curve2 = [0.2, 0.2, -1.0, 0.2]
    assert sm.recovery_time(curve2, perturbation_step=2) == 1


# --------------------------------------------------------------------------- #
#  courbes : mapping preserve la longueur de la trajectoire                     #
# --------------------------------------------------------------------------- #


def test_curves_map_and_preserve_length():
    """Chaque courbe applique la metrique element par element, meme longueur."""
    traj = [[3, 1, 2], [1, 2, 3], [3, 2, 1]]
    sc = sm.sortedness_curve(traj)
    mc = sm.monotonicity_curve(traj)
    ic = sm.inversions_curve(traj)
    ac = sm.aggregation_curve([[1, 1, 2], [1, 2, 1]])
    assert len(sc) == len(mc) == len(ic) == len(traj) == 3
    assert sc == [sm.sortedness(t) for t in traj]
    assert mc == [sm.monotonicity_error(t) for t in traj]
    assert ic == [sm.inversion_count(t) for t in traj]
    assert ac == [sm.aggregation_index(t) for t in [[1, 1, 2], [1, 2, 1]]]
