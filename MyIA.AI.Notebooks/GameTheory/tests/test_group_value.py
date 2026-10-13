"""
Tests pour la valeur de Shapley de groupe (cooperative_games.group_value).

Référence : Flores R., Molina E., Tejada J. (2019). Evaluating groups with the
generalized Shapley value. 4OR 17(2):141-172. doi:10.1007/s10288-018-0380-8

Les tests assertent des RÉSULTATS PUBLIÉS et des AXIOMES, pas seulement la
cohérence interne :
  - Exemple 1 de l'article (jeu de connectivité à 9 joueurs) : valeurs
    individuelles 360*phi = (-8, -8, -8, 139, 130, 139, -8, -8, -8),
    phi_g({4,6}) = 1/2, phi_g({4,5}) = 187/280, et la décomposition du
    théorème 2 (phi_6(N-4) = 1/8, psi_46 = -1/90, phi_5(N-4) = 1/56,
    psi_45 = 19/72), en arithmétique exacte.
  - Axiomes du théorème 1 : G-null player, G-linearity, G-CBC, G-SPB, et la
    remarque 2 (la valeur additive donne c/n au lieu de 1/(n-c+1)).
  - Théorème 2 et proposition 1 sur des jeux aléatoires.
  - Deux implémentations indépendantes (formule directe / tabulation numpy)
    et la valeur de Shapley du module shapley.py doivent coïncider.

Run with: pytest tests/test_group_value.py -v
"""

import sys
from fractions import Fraction
from itertools import combinations
from pathlib import Path

import numpy as np
import pytest

sys.path.insert(0, str(Path(__file__).parent.parent))

from cooperative_games import (  # noqa: E402
    CoalitionGame,
    GroupValueTable,
    additive_group_value,
    connectivity_game,
    merging_game,
    shapley_group_value,
    shapley_group_value_monte_carlo,
    shapley_value_formula,
)

# Exemple 1 de l'article : sommets 1..9, ramenés aux indices 0..8.
EXAMPLE1_EDGES = [(1, 4), (2, 4), (3, 4), (4, 5), (5, 6), (6, 7), (6, 8), (6, 9)]


def node(k: int) -> int:
    """Indice 0-based du sommet k de l'article."""
    return k - 1


@pytest.fixture(scope="module")
def example1():
    return connectivity_game(
        9, [(node(a), node(b)) for a, b in EXAMPLE1_EDGES], [str(k) for k in range(1, 10)]
    )


@pytest.fixture(scope="module")
def example1_table(example1):
    return GroupValueTable(example1)


def random_game(n: int, seed: int) -> CoalitionGame:
    """Jeu aléatoire gaussien avec v(vide) = 0 (tabulé, donc déterministe)."""
    rng = np.random.default_rng(seed)
    table = {frozenset(): 0.0}
    for size in range(1, n + 1):
        for coalition in combinations(range(n), size):
            table[frozenset(coalition)] = float(rng.normal())
    return CoalitionGame(n, lambda s: table[frozenset(s)])


def restrict(game: CoalitionGame, removed: int) -> tuple:
    """Sous-jeu (N - j, v_{-j}) réindexé, avec la correspondance des indices."""
    kept = [i for i in range(game.n_players) if i != removed]
    sub = CoalitionGame(len(kept), lambda s: game.value({kept[k] for k in s}))
    return sub, {orig: k for k, orig in enumerate(kept)}


# ---------------------------------------------------------------------------
# Exemple 1 de l'article, en arithmétique exacte
# ---------------------------------------------------------------------------


class TestExample1:
    def test_individual_values(self, example1):
        phi360 = [shapley_group_value(example1, {i}, exact=True) * 360 for i in range(9)]
        assert phi360 == [-8, -8, -8, 139, 130, 139, -8, -8, -8]

    def test_group_values(self, example1):
        assert shapley_group_value(example1, {node(4), node(6)}, exact=True) == Fraction(1, 2)
        assert shapley_group_value(example1, {node(4), node(5)}, exact=True) == Fraction(187, 280)
        assert Fraction(187, 280) == Fraction(1, 2) + Fraction(47, 280)

    def test_theorem2_decomposition(self, example1_table):
        t = example1_table
        assert t.restricted_shapley(node(6), [node(4)]) == pytest.approx(1 / 8)
        assert t.complementarity(node(4), node(6)) == pytest.approx(-1 / 90)
        assert t.restricted_shapley(node(5), [node(4)]) == pytest.approx(1 / 56)
        assert t.complementarity(node(4), node(5)) == pytest.approx(19 / 72)

    def test_best_pair_is_not_the_two_best_individuals(self, example1_table):
        (best, value), = example1_table.best_groups(2, top=1)
        assert node(5) in best and value == pytest.approx(187 / 280)
        assert example1_table.group_value([node(4), node(6)]) == pytest.approx(0.5)

    def test_additive_value_ranks_pairs_the_other_way(self, example1):
        # Les deux centres gagnent en valeur additive, perdent en valeur de groupe.
        add_46 = additive_group_value(example1, {node(4), node(6)}, exact=True)
        add_45 = additive_group_value(example1, {node(4), node(5)}, exact=True)
        assert add_46 == Fraction(278, 360) and add_45 == Fraction(269, 360)
        assert add_46 > add_45

    def test_profitability(self, example1_table):
        expected = Fraction(187, 280) - Fraction(139 + 130, 360)
        assert example1_table.profitability([node(4), node(5)]) == pytest.approx(float(expected))


# ---------------------------------------------------------------------------
# Cohérence entre implémentations
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("seed", [0, 1, 2])
def test_table_matches_direct_formula(seed):
    game = random_game(6, seed)
    table = GroupValueTable(game)
    for size in (1, 2, 3, 5):
        for group in combinations(range(6), size):
            assert table.group_value(group) == pytest.approx(shapley_group_value(game, group))


@pytest.mark.parametrize("seed", [3, 4])
def test_singletons_equal_shapley_module(seed):
    game = random_game(6, seed)
    reference = shapley_value_formula(game)
    np.testing.assert_allclose(GroupValueTable(game).shapley(), reference, atol=1e-12)
    for i in range(6):
        assert shapley_group_value(game, {i}) == pytest.approx(reference[i])


def test_merging_game_proxy_carries_group_value():
    game = random_game(6, 5)
    group = {1, 4}
    merged, mapping = merging_game(game, group)
    assert merged.n_players == 5 and mapping[-1] == -1
    proxy_value = shapley_value_formula(merged)[-1]
    assert proxy_value == pytest.approx(shapley_group_value(game, group))


# ---------------------------------------------------------------------------
# Axiomes du théorème 1 et remarque 2
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("n", [3, 5, 6])
def test_g_spb_against_additive_value(n):
    unanimity = CoalitionGame(n, lambda s: 1 if len(s) == n else 0)
    for c in range(1, n + 1):
        group = set(range(c))
        assert shapley_group_value(unanimity, group, exact=True) == Fraction(1, n - c + 1)
        assert additive_group_value(unanimity, group, exact=True) == Fraction(c, n)


def test_g_null_player():
    base = random_game(5, 6)
    # Le joueur 5 est nul : v(S ∪ 5) = v(S).
    game = CoalitionGame(6, lambda s: base.value({i for i in s if i != 5}))
    table = GroupValueTable(game)
    for size in (1, 2, 3):
        for group in combinations(range(5), size):
            assert table.group_value(list(group) + [5]) == pytest.approx(table.group_value(group))


def test_g_linearity():
    v, w = random_game(5, 7), random_game(5, 8)
    a, b = 2.5, -1.25
    mix = CoalitionGame(5, lambda s: a * v.value(s) + b * w.value(s))
    for group in [(0,), (1, 3), (0, 2, 4)]:
        expected = a * shapley_group_value(v, group) + b * shapley_group_value(w, group)
        assert shapley_group_value(mix, group) == pytest.approx(expected)


def test_g_coalitional_balanced_contributions():
    game = random_game(6, 9)
    max_gap = 0.0
    for c in (1, 2):
        for group in combinations(range(6), c):
            outside = [k for k in range(6) if k not in group]
            for i, j in combinations(outside, 2):
                sub_j, idx_j = restrict(game, j)
                sub_i, idx_i = restrict(game, i)
                g_j = {idx_j[k] for k in group}
                g_i = {idx_i[k] for k in group}
                lhs = (shapley_group_value(game, set(group) | {i}) - shapley_group_value(game, group)) - (
                    shapley_group_value(sub_j, g_j | {idx_j[i]}) - shapley_group_value(sub_j, g_j)
                )
                rhs = (shapley_group_value(game, set(group) | {j}) - shapley_group_value(game, group)) - (
                    shapley_group_value(sub_i, g_i | {idx_i[j]}) - shapley_group_value(sub_i, g_i)
                )
                max_gap = max(max_gap, abs(lhs - rhs))
    assert max_gap < 1e-12


# ---------------------------------------------------------------------------
# Théorème 2 et proposition 1
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("seed", [10, 11, 12])
def test_theorem2_on_random_games(seed):
    table = GroupValueTable(random_game(6, seed))
    for c in (1, 2, 3):
        for group in combinations(range(6), c):
            for i in set(range(6)) - set(group):
                lhs = table.group_value(list(group) + [i]) - table.group_value(group)
                rhs = table.restricted_shapley(i, group) + table.group_complementarity(group, i)
                assert lhs == pytest.approx(rhs, abs=1e-12)


def test_group_complementarity_of_singleton_is_psi():
    table = GroupValueTable(random_game(5, 13))
    for i, j in combinations(range(5), 2):
        assert table.group_complementarity({i}, j) == pytest.approx(table.complementarity(i, j))


def test_proposition1_rationality_and_monotonicity():
    # v(S) = |S|^2 est superadditif et monotone.
    game = CoalitionGame(6, lambda s: len(s) ** 2)
    table = GroupValueTable(game)
    for size in range(1, 6):
        for group in combinations(range(6), size):
            assert table.group_value(group) >= game.value(set(group)) - 1e-12
            for extra in set(range(6)) - set(group):
                assert table.group_value(group) <= table.group_value(list(group) + [extra]) + 1e-12


# ---------------------------------------------------------------------------
# Monte Carlo, recherche gloutonne, garde-fous
# ---------------------------------------------------------------------------


def test_monte_carlo_is_unbiased_and_reproducible(example1):
    group = {node(4), node(5)}
    estimate, stderr = shapley_group_value_monte_carlo(example1, group, n_samples=4000, seed=42)
    assert stderr > 0
    assert abs(estimate - 187 / 280) < 4 * stderr
    again = shapley_group_value_monte_carlo(example1, group, n_samples=4000, seed=42)
    assert again == (estimate, stderr)


def test_greedy_starts_with_best_individual(example1_table):
    path = example1_table.greedy_group(2)
    phi = example1_table.shapley()
    assert path[0][0] == int(np.argmax(phi))
    assert path[1][1] == pytest.approx(187 / 280)


def test_invalid_inputs_raise(example1, example1_table):
    with pytest.raises(ValueError):
        shapley_group_value(example1, set())
    with pytest.raises(ValueError):
        shapley_group_value(example1, {9})
    with pytest.raises(ValueError):
        example1_table.group_complementarity({0}, 0)
    with pytest.raises(ValueError):
        shapley_group_value_monte_carlo(example1, {0}, n_samples=1)
    with pytest.raises(ValueError):
        GroupValueTable(CoalitionGame(23, lambda s: 0))
