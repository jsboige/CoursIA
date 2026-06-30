"""
Tests pour le calcul de la valeur de Shapley (cooperative_games.shapley).

Couvre les contrats pedagogiquement actifs du module, c'est-a-dire ceux
consommes par les notebooks GameTheory-15 / 15b / 15c (Cooperative Games) :
  - shapley_value_exact / shapley_value_formula / shapley_value_monte_carlo
  - shapley_value_with_variance
  - ShapleyCalculator (interface unifiee + selection auto de methode)
  - shapley_decomposition / marginal_contribution

Les tests assertent des RESULTATS MATHEMATIQUES CONNUS (forme close), pas
seulement la coherence interne entre deux fonctions du module :
  - Airport game (Littlechild & Owen 1973) : allocation de cout pour
    c = [1, 2, 3] -> phi = [1/3, 5/6, 11/6]. Cas canonique de cost-sharing,
    verifiable a la main (6 permutations, somme telescopee = v(N)).
  - Axiomes de Shapley : efficiency (sum phi = v(N)), symetrie (joueurs
    interchangeables -> phi egaux), null player (joueur inutile -> phi = 0),
    additivite (phi(v + w) = phi(v) + phi(w)).
  - Cohesion exact vs formula : deux implementations independantes du meme
    concept doivent converger (permutations vs coalitions ponderees).

Run with: pytest tests/test_shapley.py -v
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Ajoute GameTheory/ au path pour pouvoir importer le package cooperative_games
sys.path.insert(0, str(Path(__file__).parent.parent))

from cooperative_games import (
    CoalitionGame,
    WeightedVotingGame,
    marginal_contribution,
    shapley_value_exact,
    shapley_value_formula,
    shapley_value_monte_carlo,
    shapley_value_with_variance,
    ShapleyCalculator,
    shapley_decomposition,
)
# majority_game / unanimity_game sont des helpers de coalition_games (non
# re-exportes par le __init__ du package) -> import depuis le sous-module.
from cooperative_games.coalition_games import majority_game, unanimity_game


# ----------------------------------------------------------------------------
# Fixtures : jeux cooperatifs canoniques reutilisables.
# ----------------------------------------------------------------------------

@pytest.fixture
def airport_game():
    """
    Airport game (cost-sharing) : v(S) = max des couts des membres de S.

    Cas canonique de la valeur de Shapley (Littlechild & Owen 1973) : n
    compagnies partagent une piste ; la compagnie i a besoin d'une longueur
    c_i ; le cout de servir une coalition est la longueur la plus longue
    requise. Forme close de l'allocation de Shapley pour c croissants :

        phi_i = sum_{k=1}^{i} (c_k - c_{k-1}) / (n - k + 1),   c_0 = 0

    Pour c = [1, 2, 3] (n = 3) :
        phi_1 = 1/3
        phi_2 = 1/3 + 1/2 = 5/6
        phi_3 = 1/3 + 1/2 + 1 = 11/6
    Verifie a la main sur les 6 permutations (somme telescopee = v(N) = 3).
    """
    costs = [1.0, 2.0, 3.0]

    def v(coalition):
        # max sur les couts des membres ; 0 pour la coalition vide (v(vide) = 0).
        return max((costs[i] for i in coalition), default=0.0)

    return CoalitionGame(3, v, player_names=["Court", "Moyen", "Long"])


@pytest.fixture
def airport_expected():
    """Forme close de l'allocation de Shapley pour l'airport c=[1,2,3]."""
    return np.array([1.0 / 3.0, 5.0 / 6.0, 11.0 / 6.0])


# ----------------------------------------------------------------------------
# Airport game : le cas canonique (cost-sharing, forme close connue).
# ----------------------------------------------------------------------------

class TestAirportGame:
    """Allocation de Shapley sur l'airport game (forme close de Littlechild-Owen)."""

    def test_shapley_exact_matches_closed_form(self, airport_game, airport_expected):
        """shapley_value_exact doit donner [1/3, 5/6, 11/6] pour c=[1,2,3]."""
        phi = shapley_value_exact(airport_game)
        np.testing.assert_allclose(phi, airport_expected, atol=1e-10)

    def test_shapley_formula_matches_closed_form(self, airport_game, airport_expected):
        """La formule par coalitions ponderees doit donner la meme forme close."""
        phi = shapley_value_formula(airport_game)
        np.testing.assert_allclose(phi, airport_expected, atol=1e-10)

    def test_efficiency_airport(self, airport_game):
        """Axiome d'efficiency : sum(phi) = v(grande coalition) = 3."""
        phi = shapley_value_exact(airport_game)
        assert np.isclose(phi.sum(), airport_game.grand_coalition_value())
        assert np.isclose(phi.sum(), 3.0)

    def test_monotone_allocation(self, airport_game):
        """Un joueur demandant une piste plus longue paie davantage."""
        phi = shapley_value_exact(airport_game)
        assert phi[0] < phi[1] < phi[2]


# ----------------------------------------------------------------------------
# Axiomes de Shapley : efficiency, symetrie, null player, additivite.
# ----------------------------------------------------------------------------

class TestShapleyAxioms:
    """Les 4 axiomes caracterisant la valeur de Shapley."""

    def test_efficiency_majority(self):
        """sum(phi) = v(N) sur un majority game (axiome d'efficiency)."""
        game = majority_game(3)  # VotingGame(3, quota=2)
        phi = shapley_value_exact(game)
        assert np.isclose(phi.sum(), game.grand_coalition_value())
        assert np.isclose(phi.sum(), 1.0)

    def test_symmetry_majority(self):
        """Joueur symetriques d'un majority game -> phi egaux (axiome de symetrie)."""
        game = majority_game(4)  # quota 3, tous interchangeables
        phi = shapley_value_exact(game)
        np.testing.assert_allclose(phi, np.full(4, 0.25), atol=1e-10)

    def test_symmetry_weighted_voting_equal_weights(self):
        """Jeu de vote ponderé a poids egaux : tous symetriques."""
        game = WeightedVotingGame([1, 1, 1, 1, 1], quota=3)
        phi = shapley_value_exact(game)
        np.testing.assert_allclose(phi, np.full(5, 0.2), atol=1e-10)

    def test_null_player_unanimity(self):
        """Unanimity game : le joueur hors de l'ensemble requis est un null player (phi = 0)."""
        game = unanimity_game(3, {0, 1})  # joueur 2 jamais requis
        phi = shapley_value_exact(game)
        assert np.isclose(phi[2], 0.0)
        # Les joueurs requis sont symetriques -> parts egales.
        np.testing.assert_allclose(phi, [0.5, 0.5, 0.0], atol=1e-10)

    def test_weighted_voting_shapley_shubik(self):
        """Indice de pouvoir de Shapley-Shubik pour [3; 2, 1, 1] = [2/3, 1/6, 1/6].

        Resultat de manuel : le joueur 0 (poids 2) est pivotal dans 4 des 6
        permutations ; les deux joueurs de poids 1 sont symetriques et
        pivotaux dans 1 permutation chacun. Aucun n'est un dummy : un joueur
        de poids 1 est decisif des qu'il s'associe au joueur 0 (coalition
        {0, i} de poids 3 >= quota 3).
        """
        game = WeightedVotingGame([2, 1, 1], quota=3)
        phi = shapley_value_exact(game)
        np.testing.assert_allclose(phi, [2.0 / 3.0, 1.0 / 6.0, 1.0 / 6.0], atol=1e-10)
        # Symetrie des deux joueurs de poids 1.
        assert np.isclose(phi[1], phi[2])
        # Le joueur lourd concentre le pouvoir.
        assert phi[0] > phi[1]

    def test_additivity(self):
        """Axiome d'additivite : phi(v + w) = phi(v) + phi(w)."""
        n = 3

        def v(S):
            return float(len(S) ** 2)

        def w(S):
            return float(2 * len(S))

        def v_plus_w(S):
            return v(S) + w(S)

        phi_v = shapley_value_exact(CoalitionGame(n, v))
        phi_w = shapley_value_exact(CoalitionGame(n, w))
        phi_sum = shapley_value_exact(CoalitionGame(n, v_plus_w))
        np.testing.assert_allclose(phi_sum, phi_v + phi_w, atol=1e-10)


# ----------------------------------------------------------------------------
# Cohesion exact vs formula : deux implementations independantes.
# ----------------------------------------------------------------------------

class TestExactVsFormula:
    """shapley_value_exact (permutations) et _formula (coalitions ponderees)
    implementent le meme concept -> resultats identiques."""

    def test_match_voting_game(self):
        game = majority_game(3)
        np.testing.assert_allclose(
            shapley_value_exact(game), shapley_value_formula(game), atol=1e-10
        )

    def test_match_weighted_voting(self):
        game = WeightedVotingGame([4, 3, 2, 1], quota=6)
        np.testing.assert_allclose(
            shapley_value_exact(game), shapley_value_formula(game), atol=1e-10
        )

    def test_match_airport(self, airport_game):
        np.testing.assert_allclose(
            shapley_value_exact(airport_game),
            shapley_value_formula(airport_game),
            atol=1e-10,
        )


# ----------------------------------------------------------------------------
# Monte Carlo : convergence + reproductibilite + variance.
# ----------------------------------------------------------------------------

class TestMonteCarlo:
    """Approximation Monte Carlo (sans biais, variance en O(1/sqrt(n)))."""

    def test_mc_converges_to_exact(self):
        """L'estimation MC seeded converge vers la valeur exacte."""
        game = majority_game(3)  # exact [1/3, 1/3, 1/3]
        exact = shapley_value_exact(game)
        mc = shapley_value_monte_carlo(game, n_samples=20000, seed=42)
        np.testing.assert_allclose(mc, exact, atol=0.02)

    def test_mc_reproducible_with_seed(self):
        """Meme graine -> meme estimation (determinisme)."""
        game = WeightedVotingGame([4, 3, 2, 1], quota=6)
        a = shapley_value_monte_carlo(game, n_samples=5000, seed=7)
        b = shapley_value_monte_carlo(game, n_samples=5000, seed=7)
        np.testing.assert_array_equal(a, b)

    def test_mc_efficiency_holds_exactly(self):
        """Chaque permutation telescope : la moyenne MC somme a v(N) exactement."""
        game = WeightedVotingGame([4, 3, 2, 1], quota=6)
        mc = shapley_value_monte_carlo(game, n_samples=2000, seed=0)
        assert np.isclose(mc.sum(), game.grand_coalition_value())

    def test_with_variance_returns_shapes(self):
        game = majority_game(3)
        vals, errs = shapley_value_with_variance(game, n_samples=5000, seed=0)
        assert vals.shape == (3,)
        assert errs.shape == (3,)
        assert np.all(errs >= 0)

    def test_with_variance_converges(self):
        game = majority_game(3)
        exact = shapley_value_exact(game)
        vals, errs = shapley_value_with_variance(game, n_samples=20000, seed=0)
        np.testing.assert_allclose(vals, exact, atol=0.03)
        # Les erreurs standards decroissent en ~1/sqrt(n) -> petites ici.
        assert np.all(errs < 0.05)


# ----------------------------------------------------------------------------
# ShapleyCalculator : interface unifiee + selection auto de methode.
# ----------------------------------------------------------------------------

class TestShapleyCalculator:
    """L'interface unifiee choisit automatiquement entre exact / formula / MC."""

    def test_method_exact(self):
        game = majority_game(3)
        calc = ShapleyCalculator(game, method='exact')
        vals = calc.compute()
        np.testing.assert_allclose(vals, [1 / 3, 1 / 3, 1 / 3], atol=1e-10)
        assert calc._method_used == 'exact'

    def test_method_formula(self):
        game = majority_game(3)
        calc = ShapleyCalculator(game, method='formula')
        vals = calc.compute()
        np.testing.assert_allclose(vals, [1 / 3, 1 / 3, 1 / 3], atol=1e-10)
        assert calc._method_used == 'formula'

    def test_auto_small_game_uses_formula(self):
        """auto avec n <= EXACT_THRESHOLD (10) -> formula (exact)."""
        game = majority_game(3)
        calc = ShapleyCalculator(game, method='auto')
        vals = calc.compute()
        assert calc._method_used == 'formula'
        np.testing.assert_allclose(vals, [1 / 3, 1 / 3, 1 / 3], atol=1e-10)

    def test_auto_large_game_uses_monte_carlo(self):
        """auto avec n > EXACT_THRESHOLD -> monte_carlo."""
        game = majority_game(11)  # n = 11 > 10
        calc = ShapleyCalculator(game, method='auto', n_samples=5000, seed=1)
        vals = calc.compute()
        assert calc._method_used == 'monte_carlo'
        assert vals.shape == (11,)
        # Game symetrique -> chaque joueur ~ 1/11 ; efficiency exacte par telescope.
        assert np.isclose(vals.sum(), game.grand_coalition_value())
        np.testing.assert_allclose(vals, np.full(11, 1.0 / 11.0), atol=0.03)

    def test_standard_errors_none_for_exact(self):
        """Les erreurs standards ne sont calculees qu'en mode monte_carlo."""
        game = majority_game(3)
        c_exact = ShapleyCalculator(game, method='exact')
        c_exact.compute()
        assert c_exact.standard_errors is None
        c_mc = ShapleyCalculator(game, method='monte_carlo', n_samples=2000, seed=0)
        c_mc.compute()
        assert c_mc.standard_errors is not None

    def test_unknown_method_raises(self):
        game = majority_game(3)
        calc = ShapleyCalculator(game, method='bogus')
        with pytest.raises(ValueError):
            calc.compute()

    def test_values_property_is_lazy(self):
        """La propriete .values declenche le calcul si non encore fait."""
        game = majority_game(3)
        calc = ShapleyCalculator(game, method='exact')
        assert calc._values is None
        _ = calc.values
        assert calc._values is not None

    def test_summary_contains_expected_fields(self):
        game = majority_game(3)
        calc = ShapleyCalculator(game, method='exact')
        text = calc.summary()
        assert "Shapley Value Analysis" in text
        assert "Player_0" in text
        assert "Efficiency check" in text

    def test_to_dict_structure(self):
        game = majority_game(3)
        calc = ShapleyCalculator(game, method='exact')
        out = calc.to_dict()
        assert {"player_names", "shapley_values", "grand_coalition_value", "method"} <= set(out.keys())
        assert len(out["shapley_values"]) == 3
        assert out["method"] == 'exact'


# ----------------------------------------------------------------------------
# Decomposition & marginal contribution.
# ----------------------------------------------------------------------------

class TestDecompositionAndMarginal:
    """shapley_decomposition et marginal_contribution."""

    def test_decomposition_total_matches_formula(self):
        """La decomposition par taille de coalition somme a la valeur de Shapley."""
        game = WeightedVotingGame([4, 3, 2, 1], quota=6)
        phi = shapley_value_formula(game)
        for i in range(game.n_players):
            dec = shapley_decomposition(game, i)
            assert np.isclose(dec["total"], phi[i])
            assert dec["by_size"].shape == (game.n_players,)
            assert dec["player"] == i
            assert dec["player_name"] == game.player_names[i]

    def test_decomposition_null_player_zero(self):
        """Un null player a une decomposition nulle a toutes les tailles."""
        game = unanimity_game(3, {0, 1})  # joueur 2 = null
        dec = shapley_decomposition(game, 2)
        assert np.isclose(dec["total"], 0.0)
        assert np.allclose(dec["by_size"], 0.0)

    def test_marginal_contribution_wrapper(self):
        """marginal_contribution delegue au jeu (v(S u {i}) - v(S))."""
        costs = [1.0, 2.0, 3.0]

        def v(S):
            return max((costs[i] for i in S), default=0.0)

        game = CoalitionGame(3, v)
        # Joueur 2 (cout 3) rejoint {0,1} : 3 - 2 = 1.
        assert np.isclose(marginal_contribution(game, 2, {0, 1}), 1.0)
        # Joueur 0 rejoint {} : 1 - 0 = 1.
        assert np.isclose(marginal_contribution(game, 0, set()), 1.0)
        # Joueur 0 rejoint {1} (cout 2) : 2 - 2 = 0 (deja couvert).
        assert np.isclose(marginal_contribution(game, 0, {1}), 0.0)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
