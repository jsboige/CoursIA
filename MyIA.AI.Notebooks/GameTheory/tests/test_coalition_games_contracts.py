"""
Tests de contrat pour WeightedVotingGame (cooperative_games.coalition_games).

Deux contrats etaient implicites et donc non verifies (#20309) :

  - **Les poids sont non negatifs.** Toute la classe repose sur la monotonie
    du jeu (ajouter un joueur ne fait jamais perdre une coalition), qui est
    ce qui rend l'egalite "contribution marginale nulle" et "joueur inutile"
    equivalentes. Un poids negatif casse cette premisse en silence.
  - **`banzhaf_index` quand aucun joueur n'est critique.** L'indice normalise
    est alors le rapport 0/0 ; la fonction rendait une distribution uniforme
    sans le dire, ce qui donne a un jeu degenere l'apparence d'une mesure de
    pouvoir reelle.

Run with: pytest tests/test_coalition_games_contracts.py -v
"""

import sys
import warnings
from pathlib import Path

import numpy as np
import pytest

# Ajoute GameTheory/ au path pour pouvoir importer le package cooperative_games
sys.path.insert(0, str(Path(__file__).parent.parent))

from cooperative_games.coalition_games import WeightedVotingGame


class TestNonNegativeWeightsContract:
    """Le constructeur refuse un poids negatif (voie 1 de #20309)."""

    def test_negative_weight_is_rejected(self):
        with pytest.raises(ValueError, match="non-negative"):
            WeightedVotingGame([-1, 2, 2], quota=3)

    def test_rejection_names_the_offending_weights(self):
        with pytest.raises(ValueError, match=r"\[2, -1\]"):
            WeightedVotingGame([2, -1], quota=2)

    def test_rejected_game_is_one_where_is_dummy_would_have_lied(self):
        """Le jeu refuse n'est pas un cas d'ecole abstrait : mesure sur la
        version d'avant le garde-fou, `[-2, 3, 2]` avec quota 3 donne
        v({1}) = 1, v({0,1}) = 0, donc mc(0, {1}) = -1 - le joueur 0 DETRUIT
        une coalition gagnante - et pourtant `is_dummy(0)` repondait True,
        sa garde `mc > 1e-10` etant aveugle a une contribution negative.
        C'est le contre-exemple qui fonde le rejet au constructeur (voie 1)
        plutot qu'un simple `abs()` dans `is_dummy` (voie 2) : le jeu reste
        incoherent pour les autres methodes, l'indice de Banzhaf y donnant
        deja 0.0 de pouvoir au joueur 0."""
        with pytest.raises(ValueError, match="non-negative"):
            WeightedVotingGame([-2, 3, 2], quota=3)

    def test_zero_weight_is_accepted(self):
        """Un poids nul est legitime : le joueur existe mais ne pese rien."""
        game = WeightedVotingGame([3, 0, 1], quota=4)
        assert game.is_dummy(1) is True

    def test_all_positive_weights_are_accepted(self):
        game = WeightedVotingGame([2, 1, 1], quota=3)
        assert game.value({0, 1}) == 1.0
        assert game.value({1, 2}) == 0.0

    def test_fractional_quota_is_accepted(self):
        """Un quota fractionnaire reste legitime (cf. usages politiques)."""
        game = WeightedVotingGame([25, 20, 15], quota=0.65)
        assert game.is_winning({0})

    def test_monotonicity_holds_for_every_non_negative_game(self):
        """La propriete qui justifie voie 1 : avec des poids >= 0, rejoindre
        une coalition ne peut pas la faire perdre, donc toute contribution
        marginale est >= 0 - et `mc > 0` y equivaut a `abs(mc) > 0`, ce qui
        rend le test de `is_dummy` correct sans valeur absolue."""
        game = WeightedVotingGame([3, 2, 1, 1], quota=4)
        for player in range(game.n_players):
            for coalition in game.all_coalitions():
                if player in coalition:
                    continue
                assert game.marginal_contribution(player, set(coalition)) >= 0

    def test_is_dummy_agrees_with_its_definition(self):
        """`is_dummy` doit coincider avec "toutes les contributions
        marginales sont nulles", la definition que sa docstring annonce."""
        for weights, quota in ([[2, 1, 1], 3], [[3, 0, 1], 4], [[1, 1, 1], 2]):
            game = WeightedVotingGame(weights, quota=quota)
            for player in range(game.n_players):
                marginals = [
                    game.marginal_contribution(player, set(coalition))
                    for coalition in game.all_coalitions()
                    if player not in coalition
                ]
                assert game.is_dummy(player) == all(
                    abs(mc) <= 1e-10 for mc in marginals
                ), f"{weights} q={quota} joueur {player}"


class TestBanzhafIndexContracts:
    """L'indice de Banzhaf : valeur connue, et cas degenere signale."""

    def test_known_index_for_a_veto_game(self):
        """[3; 2,1,1] : comptes critiques 3 pour le joueur 0, 1 pour chacun
        des deux autres -> indice normalise [0.6, 0.2, 0.2]."""
        game = WeightedVotingGame([2, 1, 1], quota=3)
        assert game.banzhaf_index() == pytest.approx([0.6, 0.2, 0.2])

    def test_index_sums_to_one(self):
        game = WeightedVotingGame([4, 3, 2, 1], quota=6)
        assert game.banzhaf_index().sum() == pytest.approx(1.0)

    def test_unreachable_quota_warns_and_falls_back_to_uniform(self):
        """Quota inatteignable : aucune coalition gagnante, donc aucun joueur
        critique. L'indice est 0/0 ; la fonction le dit au lieu de rendre une
        mesure de pouvoir plausible."""
        game = WeightedVotingGame([1, 1], quota=5)
        with pytest.warns(UserWarning, match="no player is critical"):
            index = game.banzhaf_index()
        assert index == pytest.approx([0.5, 0.5])

    def test_warning_does_not_fire_when_the_quota_is_reachable(self):
        """Le signal n'est utile que s'il distingue le cas degenere : sur un
        jeu normal, aucun avertissement ne doit sortir."""
        game = WeightedVotingGame([2, 1, 1], quota=3)
        with warnings.catch_warnings(record=True) as caught:
            warnings.simplefilter("always")
            game.banzhaf_index()
        assert [w for w in caught if issubclass(w.category, UserWarning)] == []

    def test_degenerate_case_is_exactly_the_unreachable_quota(self):
        """Delimite le cas : quota atteignable par la grande coalition, meme
        sans coalition gagnante propre, -> pas d'avertissement."""
        game = WeightedVotingGame([1, 1], quota=2)
        assert game.is_winning({0, 1})
        with warnings.catch_warnings(record=True) as caught:
            warnings.simplefilter("always")
            index = game.banzhaf_index()
        assert [w for w in caught if issubclass(w.category, UserWarning)] == []
        assert index.sum() == pytest.approx(1.0)

    def test_fallback_still_returns_a_normalized_vector(self):
        """Contrat de forme conserve pour les consommateurs directs (cf.
        `french_politics.create_voting_game_assembly`, qui rend le resultat
        de `banzhaf_index()` tel quel) : jamais None, toujours de somme 1."""
        game = WeightedVotingGame([1, 1], quota=5)
        with warnings.catch_warnings():
            warnings.simplefilter("ignore", UserWarning)
            index = game.banzhaf_index()
        assert isinstance(index, np.ndarray)
        assert index.shape == (2,)
        assert index.sum() == pytest.approx(1.0)
