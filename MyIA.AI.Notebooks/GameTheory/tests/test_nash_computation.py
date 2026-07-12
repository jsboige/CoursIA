"""
Tests for Nash equilibrium computation functions.

Run with: pytest tests/test_nash_computation.py
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from game_theory_utils import (
    NormalFormGame, ZeroSumGame,
    find_pure_nash, find_mixed_nash_2x2,
    solve_minimax_lp, maximin_pure, minimax_pure,
    create_classic_games
)


class TestPureNashEquilibria:
    """Tests for pure Nash equilibrium finder."""

    def test_prisoners_dilemma_has_one_nash(self):
        """Prisoner's Dilemma has exactly one Nash: (Defect, Defect)."""
        game = NormalFormGame(
            A=[[3, 0], [5, 1]],
            B=[[3, 5], [0, 1]],
            name="PD"
        )
        equilibria = find_pure_nash(game)

        assert len(equilibria) == 1
        assert equilibria[0] == (1, 1)  # (Defect, Defect)

    def test_stag_hunt_has_two_nash(self):
        """Stag Hunt has two pure Nash equilibria."""
        game = NormalFormGame(
            A=[[4, 0], [3, 3]],
            B=[[4, 3], [0, 3]],
            name="Stag Hunt"
        )
        equilibria = find_pure_nash(game)

        assert len(equilibria) == 2
        assert (0, 0) in equilibria  # (Stag, Stag)
        assert (1, 1) in equilibria  # (Hare, Hare)

    def test_matching_pennies_has_no_pure_nash(self):
        """Matching Pennies has no pure Nash equilibrium."""
        game = NormalFormGame(
            A=[[1, -1], [-1, 1]],
            B=[[-1, 1], [1, -1]],
            name="Matching Pennies"
        )
        equilibria = find_pure_nash(game)

        assert len(equilibria) == 0

    def test_battle_of_sexes_has_two_nash(self):
        """Battle of the Sexes has two pure Nash equilibria."""
        game = NormalFormGame(
            A=[[3, 0], [0, 2]],
            B=[[2, 0], [0, 3]],
            name="BoS"
        )
        equilibria = find_pure_nash(game)

        assert len(equilibria) == 2


class TestMixedNashEquilibrium:
    """Tests for mixed Nash equilibrium computation."""

    def test_matching_pennies_mixed_nash(self):
        """Matching Pennies has mixed Nash at (0.5, 0.5)."""
        game = NormalFormGame(
            A=[[1, -1], [-1, 1]],
            B=[[-1, 1], [1, -1]],
            name="MP"
        )
        result = find_mixed_nash_2x2(game)

        assert result is not None
        sigma_row, sigma_col = result

        np.testing.assert_array_almost_equal(sigma_row, [0.5, 0.5])
        np.testing.assert_array_almost_equal(sigma_col, [0.5, 0.5])

    def test_battle_of_sexes_mixed_nash(self):
        """Battle of the Sexes has an interior mixed Nash."""
        game = NormalFormGame(
            A=[[3, 0], [0, 2]],
            B=[[2, 0], [0, 3]],
            name="BoS"
        )
        result = find_mixed_nash_2x2(game)

        assert result is not None
        sigma_row, sigma_col = result

        # Verify it's interior
        assert 0 < sigma_row[0] < 1
        assert 0 < sigma_col[0] < 1


class TestZeroSumGames:
    """Tests for zero-sum game solvers."""

    def test_minimax_lp_matching_pennies(self):
        """Matching Pennies: value = 0, optimal = (0.5, 0.5)."""
        game = ZeroSumGame(
            A=[[1, -1], [-1, 1]],
            name="MP"
        )
        sigma, v = solve_minimax_lp(game)

        assert abs(v) < 1e-6  # Value should be 0
        np.testing.assert_array_almost_equal(sigma, [0.5, 0.5])

    def test_minimax_lp_rps(self):
        """Rock-Paper-Scissors: value = 0, optimal = (1/3, 1/3, 1/3)."""
        game = ZeroSumGame(
            A=[[0, -1, 1], [1, 0, -1], [-1, 1, 0]],
            name="RPS"
        )
        sigma, v = solve_minimax_lp(game)

        assert abs(v) < 1e-6
        np.testing.assert_array_almost_equal(sigma, [1/3, 1/3, 1/3], decimal=4)

    def test_saddle_point_game(self):
        """Game with saddle point: pure strategy is optimal."""
        # Game where (0, 0) is a saddle point with value 2
        # Row 0: min(2, 3) = 2, Row 1: min(1, 4) = 1 -> maximin = 2
        # Col 0: max(2, 1) = 2, Col 1: max(3, 4) = 4 -> minimax = 2
        game = ZeroSumGame(
            A=[[2, 3], [1, 4]],
            name="Saddle"
        )

        maximin_row, maximin_val = maximin_pure(game)
        minimax_col, minimax_val = minimax_pure(game)

        # Saddle point exists if maximin = minimax
        assert maximin_val == minimax_val
        assert maximin_val == 2

    def test_no_saddle_point(self):
        """Matching Pennies has no saddle point in pure strategies."""
        game = ZeroSumGame(
            A=[[1, -1], [-1, 1]],
            name="MP"
        )

        _, maximin_val = maximin_pure(game)
        _, minimax_val = minimax_pure(game)

        assert maximin_val < minimax_val  # Gap exists


class TestClassicGames:
    """Tests for the classic games collection."""

    def test_all_games_created(self):
        """All classic games should be created."""
        games = create_classic_games()

        expected_games = [
            "Prisoner's Dilemma",
            "Stag Hunt",
            "Battle of the Sexes",
            "Chicken",
            "Matching Pennies"
        ]

        for name in expected_games:
            assert name in games

    def test_games_are_valid(self):
        """All games should have valid dimensions."""
        games = create_classic_games()

        for name, game in games.items():
            assert game.A.shape == game.B.shape
            assert len(game.row_labels) == game.m
            assert len(game.col_labels) == game.n


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
