"""
Tests for Nash equilibrium computation functions.

Run with: pytest tests/test_nash_computation.py
"""

import pytest
import numpy as np
import random
import sys
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from game_theory_utils import (
    NormalFormGame, ZeroSumGame,
    find_pure_nash, find_mixed_nash_2x2,
    solve_minimax_lp, maximin_pure, minimax_pure,
    create_classic_games,
    TitForTat, RandomStrategy, AlwaysCooperate,
    compute_payoff_matrix, play_match, run_tournament
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


class TestNormalFormGameConstruction:
    """NormalFormGame constructor must reject ill-formed inputs.

    Before the guard, __post_init__ took the shape from A only and never
    checked B. A mismatched A/B pair was silently accepted, and downstream
    solvers (find_pure_nash, etc.) returned WRONG results computed on the
    mismatched B (out-of-range rows/cols silently ignored). Constructing a
    game with mismatched payoff matrices is always a caller bug — the
    constructor is the right place to catch it."""

    def test_shape_mismatch_rejected(self):
        with pytest.raises(ValueError, match="A and B must have the same shape"):
            NormalFormGame(A=[[1, 2], [3, 4]], B=[[1, 2, 3], [4, 5, 6]])

    def test_row_count_mismatch_rejected(self):
        with pytest.raises(ValueError, match="A and B must have the same shape"):
            NormalFormGame(A=[[1, 2], [3, 4]], B=[[1, 2], [3, 4], [5, 6]])

    def test_square_mismatch_rejected(self):
        """A=2x2, B=3x3 (both square but different sizes) must be rejected."""
        with pytest.raises(ValueError, match="A and B must have the same shape"):
            NormalFormGame(
                A=[[1, 2], [3, 4]],
                B=[[1, 2, 3], [4, 5, 6], [7, 8, 9]],
            )

    def test_non_2d_A_rejected(self):
        with pytest.raises(ValueError, match="A must be a 2-D payoff matrix"):
            NormalFormGame(A=[1, 2, 3], B=[1, 2, 3])

    def test_matching_shapes_accepted(self):
        """The guard does not impact valid construction (2x2 invariant)."""
        game = NormalFormGame(A=[[3, 0], [5, 1]], B=[[3, 5], [0, 1]])
        assert game.m == 2
        assert game.n == 2
        assert game.A.shape == game.B.shape == (2, 2)

    def test_non_square_matching_accepted(self):
        """Non-square games with matching A/B are valid (m != n)."""
        game = NormalFormGame(
            A=[[1, 2, 3], [4, 5, 6]],
            B=[[6, 5, 4], [3, 2, 1]],
        )
        assert game.m == 2
        assert game.n == 3


class TestDegenerateAndTies:
    """#20306: degenerate inputs and payoff ties get definition-verified
    behavior, not just the classic happy paths. find_pure_nash uses weak
    best responses (>=), so ties legitimately multiply equilibria."""

    def test_zero_game_every_profile_is_equilibrium(self):
        """All-zero payoffs: every cell is a weak best-response pair,
        so all 4 cells of the 2x2 are pure Nash equilibria."""
        game = NormalFormGame(A=[[0, 0], [0, 0]], B=[[0, 0], [0, 0]])
        assert find_pure_nash(game) == [(0, 0), (0, 1), (1, 0), (1, 1)]

    def test_constant_payoffs_indifference_all_cells_nash(self):
        """Each player has constant payoffs (pure indifference): every
        cell is an equilibrium."""
        game = NormalFormGame(A=[[2, 2], [2, 2]], B=[[1, 1], [1, 1]])
        assert len(find_pure_nash(game)) == 4

    def test_row_tie_doubles_equilibria_in_same_column(self):
        """A=[[3,0],[3,1]]: Row ties in column 0 (3 == 3). With B
        strictly preferring column 0, BOTH (0,0) and (1,0) are
        equilibria -- the tie propagates to two solutions, while the
        cells in column 1 are not (Row deviates to 3, Col to 5)."""
        game = NormalFormGame(A=[[3, 0], [3, 1]], B=[[5, 0], [5, 0]])
        assert find_pure_nash(game) == [(0, 0), (1, 0)]

    def test_mixed_nash_none_when_row_indifferent_everywhere(self):
        """denom_q == 0 (Row's payoff difference is constant across
        columns): the indifference formula has no interior crossing;
        the solver must return None, not crash or fabricate."""
        # A[0,0]-A[0,1]-A[1,0]+A[1,1] = 1-2-3+4 = 0
        game = NormalFormGame(A=[[1, 2], [3, 4]], B=[[0, 1], [1, 0]])
        assert find_mixed_nash_2x2(game) is None

    def test_mixed_nash_none_when_dominated_strategy(self):
        """Prisoner's Dilemma: the indifference crossing lies outside
        [0,1] (Defect dominates), so there is no interior mixed
        equilibrium -- None is the correct answer."""
        game = NormalFormGame(A=[[3, 0], [5, 1]], B=[[3, 5], [0, 1]])
        assert find_mixed_nash_2x2(game) is None


class TestRandomFamilyProperties:
    """#20306: properties verified against the DEFINITION on sampled
    games (multi-seed), not against memorized answers."""

    @pytest.mark.parametrize("seed", [0, 1, 7, 42, 99])
    def test_every_returned_pure_nash_has_no_profitable_deviation(self, seed):
        """For 50 random 3x3 games per seed, every equilibrium returned
        by find_pure_nash satisfies the definition directly: the row
        payoff is the column max and the column payoff is the row max."""
        rng = np.random.default_rng(seed)
        for _ in range(50):
            A = rng.integers(-5, 10, size=(3, 3)).astype(float)
            B = rng.integers(-5, 10, size=(3, 3)).astype(float)
            game = NormalFormGame(A=A, B=B)
            equilibria = find_pure_nash(game)
            assert isinstance(equilibria, list)
            for (i, j) in equilibria:
                assert A[i, j] >= A[:, j].max(), (seed, i, j)
                assert B[i, j] >= B[i, :].max(), (seed, i, j)

    @pytest.mark.parametrize("seed", [0, 1, 7, 42, 99])
    def test_no_profitable_deviation_on_random_2x2_family(self, seed):
        """#20306 acceptance names the 2x2 form (>=50 generated games,
        fixed seed): same definition check as the 3x3 family above, on
        generated 2x2 games -- including the tie-heavy low-entropy
        draws the integer sampler produces."""
        rng = np.random.default_rng(seed)
        for _ in range(50):
            A = rng.integers(-5, 10, size=(2, 2)).astype(float)
            B = rng.integers(-5, 10, size=(2, 2)).astype(float)
            game = NormalFormGame(A=A, B=B)
            for (i, j) in find_pure_nash(game):
                assert A[i, j] >= A[:, j].max(), (seed, i, j)
                assert B[i, j] >= B[i, :].max(), (seed, i, j)

    @pytest.mark.parametrize("seed", [0, 1, 7, 42, 99])
    def test_zero_sum_lp_value_within_pure_bounds(self, seed):
        """For 50 random zero-sum games per seed, the LP value is
        sandwiched between the pure maximin (lower bound) and pure
        minimax (upper bound): mixing can only help the maximizer and
        hurt the minimizer. Both helpers return (action, value) --
        the bounds are the VALUES."""
        rng = np.random.default_rng(seed)
        for _ in range(50):
            A = rng.integers(-9, 9, size=(3, 4)).astype(float)
            game = ZeroSumGame(A=A)
            _, value = solve_minimax_lp(game)
            _, lower = maximin_pure(game)
            _, upper = minimax_pure(game)
            assert lower - 1e-9 <= value <= upper + 1e-9, seed


class TestMultiSeedStochasticSimulations:
    """#20306: stochastic simulations (noisy tournaments) validated
    across seeds, not on one lucky draw."""

    @pytest.mark.parametrize("seed", [0, 1, 7, 42, 99])
    def test_noisy_match_payoff_concentrates_per_seed(self, seed):
        """TitForTat vs Random(p=0.5) over 400 rounds: the stationary
        per-round payoff of TFT = E{T,R,P,S}/4 = 9/4 = 2.25 (TFT echoes
        the opponent's previous iid move, so its own actions are iid
        too). Every seed lands within +-0.2 (empirical spread across
        the five seeds ~ +-0.06). Unparameterized strategies on
        purpose: the parameter-preservation angle is #20304/#20328,
        not #20306."""
        random.seed(seed)
        M = compute_payoff_matrix(
            [TitForTat(), RandomStrategy()], rounds=400
        )
        assert M[0, 1] == pytest.approx(2.25, abs=0.2)

    @pytest.mark.parametrize("seed", [0, 1, 7, 42, 99])
    def test_noise_channel_flips_actions_per_seed(self, seed):
        """noise>0 witness on the play_match/run_tournament noise
        channel (#20306 acceptance; compute_payoff_matrix has no noise
        parameter, so the test above cannot exercise it). AllCooperate
        vs AllCooperate is stateless, so every round is an iid pair of
        flips of (C,C) at eps=0.1:
        E[per-round payoff] = (1-e)^2*R + e(1-e)*T + e(1-e)*S + e^2*P
                            = 3 - e - e^2 = 2.89,
        per-round sd ~1.095, so the 2500-round average has sd ~0.022
        and +-0.08 is ~3.7 sigma. The bound also DISCRIMINATES: with
        noise silently ignored the payoff is exactly 3.0, which sits
        0.11 away -- outside the bound."""
        random.seed(seed)
        s1, s2 = play_match(AlwaysCooperate(), AlwaysCooperate(),
                            rounds=2500, noise=0.1)
        assert s1 / 2500 == pytest.approx(2.89, abs=0.08)
        assert s2 / 2500 == pytest.approx(2.89, abs=0.08)

        # run_tournament threads the same noise channel: the single
        # self-play match averages both players' per-round payoffs.
        random.seed(seed)
        tournament = run_tournament([AlwaysCooperate()],
                                    rounds=2500, noise=0.1)
        (value,) = tournament.values()
        assert value / 2500 == pytest.approx(2.89, abs=0.08)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
