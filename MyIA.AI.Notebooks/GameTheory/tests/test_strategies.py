"""
Tests for IPD strategies and tournament functions.

Run with: pytest tests/test_strategies.py
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from game_theory_utils import (
    COOPERATE, DEFECT, T, R, P, S,
    Strategy, AlwaysCooperate, AlwaysDefect,
    TitForTat, TitForTwoTats, Grudger, RandomStrategy,
    ipd_payoff, play_match, run_tournament,
    compute_payoff_matrix, replicator_dynamics
)


class TestIPDPayoffs:
    """Tests for IPD payoff function."""

    def test_mutual_cooperation(self):
        """Mutual cooperation gives (R, R) = (3, 3)."""
        p1, p2 = ipd_payoff(COOPERATE, COOPERATE)
        assert p1 == R
        assert p2 == R

    def test_mutual_defection(self):
        """Mutual defection gives (P, P) = (1, 1)."""
        p1, p2 = ipd_payoff(DEFECT, DEFECT)
        assert p1 == P
        assert p2 == P

    def test_unilateral_defection(self):
        """Unilateral defection: defector gets T, cooperator gets S."""
        p1, p2 = ipd_payoff(DEFECT, COOPERATE)
        assert p1 == T
        assert p2 == S

        p1, p2 = ipd_payoff(COOPERATE, DEFECT)
        assert p1 == S
        assert p2 == T

    def test_dilemma_conditions(self):
        """Verify T > R > P > S and 2R > T + S."""
        assert T > R > P > S
        assert 2 * R > T + S


class TestAlwaysCooperate:
    """Tests for AlwaysCooperate strategy."""

    def test_always_cooperates(self):
        """AlwaysCooperate always returns COOPERATE."""
        strategy = AlwaysCooperate()

        for _ in range(10):
            assert strategy.choose() == COOPERATE
            strategy.update(COOPERATE, DEFECT)


class TestAlwaysDefect:
    """Tests for AlwaysDefect strategy."""

    def test_always_defects(self):
        """AlwaysDefect always returns DEFECT."""
        strategy = AlwaysDefect()

        for _ in range(10):
            assert strategy.choose() == DEFECT
            strategy.update(DEFECT, COOPERATE)


class TestTitForTat:
    """Tests for TitForTat strategy."""

    def test_cooperates_first(self):
        """TFT cooperates on the first move."""
        strategy = TitForTat()
        assert strategy.choose() == COOPERATE

    def test_copies_opponent(self):
        """TFT copies the opponent's last move."""
        strategy = TitForTat()

        # First move
        assert strategy.choose() == COOPERATE
        strategy.update(COOPERATE, DEFECT)

        # Should copy opponent's DEFECT
        assert strategy.choose() == DEFECT
        strategy.update(DEFECT, COOPERATE)

        # Should copy opponent's COOPERATE
        assert strategy.choose() == COOPERATE


class TestTitForTwoTats:
    """Tests for TitForTwoTats strategy."""

    def test_cooperates_first(self):
        """TF2T cooperates on first moves."""
        strategy = TitForTwoTats()
        assert strategy.choose() == COOPERATE

    def test_forgives_single_defection(self):
        """TF2T forgives a single defection."""
        strategy = TitForTwoTats()

        strategy.update(COOPERATE, DEFECT)  # Opponent defects
        assert strategy.choose() == COOPERATE  # Still cooperates

    def test_retaliates_after_two_defections(self):
        """TF2T defects after two consecutive defections."""
        strategy = TitForTwoTats()

        strategy.update(COOPERATE, DEFECT)
        strategy.update(COOPERATE, DEFECT)

        assert strategy.choose() == DEFECT


class TestGrudger:
    """Tests for Grudger strategy."""

    def test_cooperates_initially(self):
        """Grudger cooperates initially."""
        strategy = Grudger()
        assert strategy.choose() == COOPERATE

    def test_defects_forever_after_betrayal(self):
        """Grudger defects forever after being betrayed."""
        strategy = Grudger()

        # Cooperate until betrayal
        strategy.update(COOPERATE, COOPERATE)
        assert strategy.choose() == COOPERATE

        # Get betrayed
        strategy.update(COOPERATE, DEFECT)

        # Now defects forever
        for _ in range(10):
            assert strategy.choose() == DEFECT
            strategy.update(DEFECT, COOPERATE)


class TestPlayMatch:
    """Tests for match simulation."""

    def test_tft_vs_tft(self):
        """TFT vs TFT: mutual cooperation, equal scores."""
        s1 = TitForTat()
        s2 = TitForTat()

        score1, score2 = play_match(s1, s2, rounds=100)

        # Both should cooperate every round
        assert score1 == 100 * R
        assert score2 == 100 * R

    def test_tft_vs_always_defect(self):
        """TFT vs AlwaysDefect: TFT gets exploited first round."""
        s1 = TitForTat()
        s2 = AlwaysDefect()

        score1, score2 = play_match(s1, s2, rounds=100)

        # Round 1: TFT cooperates, AD defects -> (S, T)
        # Rounds 2-100: Both defect -> (P, P)
        expected_s1 = S + 99 * P
        expected_s2 = T + 99 * P

        assert score1 == expected_s1
        assert score2 == expected_s2

    def test_always_coop_vs_always_defect(self):
        """AlwaysCooperate vs AlwaysDefect: AC gets exploited."""
        s1 = AlwaysCooperate()
        s2 = AlwaysDefect()

        score1, score2 = play_match(s1, s2, rounds=100)

        assert score1 == 100 * S
        assert score2 == 100 * T


class TestTournament:
    """Tests for tournament functionality."""

    def test_tournament_runs(self):
        """Tournament should run without errors."""
        strategies = [TitForTat(), AlwaysCooperate(), AlwaysDefect()]
        results = run_tournament(strategies, rounds=50)

        assert len(results) == 3
        assert all(v > 0 for v in results.values())

    def test_tft_beats_all_defectors_in_ecosystem(self):
        """In a cooperative ecosystem, TFT does well."""
        strategies = [TitForTat(), AlwaysCooperate(), AlwaysCooperate()]
        results = run_tournament(strategies, rounds=100)

        # TFT should do at least as well as cooperators
        assert results["TitForTat"] >= results["AlwaysCooperate"] - 1


class TestReplicatorDynamics:
    """Tests for replicator dynamics."""

    def test_payoff_matrix_shape(self):
        """Payoff matrix should have correct shape."""
        strategies = [TitForTat(), AlwaysDefect()]
        M = compute_payoff_matrix(strategies, rounds=50)

        assert M.shape == (2, 2)

    def test_replicator_trajectory_shape(self):
        """Replicator dynamics should return correct shape."""
        M = np.array([[3, 0], [5, 1]])
        x0 = np.array([0.5, 0.5])

        trajectory = replicator_dynamics(M, x0, T=100)

        assert trajectory.shape == (100, 2)

    def test_replicator_preserves_normalization(self):
        """Population proportions should sum to 1."""
        M = np.array([[3, 0], [5, 1]])
        x0 = np.array([0.5, 0.5])

        trajectory = replicator_dynamics(M, x0, T=100)

        for t in range(100):
            assert abs(np.sum(trajectory[t]) - 1.0) < 1e-6


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
