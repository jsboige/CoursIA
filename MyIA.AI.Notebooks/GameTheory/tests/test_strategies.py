"""
Tests for IPD strategies and tournament functions.

Run with: pytest tests/test_strategies.py
"""

import pytest
import numpy as np
import random
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


class TestTournamentGuard:
    """run_tournament must reject degenerate inputs explicitly.

    Without the guards, degenerate inputs return a silently-empty result
    dict (no error), masking a caller-side bug:
      - run_tournament([])          -> n=0, range(0) skipped, returns {} silently
      - run_tournament([...], repetitions=0)  -> range(0) skipped, returns {} silently
      - run_tournament([...], repetitions=-2) -> range(-2) skipped, returns {} silently

    Same degenerate-input bug-class as compute_payoff_matrix rounds<=0
    (#7517), make_batch_edge_index batch_size<=0 (#7554)."""

    def test_empty_strategies_raises(self):
        with pytest.raises(ValueError, match="strategies must be a non-empty list"):
            run_tournament([])

    def test_zero_repetitions_raises(self):
        with pytest.raises(ValueError, match="repetitions must be positive"):
            run_tournament([TitForTat(), AlwaysDefect()], repetitions=0)

    def test_negative_repetitions_raises(self):
        with pytest.raises(ValueError, match="repetitions must be positive"):
            run_tournament([TitForTat(), AlwaysDefect()], repetitions=-3)

    def test_default_repetitions_unaffected(self):
        """The guard does not impact the normal path (default repetitions=1)."""
        results = run_tournament([TitForTat(), AlwaysCooperate()], rounds=50)
        assert len(results) == 2


class TestReplicatorDynamics:
    """Tests for replicator dynamics."""

    def test_payoff_matrix_shape(self):
        """Payoff matrix should have correct shape."""
        strategies = [TitForTat(), AlwaysDefect()]
        M = compute_payoff_matrix(strategies, rounds=50)

        assert M.shape == (2, 2)

    def test_compute_payoff_matrix_zero_rounds_raises(self):
        """rounds <= 0 doit echouer explicitement (ValueError), pas crasher
        en ZeroDivisionError. Avant le guard, `M[i, j] = score1 / rounds`
        divisait par 0. Meme bug-class degenerate-input que #7481 (shapley
        n_samples<=0), #7489 (kuhn_poker iterations<=0), #7495 (replicator
        normalization)."""
        strategies = [AlwaysCooperate(), AlwaysDefect()]
        with pytest.raises(ValueError, match="rounds must be positive"):
            compute_payoff_matrix(strategies, rounds=0)

    def test_compute_payoff_matrix_negative_rounds_raises(self):
        """rounds < 0 doit aussi echouer explicitement (consistance du guard)."""
        strategies = [AlwaysCooperate(), AlwaysDefect()]
        with pytest.raises(ValueError, match="rounds must be positive"):
            compute_payoff_matrix(strategies, rounds=-1)

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

    def test_replicator_degenerate_zero_x0_no_nan(self):
        """A degenerate x0 = zeros(n) must not propagate NaN through the
        trajectory. Before the normalization guard, x / np.sum(x) divided by
        0.0 and NaN-ed every row from t=1 onward (RuntimeWarning: invalid
        value encountered in divide). The guard falls back to a uniform
        distribution, so the dynamics resume from a valid simplex point."""
        M = np.array([[3.0, 0.0], [5.0, 1.0]])
        trajectory = replicator_dynamics(M, np.zeros(2), T=50, dt=0.1)

        assert not np.isnan(trajectory).any()
        # Row 0 records the given (degenerate) initial state; every subsequent
        # row must be a valid population distribution (non-negative, sums to 1).
        for t in range(1, 50):
            assert abs(np.sum(trajectory[t]) - 1.0) < 1e-9
            assert (trajectory[t] >= 0).all()

    def test_replicator_degenerate_zero_x0_falls_back_to_uniform(self):
        """After a degenerate x0 = zeros, the next iterate is the uniform
        distribution (the documented sibling-fallback, mirroring
        CFRSolver.get_strategy in the same module)."""
        M = np.array([[3.0, 0.0], [5.0, 1.0]])
        trajectory = replicator_dynamics(M, np.zeros(2), T=5, dt=0.1)

        np.testing.assert_allclose(trajectory[1], np.array([0.5, 0.5]))

    def test_replicator_negative_x0_clamped_without_nan(self):
        """A negative x0 (out-of-simplex) gets clamped by np.maximum(x, 0);
        the resulting all-zero row would also NaN without the guard. The fix
        keeps the trajectory finite for every iterate after the first."""
        M = np.array([[3.0, 0.0], [5.0, 1.0]])
        trajectory = replicator_dynamics(M, np.array([-0.2, -0.1]), T=20, dt=0.1)

        assert not np.isnan(trajectory).any()
        for t in range(1, 20):
            assert abs(np.sum(trajectory[t]) - 1.0) < 1e-9


class TestParameterPreservation:
    """#20304: tournaments must play the configuration provided, not the
    constructor defaults. run_tournament and compute_payoff_matrix used to
    re-instantiate strategies via type(s)(), silently replacing
    RandomStrategy(p=0.1) by its default p=0.5 while the scoreboard kept
    the original label."""

    def test_clone_preserves_parameters_name_and_fresh_state(self):
        original = RandomStrategy(p=0.1)
        original.update(COOPERATE, DEFECT)  # dirty the match histories

        cloned = original.clone()

        assert cloned is not original
        assert isinstance(cloned, RandomStrategy)
        assert cloned.p == 0.1
        assert cloned.name == original.name
        assert cloned.my_history == []
        assert cloned.opponent_history == []
        # The source instance is left untouched.
        assert original.my_history == [COOPERATE]

    def test_clone_resets_subclass_state(self):
        grudger = Grudger()
        grudger.update(COOPERATE, DEFECT)  # opponent defected -> betrayed
        assert grudger.betrayed is True

        cloned = grudger.clone()

        assert cloned.betrayed is False
        assert cloned.choose() == COOPERATE

    def test_tournament_accepts_required_constructor_arguments(self):
        """type(s)() raised TypeError for strategies whose parameters are
        required; clone() makes them tournament-safe without touching the
        tournament signatures."""

        class ThresholdCooperator(Strategy):
            def __init__(self, coop_rounds: int):
                super().__init__(f"Coop{coop_rounds}")
                self.coop_rounds = coop_rounds

            def choose(self) -> str:
                if len(self.my_history) < self.coop_rounds:
                    return COOPERATE
                return DEFECT

        results = run_tournament(
            [ThresholdCooperator(3), AlwaysDefect()], rounds=50
        )
        # vs AD: rounds 1-3 pay S=0, rounds 4-50 pay P=1 -> 47.
        # Self-play: rounds 1-3 mutual C (3*R=9), then mutual D (47*P) -> 56.
        assert results["Coop3"] == pytest.approx((47 + 56) / 2)

    def test_run_tournament_plays_requested_probability(self):
        """Deterministic boundary: p=0.0 turns RandomStrategy into an
        all-defector, so every match pays exactly 200 over 200 rounds.
        Under the defaults-instead-of-parameters bug the average was
        ~275 (default p=0.5)."""
        random.seed(42)
        results = run_tournament(
            [RandomStrategy(p=0.0), AlwaysDefect()], rounds=200
        )
        assert results["Random(p=0.0)"] == pytest.approx(200.0)

    def test_run_tournament_effective_p_statistical(self):
        """Acceptance criterion of #20304: p=0.1 must play at 0.1.
        Expected average per match over {self-play, vs AlwaysDefect}:
        (1.29 + 0.9) / 2 = 1.095 per round -> 219 over 200 rounds; the
        buggy default p=0.5 centers the average at 275, far outside the
        tolerance."""
        random.seed(7)
        results = run_tournament(
            [RandomStrategy(p=0.1), AlwaysDefect()], rounds=200
        )
        assert results["Random(p=0.1)"] == pytest.approx(219.0, abs=20.0)

    def test_compute_payoff_matrix_plays_requested_probability(self):
        random.seed(42)
        M = compute_payoff_matrix(
            [RandomStrategy(p=0.0), AlwaysDefect()], rounds=200
        )
        np.testing.assert_allclose(M, np.ones((2, 2)))

    def test_compute_payoff_matrix_effective_p_statistical(self):
        """M[0,1] = per-round payoff of Random(p=0.1) vs AlwaysDefect
        = p*S + (1-p)*P = 0.9 (buggy value under default p=0.5: 0.5)."""
        random.seed(7)
        M = compute_payoff_matrix(
            [RandomStrategy(p=0.1), AlwaysDefect()], rounds=200
        )
        assert M[0, 1] == pytest.approx(0.9, abs=0.08)

    def test_unparameterized_tournament_results_unchanged(self):
        """Non-regression: exact scores measured on the pre-fix module
        (type(s)() is behaviorally identical to clone() for no-argument
        constructors)."""
        strategies = [
            TitForTat(), TitForTwoTats(), Grudger(),
            AlwaysCooperate(), AlwaysDefect(),
        ]
        results = run_tournament(strategies, rounds=200)
        expected = {
            "TitForTat": 519.8,
            "TitForTwoTats": 519.6,
            "Grudger": 519.8,
            "AlwaysCooperate": 480.0,
            "AlwaysDefect": 363.2,
        }
        for name, score in expected.items():
            assert results[name] == pytest.approx(score), name

        M = compute_payoff_matrix(strategies, rounds=200)
        assert M[0, 4] == pytest.approx(0.995)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
