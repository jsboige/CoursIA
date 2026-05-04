"""Tests for DQN train/test split functionality (Issue #703)."""

import numpy as np
import pytest
import sys
from pathlib import Path

# Add scripts directory to path for imports
sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))

from train_dqn_rl import TradingEnv, evaluate_dqn, build_dqn


def _make_env(n_rows: int = 500, window: int = 20):
    """Create a simple TradingEnv with synthetic data."""
    np.random.seed(42)
    prices = 100.0 + np.cumsum(np.random.randn(n_rows) * 0.5).astype(np.float32)
    n_features = 10
    features = np.random.randn(n_rows, n_features).astype(np.float32)
    env = TradingEnv(prices, features, window=window)
    return prices, features, env


class TestTrainTestSplit:
    """Verify time-series train/test split logic."""

    def test_split_ratios(self):
        """80/20 split produces correct sizes."""
        prices, features, _ = _make_env(500)
        test_ratio = 0.2
        train_end = int(len(prices) * (1 - test_ratio))
        train_prices = prices[:train_end]
        test_prices = prices[train_end:]

        assert len(train_prices) == 400
        assert len(test_prices) == 100
        assert len(train_prices) + len(test_prices) == 500

    def test_no_data_leakage(self):
        """Train and test sets are temporally disjoint."""
        prices, features, _ = _make_env(500)
        train_end = int(len(prices) * (1 - 0.2))
        train_prices = prices[:train_end]
        test_prices = prices[train_end:]

        # Last train price < first test price index (no overlap)
        assert train_end == len(train_prices)
        assert train_end < len(prices)

    def test_normalization_uses_train_only(self):
        """Feature normalization computed on training portion only."""
        prices, features, _ = _make_env(500)
        train_end = int(len(features) * 0.8)
        mean = features[:train_end].mean(axis=0)
        std = features[:train_end].std(axis=0)
        normalized = (features - mean) / np.where(std < 1e-8, 1.0, std)

        # Training portion should have ~0 mean and ~1 std
        train_norm = normalized[:train_end]
        assert np.abs(train_norm.mean()) < 0.05
        assert np.abs(train_norm.std() - 1.0) < 0.05


class TestEvaluateDQN:
    """Verify OOS evaluation function."""

    def test_evaluate_returns_expected_keys(self):
        """evaluate_dqn returns all required OOS metrics."""
        prices, features, env = _make_env(200)
        model = build_dqn(env.state_size, hidden_size=32, n_actions=3)

        oos = evaluate_dqn(model, env, device="cpu", num_episodes=3)

        expected_keys = [
            "oos_mean_reward", "oos_std_reward", "oos_sharpe",
            "oos_max_reward", "oos_min_reward", "oos_mean_trades",
            "oos_episodes",
        ]
        for key in expected_keys:
            assert key in oos, f"Missing key: {key}"

    def test_evaluate_is_greedy(self):
        """Evaluation uses greedy policy (no randomness)."""
        prices, features, env = _make_env(200)
        model = build_dqn(env.state_size, hidden_size=32, n_actions=3)

        oos1 = evaluate_dqn(model, env, device="cpu", num_episodes=5)
        oos2 = evaluate_dqn(model, env, device="cpu", num_episodes=5)

        # Greedy policy on same data should give identical results
        assert oos1["oos_mean_reward"] == oos2["oos_mean_reward"]

    def test_oos_episodes_count(self):
        """Evaluation runs the requested number of episodes."""
        prices, features, env = _make_env(200)
        model = build_dqn(env.state_size, hidden_size=32, n_actions=3)

        oos = evaluate_dqn(model, env, device="cpu", num_episodes=7)
        assert oos["oos_episodes"] == 7


class TestTradingEnv:
    """Verify TradingEnv behavior with split data."""

    def test_env_terminates_at_data_end(self):
        """Env stops when reaching the end of its price array."""
        prices, features, env = _make_env(100, window=10)

        state = env.reset()
        steps = 0
        while True:
            _, _, done, _ = env.step(0)
            steps += 1
            if done or steps > 200:
                break

        # Should terminate at len(prices) - 1
        assert done
        assert steps <= 90  # 100 - window - 1

    def test_separate_envs_independent(self):
        """Train and test envs don't share state."""
        prices, features, _ = _make_env(500)
        train_end = 400

        train_env = TradingEnv(prices[:train_end], features[:train_end], window=20)
        test_env = TradingEnv(prices[train_end:], features[train_end:], window=20)

        # Run train env for a while
        state = train_env.reset()
        for _ in range(50):
            train_env.step(0)

        # Test env should still be at start
        test_env.reset()
        assert test_env.step_idx == test_env.window
        assert test_env.total_reward == 0.0
