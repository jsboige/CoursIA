"""Tests for the walk-forward backtesting framework."""

import numpy as np
import pytest

from wf_framework.backtest import (
    WalkForwardBacktest,
    WalkForwardResult,
    default_classification_metrics,
    default_regression_metrics,
)
from wf_framework.stats import multi_asset_eval, multi_seed_eval


class MockStrategy:
    """Minimal strategy for testing."""

    def __init__(self):
        self.fitted = False

    def fit(self, X_train, y_train, seed=42):
        self.fitted = True
        self.majority_class = int(np.mean(y_train) > 0.5)

    def predict(self, X_test):
        return np.full(len(X_test), self.majority_class)


class PerfectStrategy:
    """Strategy that memorizes training labels and predicts perfectly."""

    def __init__(self):
        self._y_train = None

    def fit(self, X_train, y_train, seed=42):
        self._y_train = y_train

    def predict(self, X_test):
        # Return training majority — not perfect but deterministic
        majority = int(np.mean(self._y_train) > 0.5)
        return np.full(len(X_test), majority)


def _make_data(n=200, n_features=5, seed=42):
    rng = np.random.RandomState(seed)
    X = rng.randn(n, n_features).astype(np.float32)
    y = rng.randint(0, 2, n)
    return X, y


class TestWalkForwardBacktest:

    def test_single_seed_basic(self):
        X, y = _make_data()
        bt = WalkForwardBacktest(
            strategy_factory=MockStrategy,
            X=X, y=y,
            n_folds=3,
        )
        result = bt.run(seed=42)
        assert result.seed == 42
        assert result.n_folds >= 1
        assert len(result.fold_results) >= 1
        assert "dir_acc" in result.mean_metrics

    def test_expanding_window(self):
        X, y = _make_data(n=500)
        bt = WalkForwardBacktest(
            strategy_factory=MockStrategy,
            X=X, y=y,
            n_folds=5,
            window_type="expanding",
        )
        result = bt.run(seed=0)
        # Train sizes should grow (expanding window)
        train_sizes = [f.train_size for f in result.fold_results]
        assert train_sizes == sorted(train_sizes)

    def test_rolling_window(self):
        X, y = _make_data(n=500)
        bt = WalkForwardBacktest(
            strategy_factory=MockStrategy,
            X=X, y=y,
            n_folds=3,
            window_type="rolling",
            train_size=100,
        )
        result = bt.run(seed=0)
        # All train sizes should be ~100 (fixed rolling window)
        for f in result.fold_results:
            assert abs(f.train_size - 100) <= 5

    def test_multi_seed(self):
        X, y = _make_data()
        bt = WalkForwardBacktest(
            strategy_factory=MockStrategy,
            X=X, y=y,
            n_folds=3,
        )
        results = bt.run_multi_seed(seeds=[0, 1, 7, 42])
        assert len(results) == 4
        seeds = [r.seed for r in results]
        assert seeds == [0, 1, 7, 42]

    def test_multi_asset(self):
        assets = {
            "A": _make_data(n=200, seed=1),
            "B": _make_data(n=200, seed=2),
        }
        bt = WalkForwardBacktest(
            strategy_factory=MockStrategy,
            X=assets["A"][0], y=assets["A"][1],
            n_folds=3,
        )
        results = bt.run_multi_asset(assets, seeds=[0, 42])
        assert set(results.keys()) == {"A", "B"}
        assert len(results["A"]) == 2
        assert len(results["B"]) == 2

    def test_gap_prevents_overlap(self):
        X, y = _make_data(n=500)
        bt = WalkForwardBacktest(
            strategy_factory=MockStrategy,
            X=X, y=y,
            n_folds=3,
            gap=20,
        )
        result = bt.run(seed=0)
        for f in result.fold_results:
            assert f.test_size > 0

    def test_single_fold(self):
        X, y = _make_data(n=100)
        bt = WalkForwardBacktest(
            strategy_factory=MockStrategy,
            X=X, y=y,
            n_folds=1,
        )
        result = bt.run(seed=42)
        assert result.n_folds == 1


class TestMetrics:

    def test_classification_metrics(self):
        y_true = np.array([0, 1, 1, 0, 1])
        y_pred = np.array([0, 1, 0, 0, 1])
        m = default_classification_metrics(y_true, y_pred)
        assert m["dir_acc"] == 0.8
        assert "majority_acc" in m
        assert "edge" in m

    def test_regression_metrics(self):
        y_true = np.array([1.0, -1.0, 0.5, -0.5])
        y_pred = np.array([0.9, -0.8, 0.3, -0.6])
        m = default_regression_metrics(y_true, y_pred)
        assert m["mse"] > 0
        assert m["mae"] > 0
        assert m["dir_acc"] == 1.0


class TestStats:

    def test_multi_seed_significant(self):
        # 5 seeds all above 0.5
        seed_metrics = [{"dir_acc": 0.55 + i * 0.01} for i in range(5)]
        result = multi_seed_eval(seed_metrics, baseline_value=0.5)
        assert result.n_seeds == 5
        assert result.mean > 0.5
        assert result.t_stat > 0

    def test_multi_seed_not_significant(self):
        # Values scattered around 0.5
        seed_metrics = [{"dir_acc": v} for v in [0.49, 0.51, 0.50, 0.49, 0.51]]
        result = multi_seed_eval(seed_metrics, baseline_value=0.5)
        assert result.p_value > 0.05

    def test_multi_seed_insufficient_seeds(self):
        seed_metrics = [{"dir_acc": 0.6}]
        result = multi_seed_eval(seed_metrics, baseline_value=0.5)
        assert result.n_seeds == 1
        assert not result.passes_rule

    def test_multi_asset_bonferroni(self):
        asset_results = {
            "A": [{"dir_acc": 0.55 + i * 0.01} for i in range(5)],
            "B": [{"dir_acc": 0.52 + i * 0.005} for i in range(5)],
            "C": [{"dir_acc": 0.49 + i * 0.002} for i in range(5)],
        }
        result = multi_asset_eval(asset_results, baseline_value=0.5)
        assert result.n_assets == 3
        assert result.alpha_bonferroni < result.alpha_raw
        assert result.n_significant_raw >= result.n_significant_bonferroni

    def test_rule_edge_ge_2std(self):
        # All seeds identical → std=0, edge > 0 → passes
        seed_metrics = [{"dir_acc": 0.55}] * 5
        result = multi_seed_eval(seed_metrics, baseline_value=0.5)
        assert result.passes_rule

    def test_rule_edge_fails(self):
        # Mean 0.51 but std=0.05 → edge=0.01 < 2*0.05=0.10 → fails
        seed_metrics = [{"dir_acc": 0.46}, {"dir_acc": 0.56}]
        result = multi_seed_eval(seed_metrics, baseline_value=0.5)
        assert not result.passes_rule


class TestResultSerialization:

    def test_to_dict(self):
        X, y = _make_data()
        bt = WalkForwardBacktest(
            strategy_factory=MockStrategy,
            X=X, y=y,
            n_folds=2,
        )
        result = bt.run(seed=7)
        d = result.to_dict()
        assert d["seed"] == 7
        assert "mean_metrics" in d
        assert "folds" in d
        assert len(d["folds"]) == 2
