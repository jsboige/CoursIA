"""Tests for eval_m15_lstm.py -- CPU-only smoke tests.

The M15 LSTM harness is self-contained (fine-tuned walk-forward, structurally
distinct from the zero-shot Chronos/Kronos window eval), so these tests cover
its own stable helpers + a tiny end-to-end walk-forward run on synthetic data.
Real GPU training (is_trained=True on the anti-bias basket) is proven by the
committed sweep results, not by these CPU unit tests.
"""

import sys
from pathlib import Path

import numpy as np
import pandas as pd
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))

from eval_m15_lstm import (
    build_lstm,
    count_params,
    compute_direction_accuracy,
    compute_majority_baseline,
    make_cumulative_targets,
    prepare_features,
    walk_forward_direction,
)


class TestDirectionAccuracy:
    def test_perfect(self):
        y_true = np.array([1.0, -1.0, 1.0, 1.0])
        y_pred = np.array([1.0, -1.0, 1.0, 1.0])
        assert compute_direction_accuracy(y_true, y_pred) == 1.0

    def test_random(self):
        y_true = np.array([1.0, -1.0, 1.0, -1.0])
        y_pred = np.array([-1.0, 1.0, -1.0, 1.0])
        assert compute_direction_accuracy(y_true, y_pred) == 0.0

    def test_empty(self):
        assert compute_direction_accuracy(np.array([]), np.array([])) == 0.0

    def test_partial(self):
        y_true = np.array([1.0, -1.0, 1.0, -1.0])
        y_pred = np.array([1.0, -1.0, -1.0, 1.0])
        assert compute_direction_accuracy(y_true, y_pred) == 0.5


class TestMajorityBaseline:
    """Parity with the Chronos/Kronos majority-baseline formula (terrain commun)."""

    def test_balanced(self):
        returns = np.array([1.0, -1.0] * 50, dtype=np.float32)
        baseline = compute_majority_baseline(returns)
        assert baseline["majority_class_accuracy"] == 0.5

    def test_biased_up(self):
        returns = np.ones(100, dtype=np.float32)
        baseline = compute_majority_baseline(returns)
        assert baseline["majority_class_accuracy"] == 1.0
        assert baseline["majority_class"] == "up"

    def test_biased_down(self):
        returns = -np.ones(100, dtype=np.float32)
        baseline = compute_majority_baseline(returns)
        assert baseline["majority_class_accuracy"] == 1.0
        assert baseline["majority_class"] == "down"


class TestPrepareFeatures:
    def test_shape_and_no_nan(self):
        rng = np.random.default_rng(0)
        n = 300
        prices = pd.Series(
            100.0 * np.exp(np.cumsum(rng.standard_normal(n) * 0.01)),
            index=pd.date_range("2020-01-01", periods=n, freq="B"),
        )
        features, log_returns = prepare_features(prices)
        assert features.shape[1] == 2  # [log_return, sign]
        assert features.shape[0] == log_returns.shape[0]
        assert np.all(np.isfinite(features))
        assert np.all(np.isfinite(log_returns))

    def test_sign_column_is_sign(self):
        rng = np.random.default_rng(1)
        n = 200
        prices = pd.Series(
            100.0 * np.exp(np.cumsum(rng.standard_normal(n) * 0.01)),
            index=pd.date_range("2020-01-01", periods=n, freq="B"),
        )
        features, log_returns = prepare_features(prices)
        # sign column (index 1) == sign of log-return column (index 0), where nonzero.
        nonzero = features[:, 0] != 0
        np.testing.assert_array_equal(
            features[nonzero, 1], np.sign(features[nonzero, 0])
        )


class TestCumulativeTargets:
    def test_shape(self):
        log_returns = np.random.default_rng(0).standard_normal(100)
        targets = make_cumulative_targets(log_returns, pred_len=24)
        assert targets.shape == (100, 24)

    def test_values_are_cumsum(self):
        log_returns = np.ones(50)
        targets = make_cumulative_targets(log_returns, pred_len=5)
        # targets[i, k] = sum of ones over [i, i+k+1] = k+1
        assert targets[0, 0] == 1.0
        assert targets[0, 4] == 5.0
        assert targets[10, 2] == 3.0

    def test_tail_is_nan(self):
        log_returns = np.ones(50)
        targets = make_cumulative_targets(log_returns, pred_len=5)
        # Last pred_len-1 starts cannot complete a full window.
        assert np.isnan(targets[49, 0])


class TestBuildLstm:
    def test_output_shape(self):
        import torch

        model = build_lstm(input_size=2, pred_len=24)
        x = torch.randn(4, 22, 2)  # (batch, window, features)
        out = model(x)
        assert out.shape == (4, 24)

    def test_param_count_reasonable(self):
        model = build_lstm(input_size=2, pred_len=24)
        n = count_params(model)
        # LSTM(2,64,1) + FC(64,24): small model, well under 50k params.
        assert 5000 < n < 50000


class TestWalkForwardDirection:
    """Tiny end-to-end smoke: the harness trains and returns is_trained=True."""

    @staticmethod
    def _prices(n=600, seed=0):
        rng = np.random.default_rng(seed)
        return pd.Series(
            100.0 * np.exp(np.cumsum(rng.standard_normal(n) * 0.01)),
            index=pd.date_range("2020-01-01", periods=n, freq="B"),
        )

    def test_runs_and_trains(self):
        out = walk_forward_direction(self._prices(), horizon=12, seed=0, n_splits=3)
        assert out["is_trained"] is True
        assert out["n_folds"] >= 1
        assert 0.0 <= out["direction_accuracy"] <= 1.0
        assert out["device"] in ("cpu", "cuda", "torch.device('cuda')", "torch.device('cpu')") or "cuda" in str(out["device"]) or "cpu" in str(out["device"])

    def test_too_short_raises(self):
        with pytest.raises(ValueError):
            walk_forward_direction(self._prices(n=50), horizon=12, seed=0, n_splits=5)
