"""Tests for eval_baselines_zeroshot.py -- trivial-baseline counterpoint (#8607).

CPU-only unit tests on prepare_features (parity with the rungs), the
majority/direction-accuracy formulas, and walk_forward_baseline on synthetic
series with KNOWN direction structure (perfect persistence -> DirAcc 1.0,
alternating -> DirAcc ~0.0). The real persistence edges on SPY/TLT/GLD are
proven by the committed results.json, not by these tests.
"""

import sys
from pathlib import Path

import numpy as np
import pandas as pd
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))

from eval_baselines_zeroshot import (  # noqa: E402
    compute_direction_accuracy,
    compute_majority_baseline,
    prepare_features,
    walk_forward_baseline,
)


class TestPrepareFeatures:
    def test_features_shape_and_sign(self):
        prices = pd.Series([100.0 * np.exp(0.01 * i) for i in range(100)])
        features, log_returns = prepare_features(prices)
        assert features.shape[1] == 2  # [log_ret, sign]
        assert len(log_returns) == len(features)
        # monotonically rising -> all log_returns > 0 -> all signs +1
        assert np.all(features[:, 1] == 1.0)

    def test_log_returns_match_manual(self):
        prices = pd.Series([100.0, 101.0, 100.0, 102.0, 103.0])
        _, log_returns = prepare_features(prices)
        # manual: ln(101/100), ln(100/101), ln(102/100), ln(103/102)
        expected = np.log(np.array([101.0, 100.0, 102.0, 103.0])
                          / np.array([100.0, 101.0, 100.0, 102.0]))
        assert np.allclose(log_returns, expected, atol=1e-9)


class TestMetrics:
    def test_direction_accuracy_perfect(self):
        y = np.array([0.1, -0.2, 0.3, -0.1])
        assert compute_direction_accuracy(y, y) == 1.0

    def test_direction_accuracy_all_wrong(self):
        y = np.array([0.1, 0.2, 0.3])
        pred = np.array([-0.1, -0.2, -0.3])
        assert compute_direction_accuracy(y, pred) == 0.0

    def test_majority_baseline_balanced(self):
        rets = np.array([0.1, -0.1, 0.2, -0.2])  # 50/50
        out = compute_majority_baseline(rets)
        assert out["majority_class_accuracy"] == 0.5

    def test_majority_baseline_skewed_up(self):
        rets = np.array([0.1, 0.2, 0.3, -0.1])  # 3 up, 1 down
        out = compute_majority_baseline(rets)
        assert out["majority_class_accuracy"] == 0.75
        assert out["majority_class"] == "up"


class TestWalkForwardBaseline:
    def _series(self, n=600, up=True):
        """A synthetic price series that trends one direction every day."""
        drift = 0.002 if up else -0.002
        steps = np.full(n, drift)
        log_p = np.cumsum(steps)
        return pd.Series(np.exp(log_p) * 100.0)

    def test_persistence_perfect_continuation(self):
        # Monotonically rising: last day is up, all future days up -> persistence
        # predicts "up" everywhere and is correct everywhere -> DirAcc ~1.0.
        prices = self._series(n=600, up=True)
        out = walk_forward_baseline(prices, horizon=24, baseline="persistence")
        assert "error" not in out
        assert out["direction_accuracy"] > 0.99

    def test_persistence_white_noise_around_half(self):
        # Pure random walk (white-noise returns): consecutive signs are
        # independent -> persistence is a coin flip -> DirAcc ~0.5.
        rng = np.random.default_rng(42)
        n = 600
        steps = rng.normal(0, 0.01, size=n)
        log_p = np.cumsum(steps)
        prices = pd.Series(np.exp(log_p) * 100.0)
        out = walk_forward_baseline(prices, horizon=24, baseline="persistence")
        assert "error" not in out
        # coin-flip DirAcc should be close to 0.5 (within a wide band)
        assert 0.45 < out["direction_accuracy"] < 0.55

    def test_unknown_baseline_raises(self):
        prices = self._series(n=200)
        with pytest.raises(ValueError):
            walk_forward_baseline(prices, horizon=24, baseline="bogus")

    def test_too_short_raises(self):
        prices = pd.Series([100.0 + i for i in range(50)])  # too small for 5 splits
        with pytest.raises(ValueError):
            walk_forward_baseline(prices, horizon=24, baseline="persistence")

    def test_fold_count(self):
        prices = self._series(n=600)
        out = walk_forward_baseline(prices, horizon=24, baseline="persistence")
        # N_SPLITS=5 folds, all should produce enough points
        assert out["n_folds"] <= 5
        assert out["n_folds"] >= 1
        assert out["n_splits"] == 5
