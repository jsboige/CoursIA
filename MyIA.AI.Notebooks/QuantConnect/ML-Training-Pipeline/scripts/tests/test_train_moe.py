"""Tests for train_moe.py — end-to-end MoE training pipeline."""

import numpy as np
import pandas as pd
import pytest
import tempfile
from pathlib import Path

from train_moe import (
    _compute_direction_target,
    _prepare_features,
    train_moe_pipeline,
)


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

@pytest.fixture
def ohlcv_df():
    """Synthetic OHLCV DataFrame mimicking real price data."""
    np.random.seed(42)
    n = 600
    dates = pd.date_range("2020-01-01", periods=n, freq="B")
    close = 100 * np.cumprod(1 + np.random.randn(n) * 0.01)
    df = pd.DataFrame({
        "Open": close * (1 + np.random.randn(n) * 0.002),
        "High": close * (1 + abs(np.random.randn(n)) * 0.005),
        "Low": close * (1 - abs(np.random.randn(n)) * 0.005),
        "Close": close,
        "Volume": np.random.randint(1_000_000, 10_000_000, n),
    }, index=dates)
    return df


# ---------------------------------------------------------------------------
# Feature computation
# ---------------------------------------------------------------------------

class TestDirectionTarget:
    def test_basic_target(self, ohlcv_df):
        target = _compute_direction_target(ohlcv_df, horizon=1)
        assert target.dtype == int
        assert set(target.dropna().unique()).issubset({0, 1})

    def test_target_length(self, ohlcv_df):
        target = _compute_direction_target(ohlcv_df, horizon=1)
        assert len(target) == len(ohlcv_df)

    def test_target_values_are_binary(self, ohlcv_df):
        target = _compute_direction_target(ohlcv_df, horizon=1)
        unique_vals = set(target.unique())
        assert unique_vals.issubset({0, 1})

    def test_threshold(self, ohlcv_df):
        target_zero = _compute_direction_target(ohlcv_df, threshold=0.0)
        target_pos = _compute_direction_target(ohlcv_cv := ohlcv_df, threshold=0.01)
        assert target_pos.sum() <= target_zero.sum()


class TestPrepareFeatures:
    def test_feature_shape(self, ohlcv_df):
        features = _prepare_features(ohlcv_df)
        assert features.shape[0] < len(ohlcv_df)
        assert features.shape[1] >= 5

    def test_no_nan(self, ohlcv_df):
        features = _prepare_features(ohlcv_df)
        assert features.isna().sum().sum() == 0

    def test_feature_columns(self, ohlcv_df):
        features = _prepare_features(ohlcv_df)
        assert "ret_1d" in features.columns
        assert "ret_20d" in features.columns
        assert "vol_20d" in features.columns

    def test_custom_lookback(self, ohlcv_df):
        features = _prepare_features(ohlcv_df, lookback=10)
        assert features.shape[0] < len(ohlcv_df)


# ---------------------------------------------------------------------------
# Pipeline integration (mocked data)
# ---------------------------------------------------------------------------

class TestPipelineIntegration:
    def test_pipeline_with_synthetic_data(self, ohlcv_df, tmp_path):
        """Test pipeline with in-memory synthetic data (no file I/O)."""
        from regime_detector import detect_regimes
        from moe_experts import MoEConfig, train_moe_walk_forward

        features = _prepare_features(ohlcv_df)
        target = _compute_direction_target(ohlcv_df, horizon=1)
        common_idx = features.index.intersection(target.dropna().index)
        features = features.loc[common_idx]
        target = target.loc[common_idx]

        prices = ohlcv_df["Close"].loc[common_idx]
        regime_series = detect_regimes(prices, method="price")
        regime_labels = regime_series.values

        X = features.values.astype(np.float32)
        y = target.values.astype(int)

        config = MoEConfig(
            min_samples_per_expert=20,
            max_iter=50,
        )

        results = train_moe_walk_forward(
            features=X, targets=y,
            regime_labels=regime_labels,
            n_folds=3, config=config,
        )

        assert len(results) == 3
        for r in results:
            assert "overall_accuracy" in r
            assert 0 <= r["overall_accuracy"] <= 1

    def test_pipeline_result_serialization(self, tmp_path):
        """Test that results can be serialized to JSON."""
        import json

        result = {
            "symbol": "TEST",
            "n_folds": 3,
            "majority_baseline": 0.54,
            "moe_mean_accuracy": 0.52,
            "beats_majority": False,
        }

        out_file = tmp_path / "results.json"
        with open(out_file, "w") as f:
            json.dump(result, f, indent=2)

        with open(out_file) as f:
            loaded = json.load(f)
        assert loaded["symbol"] == "TEST"
        assert loaded["beats_majority"] is False
