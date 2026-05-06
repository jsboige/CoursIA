"""Tests for features.py -- FeatureEngineer and indicator functions."""

import sys
from pathlib import Path

import numpy as np
import pandas as pd
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))

from features import (
    FeatureEngineer,
    compute_bollinger,
    compute_ma_ratios,
    compute_macd,
    compute_obv,
    compute_regime,
    compute_returns,
    compute_rsi,
    compute_statistical,
    compute_true_range_atr,
    compute_volatility,
    compute_volume_ratio,
    compute_momentum,
    compute_price_acceleration,
)


@pytest.fixture
def ohlcv():
    """Standard OHLCV fixture with enough rows for rolling windows."""
    np.random.seed(42)
    n = 300
    dates = pd.date_range("2020-01-01", periods=n, freq="B")
    close = 100.0 + np.cumsum(np.random.randn(n) * 0.5)
    return pd.DataFrame(
        {
            "Close": close,
            "Open": close * (1 + np.random.normal(0, 0.003, n)),
            "High": close * (1 + np.abs(np.random.normal(0, 0.008, n))),
            "Low": close * (1 - np.abs(np.random.normal(0, 0.008, n))),
            "Volume": np.abs(np.random.randn(n)) * 1e6,
        },
        index=dates,
    )


class TestComputeReturns:
    def test_default_windows(self, ohlcv):
        feat = compute_returns(ohlcv)
        assert "ret_1d" in feat.columns
        assert "ret_5d" in feat.columns
        assert "ret_10d" in feat.columns
        assert "ret_20d" in feat.columns
        assert len(feat) == len(ohlcv)

    def test_custom_windows(self, ohlcv):
        feat = compute_returns(ohlcv, windows=[3, 7])
        assert "ret_3d" in feat.columns
        assert "ret_7d" in feat.columns
        assert "ret_1d" not in feat.columns

    def test_values_reasonable(self, ohlcv):
        feat = compute_returns(ohlcv)
        assert feat["ret_1d"].dropna().abs().mean() < 0.1


class TestComputeVolatility:
    def test_columns(self, ohlcv):
        feat = compute_volatility(ohlcv)
        assert "vol_5d" in feat.columns
        assert "vol_20d" in feat.columns

    def test_non_negative(self, ohlcv):
        feat = compute_volatility(ohlcv)
        assert (feat.dropna() >= 0).all().all()


class TestComputeVolumeRatio:
    def test_column(self, ohlcv):
        feat = compute_volume_ratio(ohlcv)
        assert "vol_ratio" in feat.columns

    def test_around_one(self, ohlcv):
        feat = compute_volume_ratio(ohlcv)
        mean_val = feat["vol_ratio"].dropna().mean()
        assert 0.5 < mean_val < 2.0


class TestComputeMARatios:
    def test_columns(self, ohlcv):
        feat = compute_ma_ratios(ohlcv)
        for w in [5, 10, 20, 60]:
            assert f"ma_ratio_{w}" in feat.columns


class TestComputeRSI:
    def test_column(self, ohlcv):
        feat = compute_rsi(ohlcv)
        assert "rsi_14" in feat.columns

    def test_bounded(self, ohlcv):
        feat = compute_rsi(ohlcv)
        valid = feat["rsi_14"].dropna()
        assert valid.min() >= 0
        assert valid.max() <= 100


class TestComputeMACD:
    def test_columns(self, ohlcv):
        feat = compute_macd(ohlcv)
        assert "macd" in feat.columns
        assert "macd_signal" in feat.columns


class TestComputeBollinger:
    def test_column(self, ohlcv):
        feat = compute_bollinger(ohlcv)
        assert "bb_width" in feat.columns


class TestComputeTrueRangeATR:
    def test_columns(self, ohlcv):
        feat = compute_true_range_atr(ohlcv)
        assert "true_range" in feat.columns
        assert "atr_14" in feat.columns

    def test_no_high_low(self):
        df = pd.DataFrame({"Close": [100, 101, 102], "Volume": [1e6, 1e6, 1e6]})
        feat = compute_true_range_atr(df)
        assert len(feat.columns) == 0


class TestComputeOBV:
    def test_columns(self, ohlcv):
        feat = compute_obv(ohlcv)
        assert "obv" in feat.columns
        assert "obv_norm" in feat.columns


class TestComputeRegime:
    def test_columns(self, ohlcv):
        feat = compute_regime(ohlcv)
        assert "trend_regime" in feat.columns
        assert "trend_strength" in feat.columns
        assert "vol_regime" in feat.columns

    def test_trend_binary(self, ohlcv):
        feat = compute_regime(ohlcv)
        valid = feat["trend_regime"].dropna()
        assert set(valid.unique()).issubset({0.0, 1.0})


class TestComputeMomentum:
    def test_columns(self, ohlcv):
        feat = compute_momentum(ohlcv)
        assert "roc_5" in feat.columns
        assert "stoch_k_14" in feat.columns
        assert "williams_r_14" in feat.columns


class TestComputeStatistical:
    def test_columns(self, ohlcv):
        feat = compute_statistical(ohlcv)
        assert "skewness" in feat.columns
        assert "kurtosis" in feat.columns
        assert "autocorr" in feat.columns
        assert "downside_vol" in feat.columns
        assert "upside_vol" in feat.columns


class TestComputePriceAcceleration:
    def test_columns(self, ohlcv):
        feat = compute_price_acceleration(ohlcv)
        assert "acceleration_5" in feat.columns
        assert "acceleration_10" in feat.columns


class TestFeatureEngineer:
    def test_transform_output(self, ohlcv):
        eng = FeatureEngineer(lookback=20)
        features = eng.transform(ohlcv)
        assert "target" in features.columns
        assert len(features) > 0
        assert not features.isnull().any().any()

    def test_no_target(self, ohlcv):
        eng = FeatureEngineer(lookback=20)
        features = eng.transform(ohlcv, add_target=False)
        assert "target" not in features.columns

    def test_custom_indicators(self, ohlcv):
        eng = FeatureEngineer(lookback=20, indicators=["returns", "rsi"])
        features = eng.transform(ohlcv)
        cols = [c for c in features.columns if c != "target"]
        assert len(cols) > 0

    def test_all_indicators(self, ohlcv):
        eng = FeatureEngineer(lookback=20)
        features = eng.transform(ohlcv)
        assert len(features.columns) > 30

    def test_feature_columns_property(self):
        eng = FeatureEngineer(lookback=20, indicators=["returns"])
        cols = eng.feature_columns
        assert isinstance(cols, list)
        assert len(cols) > 0

    def test_cache_roundtrip(self, ohlcv, tmp_path):
        cache_path = tmp_path / "test_features.parquet"
        eng = FeatureEngineer(lookback=20)
        feat1 = eng.transform(ohlcv, cache_path=str(cache_path))
        assert cache_path.exists()
        feat2 = eng.load_cache(str(cache_path))
        assert len(feat1) == len(feat2)

    def test_data_hash(self, ohlcv):
        h = FeatureEngineer._data_hash(ohlcv)
        assert isinstance(h, str)
        assert len(h) == 16
