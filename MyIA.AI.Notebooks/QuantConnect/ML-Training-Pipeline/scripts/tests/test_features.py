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
    compute_cross_asset_ratios,
    compute_vix_features,
    compute_macro_features,
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
        assert "obv_norm" not in feat.columns


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


class TestComputeCrossAssetRatios:
    def test_no_external_data(self, ohlcv):
        feat = compute_cross_asset_ratios(ohlcv)
        assert len(feat.columns) == 0

    def test_bond_equity_ratio(self, ohlcv):
        np.random.seed(42)
        bond_prices = pd.Series(
            100.0 + np.cumsum(np.random.randn(len(ohlcv)) * 0.2),
            index=ohlcv.index,
        )
        feat = compute_cross_asset_ratios(ohlcv, bond=bond_prices)
        assert "bond_equity_ratio" in feat.columns
        assert "bond_equity_zscore" in feat.columns

    def test_commodity_momentum(self, ohlcv):
        np.random.seed(42)
        comm_prices = pd.Series(
            50.0 + np.cumsum(np.random.randn(len(ohlcv)) * 0.3),
            index=ohlcv.index,
        )
        feat = compute_cross_asset_ratios(ohlcv, commodity=comm_prices)
        assert "commodity_momentum" in feat.columns

    def test_equity_strength(self, ohlcv):
        np.random.seed(42)
        eq_prices = pd.Series(
            200.0 + np.cumsum(np.random.randn(len(ohlcv)) * 0.5),
            index=ohlcv.index,
        )
        feat = compute_cross_asset_ratios(ohlcv, equity_index=eq_prices)
        assert "equity_strength" in feat.columns
        assert "equity_breadth_momentum" in feat.columns

    def test_all_combined(self, ohlcv):
        np.random.seed(42)
        n = len(ohlcv)
        bond = pd.Series(100 + np.cumsum(np.random.randn(n) * 0.2), index=ohlcv.index)
        comm = pd.Series(50 + np.cumsum(np.random.randn(n) * 0.3), index=ohlcv.index)
        eq = pd.Series(200 + np.cumsum(np.random.randn(n) * 0.5), index=ohlcv.index)
        feat = compute_cross_asset_ratios(ohlcv, bond=bond, commodity=comm, equity_index=eq)
        assert len(feat.columns) == 5

    def test_misaligned_indices(self, ohlcv):
        bond = pd.Series(100.0, index=ohlcv.index[:50])
        feat = compute_cross_asset_ratios(ohlcv, bond=bond)
        assert len(feat) == len(ohlcv)


class TestComputeVixFeatures:
    def test_no_vix(self, ohlcv):
        feat = compute_vix_features(ohlcv)
        assert len(feat.columns) == 0

    def test_vix_basic(self, ohlcv):
        np.random.seed(42)
        vix_series = pd.Series(
            15.0 + np.abs(np.random.randn(len(ohlcv)) * 3),
            index=ohlcv.index,
        )
        feat = compute_vix_features(ohlcv, vix=vix_series)
        assert "vix_level" in feat.columns
        assert "vix_change_1d" in feat.columns
        assert "vix_change_5d" in feat.columns
        assert "vix_zscore" in feat.columns
        assert "vix_rank_252d" in feat.columns

    def test_vix_term_structure(self, ohlcv):
        np.random.seed(42)
        n = len(ohlcv)
        vix_series = pd.Series(15.0 + np.abs(np.random.randn(n) * 3), index=ohlcv.index)
        vix9d = pd.Series(14.0 + np.abs(np.random.randn(n) * 2), index=ohlcv.index)
        feat = compute_vix_features(ohlcv, vix=vix_series, vix9d=vix9d)
        assert "vix_term_spread" in feat.columns
        assert "vix_term_zscore" in feat.columns
        assert len(feat.columns) == 7

    def test_vix_non_negative(self, ohlcv):
        np.random.seed(42)
        vix_series = pd.Series(
            15.0 + np.abs(np.random.randn(len(ohlcv)) * 3),
            index=ohlcv.index,
        )
        feat = compute_vix_features(ohlcv, vix=vix_series)
        assert (feat["vix_level"].dropna() >= 0).all()


class TestComputeMacroFeatures:
    def test_no_rates(self, ohlcv):
        feat = compute_macro_features(ohlcv)
        assert len(feat.columns) == 0

    def test_rates_10y(self, ohlcv):
        np.random.seed(42)
        rates = pd.Series(
            3.0 + np.cumsum(np.random.randn(len(ohlcv)) * 0.02),
            index=ohlcv.index,
        )
        feat = compute_macro_features(ohlcv, rates_10y=rates)
        assert "rate_10y" in feat.columns
        assert "rate_10y_change_5d" in feat.columns
        assert "rate_10y_change_20d" in feat.columns

    def test_yield_spread(self, ohlcv):
        np.random.seed(42)
        n = len(ohlcv)
        r10 = pd.Series(3.5 + np.cumsum(np.random.randn(n) * 0.02), index=ohlcv.index)
        r2 = pd.Series(3.0 + np.cumsum(np.random.randn(n) * 0.02), index=ohlcv.index)
        feat = compute_macro_features(ohlcv, rates_10y=r10, rates_2y=r2)
        assert "yield_spread_10y_2y" in feat.columns
        assert "yield_curve_slope" in feat.columns
        assert "yield_inverted" in feat.columns
        assert "rate_2y" in feat.columns

    def test_fed_funds(self, ohlcv):
        np.random.seed(42)
        ff = pd.Series(
            2.0 + np.cumsum(np.random.randn(len(ohlcv)) * 0.01),
            index=ohlcv.index,
        )
        feat = compute_macro_features(ohlcv, fed_funds=ff)
        assert "fed_funds_rate" in feat.columns
        assert "fed_funds_change_20d" in feat.columns

    def test_all_macro(self, ohlcv):
        np.random.seed(42)
        n = len(ohlcv)
        r10 = pd.Series(3.5 + np.cumsum(np.random.randn(n) * 0.02), index=ohlcv.index)
        r2 = pd.Series(3.0 + np.cumsum(np.random.randn(n) * 0.02), index=ohlcv.index)
        ff = pd.Series(2.0 + np.cumsum(np.random.randn(n) * 0.01), index=ohlcv.index)
        feat = compute_macro_features(ohlcv, rates_10y=r10, rates_2y=r2, fed_funds=ff)
        assert len(feat.columns) == 9


class TestFeatureEngineerStage2:
    def test_cross_asset_in_engineer(self, ohlcv):
        np.random.seed(42)
        n = len(ohlcv)
        bond = pd.Series(100 + np.cumsum(np.random.randn(n) * 0.2), index=ohlcv.index)
        eng = FeatureEngineer(
            lookback=20,
            indicators=["returns", "cross_asset_ratios"],
            bond=bond,
        )
        features = eng.transform(ohlcv)
        assert "bond_equity_ratio" in features.columns

    def test_vix_in_engineer(self, ohlcv):
        np.random.seed(42)
        vix = pd.Series(15 + np.abs(np.random.randn(len(ohlcv)) * 3), index=ohlcv.index)
        eng = FeatureEngineer(
            lookback=20,
            indicators=["returns", "vix_features"],
            vix=vix,
        )
        features = eng.transform(ohlcv)
        assert "vix_level" in features.columns

    def test_macro_in_engineer(self, ohlcv):
        np.random.seed(42)
        n = len(ohlcv)
        r10 = pd.Series(3.5 + np.cumsum(np.random.randn(n) * 0.02), index=ohlcv.index)
        eng = FeatureEngineer(
            lookback=20,
            indicators=["returns", "macro_features"],
            rates_10y=r10,
        )
        features = eng.transform(ohlcv)
        assert "rate_10y" in features.columns
