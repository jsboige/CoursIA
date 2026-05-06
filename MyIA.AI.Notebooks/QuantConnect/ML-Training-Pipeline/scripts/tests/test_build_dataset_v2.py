"""Tests for build_dataset_v2.py — dataset V2 builder."""

import sys
from pathlib import Path

import numpy as np
import pandas as pd
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))

from build_dataset_v2 import (
    PANIER_SYMBOLS,
    build_features_for_symbol,
    load_auxiliary_series,
)


@pytest.fixture
def synthetic_panier():
    """3-asset synthetic panier with enough rows for features."""
    np.random.seed(42)
    T = 500
    dates = pd.date_range("2020-01-01", periods=T, freq="B")
    panier = {}
    for sym, vol in [("SPY", 0.01), ("TLT", 0.008), ("DBC", 0.012)]:
        returns = np.random.randn(T).astype(np.float32) * vol
        close = (1 + pd.Series(returns)).cumprod() * 100
        panier[sym] = pd.DataFrame(
            {
                "Close": close.values,
                "Open": close.values * (1 + np.random.normal(0, 0.002, T)),
                "High": close.values * (1 + np.abs(np.random.normal(0, 0.005, T))),
                "Low": close.values * (1 - np.abs(np.random.normal(0, 0.005, T))),
                "Volume": np.abs(np.random.randn(T)) * 1e6,
            },
            index=dates,
        )
    return panier


class TestLoadAuxiliarySeries:
    def test_extracts_bond(self, synthetic_panier):
        aux = load_auxiliary_series(synthetic_panier)
        assert "bond" in aux
        assert len(aux["bond"]) > 0

    def test_extracts_commodity(self, synthetic_panier):
        aux = load_auxiliary_series(synthetic_panier)
        assert "commodity" in aux

    def test_extracts_equity(self, synthetic_panier):
        aux = load_auxiliary_series(synthetic_panier)
        assert "equity_index" in aux


class TestBuildFeaturesForSymbol:
    def test_price_regime(self, synthetic_panier):
        aux = load_auxiliary_series(synthetic_panier)
        features = build_features_for_symbol(
            "SPY", synthetic_panier["SPY"], aux, regime_method="price",
        )
        assert features is not None
        assert "regime_price" in features.columns
        assert "target" in features.columns
        assert len(features) > 0

    def test_hmm_regime(self, synthetic_panier):
        aux = load_auxiliary_series(synthetic_panier)
        features = build_features_for_symbol(
            "SPY", synthetic_panier["SPY"], aux, regime_method="hmm",
        )
        assert features is not None
        assert "regime_hmm" in features.columns

    def test_both_regimes(self, synthetic_panier):
        aux = load_auxiliary_series(synthetic_panier)
        features = build_features_for_symbol(
            "SPY", synthetic_panier["SPY"], aux, regime_method="both",
        )
        assert features is not None
        assert "regime_price" in features.columns
        assert "regime_hmm" in features.columns

    def test_cross_asset_features(self, synthetic_panier):
        aux = load_auxiliary_series(synthetic_panier)
        features = build_features_for_symbol(
            "SPY", synthetic_panier["SPY"], aux, regime_method="price",
        )
        assert "bond_equity_ratio" in features.columns
        assert "commodity_momentum" in features.columns
        assert "equity_strength" in features.columns

    def test_insufficient_data(self):
        short_df = pd.DataFrame(
            {"Close": [100, 101, 102], "Volume": [1e6, 1e6, 1e6]},
            index=pd.date_range("2020-01-01", periods=3),
        )
        result = build_features_for_symbol("SHORT", short_df, {})
        assert result is None

    def test_no_aux(self, synthetic_panier):
        features = build_features_for_symbol(
            "SPY", synthetic_panier["SPY"], {}, regime_method="price",
        )
        assert features is not None
        # Cross-asset features should be absent
        assert "bond_equity_ratio" not in features.columns

    def test_target_is_forward_return(self, synthetic_panier):
        aux = load_auxiliary_series(synthetic_panier)
        features = build_features_for_symbol(
            "SPY", synthetic_panier["SPY"], aux, regime_method="price",
        )
        assert "target" in features.columns
        # Target should be binary-like (forward return)
        valid = features["target"].dropna()
        assert valid.abs().max() < 1.0  # returns shouldn't exceed 100%

    def test_regime_labels_valid(self, synthetic_panier):
        aux = load_auxiliary_series(synthetic_panier)
        features = build_features_for_symbol(
            "SPY", synthetic_panier["SPY"], aux, regime_method="price",
        )
        valid_regimes = {"uptrend", "downtrend", "volatility", "black_swan"}
        regime_values = set(features["regime_price"].unique())
        assert regime_values.issubset(valid_regimes)


class TestPanierSymbols:
    def test_has_crypto(self):
        assert any("BTC" in s for s in PANIER_SYMBOLS)

    def test_has_bonds(self):
        assert "TLT" in PANIER_SYMBOLS

    def test_has_commodities(self):
        assert "GLD" in PANIER_SYMBOLS

    def test_no_faang(self):
        faang = {"AAPL", "MSFT", "GOOG", "AMZN", "NVDA", "TSLA", "META"}
        assert not faang.intersection(set(PANIER_SYMBOLS))
