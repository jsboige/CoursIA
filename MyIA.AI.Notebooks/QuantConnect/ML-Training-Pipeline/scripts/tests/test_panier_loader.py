"""Tests for panier_loader: multi-asset anti-bias data loading."""

from __future__ import annotations

import sys
from pathlib import Path

import numpy as np
import pandas as pd
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent))

from panier_loader import (
    STAGE_3A_SYMBOLS,
    PANIER_GROUPS,
    FORBIDDEN_SYMBOLS,
    get_panier_symbols,
    load_panier,
    load_panier_closes,
    load_panier_returns,
    validate_panier_integrity,
    compute_cross_asset_features,
)


class TestPanierDefinitions:
    def test_stage_3a_has_expected_count(self):
        # 10 sectors + 3 bonds + 3 commodities + 2 intl + RSP + VIX = 20
        assert len(STAGE_3A_SYMBOLS) == 20

    def test_no_forbidden_symbols_in_panier(self):
        all_symbols = get_panier_symbols()
        forbidden = [s for s in all_symbols if s in FORBIDDEN_SYMBOLS]
        assert forbidden == [], f"Forbidden symbols found: {forbidden}"

    def test_all_groups_present(self):
        assert len(PANIER_GROUPS) == 7

    def test_group_sizes(self):
        assert len(PANIER_GROUPS["us_equity_sectors"]) == 10
        assert len(PANIER_GROUPS["us_bonds"]) == 3
        assert len(PANIER_GROUPS["commodities"]) == 3
        assert len(PANIER_GROUPS["international"]) == 2

    def test_get_panier_symbols_all(self):
        symbols = get_panier_symbols()
        assert len(symbols) >= 26

    def test_get_panier_symbols_group(self):
        sectors = get_panier_symbols("us_equity_sectors")
        assert len(sectors) == 10
        assert "XLF" in sectors

    def test_get_panier_symbols_invalid_group(self):
        with pytest.raises(ValueError, match="Unknown group"):
            get_panier_symbols("nonexistent")


class TestPanierLoading:
    @pytest.fixture
    def panier_dir(self, tmp_path):
        """Create synthetic panier CSVs in a temp directory."""
        np.random.seed(42)
        dates = pd.date_range("2015-01-01", periods=500, freq="B")

        for group in PANIER_GROUPS.values():
            for symbol in group:
                close = 100.0 * np.exp(np.cumsum(np.random.normal(0.0002, 0.012, len(dates))))
                df = pd.DataFrame({
                    "Close": close,
                    "Open": close * (1 + np.random.normal(0, 0.002, len(dates))),
                    "High": close * (1 + np.abs(np.random.normal(0, 0.005, len(dates)))),
                    "Low": close * (1 - np.abs(np.random.normal(0, 0.005, len(dates)))),
                    "Volume": np.random.lognormal(15, 1, len(dates)),
                }, index=dates)
                safe_name = symbol.replace("-", "_").replace("^", "")
                df.to_csv(tmp_path / f"{safe_name}_2015-01-01_2025-01-01.csv")

        return tmp_path

    def test_load_panier_all(self, panier_dir):
        result = load_panier(panier_dir=panier_dir)
        assert len(result) >= 20
        for symbol, df in result.items():
            assert "Close" in df.columns
            assert len(df) > 0

    def test_load_panier_group(self, panier_dir):
        result = load_panier(group="us_bonds", panier_dir=panier_dir)
        assert len(result) == 3

    def test_load_panier_closes(self, panier_dir):
        closes = load_panier_closes(panier_dir=panier_dir)
        assert isinstance(closes, pd.DataFrame)
        assert len(closes.columns) >= 20
        assert closes.index.name == "Date"

    def test_load_panier_returns(self, panier_dir):
        returns = load_panier_returns(panier_dir=panier_dir)
        assert isinstance(returns, pd.DataFrame)
        assert len(returns) < 500  # dropna removes first row

    def test_load_panier_date_filter(self, panier_dir):
        result = load_panier(start="2015-06-01", end="2015-12-31", panier_dir=panier_dir)
        for symbol, df in result.items():
            if len(df) > 0:
                assert df.index.min() >= pd.Timestamp("2015-06-01")
                assert df.index.max() <= pd.Timestamp("2015-12-31")


class TestPanierValidation:
    @pytest.fixture
    def panier_dir(self, tmp_path):
        np.random.seed(42)
        dates = pd.date_range("2015-01-01", periods=2000, freq="B")

        for group in PANIER_GROUPS.values():
            for symbol in group:
                close = 100.0 * np.exp(np.cumsum(np.random.normal(0.0002, 0.012, len(dates))))
                df = pd.DataFrame({
                    "Close": close,
                    "Open": close,
                    "High": close * 1.01,
                    "Low": close * 0.99,
                    "Volume": 1e6,
                }, index=dates)
                safe_name = symbol.replace("-", "_").replace("^", "")
                df.to_csv(tmp_path / f"{safe_name}_2015-01-01_2025-01-01.csv")
        return tmp_path

    def test_validate_panier_all_ok(self, panier_dir):
        results = validate_panier_integrity(panier_dir)
        assert results["ok"] == results["total"]
        assert len(results["issues"]) == 0

    def test_validate_panier_missing_file(self, tmp_path):
        results = validate_panier_integrity(tmp_path)
        assert results["missing"] > 0


class TestCrossAssetFeatures:
    def test_compute_features(self):
        np.random.seed(42)
        dates = pd.date_range("2015-01-01", periods=500, freq="B")
        closes = pd.DataFrame({
            "SPY": 100 * np.exp(np.cumsum(np.random.normal(0.0003, 0.01, 500))),
            "TLT": 100 * np.exp(np.cumsum(np.random.normal(0.0001, 0.008, 500))),
            "GLD": 100 * np.exp(np.cumsum(np.random.normal(0.0002, 0.012, 500))),
        }, index=dates)

        features = compute_cross_asset_features(closes, lookback=20)
        assert isinstance(features, pd.DataFrame)
        assert len(features) > 0
        assert any("rel_mom" in c for c in features.columns)
        assert any("corr_spy" in c for c in features.columns)
        assert any("vol_" in c for c in features.columns)
