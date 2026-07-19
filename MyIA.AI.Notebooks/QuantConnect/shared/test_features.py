#!/usr/bin/env python3
"""Pytest suite for `QuantConnect/shared/features.py`.

Co-localisé avec le module sous `shared/`. CPU-only, no network, no
QuantBook/QC Cloud. Le module importe uniquement stdlib + pandas + numpy
(L20-22) et fait du calcul pur sur Series/DataFrame de prix, donc il est
entièrement exerçable de façon déterministe.

Le module est le helper partagé de feature-engineering consommé par les
notebooks QC ML (18-21) : calculate_returns, add_technical_features
(SMA/EMA/RSI/MACD/Bollinger), create_labels, walk_forward_split,
add_lagged_features, feature_importance_scores. 0 test Python dédié avant
cette PR.

Stratégie : données déterministes (pas de RNG, sauf RF stub pour
feature_importance), séries hand-computable, assertions pin la formule
(pas valeur hardcoded). Edge cases (RSI flat, ternary zero-return, lags,
modèle sans feature_importances_) exercent les guards et la sémantique.

G.9 honnêteté : bug-hunt firsthand AVANT tests (leçon c.534). 0 bug
fonctionnel forçable sur 5 fonctions. **1 limitation de design documentée**
sur `walk_forward_split(n_splits>1)` : la formule expanding-window donne
`train_end(i=1) = train_initial + test_size = total`, donc le 2e fold de
test démarre à `total` (vide) -> le code `break` tronque TOUJOURS à
exactement 1 split quel que soit `n_splits` (vérifié firsthand pour
train_size in {0.5,0.6,0.7,0.8}). Le path multi-split est effectivement
dead. Pinné tel quel dans `test_walk_forward_multi_split_truncates_to_one`
(caractérisation honnête, pas un fix source : la correction = décision de
design rolling vs expanding-with-overlap, signalée à ai-01 pour PR séparée).
"""
from __future__ import annotations

import importlib.util
from pathlib import Path

import numpy as np
import pandas as pd
import pytest

# Load module by path (lives under shared/, stdlib + pandas + numpy only,
# no package-relative imports -> no sys.path manipulation).
_MODULE_PATH = Path(__file__).resolve().parent / "features.py"
_spec = importlib.util.spec_from_file_location("features", _MODULE_PATH)
ft = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(ft)


# ── calculate_returns ───────────────────────────────────────────────────────


class TestCalculateReturns:
    """Retours multi-période via pct_change(period). Colonne return_{p}d."""

    def test_column_names_per_period(self):
        prices = pd.Series([100.0, 101, 99, 102, 105])
        out = ft.calculate_returns(prices, periods=[1, 5, 20])
        assert list(out.columns) == ["return_1d", "return_5d", "return_20d"]

    def test_period_1_values_and_nan_head(self):
        prices = pd.Series([100.0, 110, 99])  # +10%, -10%
        out = ft.calculate_returns(prices, periods=[1])
        v = out["return_1d"].tolist()
        assert np.isnan(v[0])  # first period has no prior -> NaN
        assert v[1] == pytest.approx(0.10)
        assert v[2] == pytest.approx(-0.10)

    def test_period_2_has_two_nan_head(self):
        prices = pd.Series([100.0, 101, 99, 102])
        out = ft.calculate_returns(prices, periods=[2])
        assert np.isnan(out["return_2d"].iloc[0])
        assert np.isnan(out["return_2d"].iloc[1])
        # (102 - 100) / 100 = 0.02 over 2 periods
        assert out["return_2d"].iloc[2] == pytest.approx((99 - 100) / 100)
        assert out["return_2d"].iloc[3] == pytest.approx((102 - 101) / 101)

    def test_index_preserved(self):
        idx = pd.date_range("2020-01-01", periods=4)
        prices = pd.Series([100.0, 101, 99, 102], index=idx)
        out = ft.calculate_returns(prices, periods=[1])
        assert out.index.equals(idx)

    def test_empty_periods_returns_empty_columns(self):
        prices = pd.Series([100.0, 101])
        out = ft.calculate_returns(prices, periods=[])
        assert out.shape == (2, 0)


# ── add_technical_features ──────────────────────────────────────────────────


class TestAddTechnicalFeatures:
    """SMA / EMA / RSI / MACD / Bollinger. SMA-RSI (simple rolling mean)."""

    def test_sma_window_and_values(self):
        df = pd.DataFrame({"close": [10.0, 20, 30, 40]})
        out = ft.add_technical_features(df, {"sma": [2]})
        assert "sma_2" in out.columns
        assert np.isnan(out["sma_2"].iloc[0])
        assert out["sma_2"].iloc[1] == pytest.approx(15.0)  # (10+20)/2
        assert out["sma_2"].iloc[3] == pytest.approx(35.0)  # (30+40)/2

    def test_ema_column_added(self):
        df = pd.DataFrame({"close": [1.0, 2, 3, 4, 5]})
        out = ft.add_technical_features(df, {"ema": [3]})
        assert "ema_3" in out.columns
        # EMA is defined for all rows (no NaN head) with adjust=False.
        assert out["ema_3"].isna().sum() == 0

    def test_rsi_monotone_up_approaches_100(self):
        # Strictly increasing -> all gains after first diff -> RSI -> 100.
        up = pd.Series(list(range(100, 120)), name="close").to_frame()
        out = ft.add_technical_features(up, {"rsi": 5})
        assert out["rsi_5"].iloc[-1] == pytest.approx(100.0)

    def test_rsi_monotone_down_approaches_0(self):
        dn = pd.Series(list(range(120, 100, -1)), name="close").to_frame()
        out = ft.add_technical_features(dn, {"rsi": 5})
        assert out["rsi_5"].iloc[-1] == pytest.approx(0.0)

    def test_rsi_flat_price_is_nan(self):
        # Constant price -> gain = loss = 0 -> rs = 0/0 = NaN -> RSI = NaN.
        flat = pd.Series([100.0] * 20, name="close").to_frame()
        out = ft.add_technical_features(flat, {"rsi": 5})
        assert np.isnan(out["rsi_5"].iloc[-1])

    def test_macd_three_columns(self):
        df = pd.DataFrame({"close": list(range(1, 51))}, dtype=float)
        out = ft.add_technical_features(df, {"macd": (12, 26, 9)})
        for col in ["macd", "macd_signal", "macd_hist"]:
            assert col in out.columns
        # macd_hist = macd - signal by construction
        assert (out["macd_hist"] == out["macd"] - out["macd_signal"]).all()

    def test_bollinger_four_columns_and_geometry(self):
        df = pd.DataFrame({"close": list(range(1, 31))}, dtype=float)
        out = ft.add_technical_features(df, {"bb": (20, 2)})
        for col in ["bb_upper", "bb_middle", "bb_lower", "bb_width"]:
            assert col in out.columns
        last = out.iloc[-1]
        # middle == SMA, upper == middle + 2*std, lower symmetric, width = upper-lower.
        assert last["bb_middle"] == pytest.approx(out["close"].rolling(20).mean().iloc[-1])
        assert last["bb_upper"] > last["bb_middle"] > last["bb_lower"]
        assert last["bb_width"] == pytest.approx(last["bb_upper"] - last["bb_lower"])

    def test_does_not_mutate_input(self):
        df = pd.DataFrame({"close": [1.0, 2, 3, 4]})
        original_cols = list(df.columns)
        ft.add_technical_features(df, {"sma": [2]})
        assert list(df.columns) == original_cols  # input untouched

    def test_custom_price_col(self):
        df = pd.DataFrame({"adj": [10.0, 20, 30, 40]})
        out = ft.add_technical_features(df, {"sma": [2]}, price_col="adj")
        assert "sma_2" in out.columns


# ── create_labels ───────────────────────────────────────────────────────────


class TestCreateLabels:
    """binary (1=up), ternary (1/0/-1), regression (verbatim)."""

    def test_binary_strictly_greater(self):
        rets = pd.Series([0.01, -0.005, 0.0, 0.02])
        out = ft.create_labels(rets, threshold=0.0, method="binary")
        # 0.01>0 ->1 ; -0.005>0 ->0 ; 0.0>0 ->0 (strict) ; 0.02>0 ->1
        assert out.tolist() == [1, 0, 0, 1]

    def test_binary_respects_threshold(self):
        rets = pd.Series([0.02, 0.01, -0.01])
        out = ft.create_labels(rets, threshold=0.015, method="binary")
        # 0.02>0.015 ->1 ; 0.01>0.015 ->0 ; -0.01 ->0
        assert out.tolist() == [1, 0, 0]

    def test_ternary_neutral_band(self):
        rets = pd.Series([0.05, 0.0, -0.05])
        out = ft.create_labels(rets, threshold=0.01, method="ternary")
        # 0.05>0.01 ->1 ; |0.0|<0.01 ->0 ; -0.05<-0.01 ->-1
        assert out.tolist() == [1, 0, -1]

    def test_ternary_zero_return_is_neutral(self):
        rets = pd.Series([0.0, 0.0])
        out = ft.create_labels(rets, threshold=0.0, method="ternary")
        assert out.tolist() == [0, 0]  # not >0 and not <0 -> neutral

    def test_regression_returns_raw(self):
        rets = pd.Series([0.01, -0.02, 0.03])
        out = ft.create_labels(rets, method="regression")
        assert out.tolist() == rets.tolist()

    def test_unknown_method_raises(self):
        with pytest.raises(ValueError, match="Unknown method"):
            ft.create_labels(pd.Series([0.01]), method="bogus")


# ── walk_forward_split ──────────────────────────────────────────────────────


class TestWalkForwardSplit:
    """Split time-aware train/test. Requiert DatetimeIndex. **Limitation
    n_splits>1 documentée** (caractérisation honnête, cf module docstring)."""

    def _ts(self, n=100):
        return pd.DataFrame(
            {"p": range(n)}, index=pd.date_range("2020-01-01", periods=n)
        )

    def test_single_split_sizes(self):
        splits = ft.walk_forward_split(self._ts(100), train_size=0.7, n_splits=1)
        assert len(splits) == 1
        train, test = splits[0]
        assert len(train) == 70
        assert len(test) == 30

    def test_single_split_no_temporal_overlap(self):
        splits = ft.walk_forward_split(self._ts(100), train_size=0.6)
        train, test = splits[0]
        assert train.index[-1] < test.index[0]  # train entirely before test

    def test_non_datetime_index_raises(self):
        bad = pd.DataFrame({"p": [1, 2, 3]})
        with pytest.raises(ValueError, match="DatetimeIndex"):
            ft.walk_forward_split(bad)

    def test_multi_split_truncates_to_one(self):
        """G.9 honnêteté : limitation de design. La formule expanding-window
        donne train_end(i=1) = train_initial + test_size = total_size, donc le
        2e fold de test démarre à total_size (vide) -> break -> toujours 1
        split. Vérifié firsthand pour train_size in {0.5,0.6,0.7,0.8}. Le path
        n_splits>1 est effectivement dead. Pinné tel quel (caractérisation) ;
        le fix (rolling vs expanding-with-overlap) = décision de design à
        trancher par ai-01 dans une PR séparée, pas un fix source ici."""
        for ts_param in [0.5, 0.6, 0.7, 0.8]:
            for ns in [2, 3, 5]:
                splits = ft.walk_forward_split(
                    self._ts(200), train_size=ts_param, n_splits=ns
                )
                assert len(splits) == 1, (
                    f"expected 1 split (design limitation) for "
                    f"train_size={ts_param} n_splits={ns}, got {len(splits)}"
                )

    def test_split_proportions_train_size_half(self):
        splits = ft.walk_forward_split(self._ts(100), train_size=0.5)
        train, test = splits[0]
        assert len(train) == 50 and len(test) == 50


# ── add_lagged_features ─────────────────────────────────────────────────────


class TestAddLaggedFeatures:
    """shift(lag) sur colonnes nommées. Skip colonnes absentes."""

    def test_lag_columns_created(self):
        df = pd.DataFrame({"price": [10.0, 20, 30, 40]})
        out = ft.add_lagged_features(df, columns=["price"], lags=[1, 2])
        assert "price_lag_1" in out.columns
        assert "price_lag_2" in out.columns

    def test_lag_1_values_and_nan_head(self):
        df = pd.DataFrame({"price": [10.0, 20, 30, 40]})
        out = ft.add_lagged_features(df, columns=["price"], lags=[1])
        assert np.isnan(out["price_lag_1"].iloc[0])
        assert out["price_lag_1"].iloc[1] == pytest.approx(10.0)
        assert out["price_lag_1"].iloc[3] == pytest.approx(30.0)

    def test_skips_missing_columns_silently(self):
        df = pd.DataFrame({"a": [1.0, 2, 3]})
        out = ft.add_lagged_features(df, columns=["a", "nonexistent"], lags=[1])
        # 'a' lagged, nonexistent skipped, no crash, no stray columns.
        assert "a_lag_1" in out.columns
        assert "nonexistent_lag_1" not in out.columns

    def test_does_not_mutate_input(self):
        df = pd.DataFrame({"a": [1.0, 2, 3]})
        before = df.copy()
        ft.add_lagged_features(df, columns=["a"], lags=[1])
        pd.testing.assert_frame_equal(df, before)


# ── feature_importance_scores ───────────────────────────────────────────────


class TestFeatureImportanceScores:
    """Extrait .feature_importances_ d'un modèle, trie décroissant."""

    def test_returns_sorted_dataframe(self):
        pytest.importorskip("sklearn")
        from sklearn.ensemble import RandomForestClassifier

        # 5 features, deterministic.
        rng = np.random.RandomState(42)
        X = rng.rand(80, 5)
        y = (X[:, 0] > 0.5).astype(int)  # feature 0 is informative
        model = RandomForestClassifier(n_estimators=25, random_state=42).fit(X, y)
        out = ft.feature_importance_scores(model, [f"f{i}" for i in range(5)])
        assert list(out.columns) == ["feature", "importance"]
        # Sorted descending.
        assert out["importance"].is_monotonic_decreasing
        assert len(out) == 5

    def test_model_without_importances_raises(self):
        class NoImportances:
            pass

        with pytest.raises(ValueError, match="feature_importances_"):
            ft.feature_importance_scores(NoImportances(), ["x"])

    def test_feature_names_preserved(self):
        pytest.importorskip("sklearn")
        from sklearn.ensemble import RandomForestClassifier

        rng = np.random.RandomState(0)
        X = rng.rand(40, 3)
        y = rng.randint(0, 2, 40)
        model = RandomForestClassifier(n_estimators=5, random_state=0).fit(X, y)
        names = ["alpha", "beta", "gamma"]
        out = ft.feature_importance_scores(model, names)
        assert set(out["feature"]) == set(names)
