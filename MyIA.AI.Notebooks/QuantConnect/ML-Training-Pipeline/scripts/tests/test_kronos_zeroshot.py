"""Tests for eval_kronos_zeroshot.py and eval_chronos_bolt.py -- CPU-only smoke tests."""

import sys
from pathlib import Path

import numpy as np
import pandas as pd
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))

from eval_kronos_zeroshot import (
    NaiveKronosWrapper,
    build_evaluation_windows,
    compute_direction_accuracy,
    compute_majority_baseline,
    compute_transaction_cost,
    evaluate_window,
    load_kronos_model,
)
from baselines import sharpe_from_returns
from eval_chronos_bolt import (
    NaiveChronosWrapper,
    load_chronos_model,
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
    def test_balanced(self):
        returns = np.array([1.0, -1.0] * 50, dtype=np.float32)
        baseline = compute_majority_baseline(returns)
        assert baseline["majority_class_accuracy"] == 0.5

    def test_biased_up(self):
        returns = np.ones(100, dtype=np.float32)
        baseline = compute_majority_baseline(returns)
        assert baseline["majority_class_accuracy"] == 1.0
        assert baseline["majority_class"] == "up"


class TestSharpe:
    def test_positive_sharpe(self):
        np.random.seed(42)
        returns = np.random.randn(252) * 0.01 + 0.0005
        sharpe = sharpe_from_returns(returns)
        assert sharpe > 0

    def test_zero_returns(self):
        sharpe = sharpe_from_returns(np.array([0.0, 0.0, 0.0]))
        assert sharpe == 0.0

    def test_constant_returns(self):
        sharpe = sharpe_from_returns(np.array([0.01, 0.01, 0.01]))
        assert sharpe == 0.0


class TestTransactionCost:
    def test_no_trades(self):
        preds = np.array([1.0, 1.0, 1.0, 1.0])
        cost = compute_transaction_cost(preds, cost_bps=10.0)
        assert cost == 0.0

    def test_two_trades(self):
        preds = np.array([1.0, -1.0, 1.0])
        cost = compute_transaction_cost(preds, cost_bps=10.0)
        assert cost > 0.0

    def test_single_element(self):
        preds = np.array([1.0])
        cost = compute_transaction_cost(preds)
        assert cost == 0.0


class TestEvaluationWindows:
    @staticmethod
    def _ohlcv(n=500, seed=0):
        rng = np.random.default_rng(seed)
        dates = pd.date_range("2020-01-01", periods=n, freq="B")
        close = np.cumsum(rng.standard_normal(n) * 0.01 + 100)
        return pd.DataFrame(
            {
                "open": close, "high": close + 0.5, "low": close - 0.5,
                "close": close, "volume": 0.0,
            },
            index=dates,
        )

    def test_window_count(self):
        ohlcv = self._ohlcv()
        windows = build_evaluation_windows(ohlcv, seq_len=96, pred_len=24, n_windows=5)
        assert 0 < len(windows) <= 5

    def test_window_shapes(self):
        ohlcv = self._ohlcv()
        windows = build_evaluation_windows(ohlcv, seq_len=96, pred_len=24, n_windows=3)
        for w in windows:
            assert w["context_ohlcv"].shape == (96, 5)  # OHLCV
            assert w["actual_close"].shape == (24,)
            assert w["x_timestamp"].shape == (96,)

    def test_temporal_ordering(self):
        ohlcv = self._ohlcv()
        windows = build_evaluation_windows(ohlcv, seq_len=10, pred_len=5, n_windows=3)
        for i in range(1, len(windows)):
            assert windows[i]["start_date"] >= windows[i - 1]["start_date"]


class TestNaiveKronosWrapper:
    @staticmethod
    def _context(n=96):
        dates = pd.date_range("2020-01-01", periods=n, freq="B")
        close = np.arange(n, dtype=float) + 100
        return pd.DataFrame(
            {"open": close, "high": close, "low": close, "close": close, "volume": 0.0},
            index=dates,
        )

    def test_predict_shape(self):
        wrapper = NaiveKronosWrapper()
        ctx = self._context()
        x_ts = pd.Series(ctx.index)
        y_ts = pd.Series(pd.date_range("2020-05-01", periods=24, freq="B"))
        forecast = wrapper.predict(ctx, x_timestamp=x_ts, y_timestamp=y_ts, pred_len=24)
        assert forecast.shape == (24,)

    def test_predict_persistence(self):
        wrapper = NaiveKronosWrapper()
        ctx = self._context()
        x_ts = pd.Series(ctx.index)
        y_ts = pd.Series(pd.date_range("2020-05-01", periods=10, freq="B"))
        forecast = wrapper.predict(ctx, x_timestamp=x_ts, y_timestamp=y_ts, pred_len=10)
        assert np.all(forecast == ctx["close"].iloc[-1])

    def test_is_mock(self):
        wrapper = NaiveKronosWrapper()
        assert wrapper.is_mock is True


class TestNaiveChronosWrapper:
    def test_predict_shape(self):
        wrapper = NaiveChronosWrapper()
        context = np.random.randn(96)
        forecast = wrapper.predict(context, pred_len=24)
        assert forecast.shape == (24,)

    def test_is_mock(self):
        wrapper = NaiveChronosWrapper()
        assert wrapper.is_mock is True


class TestModelLoading:
    def test_kronos_loads_mock_without_package(self, monkeypatch):
        # Force the repo-clone step to fail so load_kronos_model exercises its
        # mock fallback (deterministic, no network). Real-load (is_mock=False)
        # is proven by the committed sweep results, not by this CPU unit test.
        import eval_kronos_zeroshot as ekz

        def _boom(_path):
            raise OSError("simulated: kronos repo unavailable (CI)")

        monkeypatch.setattr(ekz, "ensure_kronos_repo", _boom)
        model = ekz.load_kronos_model("small", device="cpu")
        assert model.is_mock is True

    def test_chronos_loads_mock_without_package(self):
        model = load_chronos_model("base", device="cpu")
        assert model.is_mock is True

    def test_kronos_model_ids(self):
        from eval_kronos_zeroshot import KRONOS_MODEL_IDS

        # Kronos-large (~499M) is NOT open-source -> intentionally absent.
        assert "mini" in KRONOS_MODEL_IDS
        assert "small" in KRONOS_MODEL_IDS
        assert "base" in KRONOS_MODEL_IDS
        assert "large" not in KRONOS_MODEL_IDS
        assert "xl" not in KRONOS_MODEL_IDS

    def test_chronos_model_ids(self):
        from eval_chronos_bolt import CHRONOS_MODEL_IDS

        assert "small" in CHRONOS_MODEL_IDS
        assert "base" in CHRONOS_MODEL_IDS
        assert "large" in CHRONOS_MODEL_IDS


class TestEvaluateWindow:
    def test_evaluate_with_mock(self):
        model = NaiveKronosWrapper()
        dates = pd.date_range("2020-01-01", periods=120, freq="B")
        rng = np.random.default_rng(0)
        close = np.cumsum(rng.standard_normal(120) * 0.5 + 100)
        ctx = pd.DataFrame(
            {"open": close, "high": close, "low": close, "close": close, "volume": 0.0},
            index=dates,
        ).iloc[:96]
        window = {
            "context_ohlcv": ctx,
            "x_timestamp": pd.Series(ctx.index),
            "y_timestamp": pd.Series(dates[96:120]),
            "actual_close": close[96:120],
            "actual_returns": np.diff(close[96:120]),
        }
        result = evaluate_window(model, window, pred_len=24)
        assert "direction_accuracy" in result
        assert "mse" in result
        assert "sharpe" in result
        assert 0.0 <= result["direction_accuracy"] <= 1.0
