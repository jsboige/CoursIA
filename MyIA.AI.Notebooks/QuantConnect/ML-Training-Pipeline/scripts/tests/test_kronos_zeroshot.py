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
    def test_window_count(self):
        dates = pd.date_range("2020-01-01", periods=500, freq="B")
        prices = pd.Series(np.cumsum(np.random.randn(500) * 0.01 + 100), index=dates)
        windows = build_evaluation_windows(prices, seq_len=96, pred_len=24, n_windows=5)
        assert len(windows) > 0
        assert len(windows) <= 5

    def test_window_shapes(self):
        dates = pd.date_range("2020-01-01", periods=500, freq="B")
        prices = pd.Series(np.cumsum(np.random.randn(500) * 0.01 + 100), index=dates)
        windows = build_evaluation_windows(prices, seq_len=96, pred_len=24, n_windows=3)
        for w in windows:
            assert w["context"].shape == (96,)
            assert w["actual_prices"].shape == (24,)
            assert w["actual_returns"].shape == (24,)

    def test_temporal_ordering(self):
        dates = pd.date_range("2020-01-01", periods=500, freq="B")
        prices = pd.Series(np.arange(500, dtype=float), index=dates)
        windows = build_evaluation_windows(prices, seq_len=10, pred_len=5, n_windows=3)
        for i in range(1, len(windows)):
            assert windows[i]["start_date"] >= windows[i - 1]["start_date"]


class TestNaiveKronosWrapper:
    def test_predict_shape(self):
        wrapper = NaiveKronosWrapper()
        context = np.random.randn(96)
        forecast = wrapper.predict(context, pred_len=24)
        assert forecast.shape == (24,)

    def test_predict_persistence(self):
        wrapper = NaiveKronosWrapper()
        context = np.arange(96, dtype=float)
        forecast = wrapper.predict(context, pred_len=10)
        assert np.all(forecast == context[-1])

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
    def test_kronos_loads_mock_without_package(self):
        model = load_kronos_model("small", device="cpu")
        assert model.is_mock is True

    def test_chronos_loads_mock_without_package(self):
        model = load_chronos_model("base", device="cpu")
        assert model.is_mock is True

    def test_kronos_model_ids(self):
        from eval_kronos_zeroshot import KRONOS_MODEL_IDS

        assert "small" in KRONOS_MODEL_IDS
        assert "base" in KRONOS_MODEL_IDS
        assert "large" in KRONOS_MODEL_IDS
        assert "xl" in KRONOS_MODEL_IDS

    def test_chronos_model_ids(self):
        from eval_chronos_bolt import CHRONOS_MODEL_IDS

        assert "small" in CHRONOS_MODEL_IDS
        assert "base" in CHRONOS_MODEL_IDS
        assert "large" in CHRONOS_MODEL_IDS


class TestEvaluateWindow:
    def test_evaluate_with_mock(self):
        model = NaiveKronosWrapper()
        window = {
            "context": np.random.randn(96),
            "actual_prices": np.random.randn(24) + 100,
            "actual_returns": np.random.randn(24) * 0.01,
        }
        result = evaluate_window(model, window, pred_len=24)
        assert "direction_accuracy" in result
        assert "mse" in result
        assert "sharpe" in result
        assert 0.0 <= result["direction_accuracy"] <= 1.0
