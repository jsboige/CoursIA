"""Tests for eval_chronos_bolt.py — Chronos-Bolt zero-shot evaluation."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np
import pandas as pd
import pytest

from eval_chronos_bolt import (
    CHRONOS_MODEL_IDS,
    NaiveChronosWrapper,
    load_chronos_model,
    run_evaluation,
)


class TestChronosModelIds:
    """Chronos model configuration tests."""

    def test_three_sizes(self):
        assert set(CHRONOS_MODEL_IDS.keys()) == {"small", "base", "large"}

    def test_all_amazon_prefix(self):
        for model_id in CHRONOS_MODEL_IDS.values():
            assert model_id.startswith("amazon/chronos-bolt-")

    def test_base_is_default(self):
        assert "base" in CHRONOS_MODEL_IDS


class TestNaiveChronosWrapper:
    """Naive wrapper tests (used when chronos-forecasting not installed)."""

    def test_predict_shape(self):
        wrapper = NaiveChronosWrapper(model_id="test-model")
        context = np.array([100.0, 101.0, 102.0, 103.0, 104.0])
        pred = wrapper.predict(context, pred_len=10)
        assert pred.shape == (10,)

    def test_predict_last_value_persist(self):
        wrapper = NaiveChronosWrapper()
        context = np.array([50.0, 60.0, 70.0, 80.0, 90.0])
        pred = wrapper.predict(context, pred_len=5)
        np.testing.assert_array_equal(pred, np.full(5, 90.0))

    def test_predict_2d_context(self):
        wrapper = NaiveChronosWrapper()
        context = np.array([[1.0, 2.0], [3.0, 4.0], [5.0, 6.0]])
        pred = wrapper.predict(context, pred_len=3)
        assert pred.shape == (3,)
        assert pred[0] == 5.0

    def test_is_mock_true(self):
        wrapper = NaiveChronosWrapper()
        assert wrapper.is_mock is True

    def test_model_id_stored(self):
        wrapper = NaiveChronosWrapper(model_id="amazon/chronos-bolt-small")
        assert wrapper.model_id == "amazon/chronos-bolt-small"


class TestLoadChronosModel:
    """Model loading tests."""

    def test_fallback_to_naive(self):
        """Without chronos-forecasting installed, returns NaiveChronosWrapper."""
        model = load_chronos_model("base", device="cpu")
        assert isinstance(model, NaiveChronosWrapper)
        assert model.is_mock is True

    def test_invalid_size_defaults_to_base(self):
        """Unknown model size falls back to base."""
        model = load_chronos_model("nonexistent", device="cpu")
        assert "base" in model.model_id

    def test_small_size(self):
        model = load_chronos_model("small", device="cpu")
        assert "small" in model.model_id


class TestRunEvaluationDryRun:
    """Dry-run integration tests."""

    def _make_args(self, **overrides):
        defaults = {
            "dry_run": True,
            "data_dir": "",
            "symbol": "SPY",
            "model_size": "base",
            "seq_len": 50,
            "pred_len": 10,
            "n_windows": 3,
            "cost_bps": 10.0,
            "output_dir": None,
        }
        defaults.update(overrides)
        return argparse.Namespace(**defaults)

    def test_returns_summary_dict(self):
        args = self._make_args()
        result = run_evaluation(args)
        assert isinstance(result, dict)

    def test_summary_keys(self):
        args = self._make_args()
        result = run_evaluation(args)
        for key in [
            "model", "is_mock", "symbol", "seq_len", "pred_len",
            "n_windows", "avg_direction_accuracy", "avg_sharpe",
            "majority_baseline", "edge_vs_majority", "windows",
            "timestamp",
        ]:
            assert key in result, f"Missing key: {key}"

    def test_is_mock_in_dry_run(self):
        args = self._make_args()
        result = run_evaluation(args)
        assert result["is_mock"] is True

    def test_direction_accuracy_bounded(self):
        args = self._make_args()
        result = run_evaluation(args)
        assert 0.0 <= result["avg_direction_accuracy"] <= 1.0

    def test_windows_count(self):
        args = self._make_args(n_windows=3)
        result = run_evaluation(args)
        assert result["n_windows"] == 3
        assert len(result["windows"]) == 3

    def test_window_metrics_keys(self):
        args = self._make_args(seq_len=50, pred_len=10, n_windows=2)
        result = run_evaluation(args)
        window = result["windows"][0]
        for key in [
            "direction_accuracy", "mse", "sharpe", "net_sharpe",
            "n_trades", "transaction_cost_bps", "forecast_mean",
            "actual_mean", "window", "start", "end",
        ]:
            assert key in window, f"Missing window key: {key}"

    def test_majority_baseline_present(self):
        args = self._make_args()
        result = run_evaluation(args)
        bl = result["majority_baseline"]
        assert "majority_class_accuracy" in bl
        assert "pct_up" in bl
        assert "pct_down" in bl

    def test_output_dir_creates_file(self, tmp_path):
        args = self._make_args(output_dir=str(tmp_path / "results"))
        result = run_evaluation(args)
        out_files = list((tmp_path / "results").glob("chronos_zeroshot_*.json"))
        assert len(out_files) == 1
        data = json.loads(out_files[0].read_text())
        assert data["model"] == result["model"]

    def test_sharpe_is_finite(self):
        args = self._make_args(seq_len=50, pred_len=10, n_windows=3)
        result = run_evaluation(args)
        assert np.isfinite(result["avg_sharpe"])

    def test_edge_vs_majority(self):
        args = self._make_args()
        result = run_evaluation(args)
        expected = result["avg_direction_accuracy"] - result["majority_baseline"]["majority_class_accuracy"]
        assert abs(result["edge_vs_majority"] - expected) < 1e-6
