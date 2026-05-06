"""Tests for eval_existing_checkpoints.py — evaluation harness."""

from __future__ import annotations

import json
import sys
from pathlib import Path
from unittest.mock import patch

import numpy as np
import pandas as pd
import pytest

# Ensure scripts/ is importable
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from eval_existing_checkpoints import (
    build_sequences,
    predict_direction,
    predict_sequences,
    run_dry_run,
    _wrap_model,
)
from data_utils import generate_synthetic_data
from features import FeatureEngineer


class TestBuildSequences:
    """Sequence building tests."""

    @pytest.fixture
    def feature_df(self):
        rng = np.random.default_rng(42)
        df = generate_synthetic_data(500)
        engineer = FeatureEngineer(lookback=10)
        features = engineer.transform(df)
        features = features.dropna()
        return features

    def test_shapes_correct(self, feature_df):
        seq_len = 10
        X, y, cols = build_sequences(feature_df, seq_len=seq_len)
        expected_n = len(feature_df) - seq_len
        assert X.shape == (expected_n, seq_len, len(cols))
        assert y.shape == (expected_n,)

    def test_target_aligned(self, feature_df):
        seq_len = 10
        X, y, cols = build_sequences(feature_df, seq_len=seq_len)
        target_col = "target"
        targets = feature_df[target_col].values
        for i in range(5):
            np.testing.assert_almost_equal(y[i], targets[seq_len + i])

    def test_feature_cols_exclude_target(self, feature_df):
        X, y, cols = build_sequences(feature_df, seq_len=10)
        assert "target" not in cols
        assert len(cols) > 0

    def test_dtype_float32(self, feature_df):
        X, y, _ = build_sequences(feature_df, seq_len=10)
        assert X.dtype == np.float32
        assert y.dtype == np.float32

    def test_short_df_few_sequences(self):
        df = generate_synthetic_data(300)
        engineer = FeatureEngineer(lookback=3)
        features = engineer.transform(df)
        features = features.dropna()
        assert len(features) > 10, f"Not enough rows after dropna: {len(features)}"
        X, y, _ = build_sequences(features, seq_len=3)
        assert len(X) > 0
        assert len(X) < 300

    def test_custom_target_col(self):
        rng = np.random.default_rng(42)
        df = generate_synthetic_data(200)
        engineer = FeatureEngineer(lookback=10)
        features = engineer.transform(df)
        features = features.dropna()
        features["custom_target"] = rng.choice([0, 1], size=len(features))
        X, y, cols = build_sequences(features, seq_len=10, target_col="custom_target")
        assert "custom_target" not in cols
        np.testing.assert_array_equal(
            y[:5], features["custom_target"].values[10:15]
        )


class DummySeqModel:
    """Predicts up with ~54% accuracy for testing."""

    def __init__(self, up_prob=0.54):
        self.rng = np.random.default_rng(42)
        self.up_prob = up_prob

    def predict(self, X):
        if X.ndim == 3:
            return self.rng.choice([0, 1], size=len(X), p=[1 - self.up_prob, self.up_prob])
        return self.rng.choice([0, 1], size=len(X), p=[1 - self.up_prob, self.up_prob])

    def __call__(self, X):
        raw = self.rng.normal(0.02, 0.1, size=len(X))
        import torch
        return torch.tensor(raw, dtype=torch.float32).unsqueeze(-1)


class TestPredictSequences:
    """Model prediction wrapper tests."""

    @pytest.fixture
    def sample_X(self):
        rng = np.random.default_rng(42)
        return rng.standard_normal((50, 10, 5)).astype(np.float32)

    def test_rf_predict(self, sample_X):
        model = DummySeqModel()
        preds = predict_sequences(model, sample_X, model_type="rf")
        assert preds.shape == (50,)

    def test_lstm_predict(self, sample_X):
        model = DummySeqModel()
        preds = predict_sequences(model, sample_X, model_type="lstm")
        assert preds.shape == (50,)

    def test_transformer_predict(self, sample_X):
        model = DummySeqModel()
        preds = predict_sequences(model, sample_X, model_type="transformer")
        assert preds.shape == (50,)


class TestPredictDirection:
    """Binary direction prediction tests."""

    @pytest.fixture
    def sample_X(self):
        rng = np.random.default_rng(42)
        return rng.standard_normal((30, 10, 5)).astype(np.float32)

    def test_rf_binary(self, sample_X):
        model = DummySeqModel()
        dirs = predict_direction(model, sample_X, model_type="rf")
        assert set(dirs).issubset({0, 1})
        assert dirs.dtype == int

    def test_lstm_binary(self, sample_X):
        model = DummySeqModel()
        dirs = predict_direction(model, sample_X, model_type="lstm")
        assert set(dirs).issubset({0, 1})

    def test_not_all_same(self, sample_X):
        model = DummySeqModel(up_prob=0.54)
        dirs = predict_direction(model, sample_X, model_type="lstm")
        assert len(set(dirs)) == 2


class TestWrapModel:
    """Model wrapper for eval_finstsb protocol."""

    @pytest.fixture
    def sample_X(self):
        rng = np.random.default_rng(42)
        return rng.standard_normal((20, 10, 5)).astype(np.float32)

    def test_rf_wrapper_has_predict(self, sample_X):
        model = DummySeqModel()
        wrapped = _wrap_model(model, "rf")
        assert hasattr(wrapped, "predict")
        preds = wrapped.predict(sample_X)
        assert len(preds) == 20

    def test_lstm_wrapper_has_predict(self, sample_X):
        model = DummySeqModel()
        wrapped = _wrap_model(model, "lstm")
        assert hasattr(wrapped, "predict")
        preds = wrapped.predict(sample_X)
        assert len(preds) == 20
        assert set(preds).issubset({0, 1})

    def test_wrapper_stores_type(self):
        model = DummySeqModel()
        wrapped = _wrap_model(model, "rf")
        assert wrapped.mtype == "rf"


class TestRunDryRun:
    """Dry-run integration test."""

    def test_returns_dict(self):
        result = run_dry_run()
        assert isinstance(result, dict)
        assert result["dry_run"] is True

    def test_has_expected_keys(self):
        result = run_dry_run()
        expected_keys = [
            "n_samples",
            "wf_oos_diracc",
            "wf_folds",
            "majority_class_acc",
            "vs_majority_class",
            "regime_avg_sharpe",
            "gross_sharpe",
            "net_sharpe",
            "cost_drag_bps",
        ]
        for k in expected_keys:
            assert k in result, f"Missing key: {k}"

    def test_oos_diracc_reasonable(self):
        result = run_dry_run()
        assert 0.3 < result["wf_oos_diracc"] < 0.7

    def test_wf_folds_positive(self):
        result = run_dry_run()
        assert result["wf_folds"] > 0

    def test_net_sharpe_lower(self):
        result = run_dry_run()
        assert result["net_sharpe"] <= result["gross_sharpe"]

    def test_cost_drag_positive(self):
        result = run_dry_run()
        assert result["cost_drag_bps"] >= 0

    def test_vs_majority_class_finite(self):
        result = run_dry_run()
        assert np.isfinite(result["vs_majority_class"])


class TestEvaluateCheckpointErrors:
    """Error handling for evaluate_checkpoint."""

    def test_missing_metadata_raises(self, tmp_path):
        from eval_existing_checkpoints import evaluate_checkpoint

        ckpt_dir = tmp_path / "fake_ckpt"
        ckpt_dir.mkdir()
        with pytest.raises(FileNotFoundError, match="metadata.json"):
            evaluate_checkpoint(ckpt_dir)

    def test_unknown_model_type_raises(self, tmp_path):
        from eval_existing_checkpoints import evaluate_checkpoint

        ckpt_dir = tmp_path / "unknown_ckpt"
        ckpt_dir.mkdir()
        metadata = {
            "model_type": "xgboost",
            "hyperparams": {},
            "metrics": {},
        }
        (ckpt_dir / "metadata.json").write_text(json.dumps(metadata))
        with pytest.raises(ValueError, match="Unknown model type"):
            evaluate_checkpoint(ckpt_dir)


class TestEvaluateAllCheckpoints:
    """Batch evaluation scanning tests."""

    def test_empty_dir(self, tmp_path):
        from eval_existing_checkpoints import evaluate_all_checkpoints

        results = evaluate_all_checkpoints(tmp_path)
        assert results == []

    def test_skips_non_checkpoint_dirs(self, tmp_path):
        from eval_existing_checkpoints import evaluate_all_checkpoints

        model_dir = tmp_path / "transformer"
        model_dir.mkdir()
        ckpt = model_dir / "20260101_000000"
        ckpt.mkdir()
        # No metadata.json → should be skipped
        results = evaluate_all_checkpoints(tmp_path)
        assert results == []

    def test_output_json(self, tmp_path):
        from eval_existing_checkpoints import evaluate_all_checkpoints

        output_path = tmp_path / "results.json"
        results = evaluate_all_checkpoints(tmp_path, output_path=output_path)
        assert output_path.exists()
        data = json.loads(output_path.read_text())
        assert isinstance(data, list)
