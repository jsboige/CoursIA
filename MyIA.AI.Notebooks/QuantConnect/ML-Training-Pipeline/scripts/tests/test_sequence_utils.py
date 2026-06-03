"""Tests for sequence_utils.py -- shared build_sequences and normalize_sequences."""

import sys
from pathlib import Path

import numpy as np
import pandas as pd
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))

from sequence_utils import build_sequences, normalize_sequences


@pytest.fixture
def feature_df():
    """Feature DataFrame with enough rows for sequence building."""
    np.random.seed(42)
    n = 200
    return pd.DataFrame(
        {
            "feat_a": np.random.randn(n).cumsum(),
            "feat_b": np.random.randn(n).cumsum(),
            "feat_c": np.random.randn(n),
            "target": np.random.randn(n),
        }
    )


class TestBuildSequences:
    def test_seq2one_default(self, feature_df):
        X, y, cols = build_sequences(feature_df)
        assert X.shape[0] == len(feature_df) - 20
        assert X.shape[1] == 20  # seq_len
        assert X.shape[2] == 3  # 3 features (excl target)
        assert y.ndim == 1  # scalar targets
        assert len(y) == X.shape[0]
        assert "target" not in cols

    def test_seq2one_custom_seq_len(self, feature_df):
        X, y, cols = build_sequences(feature_df, seq_len=10)
        assert X.shape[1] == 10
        assert X.shape[0] == len(feature_df) - 10

    def test_seq2seq_multistep(self, feature_df):
        X, y, cols = build_sequences(feature_df, seq_len=20, pred_len=5)
        assert X.shape[1] == 20
        assert y.shape[1] == 5  # multi-step targets
        assert X.shape[0] == len(feature_df) - 20 - 5 + 1

    def test_seq2seq_pred_len_1_produces_scalar(self, feature_df):
        """pred_len=1 should produce scalar targets (backward compat)."""
        X, y, cols = build_sequences(feature_df, seq_len=20, pred_len=1)
        assert y.ndim == 1

    def test_feature_cols_excludes_target(self, feature_df):
        _, _, cols = build_sequences(feature_df)
        assert "target" not in cols
        assert len(cols) == 3

    def test_dtype_float32(self, feature_df):
        X, y, _ = build_sequences(feature_df)
        assert X.dtype == np.float32
        assert y.dtype == np.float32

    def test_custom_target_col(self, feature_df):
        df = feature_df.rename(columns={"target": "label"})
        X, y, cols = build_sequences(df, target_col="label")
        assert "label" not in cols
        assert X.shape[2] == 3


class TestNormalizeSequences:
    def test_basic_two_arrays(self):
        X_train = np.random.randn(50, 10, 5).astype(np.float32)
        X_test = np.random.randn(20, 10, 5).astype(np.float32)
        result = normalize_sequences(X_train, X_test)
        assert len(result) == 4
        X_train_n, X_test_n, mean, std = result
        assert X_train_n.shape == X_train.shape
        assert X_test_n.shape == X_test.shape
        assert mean.shape == (5,)
        assert std.shape == (5,)

    def test_with_validation(self):
        X_train = np.random.randn(50, 10, 5).astype(np.float32)
        X_test = np.random.randn(20, 10, 5).astype(np.float32)
        X_val = np.random.randn(10, 10, 5).astype(np.float32)
        result = normalize_sequences(X_train, X_test, X_val=X_val)
        assert len(result) == 5
        X_train_n, X_test_n, X_val_n, mean, std = result
        assert X_val_n.shape == X_val.shape

    def test_train_mean_near_zero(self):
        X_train = np.random.randn(500, 10, 3).astype(np.float32) * 5 + 10
        X_test = np.random.randn(100, 10, 3).astype(np.float32)
        X_train_n, X_test_n, mean, std = normalize_sequences(X_train, X_test)
        assert np.abs(X_train_n.mean(axis=(0, 1))).max() < 0.1

    def test_train_std_near_one(self):
        X_train = np.random.randn(500, 10, 3).astype(np.float32) * 5 + 10
        X_test = np.random.randn(100, 10, 3).astype(np.float32)
        X_train_n, _, _, _ = normalize_sequences(X_train, X_test)
        assert np.abs(X_train_n.std(axis=(0, 1)) - 1.0).max() < 0.1

    def test_no_leakage_from_test(self):
        """Normalization stats come only from training data."""
        rng = np.random.default_rng(42)
        X_train = rng.standard_normal((100, 10, 3)).astype(np.float32)
        X_test = rng.standard_normal((50, 10, 3)).astype(np.float32) * 100 + 50
        _, X_test_n, mean, std = normalize_sequences(X_train, X_test)
        mean_manual = X_train.mean(axis=(0, 1))
        std_manual = X_train.std(axis=(0, 1))
        np.testing.assert_allclose(mean, mean_manual, atol=1e-5)
        np.testing.assert_allclose(std, std_manual, atol=1e-5)

    def test_constant_features_no_division_by_zero(self):
        X_train = np.ones((50, 10, 3), dtype=np.float32)
        X_test = np.ones((20, 10, 3), dtype=np.float32) * 2
        X_train_n, X_test_n, _, std = normalize_sequences(X_train, X_test)
        assert np.all(std == 1.0)  # fallback for zero std
        assert not np.any(np.isnan(X_train_n))
        assert not np.any(np.isnan(X_test_n))
