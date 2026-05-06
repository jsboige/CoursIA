"""Tests verifying the test-set contamination fix (val_ratio internal split).

Ensures that PatchTST, iTransformer, and Mamba train_and_evaluate() use an
internal validation split for early stopping and keep test_loader exclusively
for final OOS metrics.
"""

from __future__ import annotations

import sys
from pathlib import Path

import numpy as np
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent))

from data_utils import generate_synthetic_data
from features import FeatureEngineer


def _make_sequences(n_rows: int = 300, seq_len: int = 24, pred_len: int = 6) -> tuple:
    """Generate synthetic sequence arrays for forecasting models."""
    raw = generate_synthetic_data(n_rows)
    engineer = FeatureEngineer(lookback=seq_len)
    features = engineer.transform(raw)
    features = features.dropna()

    feature_cols = [c for c in features.columns if c != "target"]
    data = features[feature_cols].values
    targets = features["target"].values

    X, y = [], []
    for i in range(seq_len, len(data) - pred_len + 1):
        X.append(data[i - seq_len : i])
        y.append(targets[i : i + pred_len])

    return np.array(X, dtype=np.float32), np.array(y, dtype=np.float32), len(feature_cols)


# ---------------------------------------------------------------------------
# PatchTST
# ---------------------------------------------------------------------------


class TestPatchTSTContaminationFix:
    def test_train_and_evaluate_returns_metrics(self):
        from train_patchtst import train_and_evaluate

        X, y, n_vars = _make_sequences(300, seq_len=24, pred_len=6)
        n = len(X)
        split = int(n * 0.7)
        result = train_and_evaluate(
            X[:split], y[:split], X[split:], y[split:],
            n_vars=n_vars, seq_len=24, pred_len=6,
            patch_len=8, stride=4,
            d_model=32, n_heads=2, n_layers=1,
            epochs=1, batch_size=16, device="cpu",
        )

        assert "metrics" in result
        assert "history" in result
        assert "val_loss" in result["history"]
        assert "train_loss" in result["history"]
        assert result["model"] is not None

    def test_val_ratio_creates_internal_split(self):
        """Verify that val_ratio splits training data internally."""
        from train_patchtst import train_and_evaluate

        X, y, n_vars = _make_sequences(300, seq_len=24, pred_len=6)
        n = len(X)
        split = int(n * 0.7)
        n_train = split
        result = train_and_evaluate(
            X[:split], y[:split], X[split:], y[split:],
            n_vars=n_vars, seq_len=24, pred_len=6,
            patch_len=8, stride=4,
            d_model=32, n_heads=2, n_layers=1,
            epochs=1, batch_size=16, device="cpu",
            val_ratio=0.2,
        )

        # train_samples should be 80% of original train (val_ratio=0.2)
        expected_tr = int(n_train * 0.8)
        assert result["metrics"]["train_samples"] == expected_tr


# ---------------------------------------------------------------------------
# iTransformer
# ---------------------------------------------------------------------------


class TestiTransformerContaminationFix:
    def test_train_and_evaluate_returns_metrics(self):
        from train_itransformer import train_and_evaluate

        X, y, n_vars = _make_sequences(300, seq_len=24, pred_len=6)
        n = len(X)
        split = int(n * 0.7)
        result = train_and_evaluate(
            X[:split], y[:split], X[split:], y[split:],
            n_vars=n_vars, seq_len=24, pred_len=6,
            d_model=32, n_heads=2, n_layers=1,
            epochs=1, batch_size=16, device="cpu",
        )

        assert "metrics" in result
        assert "history" in result
        assert result["model"] is not None

    def test_val_ratio_creates_internal_split(self):
        from train_itransformer import train_and_evaluate

        X, y, n_vars = _make_sequences(300, seq_len=24, pred_len=6)
        n = len(X)
        split = int(n * 0.7)
        n_train = split
        result = train_and_evaluate(
            X[:split], y[:split], X[split:], y[split:],
            n_vars=n_vars, seq_len=24, pred_len=6,
            d_model=32, n_heads=2, n_layers=1,
            epochs=1, batch_size=16, device="cpu",
            val_ratio=0.2,
        )

        expected_tr = int(n_train * 0.8)
        assert result["metrics"]["train_samples"] == expected_tr


# ---------------------------------------------------------------------------
# Mamba
# ---------------------------------------------------------------------------


class TestMambaContaminationFix:
    def test_train_and_evaluate_returns_metrics(self):
        from train_mamba import train_and_evaluate

        X, y, n_vars = _make_sequences(300, seq_len=24, pred_len=6)
        n = len(X)
        split = int(n * 0.7)
        result = train_and_evaluate(
            X[:split], y[:split], X[split:], y[split:],
            n_vars=n_vars, seq_len=24, pred_len=6,
            d_model=32, d_state=8, d_conv=2, expand_factor=2,
            n_layers=1, epochs=1, batch_size=16, device="cpu",
        )

        assert "metrics" in result
        assert "history" in result
        assert result["model"] is not None

    def test_val_ratio_creates_internal_split(self):
        from train_mamba import train_and_evaluate

        X, y, n_vars = _make_sequences(300, seq_len=24, pred_len=6)
        n = len(X)
        split = int(n * 0.7)
        n_train = split
        result = train_and_evaluate(
            X[:split], y[:split], X[split:], y[split:],
            n_vars=n_vars, seq_len=24, pred_len=6,
            d_model=32, d_state=8, d_conv=2, expand_factor=2,
            n_layers=1, epochs=1, batch_size=16, device="cpu",
            val_ratio=0.2,
        )

        expected_tr = int(n_train * 0.8)
        assert result["metrics"]["train_samples"] == expected_tr
