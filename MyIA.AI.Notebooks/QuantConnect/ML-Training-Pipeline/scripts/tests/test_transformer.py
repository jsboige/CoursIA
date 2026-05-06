"""Tests for train_transformer.py -- CPU-only smoke tests."""

import sys
from pathlib import Path

import numpy as np
import pytest
import torch

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))

from train_transformer import (
    PositionalEncoding,
    build_sequences,
    build_transformer_model,
    normalize_sequences,
)


class TestPositionalEncoding:
    def test_shape(self):
        pe = PositionalEncoding.encode(seq_len=20, d_model=64)
        assert pe.shape == (20, 64)

    def test_dtype(self):
        pe = PositionalEncoding.encode(seq_len=10, d_model=32)
        assert pe.dtype == np.float32

    def test_deterministic(self):
        pe1 = PositionalEncoding.encode(seq_len=16, d_model=32)
        pe2 = PositionalEncoding.encode(seq_len=16, d_model=32)
        np.testing.assert_array_equal(pe1, pe2)


class TestBuildTransformerModel:
    def test_forward_shape(self):
        model = build_transformer_model(
            input_size=4, d_model=32, nhead=4, num_layers=2,
            dim_feedforward=64, dropout=0.1, seq_len=16,
        )
        x = torch.randn(2, 16, 4)
        out = model(x)
        assert out.shape == (2, 1)

    def test_gradient_flow(self):
        model = build_transformer_model(
            input_size=4, d_model=32, nhead=4, num_layers=2,
            dim_feedforward=64, dropout=0.0, seq_len=10,
        )
        x = torch.randn(2, 10, 4)
        out = model(x)
        loss = out.sum()
        loss.backward()
        for p in model.parameters():
            assert p.grad is not None

    def test_state_dict_roundtrip(self):
        model = build_transformer_model(
            input_size=4, d_model=32, nhead=4, num_layers=2,
            dim_feedforward=64, dropout=0.1, seq_len=10,
        )
        sd = model.state_dict()
        model2 = build_transformer_model(
            input_size=4, d_model=32, nhead=4, num_layers=2,
            dim_feedforward=64, dropout=0.1, seq_len=10,
        )
        model2.load_state_dict(sd)

    def test_pos_encoding_registered(self):
        model = build_transformer_model(
            input_size=4, d_model=32, nhead=4, num_layers=1,
            dim_feedforward=64, dropout=0.1, seq_len=10,
        )
        assert "pos_encoding" in dict(model.named_buffers())

    def test_single_variable(self):
        model = build_transformer_model(
            input_size=1, d_model=16, nhead=2, num_layers=1,
            dim_feedforward=32, dropout=0.0, seq_len=8,
        )
        x = torch.randn(2, 8, 1)
        out = model(x)
        assert out.shape == (2, 1)


class TestBuildSequences:
    def _make_features(self, n=100, n_cols=3):
        import pandas as pd

        cols = {f"f{i}": np.random.randn(n) for i in range(n_cols)}
        cols["target"] = np.random.randn(n)
        return pd.DataFrame(cols)

    def test_output_shapes(self):
        features = self._make_features()
        X, y, cols = build_sequences(features, seq_len=10)
        assert X.shape[1] == 10
        assert X.shape[2] == 3
        assert y.shape[0] == X.shape[0]
        assert len(cols) == 3

    def test_no_target_in_features(self):
        features = self._make_features()
        _, _, cols = build_sequences(features, seq_len=10)
        assert "target" not in cols


class TestNormalizeSequences:
    def test_train_stats_only(self):
        np.random.seed(42)
        X_train = np.random.randn(50, 10, 3).astype(np.float32) * 5 + 3
        X_test = np.random.randn(20, 10, 3).astype(np.float32)
        X_tr, X_te, mean, std = normalize_sequences(X_train, X_test)
        assert abs(X_tr.mean()) < 0.1
        assert abs(X_tr.std() - 1.0) < 0.2

    def test_no_leakage(self):
        np.random.seed(0)
        X_train = np.random.randn(100, 10, 3).astype(np.float32)
        X_test = np.random.randn(20, 10, 3).astype(np.float32) * 100
        X_tr, X_te, mean, std = normalize_sequences(X_train, X_test)
        assert abs(X_te.mean()) > 1.0
