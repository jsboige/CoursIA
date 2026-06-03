"""Tests for train_lstm.py -- CPU-only smoke tests."""

import sys
from pathlib import Path

import numpy as np
import pytest
import torch

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))

from train_lstm import build_model, build_sequences, normalize_sequences


class TestBuildModel:
    def test_lstm_forward_shape(self):
        model = build_model(input_size=8, hidden_size=32, num_layers=1, dropout=0.0)
        x = torch.randn(2, 10, 8)
        out = model(x)
        assert out.shape == (2, 1)

    def test_gru_forward_shape(self):
        model = build_model(input_size=4, hidden_size=16, num_layers=1, dropout=0.0, model_type="gru")
        x = torch.randn(3, 5, 4)
        out = model(x)
        assert out.shape == (3, 1)

    def test_multilayer_dropout(self):
        model = build_model(input_size=8, hidden_size=32, num_layers=3, dropout=0.3)
        assert sum(1 for p in model.parameters() if p.requires_grad) > 0

    def test_gradient_flow(self):
        model = build_model(input_size=4, hidden_size=16, num_layers=2, dropout=0.0)
        x = torch.randn(2, 10, 4)
        out = model(x)
        loss = out.sum()
        loss.backward()
        for p in model.parameters():
            assert p.grad is not None

    def test_state_dict_roundtrip(self):
        model = build_model(input_size=4, hidden_size=16, num_layers=1, dropout=0.0)
        sd = model.state_dict()
        model2 = build_model(input_size=4, hidden_size=16, num_layers=1, dropout=0.0)
        model2.load_state_dict(sd)


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

    def test_seq_len_parameter(self):
        features = self._make_features(n=50, n_cols=2)
        X, y, _ = build_sequences(features, seq_len=5)
        assert X.shape[1] == 5
        assert X.shape[2] == 2
        assert len(X) == 50 - 5


class TestNormalizeSequences:
    def test_train_stats_only(self):
        np.random.seed(42)
        X_train = np.random.randn(50, 10, 3).astype(np.float32) * 5 + 3
        X_test = np.random.randn(20, 10, 3).astype(np.float32)
        X_tr, X_te, mean, std = normalize_sequences(X_train, X_test)
        assert abs(X_tr.mean()) < 0.1
        assert abs(X_tr.std() - 1.0) < 0.2

    def test_test_uses_train_stats(self):
        np.random.seed(0)
        X_train = np.random.randn(100, 10, 3).astype(np.float32)
        X_test = np.random.randn(20, 10, 3).astype(np.float32) * 100
        X_tr, X_te, mean, std = normalize_sequences(X_train, X_test)
        assert abs(X_te.mean()) > 1.0

    def test_output_shapes_preserved(self):
        X_train = np.random.randn(30, 5, 4).astype(np.float32)
        X_test = np.random.randn(10, 5, 4).astype(np.float32)
        X_tr, X_te, mean, std = normalize_sequences(X_train, X_test)
        assert X_tr.shape == X_train.shape
        assert X_te.shape == X_test.shape
        assert mean.shape == (4,)
        assert std.shape == (4,)
