"""Tests for train_itransformer.py — CPU-only smoke tests."""

import sys
from pathlib import Path

import numpy as np
import pytest
import torch

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))

from train_itransformer import (
    iTransformerModel,
    build_sequences,
    compute_majority_class_baseline,
    normalize_sequences,
)


class TestiTransformerModel:
    def test_forward_shape(self):
        model = iTransformerModel(n_vars=4, seq_len=16, pred_len=4)
        x = torch.randn(2, 16, 4)
        out = model(x)
        assert out.shape == (2, 4)

    def test_parameters_registered(self):
        model = iTransformerModel(n_vars=4, seq_len=16, pred_len=4)
        params = list(model.parameters())
        assert len(params) > 0

    def test_state_dict_roundtrip(self):
        model = iTransformerModel(n_vars=4, seq_len=16, pred_len=4)
        sd = model.state_dict()
        assert len(sd) > 0
        model2 = iTransformerModel(n_vars=4, seq_len=16, pred_len=4)
        model2.load_state_dict(sd)

    def test_gradient_flow(self):
        model = iTransformerModel(n_vars=4, seq_len=16, pred_len=4)
        x = torch.randn(2, 16, 4)
        pred = model(x)
        loss = pred.sum()
        loss.backward()
        for p in model.parameters():
            assert p.grad is not None

    def test_single_variable(self):
        model = iTransformerModel(n_vars=1, seq_len=16, pred_len=4)
        x = torch.randn(2, 16, 1)
        out = model(x)
        assert out.shape == (2, 4)

    def test_many_variables(self):
        model = iTransformerModel(n_vars=32, seq_len=16, pred_len=4)
        x = torch.randn(2, 16, 32)
        out = model(x)
        assert out.shape == (2, 4)


class TestBuildSequences:
    def _make_features(self, n=100, n_cols=3):
        import pandas as pd
        cols = {f"f{i}": np.random.randn(n) for i in range(n_cols)}
        cols["target"] = np.random.randn(n)
        return pd.DataFrame(cols)

    def test_output_shapes(self):
        features = self._make_features()
        X, y, cols = build_sequences(features, seq_len=10, pred_len=5)
        assert X.shape[1] == 10
        assert y.shape[1] == 5
        assert len(cols) == 3

    def test_no_target_leakage(self):
        features = self._make_features()
        _, _, cols = build_sequences(features, seq_len=10, pred_len=5)
        assert "target" not in cols


class TestNormalizeSequences:
    def test_train_stats_only(self):
        X_train = np.random.randn(50, 10, 3).astype(np.float32) * 5 + 3
        X_test = np.random.randn(20, 10, 3).astype(np.float32)
        X_tr, X_te, mean, std = normalize_sequences(X_train, X_test)
        assert abs(X_tr.mean()) < 0.1
        assert abs(X_tr.std() - 1.0) < 0.2

    def test_with_val(self):
        X_train = np.random.randn(50, 10, 3).astype(np.float32)
        X_val = np.random.randn(10, 10, 3).astype(np.float32)
        X_test = np.random.randn(10, 10, 3).astype(np.float32)
        result = normalize_sequences(X_train, X_val, X_test)
        assert len(result) == 5
