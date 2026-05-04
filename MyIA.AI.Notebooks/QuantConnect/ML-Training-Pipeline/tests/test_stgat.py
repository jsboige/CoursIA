"""Tests for train_stgat.py — CPU-only smoke tests."""

import sys
from pathlib import Path

import numpy as np
import pytest
import torch

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))

from train_stgat import (
    GraphAttentionLayer,
    MultiHeadGAT,
    TemporalAttention,
    STGATBlock,
    STGATModel,
    build_sequences,
    normalize_sequences,
    compute_majority_class_baseline,
)


class TestGraphAttentionLayer:
    def test_output_shape(self):
        gat = GraphAttentionLayer(in_features=16, out_features=16)
        h = torch.randn(2, 4, 16)
        out = gat(h)
        assert out.shape == (2, 4, 16)

    def test_with_adjacency_mask(self):
        gat = GraphAttentionLayer(in_features=16, out_features=16)
        h = torch.randn(2, 4, 16)
        adj = torch.tensor([
            [0, 1, 0, 0],
            [1, 0, 1, 0],
            [0, 1, 0, 1],
            [0, 0, 1, 0],
        ], dtype=torch.float32)
        out = gat(h, adj)
        assert out.shape == (2, 4, 16)

    def test_gradient_flow(self):
        gat = GraphAttentionLayer(in_features=16, out_features=16)
        h = torch.randn(2, 4, 16)
        out = gat(h)
        out.sum().backward()
        assert gat.W.grad is not None
        assert gat.a.grad is not None

    def test_no_nan(self):
        gat = GraphAttentionLayer(in_features=16, out_features=16)
        h = torch.randn(2, 4, 16)
        out = gat(h)
        assert not torch.isnan(out).any()


class TestMultiHeadGAT:
    def test_output_shape(self):
        gat = MultiHeadGAT(in_features=16, out_features=16, n_heads=4)
        h = torch.randn(2, 4, 16)
        out = gat(h)
        assert out.shape == (2, 4, 16)

    def test_gradient_flow(self):
        gat = MultiHeadGAT(in_features=16, out_features=16, n_heads=4)
        h = torch.randn(2, 4, 16)
        out = gat(h)
        out.sum().backward()
        for p in gat.parameters():
            assert p.grad is not None


class TestTemporalAttention:
    def test_output_shape(self):
        ta = TemporalAttention(d_model=16, n_heads=4)
        x = torch.randn(2, 8, 16)
        out = ta(x)
        assert out.shape == (2, 8, 16)

    def test_causal_mask(self):
        ta = TemporalAttention(d_model=16, n_heads=4)
        x = torch.randn(1, 8, 16)
        out = ta(x)
        assert not torch.isnan(out).any()

    def test_gradient_flow(self):
        ta = TemporalAttention(d_model=16, n_heads=4)
        x = torch.randn(2, 8, 16)
        out = ta(x)
        out.sum().backward()
        for p in ta.parameters():
            assert p.grad is not None


class TestSTGATBlock:
    def test_output_shape(self):
        block = STGATBlock(d_model=16, n_heads_spatial=2, n_heads_temporal=2, n_nodes=4)
        x = torch.randn(2, 8, 4, 16)
        out = block(x)
        assert out.shape == (2, 8, 4, 16)

    def test_with_adjacency(self):
        block = STGATBlock(d_model=16, n_heads_spatial=2, n_heads_temporal=2, n_nodes=4)
        x = torch.randn(2, 8, 4, 16)
        adj = torch.softmax(torch.randn(4, 4), dim=-1)
        out = block(x, adj)
        assert out.shape == (2, 8, 4, 16)

    def test_gradient_flow(self):
        block = STGATBlock(d_model=16, n_heads_spatial=2, n_heads_temporal=2, n_nodes=4)
        x = torch.randn(2, 8, 4, 16)
        out = block(x)
        out.sum().backward()
        for p in block.parameters():
            assert p.grad is not None


class TestSTGATModel:
    def test_forward_shape(self):
        model = STGATModel(n_vars=4, seq_len=16, pred_len=4, d_model=16, n_blocks=1)
        x = torch.randn(2, 16, 4)
        out = model(x)
        assert out.shape == (2, 4)

    def test_parameters_registered(self):
        model = STGATModel(n_vars=4, seq_len=16, pred_len=4, d_model=16, n_blocks=1)
        params = list(model.parameters())
        assert len(params) > 0
        for p in params:
            assert p.requires_grad

    def test_state_dict_roundtrip(self):
        model = STGATModel(n_vars=4, seq_len=16, pred_len=4, d_model=16, n_blocks=1)
        sd = model.state_dict()
        model2 = STGATModel(n_vars=4, seq_len=16, pred_len=4, d_model=16, n_blocks=1)
        model2.load_state_dict(sd)

    def test_gradient_flow(self):
        model = STGATModel(n_vars=4, seq_len=16, pred_len=4, d_model=16, n_blocks=1)
        x = torch.randn(2, 16, 4)
        y = torch.randn(2, 4)
        pred = model(x)
        loss = pred.sum()
        loss.backward()
        grad_count = sum(1 for p in model.parameters() if p.grad is not None)
        assert grad_count > 0

    def test_with_adjacency(self):
        adj = torch.softmax(torch.randn(4, 4), dim=-1)
        model = STGATModel(n_vars=4, seq_len=16, pred_len=4, d_model=16, n_blocks=1)
        x = torch.randn(2, 16, 4)
        out = model(x, adj=adj)
        assert out.shape == (2, 4)

    def test_single_variable(self):
        model = STGATModel(n_vars=1, seq_len=16, pred_len=4, d_model=16, n_blocks=1)
        x = torch.randn(2, 16, 1)
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
        assert X.shape[2] == 3
        assert y.shape[1] == 5
        assert len(cols) == 3

    def test_no_target_leakage(self):
        features = self._make_features()
        _, _, cols = build_sequences(features, seq_len=10, pred_len=5)
        assert "target" not in cols


class TestNormalizeSequences:
    def test_train_stats_only(self):
        np.random.seed(42)
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


class TestMajorityBaseline:
    def test_balanced(self):
        y = np.array([[1, -1, 1, -1]] * 10, dtype=np.float32)
        baseline = compute_majority_class_baseline(y)
        assert baseline["majority_class_accuracy"] == 0.5

    def test_biased_up(self):
        y = np.ones((10, 4), dtype=np.float32)
        baseline = compute_majority_class_baseline(y)
        assert baseline["majority_class_accuracy"] == 1.0
        assert baseline["pct_up"] == 1.0
