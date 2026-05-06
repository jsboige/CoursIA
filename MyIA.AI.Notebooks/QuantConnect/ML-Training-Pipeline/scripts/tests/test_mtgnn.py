"""Tests for train_mtgnn.py — CPU-only smoke tests."""

import sys
from pathlib import Path

import numpy as np
import pytest
import torch

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))

from train_mtgnn import (
    GraphConstructor,
    MixHopPropagation,
    DilatedCausalConv,
    TCNBlock,
    MTGNNModel,
    build_sequences,
    build_sector_adjacency,
    build_pearson_adjacency,
    normalize_sequences,
)
from baselines import oos_direction_distribution


class TestGraphConstructor:
    def test_output_shape(self):
        gc = GraphConstructor(n_nodes=4, embed_dim=8)
        adj = gc()
        assert adj.shape == (4, 4)

    def test_softmax_rows(self):
        gc = GraphConstructor(n_nodes=4, embed_dim=8)
        adj = gc()
        row_sums = adj.sum(dim=-1)
        assert torch.allclose(row_sums, torch.ones(4), atol=1e-5)

    def test_gradient_flow(self):
        gc = GraphConstructor(n_nodes=4, embed_dim=8)
        adj = gc()
        loss = adj.sum()
        loss.backward()
        assert gc.node_emb1.grad is not None
        assert gc.node_emb2.grad is not None

    def test_no_nan(self):
        gc = GraphConstructor(n_nodes=4, embed_dim=8)
        adj = gc()
        assert not torch.isnan(adj).any()


class TestMixHopPropagation:
    def test_forward_shape(self):
        mhp = MixHopPropagation(c_in=16, c_out=16, n_nodes=4, depth=2)
        x = torch.randn(2, 4, 16)
        adj = torch.softmax(torch.randn(4, 4), dim=-1)
        out = mhp(x, adj)
        assert out.shape == (2, 4, 16)

    def test_gradient_flow(self):
        mhp = MixHopPropagation(c_in=16, c_out=16, n_nodes=4, depth=2)
        x = torch.randn(2, 4, 16)
        adj = torch.softmax(torch.randn(4, 4), dim=-1)
        out = mhp(x, adj)
        out.sum().backward()
        for p in mhp.parameters():
            assert p.grad is not None


class TestDilatedCausalConv:
    def test_output_length_matches_input(self):
        conv = DilatedCausalConv(c_in=8, c_out=8, kernel_size=2, dilation=1)
        x = torch.randn(2, 8, 16)
        out = conv(x)
        assert out.shape == (2, 8, 16)

    def test_dilation_doubles(self):
        conv = DilatedCausalConv(c_in=8, c_out=8, kernel_size=2, dilation=4)
        x = torch.randn(2, 8, 16)
        out = conv(x)
        assert out.shape == (2, 8, 16)


class TestTCNBlock:
    def test_residual_shape(self):
        block = TCNBlock(channels=16, kernel_size=2, dilation=1)
        x = torch.randn(2, 8, 16)
        out = block(x)
        assert out.shape == (2, 8, 16)

    def test_gradient_flow(self):
        block = TCNBlock(channels=16, kernel_size=2, dilation=1)
        x = torch.randn(2, 8, 16)
        out = block(x)
        out.sum().backward()
        for p in block.parameters():
            assert p.grad is not None


class TestMTGNNModel:
    def test_forward_shape(self):
        model = MTGNNModel(n_vars=4, seq_len=16, pred_len=4, d_model=16, tcn_layers=2)
        x = torch.randn(2, 16, 4)
        out = model(x)
        assert out.shape == (2, 4)

    def test_parameters_registered(self):
        model = MTGNNModel(n_vars=4, seq_len=16, pred_len=4, d_model=16, tcn_layers=2)
        params = list(model.parameters())
        assert len(params) > 0
        for p in params:
            assert p.requires_grad

    def test_state_dict_roundtrip(self):
        model = MTGNNModel(n_vars=4, seq_len=16, pred_len=4, d_model=16, tcn_layers=2)
        sd = model.state_dict()
        model2 = MTGNNModel(n_vars=4, seq_len=16, pred_len=4, d_model=16, tcn_layers=2)
        model2.load_state_dict(sd)

    def test_gradient_flow(self):
        model = MTGNNModel(n_vars=4, seq_len=16, pred_len=4, d_model=16, tcn_layers=2)
        x = torch.randn(2, 16, 4)
        y = torch.randn(2, 4)
        pred = model(x)
        loss = pred.sum()
        loss.backward()
        grad_count = sum(1 for p in model.parameters() if p.grad is not None)
        assert grad_count > 0

    def test_with_static_adj(self):
        adj = torch.tensor([
            [0.0, 1.0, 0.0, 0.0],
            [1.0, 0.0, 0.0, 0.0],
            [0.0, 0.0, 0.0, 1.0],
            [0.0, 0.0, 1.0, 0.0],
        ])
        model = MTGNNModel(n_vars=4, seq_len=16, pred_len=4, d_model=16, tcn_layers=2, static_adj=adj)
        x = torch.randn(2, 16, 4)
        out = model(x)
        assert out.shape == (2, 4)

    def test_with_dynamic_adj(self):
        model = MTGNNModel(n_vars=4, seq_len=16, pred_len=4, d_model=16, tcn_layers=2)
        x = torch.randn(2, 16, 4)
        dyn_adj = torch.softmax(torch.randn(4, 4), dim=-1)
        out = model(x, dynamic_adj=dyn_adj)
        assert out.shape == (2, 4)


class TestAdjacencyBuilders:
    def test_sector_adjacency_shape(self):
        symbols = ["SPY", "RSP", "AGG", "GLD"]
        adj = build_sector_adjacency(symbols)
        assert adj.shape == (4, 4)

    def test_sector_adjacency_groups(self):
        symbols = ["SPY", "RSP", "AGG", "GLD"]
        adj = build_sector_adjacency(symbols)
        assert adj[0, 1] == 1.0  # SPY-RSP: same equity_us sector
        assert adj[2, 3] == 0.0  # AGG-GLD: different sectors
        assert adj[0, 0] == 0.0  # diagonal zeroed

    def test_pearson_adjacency_shape(self):
        np.random.seed(42)
        returns = np.random.randn(100, 4).astype(np.float32)
        adj = build_pearson_adjacency(returns, window=60)
        assert adj.shape == (4, 4)
        assert adj[0, 0] == 0.0  # diagonal zeroed

    def test_pearson_adjacency_symmetric(self):
        np.random.seed(42)
        returns = np.random.randn(100, 4).astype(np.float32)
        adj = build_pearson_adjacency(returns, window=60)
        np.testing.assert_array_almost_equal(adj, adj.T)


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
        X_tr, X_te, mean, std = normalize_sequences(X_train, X_test=X_test)
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
        baseline = oos_direction_distribution(y)
        assert baseline["majority_class_accuracy"] == 0.5

    def test_biased_up(self):
        y = np.ones((10, 4), dtype=np.float32)
        baseline = oos_direction_distribution(y)
        assert baseline["majority_class_accuracy"] == 1.0
        assert baseline["pct_up"] == 1.0
