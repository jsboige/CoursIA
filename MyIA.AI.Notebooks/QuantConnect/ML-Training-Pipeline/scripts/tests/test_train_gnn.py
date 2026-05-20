"""Tests for train_gnn module."""

import numpy as np
import pandas as pd
import pytest
import torch

from train_gnn import (
    GCNModel,
    GATModel,
    RGCNModel,
    create_model,
    prepare_gnn_data,
    train_and_evaluate,
    run_multi_seed,
    MODEL_REGISTRY,
)


@pytest.fixture
def synthetic_closes():
    """4-asset synthetic prices, 300 days."""
    np.random.seed(42)
    T, N = 300, 4
    symbols = ["BTC-USD", "ETH-USD", "LTC-USD", "XRP-USD"]
    returns = np.random.randn(T, N).astype(np.float32) * 0.02
    returns[:, 1] += 0.3 * returns[:, 0]  # BTC-ETH correlation
    closes = (1 + pd.DataFrame(returns, columns=symbols)).cumprod() * 100
    return closes


class TestModelRegistry:
    def test_all_models_registered(self):
        assert "gcn" in MODEL_REGISTRY
        assert "gat" in MODEL_REGISTRY
        assert "rgcn" in MODEL_REGISTRY

    def test_create_gcn(self):
        model = create_model("gcn", n_assets=4, n_features=3, d_model=32, n_layers=2)
        assert isinstance(model, GCNModel)

    def test_create_gat(self):
        model = create_model("gat", n_assets=4, n_features=3, d_model=32, n_layers=2, n_heads=4)
        assert isinstance(model, GATModel)

    def test_create_rgcn(self):
        model = create_model("rgcn", n_assets=4, n_features=3, d_model=32, n_layers=2, n_relations=3)
        assert isinstance(model, RGCNModel)

    def test_unknown_model_raises(self):
        with pytest.raises(ValueError, match="Unknown model"):
            create_model("transformer", n_assets=4, n_features=3)


class TestModelForward:
    def test_gcn_forward(self):
        model = GCNModel(n_assets=4, n_features=3, d_model=32, n_layers=2)
        x = torch.randn(8, 4, 3)
        adj = torch.eye(4) * 0.5
        adj[0, 1] = adj[1, 0] = 0.5
        out = model(x, adj)
        assert out.shape == (8, 1)

    def test_gat_forward(self):
        model = GATModel(n_assets=4, n_features=3, d_model=32, n_layers=2, n_heads=4)
        x = torch.randn(8, 4, 3)
        adj = torch.eye(4)
        out = model(x, adj)
        assert out.shape == (8, 1)

    def test_rgcn_forward(self):
        model = RGCNModel(n_assets=4, n_features=3, d_model=32, n_layers=2, n_relations=2)
        x = torch.randn(8, 4, 3)
        adj1 = torch.eye(4)
        adj2 = torch.eye(4)
        out = model(x, [adj1, adj2])
        assert out.shape == (8, 1)


class TestPrepareData:
    def test_output_shapes(self, synthetic_closes):
        X, y, adjs = prepare_gnn_data(
            synthetic_closes, seq_len=60, window=60,
            adj_method="correlation", adj_threshold=0.3,
        )
        assert X.ndim == 3  # (T, N, F)
        assert X.shape[1] == 4  # 4 assets
        assert X.shape[2] > 0  # features
        assert y.ndim == 1
        assert adjs.ndim == 3  # (T', N, N)
        assert adjs.shape[1] == adjs.shape[2] == 4


class TestTrainAndEvaluate:
    def test_dry_run_gcn(self, synthetic_closes):
        X, y, adjs = prepare_gnn_data(
            synthetic_closes, seq_len=60, window=60,
            adj_method="correlation", adj_threshold=0.1,
        )
        n = len(X)
        split = int(n * 0.8)
        result = train_and_evaluate(
            X[:split], y[:split], X[split:], y[split:],
            adjs[:split], adjs[split:],
            model_type="gcn", d_model=16, n_layers=1,
            epochs=2, batch_size=16, device="cpu",
        )
        assert "metrics" in result
        assert "direction_accuracy" in result["metrics"]
        assert "edge_over_majority" in result["metrics"]
        assert "model" in result

    def test_dry_run_gat(self, synthetic_closes):
        X, y, adjs = prepare_gnn_data(
            synthetic_closes, seq_len=60, window=60,
            adj_method="correlation", adj_threshold=0.1,
        )
        n = len(X)
        split = int(n * 0.8)
        result = train_and_evaluate(
            X[:split], y[:split], X[split:], y[split:],
            adjs[:split], adjs[split:],
            model_type="gat", d_model=16, n_layers=1, n_heads=2,
            epochs=2, batch_size=16, device="cpu",
        )
        assert result["metrics"]["direction_accuracy"] > 0

    def test_dry_run_rgcn(self, synthetic_closes):
        X, y, adjs = prepare_gnn_data(
            synthetic_closes, seq_len=60, window=60,
            adj_method="correlation", adj_threshold=0.1,
        )
        n = len(X)
        split = int(n * 0.8)
        result = train_and_evaluate(
            X[:split], y[:split], X[split:], y[split:],
            adjs[:split], adjs[split:],
            model_type="rgcn", d_model=16, n_layers=1, n_relations=2,
            epochs=2, batch_size=16, device="cpu",
        )
        assert result["metrics"]["direction_accuracy"] > 0


class TestMultiSeed:
    def test_multi_seed_minimum(self, synthetic_closes):
        X, y, adjs = prepare_gnn_data(
            synthetic_closes, seq_len=60, window=60,
            adj_method="correlation", adj_threshold=0.1,
        )
        summary = run_multi_seed(
            X, y, adjs,
            seeds=[42, 123, 456, 789],
            model_type="gcn", d_model=16, n_layers=1,
            epochs=2, batch_size=16, device="cpu",
        )
        assert summary["n_seeds"] == 4
        assert "mean_direction_accuracy" in summary
        assert "mean_edge" in summary
        assert "beats_claim" in summary
        assert len(summary["per_seed"]) == 4

    def test_multi_seed_requires_4(self, synthetic_closes):
        X, y, adjs = prepare_gnn_data(
            synthetic_closes, seq_len=60, window=60,
            adj_method="correlation", adj_threshold=0.1,
        )
        with pytest.raises(AssertionError, match=">=4"):
            run_multi_seed(
                X, y, adjs,
                seeds=[42, 123],
                model_type="gcn", d_model=16, n_layers=1,
                epochs=2, batch_size=16, device="cpu",
            )
