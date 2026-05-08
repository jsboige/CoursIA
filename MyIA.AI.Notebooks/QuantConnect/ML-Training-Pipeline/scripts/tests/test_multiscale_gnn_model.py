"""Tests for multiscale_gnn_model.py — MultiScaleGNN forward pass + sanity."""

from __future__ import annotations

import numpy as np
import pytest
import torch

from multiscale_gnn_model import MultiScaleGNN, MultiScaleGNNConfig


def _make_inputs(n_nodes: int = 3, n_features: int = 4, seed: int = 0):
    g = torch.Generator().manual_seed(seed)
    x = torch.randn(n_nodes, n_features, generator=g)
    # Fully connected with self loops, ring-like
    edges = []
    for i in range(n_nodes):
        for j in range(n_nodes):
            edges.append((i, j))
    edge_index = torch.tensor(edges, dtype=torch.long).t()
    edge_weight = torch.ones(edge_index.shape[1])
    return x, edge_index, edge_weight


class TestForwardShape:
    def test_output_shape_n_nodes(self):
        model = MultiScaleGNN()
        x, ei, ew = _make_inputs()
        out = model(x, x, x, ei, ew)
        assert out.shape == (3,)

    def test_supports_n_nodes_10(self):
        model = MultiScaleGNN()
        x, ei, ew = _make_inputs(n_nodes=10)
        out = model(x, x, x, ei, ew)
        assert out.shape == (10,)

    def test_dtype_float32(self):
        model = MultiScaleGNN()
        x, ei, ew = _make_inputs()
        out = model(x, x, x, ei, ew)
        assert out.dtype == torch.float32


class TestParameters:
    def test_param_count_matches_config(self):
        cfg = MultiScaleGNNConfig(hidden=32, heads=4, n_features=4)
        model = MultiScaleGNN(cfg)
        n = model.num_parameters()
        # Should be of order 3*GAT(2 layer hidden=32) + fusion(96 → 32 → 1)
        # Reasonable bounds: 3000 < n < 30000
        assert 3000 < n < 30000

    def test_grad_flows_through_all_scales(self):
        cfg = MultiScaleGNNConfig(hidden=16, heads=2, n_features=4, dropout=0.0)
        model = MultiScaleGNN(cfg)
        x, ei, ew = _make_inputs()
        out = model(x, x.clone(), x.clone(), ei, ew)
        out.sum().backward()
        # All three scale branches must have non-None gradients
        for branch in [model.scale_d, model.scale_w, model.scale_m]:
            grads = [p.grad for p in branch.parameters()]
            assert all(g is not None for g in grads)
            # At least one tensor with non-zero grad
            assert any((g.abs().sum() > 0).item() for g in grads)


class TestDifferentScalesProduceDifferentOutputs:
    def test_distinct_inputs_yield_distinct_predictions(self):
        cfg = MultiScaleGNNConfig(hidden=32, heads=4, n_features=4, dropout=0.0)
        torch.manual_seed(7)
        model = MultiScaleGNN(cfg).eval()
        x, ei, ew = _make_inputs(seed=1)
        x2, _, _ = _make_inputs(seed=2)
        x3, _, _ = _make_inputs(seed=3)
        with torch.no_grad():
            out_a = model(x, x2, x3, ei, ew)
            out_b = model(x3, x, x2, ei, ew)
        # Permuting scale inputs must change the output (paths are not shared)
        assert not torch.allclose(out_a, out_b)


class TestEval:
    def test_eval_mode_disables_dropout(self):
        cfg = MultiScaleGNNConfig(hidden=16, heads=2, n_features=4, dropout=0.5)
        model = MultiScaleGNN(cfg)
        model.eval()
        x, ei, ew = _make_inputs()
        with torch.no_grad():
            out_a = model(x, x, x, ei, ew)
            out_b = model(x, x, x, ei, ew)
        # Deterministic in eval mode
        torch.testing.assert_close(out_a, out_b)
