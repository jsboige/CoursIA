#!/usr/bin/env python3
"""
Tests for scripts/sudoku/core/models.py

Covers: SudokuRRN (construction, attributes, layers, forward pass),
count_params (parameter counting).
CPU-only: small tensors, no GPU required.

LIVE: 10+ callers (train_v4, train_classical, overnight_sweep, finetune,
eval_notebook, cpu_diagnostic, +5 archived).
"""

import torch
import torch.nn as nn
import pytest
import sys
from pathlib import Path

# Add sudoku/core to sys.path
_sudoku_core = str(Path(__file__).resolve().parent.parent / "sudoku" / "core")
if _sudoku_core not in sys.path:
    sys.path.insert(0, _sudoku_core)

from models import SudokuRRN, count_params
from graph import build_sudoku_edge_index, make_batch_edge_index


# ─── SudokuRRN.__init__ ──────────────────────────────────────────────


class TestSudokuRRNInit:
    def test_is_nn_module(self):
        model = SudokuRRN()
        assert isinstance(model, nn.Module)

    def test_default_hidden_dim(self):
        model = SudokuRRN()
        assert model.hidden_dim == 128

    def test_default_msg_dim(self):
        model = SudokuRRN()
        assert model.msg_dim == 128

    def test_default_n_steps(self):
        model = SudokuRRN()
        assert model.n_steps == 32

    def test_custom_hidden_dim(self):
        model = SudokuRRN(hidden_dim=64)
        assert model.hidden_dim == 64

    def test_custom_msg_dim(self):
        model = SudokuRRN(msg_dim=32)
        assert model.msg_dim == 32

    def test_custom_n_steps(self):
        model = SudokuRRN(n_steps=8)
        assert model.n_steps == 8

    def test_custom_dropout(self):
        """Custom dropout rate accepted without error."""
        model = SudokuRRN(dropout=0.3)
        assert isinstance(model, nn.Module)

    def test_all_defaults_combined(self):
        model = SudokuRRN()
        assert model.hidden_dim == 128
        assert model.msg_dim == 128
        assert model.n_steps == 32


# ─── SudokuRRN layers ───────────────────────────────────────────────


class TestSudokuRRNLayers:
    def test_input_embed_exists(self):
        model = SudokuRRN()
        assert hasattr(model, 'input_embed')
        assert isinstance(model.input_embed, nn.Sequential)

    def test_input_embed_linear(self):
        """First layer of input_embed is Linear(10, hidden_dim)."""
        model = SudokuRRN(hidden_dim=64)
        linear = model.input_embed[0]
        assert isinstance(linear, nn.Linear)
        assert linear.in_features == 10
        assert linear.out_features == 64

    def test_input_embed_layernorm(self):
        """Second layer of input_embed is LayerNorm(hidden_dim)."""
        model = SudokuRRN(hidden_dim=64)
        ln = model.input_embed[1]
        assert isinstance(ln, nn.LayerNorm)
        assert ln.normalized_shape[0] == 64

    def test_pos_embed_exists(self):
        model = SudokuRRN()
        assert hasattr(model, 'pos_embed')
        assert isinstance(model.pos_embed, nn.Parameter)

    def test_pos_embed_shape(self):
        """Position embedding: (81, hidden_dim)."""
        model = SudokuRRN(hidden_dim=64)
        assert model.pos_embed.shape == (81, 64)

    def test_msg_mlp_exists(self):
        model = SudokuRRN()
        assert hasattr(model, 'msg_mlp')
        assert isinstance(model.msg_mlp, nn.Sequential)

    def test_msg_mlp_first_linear(self):
        """First layer of msg_mlp: Linear(hidden_dim*2, msg_dim)."""
        model = SudokuRRN(hidden_dim=64, msg_dim=32)
        linear = model.msg_mlp[0]
        assert isinstance(linear, nn.Linear)
        assert linear.in_features == 128  # hidden_dim * 2
        assert linear.out_features == 32

    def test_gru_exists(self):
        model = SudokuRRN()
        assert hasattr(model, 'gru')
        assert isinstance(model.gru, nn.GRUCell)

    def test_gru_dims(self):
        """GRUCell: (msg_dim, hidden_dim)."""
        model = SudokuRRN(hidden_dim=64, msg_dim=32)
        assert model.gru.input_size == 32
        assert model.gru.hidden_size == 64

    def test_norm_exists(self):
        model = SudokuRRN()
        assert hasattr(model, 'norm')
        assert isinstance(model.norm, nn.LayerNorm)

    def test_output_exists(self):
        model = SudokuRRN()
        assert hasattr(model, 'output')
        assert isinstance(model.output, nn.Linear)

    def test_output_dims(self):
        """Output layer: Linear(hidden_dim, 9) for 9 digit classes."""
        model = SudokuRRN(hidden_dim=64)
        assert model.output.in_features == 64
        assert model.output.out_features == 9


# ─── count_params ────────────────────────────────────────────────────


class TestCountParams:
    def test_returns_int(self):
        model = SudokuRRN()
        result = count_params(model)
        assert isinstance(result, int)

    def test_returns_positive(self):
        model = SudokuRRN()
        assert count_params(model) > 0

    def test_default_params_order(self):
        """Default model (h=128, m=128) should have ~200k+ params."""
        model = SudokuRRN()
        n = count_params(model)
        assert n > 100_000

    def test_smaller_model_fewer_params(self):
        """Smaller hidden_dim = fewer parameters."""
        big = SudokuRRN(hidden_dim=128)
        small = SudokuRRN(hidden_dim=32)
        assert count_params(small) < count_params(big)

    def test_different_n_steps_same_params(self):
        """n_steps affects forward iterations, not parameter count."""
        m1 = SudokuRRN(n_steps=8)
        m2 = SudokuRRN(n_steps=32)
        assert count_params(m1) == count_params(m2)

    def test_custom_dims(self):
        """Custom hidden/msg dims produce different param counts."""
        m1 = SudokuRRN(hidden_dim=64, msg_dim=64)
        m2 = SudokuRRN(hidden_dim=128, msg_dim=128)
        assert count_params(m1) != count_params(m2)

    def test_only_trainable(self):
        """count_params counts only requires_grad parameters."""
        model = SudokuRRN()
        # Freeze one parameter
        model.output.weight.requires_grad = False
        full = count_params(model)
        # Should be less than with all trainable
        model2 = SudokuRRN()
        assert full < count_params(model2)


# ─── SudokuRRN forward ──────────────────────────────────────────────


class TestSudokuRRNForward:
    def _make_input(self, batch_size=2):
        """Create minimal input tensors for forward pass."""
        x = torch.zeros(batch_size, 81, 10)
        # Set some given cells in first sample
        x[0, 0, 0] = 1.0  # digit 1
        x[0, 0, 9] = 1.0  # is_given
        if batch_size > 1:
            x[1, 5, 4] = 1.0  # digit 5
            x[1, 5, 9] = 1.0  # is_given
        edges = build_sudoku_edge_index()
        batched_edges = make_batch_edge_index(edges, batch_size)
        return x, batched_edges

    def test_forward_returns_list(self):
        model = SudokuRRN(n_steps=2)
        x, edges = self._make_input(1)
        with torch.no_grad():
            output = model(x, edges)
        assert isinstance(output, list)

    def test_forward_list_length_matches_n_steps(self):
        """Output list length should equal n_steps."""
        model = SudokuRRN(n_steps=3)
        x, edges = self._make_input(1)
        with torch.no_grad():
            output = model(x, edges)
        assert len(output) == 3

    def test_forward_output_shape(self):
        """Each step output: (batch_size, 81, 9)."""
        model = SudokuRRN(n_steps=2)
        x, edges = self._make_input(2)
        with torch.no_grad():
            output = model(x, edges)
        for logits in output:
            assert logits.shape == (2, 81, 9)

    def test_forward_output_is_tensor(self):
        model = SudokuRRN(n_steps=2)
        x, edges = self._make_input(1)
        with torch.no_grad():
            output = model(x, edges)
        assert isinstance(output[0], torch.Tensor)

    def test_forward_batch_size_1(self):
        model = SudokuRRN(n_steps=2, hidden_dim=32, msg_dim=32)
        x, edges = self._make_input(1)
        with torch.no_grad():
            output = model(x, edges)
        assert output[0].shape == (1, 81, 9)

    def test_forward_batch_size_4(self):
        model = SudokuRRN(n_steps=2, hidden_dim=32, msg_dim=32)
        x, edges = self._make_input(4)
        with torch.no_grad():
            output = model(x, edges)
        assert output[0].shape == (4, 81, 9)

    def test_forward_output_dtype_float(self):
        model = SudokuRRN(n_steps=2, hidden_dim=32, msg_dim=32)
        x, edges = self._make_input(1)
        with torch.no_grad():
            output = model(x, edges)
        assert output[0].dtype in (torch.float32, torch.float64)

    def test_forward_logits_finite(self):
        """Output logits should not contain NaN or Inf."""
        model = SudokuRRN(n_steps=2, hidden_dim=32, msg_dim=32)
        x, edges = self._make_input(1)
        with torch.no_grad():
            output = model(x, edges)
        for logits in output:
            assert torch.all(torch.isfinite(logits))

    def test_forward_deterministic_eval(self):
        """Same input in eval mode produces same output."""
        model = SudokuRRN(n_steps=2, hidden_dim=32, msg_dim=32)
        model.eval()
        x, edges = self._make_input(1)
        with torch.no_grad():
            o1 = model(x, edges)
            o2 = model(x, edges)
        for a, b in zip(o1, o2):
            assert torch.allclose(a, b, atol=1e-6)


# ─── Cross-invariants ────────────────────────────────────────────────


class TestCrossInvariants:
    def test_model_compatible_with_graph(self):
        """Model forward works with build_sudoku_edge_index output."""
        model = SudokuRRN(n_steps=1, hidden_dim=32, msg_dim=32)
        edges = build_sudoku_edge_index()
        batched = make_batch_edge_index(edges, 1)
        x = torch.zeros(1, 81, 10)
        with torch.no_grad():
            output = model(x, batched)
        assert len(output) == 1
        assert output[0].shape == (1, 81, 9)

    def test_count_params_matches_parameter_count(self):
        """count_params should match sum of parameter elements."""
        model = SudokuRRN(hidden_dim=32, msg_dim=32, n_steps=2)
        total = sum(p.numel() for p in model.parameters() if p.requires_grad)
        assert count_params(model) == total

    def test_model_state_dict_keys(self):
        """State dict has expected key groups."""
        model = SudokuRRN(hidden_dim=32, msg_dim=32)
        keys = set(model.state_dict().keys())
        assert any('input_embed' in k for k in keys)
        assert any('pos_embed' in k for k in keys)
        assert any('msg_mlp' in k for k in keys)
        assert any('gru' in k for k in keys)
        assert any('output' in k for k in keys)

    def test_output_compatible_with_loss(self):
        """Model output can be used with CrossEntropyLoss."""
        model = SudokuRRN(n_steps=1, hidden_dim=32, msg_dim=32)
        edges = build_sudoku_edge_index()
        batched = make_batch_edge_index(edges, 2)
        x = torch.zeros(2, 81, 10)
        with torch.no_grad():
            logits_list = model(x, batched)
        # logits: (2, 81, 9) → reshape for loss
        logits = logits_list[-1].reshape(-1, 9)
        target = torch.zeros(2 * 81, dtype=torch.long)
        loss = torch.nn.functional.cross_entropy(logits, target)
        assert loss.item() > 0
        assert torch.isfinite(loss)

    def test_collate_output_compatible_with_model(self):
        """sudoku_collate_fn output is compatible with model forward."""
        from dataset import SudokuGraphDataset, sudoku_collate_fn
        import numpy as np

        puzzles = np.zeros((2, 81), dtype=np.int64)
        solutions = np.ones((2, 81), dtype=np.int64)
        ds = SudokuGraphDataset(puzzles, solutions)
        batch = [ds[i] for i in range(2)]
        x, y, mask = sudoku_collate_fn(batch)

        model = SudokuRRN(n_steps=1, hidden_dim=32, msg_dim=32)
        edges = build_sudoku_edge_index()
        batched = make_batch_edge_index(edges, 2)

        with torch.no_grad():
            output = model(x, batched)
        assert output[0].shape[0] == 2  # batch_size
        assert output[0].shape[1] == 81  # cells
        assert output[0].shape[2] == 9   # classes
