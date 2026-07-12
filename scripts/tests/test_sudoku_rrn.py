#!/usr/bin/env python3
"""
Tests for scripts/sudoku/sudoku_rrn.py

Covers: build_sudoku_edge_index, make_batch_edge_index, parse_81,
SudokuRRN (construction, attributes, layers, forward, count_params).
CPU-only: small tensors, no GPU required.

LIVE: 4 callers (phase2_iterative, sudoku_curriculum_train,
sudoku_double_track, train_phase2_hard).
"""

import torch
import torch.nn as nn
import numpy as np
import pytest
import sys
from pathlib import Path

# Add sudoku/ to sys.path
_sudoku_dir = str(Path(__file__).resolve().parent.parent / "sudoku")
if _sudoku_dir not in sys.path:
    sys.path.insert(0, _sudoku_dir)

from sudoku_rrn import (
    build_sudoku_edge_index,
    make_batch_edge_index,
    parse_81,
    SudokuRRN,
)


# ─── build_sudoku_edge_index ──────────────────────────────────────────


class TestBuildSudokuEdgeIndex:
    def test_returns_tensor(self):
        edges = build_sudoku_edge_index()
        assert isinstance(edges, torch.Tensor)

    def test_shape(self):
        """Edge index should be (2, N) where N is number of directed edges."""
        edges = build_sudoku_edge_index()
        assert edges.dim() == 2
        assert edges.shape[0] == 2

    def test_dtype_long(self):
        edges = build_sudoku_edge_index()
        assert edges.dtype == torch.long

    def test_nodes_in_range(self):
        """All node indices should be in [0, 80]."""
        edges = build_sudoku_edge_index()
        assert edges.min() >= 0
        assert edges.max() <= 80

    def test_no_self_loops(self):
        """No cell should have an edge to itself."""
        edges = build_sudoku_edge_index()
        src, dst = edges[1], edges[0]
        assert not torch.any(src == dst)

    def test_symmetric_peers(self):
        """If (i,j) is an edge, (j,i) should also be an edge."""
        edges = build_sudoku_edge_index()
        edge_set = set(map(tuple, edges.T.tolist()))
        for s, d in edge_set:
            assert (d, s) in edge_set, f"Missing reverse edge ({d}, {s})"

    def test_row_peers(self):
        """Each cell connects to all other cells in its row."""
        edges = build_sudoku_edge_index()
        edge_set = set(map(tuple, edges.T.tolist()))
        for i in range(81):
            r = i // 9
            for j in range(9):
                k = r * 9 + j
                if k != i:
                    assert (k, i) in edge_set, f"Missing row peer ({k}, {i})"

    def test_col_peers(self):
        """Each cell connects to all other cells in its column."""
        edges = build_sudoku_edge_index()
        edge_set = set(map(tuple, edges.T.tolist()))
        for i in range(81):
            c = i % 9
            for j in range(9):
                k = j * 9 + c
                if k != i:
                    assert (k, i) in edge_set, f"Missing col peer ({k}, {i})"

    def test_block_peers(self):
        """Each cell connects to all other cells in its 3x3 block."""
        edges = build_sudoku_edge_index()
        edge_set = set(map(tuple, edges.T.tolist()))
        for i in range(81):
            r, c = i // 9, i % 9
            br, bc = 3 * (r // 3), 3 * (c // 3)
            for dr in range(3):
                for dc in range(3):
                    k = (br + dr) * 9 + (bc + dc)
                    if k != i:
                        assert (k, i) in edge_set, f"Missing block peer ({k}, {i})"

    def test_edge_count_reasonable(self):
        """Should have > 500 directed edges (81 cells * ~20 peers each)."""
        edges = build_sudoku_edge_index()
        assert edges.shape[1] > 500

    def test_deterministic(self):
        """Same call produces same result."""
        e1 = build_sudoku_edge_index()
        e2 = build_sudoku_edge_index()
        assert torch.equal(e1, e2)


# ─── make_batch_edge_index ────────────────────────────────────────────


class TestMakeBatchEdgeIndex:
    def test_returns_tensor(self):
        base = build_sudoku_edge_index()
        result = make_batch_edge_index(base, 2)
        assert isinstance(result, torch.Tensor)

    def test_batch_size_1(self):
        """Batch size 1 should return same as base."""
        base = build_sudoku_edge_index()
        result = make_batch_edge_index(base, 1)
        assert torch.equal(result, base)

    def test_batch_size_2_edges_doubled(self):
        """Batch size 2 should have 2x the edges."""
        base = build_sudoku_edge_index()
        result = make_batch_edge_index(base, 2)
        assert result.shape[1] == base.shape[1] * 2

    def test_batch_size_3(self):
        base = build_sudoku_edge_index()
        result = make_batch_edge_index(base, 3)
        assert result.shape[1] == base.shape[1] * 3

    def test_offset_correct(self):
        """Second graph's nodes should be offset by 81."""
        base = build_sudoku_edge_index()
        result = make_batch_edge_index(base, 2)
        n = base.shape[1]
        second_graph = result[:, n:]
        expected = base + 81
        assert torch.equal(second_graph, expected)

    def test_all_nodes_in_range(self):
        """All node indices should be in [0, batch_size * 81 - 1]."""
        base = build_sudoku_edge_index()
        bs = 4
        result = make_batch_edge_index(base, bs)
        assert result.min() >= 0
        assert result.max() <= bs * 81 - 1

    def test_dtype_preserved(self):
        base = build_sudoku_edge_index()
        result = make_batch_edge_index(base, 3)
        assert result.dtype == base.dtype


# ─── parse_81 ─────────────────────────────────────────────────────────


class TestParse81:
    def test_returns_numpy(self):
        result = parse_81("0" * 81)
        assert isinstance(result, np.ndarray)

    def test_shape(self):
        result = parse_81("0" * 81)
        assert result.shape == (9, 9)

    def test_dtype(self):
        result = parse_81("0" * 81)
        assert result.dtype == np.int64

    def test_all_zeros(self):
        result = parse_81("0" * 81)
        assert np.all(result == 0)

    def test_all_ones(self):
        result = parse_81("1" * 81)
        assert np.all(result == 1)

    def test_mixed_values(self):
        s = "123456789" * 9
        result = parse_81(s)
        assert result[0, 0] == 1
        assert result[0, 8] == 9
        assert result[1, 0] == 1

    def test_single_nine(self):
        s = "0" * 40 + "9" + "0" * 40
        result = parse_81(s)
        r, c = 40 // 9, 40 % 9
        assert result[r, c] == 9
        # All others are zero
        flat = result.flatten()
        flat_copy = flat.copy()
        flat_copy[r * 9 + c] = 0
        assert np.all(flat_copy == 0)

    def test_flatten_roundtrip(self):
        """Flatten should recover the original digit sequence."""
        s = "5" + "0" * 80
        result = parse_81(s)
        flat = result.flatten()
        assert str(flat[0]) == "5"


# ─── SudokuRRN.__init__ ──────────────────────────────────────────────


class TestSudokuRRNInit:
    def test_is_nn_module(self):
        model = SudokuRRN()
        assert isinstance(model, nn.Module)

    def test_default_hidden_dim(self):
        model = SudokuRRN()
        assert model.hidden_dim == 192

    def test_default_msg_dim(self):
        """Default msg_dim should equal hidden_dim when not specified."""
        model = SudokuRRN()
        assert model.msg_dim == 192

    def test_default_n_steps(self):
        model = SudokuRRN()
        assert model.n_steps == 16

    def test_custom_hidden_dim(self):
        model = SudokuRRN(hidden_dim=64)
        assert model.hidden_dim == 64

    def test_custom_msg_dim_explicit(self):
        model = SudokuRRN(hidden_dim=128, msg_dim=64)
        assert model.msg_dim == 64

    def test_custom_n_steps(self):
        model = SudokuRRN(n_steps=4)
        assert model.n_steps == 4

    def test_custom_dropout(self):
        model = SudokuRRN(dropout=0.5)
        assert isinstance(model, nn.Module)


# ─── SudokuRRN layers ───────────────────────────────────────────────


class TestSudokuRRNLayers:
    def test_input_embed_exists(self):
        model = SudokuRRN()
        assert hasattr(model, 'input_embed')
        assert isinstance(model.input_embed, nn.Sequential)

    def test_input_embed_linear(self):
        """First layer: Linear(10, hidden_dim)."""
        model = SudokuRRN(hidden_dim=64)
        linear = model.input_embed[0]
        assert isinstance(linear, nn.Linear)
        assert linear.in_features == 10
        assert linear.out_features == 64

    def test_pos_embed_shape(self):
        model = SudokuRRN(hidden_dim=64)
        assert model.pos_embed.shape == (81, 64)

    def test_msg_mlp_structure(self):
        model = SudokuRRN(hidden_dim=64, msg_dim=32)
        # msg_mlp: Linear(128, 32) -> Dropout -> ReLU -> Linear(32, 32)
        assert isinstance(model.msg_mlp[0], nn.Linear)
        assert model.msg_mlp[0].in_features == 128
        assert model.msg_mlp[0].out_features == 32

    def test_gru_dims(self):
        model = SudokuRRN(hidden_dim=64, msg_dim=32)
        assert model.gru.input_size == 32
        assert model.gru.hidden_size == 64

    def test_output_dims(self):
        model = SudokuRRN(hidden_dim=64)
        assert model.output.in_features == 64
        assert model.output.out_features == 9


# ─── SudokuRRN.count_params ─────────────────────────────────────────


class TestSudokuRRNCountParams:
    def test_returns_int(self):
        model = SudokuRRN(hidden_dim=32, msg_dim=32, n_steps=2)
        assert isinstance(model.count_params(), int)

    def test_positive(self):
        model = SudokuRRN(hidden_dim=32, msg_dim=32, n_steps=2)
        assert model.count_params() > 0

    def test_different_hidden_dims(self):
        big = SudokuRRN(hidden_dim=128)
        small = SudokuRRN(hidden_dim=32)
        assert big.count_params() > small.count_params()

    def test_n_steps_no_effect(self):
        """n_steps affects iterations, not parameter count."""
        m1 = SudokuRRN(n_steps=4)
        m2 = SudokuRRN(n_steps=16)
        assert m1.count_params() == m2.count_params()

    def test_matches_manual_count(self):
        model = SudokuRRN(hidden_dim=32, msg_dim=32, n_steps=2)
        manual = sum(p.numel() for p in model.parameters())
        assert model.count_params() == manual


# ─── SudokuRRN forward ──────────────────────────────────────────────


class TestSudokuRRNForward:
    def _make_input(self, batch_size=2):
        """Create minimal input for forward pass.

        Note: sudoku_rrn.SudokuRRN.forward takes flat inputs
        (batch*81, 10) and (2, batch*num_edges).
        """
        n_nodes = batch_size * 81
        x = torch.zeros(n_nodes, 10)
        # Set some given cells
        x[0, 0] = 1.0  # digit 1
        x[0, 9] = 1.0  # is_given
        if batch_size > 1:
            x[81 + 5, 4] = 1.0  # digit 5 in second graph
            x[81 + 5, 9] = 1.0  # is_given

        base_edges = build_sudoku_edge_index()
        batched_edges = make_batch_edge_index(base_edges, batch_size)
        return x, batched_edges

    def test_forward_returns_tuple(self):
        model = SudokuRRN(n_steps=2, hidden_dim=32, msg_dim=32)
        x, edges = self._make_input(1)
        with torch.no_grad():
            output = model(x, edges)
        assert isinstance(output, tuple)
        assert len(output) == 2

    def test_forward_final_logits_shape(self):
        """Final logits: (batch*81, 9)."""
        model = SudokuRRN(n_steps=2, hidden_dim=32, msg_dim=32)
        x, edges = self._make_input(2)
        with torch.no_grad():
            final, all_logits = model(x, edges)
        assert final.shape == (2 * 81, 9)

    def test_forward_all_logits_length(self):
        """all_logits list length should equal n_steps."""
        model = SudokuRRN(n_steps=3, hidden_dim=32, msg_dim=32)
        x, edges = self._make_input(1)
        with torch.no_grad():
            _, all_logits = model(x, edges)
        assert len(all_logits) == 3

    def test_forward_each_step_shape(self):
        model = SudokuRRN(n_steps=2, hidden_dim=32, msg_dim=32)
        x, edges = self._make_input(2)
        with torch.no_grad():
            _, all_logits = model(x, edges)
        for logits in all_logits:
            assert logits.shape == (2 * 81, 9)

    def test_forward_logits_finite(self):
        model = SudokuRRN(n_steps=2, hidden_dim=32, msg_dim=32)
        x, edges = self._make_input(1)
        with torch.no_grad():
            final, all_logits = model(x, edges)
        assert torch.all(torch.isfinite(final))
        for logits in all_logits:
            assert torch.all(torch.isfinite(logits))

    def test_forward_deterministic_eval(self):
        model = SudokuRRN(n_steps=2, hidden_dim=32, msg_dim=32)
        model.eval()
        x, edges = self._make_input(1)
        with torch.no_grad():
            o1_final, o1_all = model(x, edges)
            o2_final, o2_all = model(x, edges)
        assert torch.allclose(o1_final, o2_final, atol=1e-6)

    def test_forward_dtype_float(self):
        model = SudokuRRN(n_steps=2, hidden_dim=32, msg_dim=32)
        x, edges = self._make_input(1)
        with torch.no_grad():
            final, _ = model(x, edges)
        assert final.dtype in (torch.float32, torch.float64)


# ─── Cross-invariants ────────────────────────────────────────────────


class TestCrossInvariants:
    def test_parse_81_compatible_with_solver(self):
        """parse_81 output shape compatible with Sudoku conventions."""
        s = "123456789" * 9
        grid = parse_81(s)
        assert grid.shape == (9, 9)
        # All values 1-9
        assert np.all(grid >= 1)
        assert np.all(grid <= 9)

    def test_edge_index_compatible_with_model(self):
        """Edge index works with model forward pass."""
        model = SudokuRRN(n_steps=1, hidden_dim=32, msg_dim=32)
        edges = build_sudoku_edge_index()
        batched = make_batch_edge_index(edges, 1)
        x = torch.zeros(81, 10)
        with torch.no_grad():
            final, all_logits = model(x, batched)
        assert final.shape == (81, 9)
        assert len(all_logits) == 1

    def test_output_compatible_with_loss(self):
        """Model output can be used with CrossEntropyLoss."""
        model = SudokuRRN(n_steps=1, hidden_dim=32, msg_dim=32)
        edges = build_sudoku_edge_index()
        batched = make_batch_edge_index(edges, 2)
        x = torch.zeros(162, 10)
        with torch.no_grad():
            final, _ = model(x, batched)
        # final: (162, 9) -> loss
        target = torch.zeros(162, dtype=torch.long)
        loss = torch.nn.functional.cross_entropy(final, target)
        assert loss.item() > 0
        assert torch.isfinite(loss)

    def test_count_params_matches_parameters(self):
        """count_params() matches sum of parameter elements."""
        model = SudokuRRN(hidden_dim=32, msg_dim=32, n_steps=2)
        total = sum(p.numel() for p in model.parameters())
        assert model.count_params() == total

    def test_state_dict_has_expected_keys(self):
        """State dict should contain all expected layer groups."""
        model = SudokuRRN(hidden_dim=32, msg_dim=32)
        keys = set(model.state_dict().keys())
        assert any('input_embed' in k for k in keys)
        assert any('pos_embed' in k for k in keys)
        assert any('msg_mlp' in k for k in keys)
        assert any('gru' in k for k in keys)
        assert any('output' in k for k in keys)
