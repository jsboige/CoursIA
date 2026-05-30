#!/usr/bin/env python3
"""
Tests for scripts/sudoku/core/graph.py + dataset.py

graph.py: Sudoku constraint graph construction (build_sudoku_edge_index,
make_batch_edge_index). Pure computation, deterministic output.
dataset.py: parse_81 (string -> numpy array conversion).

LIVE: 13+ callers across training/eval/diagnostic scripts.
"""

import numpy as np
import pytest
import torch
import sys
from pathlib import Path

# Add sudoku/core to sys.path
_sudoku_core = str(Path(__file__).resolve().parent.parent / "sudoku" / "core")
if _sudoku_core not in sys.path:
    sys.path.insert(0, _sudoku_core)

from graph import build_sudoku_edge_index, make_batch_edge_index
from dataset import parse_81, SudokuGraphDataset, sudoku_collate_fn


# ─── parse_81 ─────────────────────────────────────────────────────────


class TestParse81:
    def test_basic_conversion(self):
        result = parse_81("123456789" * 9)
        assert len(result) == 81
        assert result[0] == 1
        assert result[80] == 9

    def test_zeros(self):
        result = parse_81("0" * 81)
        assert np.all(result == 0)

    def test_returns_numpy(self):
        result = parse_81("1" * 81)
        assert isinstance(result, np.ndarray)

    def test_dtype(self):
        result = parse_81("5" * 81)
        assert result.dtype == np.int64

    def test_single_digit(self):
        result = parse_81("5")
        assert len(result) == 1
        assert result[0] == 5

    def test_all_different(self):
        s = "123456789" * 9
        result = parse_81(s)
        assert len(result) == 81
        # First 9 should be 1-9
        for i in range(9):
            assert result[i] == i + 1

    def test_preserves_zeros_in_middle(self):
        result = parse_81("123450000" * 9)
        assert result[5] == 0
        assert result[4] == 5

    def test_long_string(self):
        """81 characters of mixed digits."""
        s = "530070900600195000098000060800060003400803001700020006060000280000419005000080079"
        result = parse_81(s)
        assert len(result) == 81
        assert result[0] == 5
        assert result[1] == 3
        assert result[4] == 7


# ─── build_sudoku_edge_index ──────────────────────────────────────────


class TestBuildSudokuEdgeIndex:
    def test_returns_tensor(self):
        edges = build_sudoku_edge_index()
        assert isinstance(edges, torch.Tensor)

    def test_shape_is_2x1620(self):
        """81 cells * 20 neighbors = 1620 directed edges."""
        edges = build_sudoku_edge_index()
        assert edges.shape == (2, 1620)

    def test_dtype_is_long(self):
        edges = build_sudoku_edge_index()
        assert edges.dtype == torch.long

    def test_all_indices_in_range(self):
        """All node indices must be 0-80."""
        edges = build_sudoku_edge_index()
        assert edges.min().item() >= 0
        assert edges.max().item() <= 80

    def test_no_self_loops(self):
        """No edge from a node to itself."""
        edges = build_sudoku_edge_index()
        src, dst = edges[0], edges[1]
        assert not torch.any(src == dst)

    def test_each_node_has_20_incoming(self):
        """Each cell receives exactly 20 constraint edges."""
        edges = build_sudoku_edge_index()
        dst = edges[1]
        for i in range(81):
            count = (dst == i).sum().item()
            assert count == 20, f"Node {i} has {count} incoming edges, expected 20"

    def test_row_neighbors(self):
        """Cell 0 (row 0, col 0) should have row neighbors 1-8."""
        edges = build_sudoku_edge_index()
        src, dst = edges[0], edges[1]
        incoming_to_0 = src[dst == 0].tolist()
        # Row neighbors: cells 1-8 in row 0
        for c in range(1, 9):
            assert c in incoming_to_0, f"Row neighbor {c} missing for cell 0"

    def test_col_neighbors(self):
        """Cell 0 (row 0, col 0) should have col neighbors at rows 1-8."""
        edges = build_sudoku_edge_index()
        src, dst = edges[0], edges[1]
        incoming_to_0 = src[dst == 0].tolist()
        # Column neighbors: cells 9, 18, 27, 36, 45, 54, 63, 72
        for r in range(1, 9):
            assert r * 9 in incoming_to_0, f"Col neighbor {r * 9} missing for cell 0"

    def test_box_neighbors(self):
        """Cell 0 (row 0, col 0) should have box neighbors 1,2,9,10,11,18,19,20
        but some are shared with row/col — total 20 unique."""
        edges = build_sudoku_edge_index()
        src, dst = edges[0], edges[1]
        incoming_to_0 = set(src[dst == 0].tolist())
        # Box (0,0) neighbors not already in row/col: 10, 11, 19, 20
        assert 10 in incoming_to_0
        assert 11 in incoming_to_0
        assert 19 in incoming_to_0
        assert 20 in incoming_to_0

    def test_deterministic(self):
        """Calling twice gives identical result."""
        e1 = build_sudoku_edge_index()
        e2 = build_sudoku_edge_index()
        assert torch.equal(e1, e2)


# ─── make_batch_edge_index ────────────────────────────────────────────


class TestMakeBatchEdgeIndex:
    def _base(self):
        return build_sudoku_edge_index()

    def test_batch_size_1_same_as_base(self):
        base = self._base()
        batched = make_batch_edge_index(base, 1)
        assert torch.equal(batched, base)

    def test_batch_size_2_doubled_edges(self):
        base = self._base()
        batched = make_batch_edge_index(base, 2)
        assert batched.shape[1] == base.shape[1] * 2

    def test_batch_offset(self):
        """Second graph's edges should be offset by 81."""
        base = self._base()
        batched = make_batch_edge_index(base, 2)
        # First half is original
        first_half = batched[:, :base.shape[1]]
        assert torch.equal(first_half, base)
        # Second half is offset by 81
        second_half = batched[:, base.shape[1]:]
        assert torch.equal(second_half, base + 81)

    def test_batch_size_3(self):
        base = self._base()
        batched = make_batch_edge_index(base, 3)
        assert batched.shape[1] == base.shape[1] * 3

    def test_returns_tensor(self):
        batched = make_batch_edge_index(self._base(), 2)
        assert isinstance(batched, torch.Tensor)

    def test_all_indices_valid_batch2(self):
        """All indices in range [0, 162) for batch_size=2."""
        batched = make_batch_edge_index(self._base(), 2)
        assert batched.min().item() >= 0
        assert batched.max().item() < 162

    def test_all_indices_valid_batch5(self):
        batched = make_batch_edge_index(self._base(), 5)
        assert batched.min().item() >= 0
        assert batched.max().item() < 81 * 5


# ─── SudokuGraphDataset ──────────────────────────────────────────────


class TestSudokuGraphDataset:
    def test_len(self):
        puzzles = np.zeros((10, 81), dtype=np.int64)
        solutions = np.ones((10, 81), dtype=np.int64)
        ds = SudokuGraphDataset(puzzles, solutions)
        assert len(ds) == 10

    def test_getitem(self):
        puzzles = np.full((3, 81), 5, dtype=np.int64)
        solutions = np.full((3, 81), 9, dtype=np.int64)
        ds = SudokuGraphDataset(puzzles, solutions)
        p, s = ds[1]
        assert p[0] == 5
        assert s[0] == 9

    def test_casts_to_int8(self):
        puzzles = np.zeros((1, 81), dtype=np.int64)
        solutions = np.ones((1, 81), dtype=np.int64)
        ds = SudokuGraphDataset(puzzles, solutions)
        assert ds.puzzles.dtype == np.int8
        assert ds.solutions.dtype == np.int8


# ─── Cross-invariants ────────────────────────────────────────────────


class TestCrossInvariants:
    def test_edge_count_matches_peer_count(self):
        """81 cells * 20 peers = 1620 edges, consistent with solvers.py peer logic."""
        edges = build_sudoku_edge_index()
        assert edges.shape[1] == 81 * 20

    def test_batch_preserves_edge_structure(self):
        """Each subgraph in batch has same local structure as base."""
        base = build_sudoku_edge_index()
        batched = make_batch_edge_index(base, 3)
        for b in range(3):
            offset = b * base.shape[1]
            sub = batched[:, offset:offset + base.shape[1]] - b * 81
            assert torch.equal(sub, base)

    def test_parse_81_then_solve(self):
        """parse_81 output is compatible with solver input format."""
        from solvers import solve_sudoku
        s = "530070900600195000098000060800060003400803001700020006060000280000419005000080079"
        puzzle = parse_81(s)
        result = solve_sudoku(puzzle)
        assert result is not None
        assert np.all(result > 0)
