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


# ─── sudoku_collate_fn ────────────────────────────────────────────────


class TestSudokuCollateFn:
    """Tests for the vectorized collate function (7 LIVE callers)."""

    def _make_batch(self, bs, puzzle_val=0, solution_val=1):
        """Helper: create a batch of (puzzle, solution) tuples."""
        puzzles = np.full((bs, 81), puzzle_val, dtype=np.int8)
        solutions = np.full((bs, 81), solution_val, dtype=np.int8)
        return [(puzzles[i], solutions[i]) for i in range(bs)]

    # --- Output structure ---

    def test_returns_three_tensors(self):
        batch = self._make_batch(2)
        result = sudoku_collate_fn(batch)
        assert len(result) == 3
        assert isinstance(result[0], torch.Tensor)
        assert isinstance(result[1], torch.Tensor)
        assert isinstance(result[2], torch.Tensor)

    def test_x_shape(self):
        """x should be (batch_size, 81, 10): 9 one-hot channels + is_given."""
        batch = self._make_batch(4)
        x, y, mask = sudoku_collate_fn(batch)
        assert x.shape == (4, 81, 10)

    def test_y_shape(self):
        """y should be (batch_size, 81): class indices 0-8."""
        batch = self._make_batch(3)
        x, y, mask = sudoku_collate_fn(batch)
        assert y.shape == (3, 81)

    def test_mask_shape(self):
        """is_given mask should be (batch_size, 81)."""
        batch = self._make_batch(5)
        x, y, mask = sudoku_collate_fn(batch)
        assert mask.shape == (5, 81)

    def test_x_dtype_float32(self):
        batch = self._make_batch(2)
        x, _, _ = sudoku_collate_fn(batch)
        assert x.dtype == torch.float32

    def test_y_dtype_long(self):
        batch = self._make_batch(2, solution_val=5)
        _, y, _ = sudoku_collate_fn(batch)
        assert y.dtype == torch.long

    def test_mask_dtype_float32(self):
        batch = self._make_batch(2)
        _, _, mask = sudoku_collate_fn(batch)
        assert mask.dtype == torch.float32

    # --- One-hot encoding ---

    def test_all_zeros_puzzle_one_hot(self):
        """All-zero puzzle: one-hot channels 0-8 all zero, is_given=0."""
        batch = self._make_batch(1, puzzle_val=0)
        x, _, mask = sudoku_collate_fn(batch)
        # Channels 0-8 should all be 0 (no digit present)
        assert torch.all(x[:, :, :9] == 0)
        # Channel 9 (is_given) should be 0
        assert torch.all(x[:, :, 9] == 0)
        # Mask should be all 0
        assert torch.all(mask == 0)

    def test_digit_one_hot_encoding(self):
        """Puzzle value 5 activates channel 4 (digit-1), is_given=1."""
        batch = self._make_batch(1, puzzle_val=5)
        x, _, mask = sudoku_collate_fn(batch)
        # Channel 4 (= digit 5 - 1) should be 1
        assert torch.all(x[:, :, 4] == 1.0)
        # All other digit channels should be 0
        for ch in range(9):
            if ch != 4:
                assert torch.all(x[:, :, ch] == 0.0), f"Channel {ch} should be 0"
        # is_given channel should be 1
        assert torch.all(x[:, :, 9] == 1.0)
        assert torch.all(mask == 1.0)

    def test_digit_1_activates_channel_0(self):
        batch = self._make_batch(1, puzzle_val=1)
        x, _, _ = sudoku_collate_fn(batch)
        assert torch.all(x[:, :, 0] == 1.0)

    def test_digit_9_activates_channel_8(self):
        batch = self._make_batch(1, puzzle_val=9)
        x, _, _ = sudoku_collate_fn(batch)
        assert torch.all(x[:, :, 8] == 1.0)

    def test_mixed_digits_one_hot(self):
        """Different cells with different values get correct one-hot."""
        puzzle = np.zeros(81, dtype=np.int8)
        puzzle[0] = 1
        puzzle[1] = 5
        puzzle[2] = 9
        batch = [(puzzle, np.ones(81, dtype=np.int8))]
        x, _, _ = sudoku_collate_fn(batch)
        # Cell 0: digit 1 -> channel 0
        assert x[0, 0, 0] == 1.0
        # Cell 1: digit 5 -> channel 4
        assert x[0, 1, 4] == 1.0
        # Cell 2: digit 9 -> channel 8
        assert x[0, 2, 8] == 1.0
        # Empty cells: all channels 0 except is_given
        assert x[0, 3, :9].sum() == 0

    # --- Solution indexing ---

    def test_solutions_shifted_by_minus_1(self):
        """Solutions are converted to 0-indexed (1->0, 5->4, 9->8)."""
        batch = self._make_batch(1, solution_val=5)
        _, y, _ = sudoku_collate_fn(batch)
        assert torch.all(y == 4)

    def test_solution_1_becomes_0(self):
        batch = self._make_batch(1, solution_val=1)
        _, y, _ = sudoku_collate_fn(batch)
        assert torch.all(y == 0)

    def test_solution_9_becomes_8(self):
        batch = self._make_batch(1, solution_val=9)
        _, y, _ = sudoku_collate_fn(batch)
        assert torch.all(y == 8)

    # --- is_given mask ---

    def test_is_given_for_nonzero(self):
        batch = self._make_batch(1, puzzle_val=3)
        _, _, mask = sudoku_collate_fn(batch)
        assert torch.all(mask == 1.0)

    def test_is_not_given_for_zero(self):
        batch = self._make_batch(1, puzzle_val=0)
        _, _, mask = sudoku_collate_fn(batch)
        assert torch.all(mask == 0.0)

    def test_mixed_given_mask(self):
        """Mix of given (nonzero) and empty (zero) cells."""
        puzzle = np.zeros(81, dtype=np.int8)
        puzzle[0] = 5
        puzzle[40] = 3
        batch = [(puzzle, np.ones(81, dtype=np.int8))]
        _, _, mask = sudoku_collate_fn(batch)
        assert mask[0, 0] == 1.0
        assert mask[0, 40] == 1.0
        assert mask[0, 1] == 0.0

    # --- Batch dimension ---

    def test_batch_size_8(self):
        batch = self._make_batch(8, puzzle_val=3, solution_val=7)
        x, y, mask = sudoku_collate_fn(batch)
        assert x.shape[0] == 8
        assert y.shape[0] == 8
        assert mask.shape[0] == 8

    def test_independent_samples(self):
        """Each sample in batch is encoded independently."""
        p1 = np.full(81, 1, dtype=np.int8)
        p2 = np.full(81, 9, dtype=np.int8)
        batch = [(p1, np.ones(81, dtype=np.int8)), (p2, np.ones(81, dtype=np.int8))]
        x, _, _ = sudoku_collate_fn(batch)
        # Sample 0: digit 1 -> channel 0
        assert torch.all(x[0, :, 0] == 1.0)
        # Sample 1: digit 9 -> channel 8
        assert torch.all(x[1, :, 8] == 1.0)

    # --- Determinism ---

    def test_deterministic(self):
        batch = self._make_batch(3, puzzle_val=4, solution_val=6)
        r1 = sudoku_collate_fn(batch)
        r2 = sudoku_collate_fn(batch)
        assert torch.equal(r1[0], r2[0])
        assert torch.equal(r1[1], r2[1])
        assert torch.equal(r1[2], r2[2])


# ─── SudokuGraphDataset (extended) ──────────────────────────────────


class TestSudokuGraphDatasetExtended:
    """Additional tests for SudokuGraphDataset edge cases."""

    def test_single_element(self):
        puzzles = np.zeros((1, 81), dtype=np.int64)
        solutions = np.ones((1, 81), dtype=np.int64)
        ds = SudokuGraphDataset(puzzles, solutions)
        assert len(ds) == 1
        p, s = ds[0]
        assert len(p) == 81

    def test_returns_tuple(self):
        puzzles = np.zeros((1, 81), dtype=np.int64)
        solutions = np.ones((1, 81), dtype=np.int64)
        ds = SudokuGraphDataset(puzzles, solutions)
        result = ds[0]
        assert isinstance(result, tuple)
        assert len(result) == 2

    def test_preserves_values(self):
        """Values are preserved after int8 cast."""
        puzzles = np.full((1, 81), 7, dtype=np.int64)
        solutions = np.full((1, 81), 3, dtype=np.int64)
        ds = SudokuGraphDataset(puzzles, solutions)
        p, s = ds[0]
        assert p[0] == 7
        assert s[0] == 3

    def test_index_out_of_range(self):
        puzzles = np.zeros((2, 81), dtype=np.int64)
        solutions = np.ones((2, 81), dtype=np.int64)
        ds = SudokuGraphDataset(puzzles, solutions)
        with pytest.raises(IndexError):
            ds[2]

    def test_all_zeros_values(self):
        """All-zero puzzle/solution is valid."""
        puzzles = np.zeros((1, 81), dtype=np.int64)
        solutions = np.zeros((1, 81), dtype=np.int64)
        ds = SudokuGraphDataset(puzzles, solutions)
        p, s = ds[0]
        assert np.all(p == 0)
        assert np.all(s == 0)


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

    def test_dataset_then_collate_fn(self):
        """SudokuGraphDataset output is compatible with sudoku_collate_fn."""
        puzzles = np.zeros((4, 81), dtype=np.int64)
        solutions = np.ones((4, 81), dtype=np.int64)
        # Set some given cells
        puzzles[0, 0] = 5
        puzzles[1, 10] = 3
        puzzles[2, 40] = 7
        puzzles[3, 80] = 9

        ds = SudokuGraphDataset(puzzles, solutions)
        batch = [ds[i] for i in range(4)]
        x, y, mask = sudoku_collate_fn(batch)

        assert x.shape == (4, 81, 10)
        assert y.shape == (4, 81)
        assert mask.shape == (4, 81)
        # Solution 1 -> class 0
        assert torch.all(y == 0)
        # Given cells detected
        assert mask[0, 0] == 1.0
        assert mask[1, 10] == 1.0
        assert mask[2, 40] == 1.0
        assert mask[3, 80] == 1.0

    def test_collate_fn_y_range_0_to_8(self):
        """Collate output y has values in [0, 8] (0-indexed classes)."""
        puzzles = np.zeros((1, 81), dtype=np.int8)
        # Solutions with all values 1-9
        solutions = np.array([(i % 9) + 1 for i in range(81)], dtype=np.int8)
        batch = [(puzzles[0], solutions)]
        _, y, _ = sudoku_collate_fn(batch)
        assert y.min().item() >= 0
        assert y.max().item() <= 8
