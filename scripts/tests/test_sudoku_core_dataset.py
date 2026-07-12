"""Tests for scripts/sudoku/core/dataset.py

Covers: parse_81, SudokuGraphDataset, sudoku_collate_fn.
Pure computation on CPU. No HuggingFace/network dependency.

LIVE: 4 callers (train_*.py, cpu_diagnostic.py, eval_notebook.py).
"""

import sys
from pathlib import Path

import numpy as np
import pytest

# Add sudoku/core to sys.path
_sudoku_core = str(Path(__file__).resolve().parent.parent / "sudoku" / "core")
if _sudoku_core not in sys.path:
    sys.path.insert(0, _sudoku_core)

from dataset import parse_81, SudokuGraphDataset, sudoku_collate_fn


# --- parse_81 ---

class TestParse81:
    def test_valid_complete_string(self):
        s = "530070100600040050078600000800006000600070002000500008700000680050060090100200070"
        result = parse_81(s)
        assert result.shape == (81,)
        assert result.dtype == np.int64
        assert result[0] == 5
        assert result[4] == 7

    def test_all_zeros(self):
        s = "0" * 81
        result = parse_81(s)
        assert (result == 0).all()

    def test_all_nines(self):
        s = "9" * 81
        result = parse_81(s)
        assert (result == 9).all()

    def test_single_digit(self):
        # Not 81 chars — should still parse what's given
        result = parse_81("5")
        assert result.shape == (1,)
        assert result[0] == 5

    def test_returns_numpy(self):
        result = parse_81("1" * 81)
        assert isinstance(result, np.ndarray)

    def test_deterministic(self):
        s = "123456789" * 9
        r1 = parse_81(s)
        r2 = parse_81(s)
        np.testing.assert_array_equal(r1, r2)

    def test_empty_string(self):
        result = parse_81("")
        assert result.shape == (0,)

    def test_mixed_digits(self):
        s = "1234567890" * 8 + "1"
        result = parse_81(s)
        assert result.shape == (81,)
        assert result[0] == 1
        assert result[9] == 0


# --- SudokuGraphDataset ---

class TestSudokuGraphDataset:
    @pytest.fixture
    def sample_data(self):
        puzzles = np.array([
            [5, 3, 0, 0, 7, 0, 0, 0, 0] + [0] * 72,
            [0, 0, 0, 2, 0, 0, 0, 6, 0] + [0] * 72,
        ], dtype=np.int8)
        solutions = np.array([
            [5, 3, 4, 6, 7, 8, 9, 1, 2] + [1] * 72,
            [1, 2, 3, 4, 5, 6, 7, 8, 9] + [2] * 72,
        ], dtype=np.int8)
        return puzzles, solutions

    def test_len(self, sample_data):
        puzzles, solutions = sample_data
        ds = SudokuGraphDataset(puzzles, solutions)
        assert len(ds) == 2

    def test_getitem_shape(self, sample_data):
        puzzles, solutions = sample_data
        ds = SudokuGraphDataset(puzzles, solutions)
        p, s = ds[0]
        assert p.shape == (81,)
        assert s.shape == (81,)

    def test_dtype_preserved(self, sample_data):
        puzzles, solutions = sample_data
        ds = SudokuGraphDataset(puzzles, solutions)
        p, s = ds[0]
        assert p.dtype == np.int8
        assert s.dtype == np.int8

    def test_values_correct(self, sample_data):
        puzzles, solutions = sample_data
        ds = SudokuGraphDataset(puzzles, solutions)
        p, s = ds[1]
        assert p[3] == 2
        assert s[0] == 1

    def test_single_item(self):
        puzzles = np.zeros((1, 81), dtype=np.int8)
        solutions = np.ones((1, 81), dtype=np.int8)
        ds = SudokuGraphDataset(puzzles, solutions)
        assert len(ds) == 1
        p, s = ds[0]
        assert (p == 0).all()
        assert (s == 1).all()


# --- sudoku_collate_fn ---

class TestSudokuCollateFn:
    @pytest.fixture
    def sample_batch(self):
        puzzles = [
            np.array([5, 3, 0, 0, 7, 0, 0, 0, 0] + [0] * 72, dtype=np.int8),
            np.array([0, 0, 0, 2, 0, 0, 0, 6, 0] + [0] * 72, dtype=np.int8),
        ]
        solutions = [
            np.array([5, 3, 4, 6, 7, 8, 9, 1, 2] + [1] * 72, dtype=np.int8),
            np.array([1, 2, 3, 4, 5, 6, 7, 8, 9] + [2] * 72, dtype=np.int8),
        ]
        return list(zip(puzzles, solutions))

    def test_output_types(self, sample_batch):
        import torch
        x, y, given = sudoku_collate_fn(sample_batch)
        assert isinstance(x, torch.Tensor)
        assert isinstance(y, torch.Tensor)
        assert isinstance(given, torch.Tensor)

    def test_x_shape(self, sample_batch):
        x, y, given = sudoku_collate_fn(sample_batch)
        assert x.shape == (2, 81, 10)

    def test_y_shape(self, sample_batch):
        x, y, given = sudoku_collate_fn(sample_batch)
        assert y.shape == (2, 81)

    def test_given_shape(self, sample_batch):
        x, y, given = sudoku_collate_fn(sample_batch)
        assert given.shape == (2, 81)

    def test_y_zero_indexed(self, sample_batch):
        # solutions are 1-9, y should be 0-8
        x, y, given = sudoku_collate_fn(sample_batch)
        # First puzzle, first cell: solution=5 -> y should be 4
        assert y[0, 0].item() == 4

    def test_given_mask(self, sample_batch):
        x, y, given = sudoku_collate_fn(sample_batch)
        # First puzzle: puzzle[0]=5 (given), puzzle[2]=0 (empty)
        assert given[0, 0].item() == 1.0
        assert given[0, 2].item() == 0.0

    def test_one_hot_encoding(self, sample_batch):
        x, y, given = sudoku_collate_fn(sample_batch)
        # First puzzle, cell 0: puzzle=5 -> x[0,0,4]=1 (digit 5 -> index 4)
        assert x[0, 0, 4].item() == 1.0
        # First puzzle, cell 2: puzzle=0 -> no digit channel, only is_given channel
        assert x[0, 2, 9].item() == 0.0  # not given
        for d in range(9):
            assert x[0, 2, d].item() == 0.0  # no digit

    def test_is_given_channel(self, sample_batch):
        x, y, given = sudoku_collate_fn(sample_batch)
        # Channel 9 = is_given
        # First puzzle, cell 0: puzzle=5 -> is_given=1
        assert x[0, 0, 9].item() == 1.0
        # First puzzle, cell 2: puzzle=0 -> is_given=0
        assert x[0, 2, 9].item() == 0.0

    def test_single_item_batch(self):
        import torch
        batch = [
            (np.array([1] * 81, dtype=np.int8), np.array([5] * 81, dtype=np.int8))
        ]
        x, y, given = sudoku_collate_fn(batch)
        assert x.shape == (1, 81, 10)
        assert y.shape == (1, 81)
        assert (given == 1.0).all()

    def test_all_zeros_puzzle(self):
        import torch
        batch = [
            (np.zeros(81, dtype=np.int8), np.ones(81, dtype=np.int8) * 9)
        ]
        x, y, given = sudoku_collate_fn(batch)
        assert (given == 0.0).all()
        # All digit channels should be 0 for empty puzzle
        for d in range(9):
            assert (x[0, :, d] == 0.0).all()
