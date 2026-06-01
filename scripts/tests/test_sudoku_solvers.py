#!/usr/bin/env python3
"""
Tests for scripts/sudoku/core/solvers.py

Covers Norvig-style constraint propagation solver:
- solve_sudoku: full solver (constraint propagation + MRV backtracking)
- is_valid_puzzle: duplicate check in rows/cols/boxes
- Edge cases: empty puzzle, full puzzle, unsolvable, multiple solutions
"""

import numpy as np
import pytest
import sys
from pathlib import Path

# Add sudoku/core to sys.path
_sudoku_core = str(Path(__file__).resolve().parent.parent / "sudoku" / "core")
if _sudoku_core not in sys.path:
    sys.path.insert(0, _sudoku_core)

from solvers import solve_sudoku, is_valid_puzzle


# ─── Helpers ──────────────────────────────────────────────────────────


def _puzzle(*rows):
    """Build an 81-element numpy array from 9 row strings."""
    s = "".join(rows)
    return np.array([int(c) for c in s], dtype=np.int64)


def _solved_sudoku():
    """A known valid solved Sudoku grid."""
    return _puzzle(
        "534678912",
        "672195348",
        "198342567",
        "859761423",
        "426853791",
        "713924856",
        "961537284",
        "287419635",
        "345286179",
    )


# ─── is_valid_puzzle ──────────────────────────────────────────────────


class TestIsValidPuzzle:
    def test_valid_complete_grid(self):
        p = _solved_sudoku()
        assert is_valid_puzzle(p) is True

    def test_valid_partial_grid(self):
        p = _puzzle(
            "530070900",
            "600195000",
            "098000060",
            "800060003",
            "400803001",
            "700020006",
            "060000280",
            "000419005",
            "000080079",
        )
        assert is_valid_puzzle(p) is True

    def test_empty_grid(self):
        p = np.zeros(81, dtype=np.int64)
        assert is_valid_puzzle(p) is True

    def test_duplicate_in_row(self):
        p = _solved_sudoku().copy()
        p[0] = 5  # row 0 already has 5 at index 0 — now duplicate at [0,0]
        # Actually [0,0]=5 is already there, so make a real duplicate
        p[1] = 5  # row 0 now has 5 at positions 0 AND 1
        assert is_valid_puzzle(p) is False

    def test_duplicate_in_col(self):
        p = _solved_sudoku().copy()
        # Column 0: 5,6,1,8,4,7,9,2,3 — set row 1 col 0 to 5
        p[9] = 5  # was 6, now 5 — duplicate with p[0]=5 in col 0
        assert is_valid_puzzle(p) is False

    def test_duplicate_in_box(self):
        p = _solved_sudoku().copy()
        # Box (0,0) = rows 0-2, cols 0-2: 5,3,4, 6,7,2, 1,9,8
        p[1] = 5  # was 3, now duplicate 5 in box (0,0) with p[0]=5
        assert is_valid_puzzle(p) is False

    def test_single_nonzero_cell(self):
        p = np.zeros(81, dtype=np.int64)
        p[0] = 5
        assert is_valid_puzzle(p) is True

    def test_all_same_value(self):
        p = np.full(81, 5, dtype=np.int64)
        assert is_valid_puzzle(p) is False

    def test_valid_with_zeros_scattered(self):
        """Zeros (empty cells) should not cause false negatives."""
        p = _solved_sudoku().copy()
        p[0:5] = 0  # clear first 5 cells
        assert is_valid_puzzle(p) is True


# ─── solve_sudoku ─────────────────────────────────────────────────────


class TestSolveSudoku:
    def test_easy_puzzle(self):
        puzzle = _puzzle(
            "530070900",
            "600195000",
            "098000060",
            "800060003",
            "400803001",
            "700020006",
            "060000280",
            "000419005",
            "000080079",
        )
        result = solve_sudoku(puzzle)
        assert result is not None
        assert len(result) == 81
        # Verify all cells filled (no zeros)
        assert np.all(result > 0)
        # Verify solution is valid
        assert is_valid_puzzle(result)

    def test_already_solved(self):
        p = _solved_sudoku()
        result = solve_sudoku(p)
        assert result is not None
        assert np.array_equal(result, p)

    def test_empty_puzzle(self):
        """Empty puzzle (all zeros) should have a solution."""
        p = np.zeros(81, dtype=np.int64)
        result = solve_sudoku(p)
        assert result is not None
        assert np.all(result > 0)
        assert is_valid_puzzle(result)

    def test_returns_numpy_array(self):
        puzzle = _puzzle(
            "530070900",
            "600195000",
            "098000060",
            "800060003",
            "400803001",
            "700020006",
            "060000280",
            "000419005",
            "000080079",
        )
        result = solve_sudoku(puzzle)
        assert isinstance(result, np.ndarray)
        assert result.dtype == np.int64

    def test_unsolvable_puzzle(self):
        """Row with two identical values should be unsolvable."""
        p = np.zeros(81, dtype=np.int64)
        p[0] = 5
        p[1] = 5  # Two 5s in row 0
        result = solve_sudoku(p)
        assert result is None

    def test_preserves_given_cells(self):
        puzzle = _puzzle(
            "530070900",
            "600195000",
            "098000060",
            "800060003",
            "400803001",
            "700020006",
            "060000280",
            "000419005",
            "000080079",
        )
        result = solve_sudoku(puzzle)
        assert result is not None
        # Given cells should be preserved
        given_mask = puzzle > 0
        assert np.all(result[given_mask] == puzzle[given_mask])

    def test_hard_puzzle(self):
        """A hard puzzle (many empty cells, requires backtracking)."""
        puzzle = _puzzle(
            "800000000",
            "003600000",
            "070090200",
            "050007000",
            "000045700",
            "000100030",
            "001000068",
            "008500010",
            "090000400",
        )
        result = solve_sudoku(puzzle)
        assert result is not None
        assert is_valid_puzzle(result)

    def test_solution_values_in_range(self):
        puzzle = _puzzle(
            "530070900",
            "600195000",
            "098000060",
            "800060003",
            "400803001",
            "700020006",
            "060000280",
            "000419005",
            "000080079",
        )
        result = solve_sudoku(puzzle)
        assert result is not None
        assert np.all(result >= 1)
        assert np.all(result <= 9)

    def test_single_empty_cell(self):
        p = _solved_sudoku().copy()
        p[40] = 0  # Remove one cell
        result = solve_sudoku(p)
        assert result is not None
        assert result[40] != 0

    def test_unsolvable_conflict_in_box(self):
        p = np.zeros(81, dtype=np.int64)
        p[0] = 1
        p[1] = 1  # Duplicate in box (0,0)
        result = solve_sudoku(p)
        assert result is None

    def test_unsolvable_conflict_in_col(self):
        p = np.zeros(81, dtype=np.int64)
        p[0] = 7
        p[9] = 7  # Same column (col 0), different rows
        result = solve_sudoku(p)
        assert result is None


# ─── Cross-invariants ────────────────────────────────────────────────


class TestCrossInvariants:
    def test_solve_produces_valid_puzzle(self):
        """Every solve_sudoku result must pass is_valid_puzzle."""
        puzzle = _puzzle(
            "530070900",
            "600195000",
            "098000060",
            "800060003",
            "400803001",
            "700020006",
            "060000280",
            "000419005",
            "000080079",
        )
        result = solve_sudoku(puzzle)
        assert result is not None
        assert is_valid_puzzle(result)

    def test_valid_complete_grid_is_solvable(self):
        """A valid complete grid should solve to itself."""
        p = _solved_sudoku()
        assert is_valid_puzzle(p) is True
        result = solve_sudoku(p)
        assert np.array_equal(result, p)

    def test_invalid_puzzle_fails_both_checks(self):
        """Invalid puzzle: is_valid_puzzle=False AND solve_sudoku=None."""
        p = np.zeros(81, dtype=np.int64)
        p[0] = 5
        p[1] = 5  # Duplicate in row
        assert is_valid_puzzle(p) is False
        assert solve_sudoku(p) is None

    def test_solve_multiple_puzzles_consistent(self):
        """Solving the same puzzle twice gives the same answer."""
        puzzle = _puzzle(
            "530070900",
            "600195000",
            "098000060",
            "800060003",
            "400803001",
            "700020006",
            "060000280",
            "000419005",
            "000080079",
        )
        r1 = solve_sudoku(puzzle)
        r2 = solve_sudoku(puzzle)
        assert np.array_equal(r1, r2)
