#!/usr/bin/env python3
"""
Tests for scripts/sudoku/core/solvers.py

Covers: is_valid_puzzle (valid/invalid grids, edge cases),
solve_sudoku (solving, unsolvable, edge cases).
Pure computation on CPU. Deterministic.

LIVE: 8+ callers (generation.py, evaluate.py, train_classical.py,
train_baselines_comparison.py, cpu_diagnostic.py, +3 archived).
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


def _solved_grid():
    """A known valid solved Sudoku grid (81-element array, 1-9)."""
    return np.array([
        5, 3, 4, 6, 7, 8, 9, 1, 2,
        6, 7, 2, 1, 9, 5, 3, 4, 8,
        1, 9, 8, 3, 4, 2, 5, 6, 7,
        8, 5, 9, 7, 6, 1, 4, 2, 3,
        4, 2, 6, 8, 5, 3, 7, 9, 1,
        7, 1, 3, 9, 2, 4, 8, 5, 6,
        9, 6, 1, 5, 3, 7, 2, 8, 4,
        2, 8, 7, 4, 1, 9, 6, 3, 5,
        3, 4, 5, 2, 8, 6, 1, 7, 9,
    ], dtype=np.int64)


def _easy_puzzle():
    """Puzzle with a few empty cells (zeros). Solvable."""
    grid = _solved_grid().copy()
    # Remove 10 cells
    for idx in [0, 5, 12, 20, 30, 40, 50, 60, 70, 80]:
        grid[idx] = 0
    return grid


def _hard_puzzle():
    """Puzzle with many empty cells. Still solvable."""
    grid = _solved_grid().copy()
    # Remove ~40 cells
    rng = np.random.RandomState(42)
    indices = rng.choice(81, size=40, replace=False)
    grid[indices] = 0
    return grid


# ─── is_valid_puzzle ──────────────────────────────────────────────────


class TestIsValidPuzzle:
    def test_solved_grid_is_valid(self):
        grid = _solved_grid()
        assert is_valid_puzzle(grid) is True

    def test_all_zeros_is_valid(self):
        """Empty grid has no conflicts."""
        grid = np.zeros(81, dtype=np.int64)
        assert is_valid_puzzle(grid) is True

    def test_single_value_is_valid(self):
        grid = np.zeros(81, dtype=np.int64)
        grid[0] = 5
        assert is_valid_puzzle(grid) is True

    def test_duplicate_in_row(self):
        grid = _solved_grid().copy()
        grid[1] = grid[0]  # Row 0 now has two 5s
        assert is_valid_puzzle(grid) is False

    def test_duplicate_in_col(self):
        grid = _solved_grid().copy()
        grid[9] = grid[0]  # Col 0 now has two 5s
        assert is_valid_puzzle(grid) is False

    def test_duplicate_in_box(self):
        grid = _solved_grid().copy()
        # Box (0,0) cells: indices 0,1,2,9,10,11,18,19,20
        grid[1] = grid[0]  # Same box duplicate
        assert is_valid_puzzle(grid) is False

    def test_puzzle_with_zeros_valid(self):
        """Puzzle with empty cells but no conflicts is valid."""
        grid = _easy_puzzle()
        assert is_valid_puzzle(grid) is True

    def test_puzzle_with_conflict_invalid(self):
        grid = _easy_puzzle()
        # Force a conflict: set two cells in same row to same value
        grid[0] = 5
        grid[1] = 5
        assert is_valid_puzzle(grid) is False

    def test_accepts_list(self):
        """Should work with Python list (not just numpy array)."""
        grid = _solved_grid().tolist()
        assert is_valid_puzzle(grid) is True

    def test_returns_bool(self):
        grid = _solved_grid()
        result = is_valid_puzzle(grid)
        assert isinstance(result, bool)

    def test_full_grid_all_same_invalid(self):
        """Grid full of 1s is invalid."""
        grid = np.ones(81, dtype=np.int64)
        assert is_valid_puzzle(grid) is False


# ─── solve_sudoku ─────────────────────────────────────────────────────


class TestSolveSudoku:
    def test_solved_grid_stays_solved(self):
        """Already-solved grid: solution should be identical."""
        grid = _solved_grid()
        # No zeros, so it's already solved
        result = solve_sudoku(grid)
        assert result is not None
        assert np.array_equal(result, grid)

    def test_easy_puzzle_solved(self):
        puzzle = _easy_puzzle()
        result = solve_sudoku(puzzle)
        assert result is not None
        assert np.all(result > 0), "Solution should have no zeros"
        assert np.all(result <= 9), "Solution values should be 1-9"

    def test_easy_puzzle_preserves_given(self):
        """Given (non-zero) cells must be preserved in solution."""
        puzzle = _easy_puzzle()
        result = solve_sudoku(puzzle)
        assert result is not None
        mask = puzzle > 0
        assert np.all(result[mask] == puzzle[mask])

    def test_easy_puzzle_valid_solution(self):
        """Solution must be a valid Sudoku."""
        puzzle = _easy_puzzle()
        result = solve_sudoku(puzzle)
        assert result is not None
        assert is_valid_puzzle(result)

    def test_hard_puzzle_solved(self):
        """Harder puzzle (more empties) still solvable."""
        puzzle = _hard_puzzle()
        result = solve_sudoku(puzzle)
        assert result is not None
        assert np.all(result > 0)
        mask = puzzle > 0
        assert np.all(result[mask] == puzzle[mask])

    def test_unsolvable_returns_none(self):
        """Puzzle with conflicting given cells returns None."""
        grid = np.zeros(81, dtype=np.int64)
        grid[0] = 5
        grid[1] = 5  # Same row has two 5s
        result = solve_sudoku(grid)
        assert result is None

    def test_empty_grid_solved(self):
        """Empty grid (all zeros) should be solvable."""
        grid = np.zeros(81, dtype=np.int64)
        result = solve_sudoku(grid)
        assert result is not None
        assert np.all(result > 0)
        assert is_valid_puzzle(result)

    def test_returns_int64_array(self):
        puzzle = _easy_puzzle()
        result = solve_sudoku(puzzle)
        assert result is not None
        assert result.dtype == np.int64

    def test_returns_81_elements(self):
        puzzle = _easy_puzzle()
        result = solve_sudoku(puzzle)
        assert result is not None
        assert result.shape == (81,)

    def test_single_empty_cell(self):
        """Grid with exactly one empty cell."""
        grid = _solved_grid().copy()
        grid[40] = 0
        result = solve_sudoku(grid)
        assert result is not None
        assert result[40] == _solved_grid()[40]


# ─── Cross-invariants ─────────────────────────────────────────────────


class TestCrossInvariants:
    def test_solve_then_validate(self):
        """Solve a puzzle, then verify the solution is valid."""
        puzzle = _hard_puzzle()
        solution = solve_sudoku(puzzle)
        assert solution is not None
        assert is_valid_puzzle(solution)

    def test_solve_finds_valid_solution_for_generated(self):
        """Solve should find a valid solution for generated puzzles.

        Note: puzzles with many empty cells may have multiple valid solutions,
        so we check validity and given-cell preservation, not exact match.
        """
        from generation import generate_puzzles
        puzzles, solutions = generate_puzzles(5, seed=42)
        for i in range(5):
            result = solve_sudoku(puzzles[i])
            assert result is not None, f"Puzzle {i} unsolvable"
            assert is_valid_puzzle(result), f"Puzzle {i}: solution invalid"
            # Given cells must be preserved
            mask = puzzles[i] > 0
            assert np.all(result[mask] == puzzles[i][mask]), \
                f"Puzzle {i}: solution changes given cells"

    def test_solve_compatible_with_graph(self):
        """Solved output is compatible with graph edge construction."""
        from graph import build_sudoku_edge_index
        puzzle = _easy_puzzle()
        result = solve_sudoku(puzzle)
        assert result is not None
        edges = build_sudoku_edge_index()
        # Edges reference 81 nodes, solution has 81 cells
        assert edges.max() < len(result)

    def test_valid_puzzle_indices_covered(self):
        """is_valid_puzzle checks all 81 cells."""
        grid = np.zeros(81, dtype=np.int64)
        # Place a conflict at the last cell
        grid[80] = 5
        grid[8] = 5  # Same row (row 8)
        assert is_valid_puzzle(grid) is False
