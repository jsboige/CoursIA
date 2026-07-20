#!/usr/bin/env python3
"""
Tests for scripts/sudoku/core/generation.py

Covers: generate_complete_grid, generate_puzzles.
Pure computation on CPU. Deterministic with fixed seed.

LIVE: 5 callers (cpu_diagnostic.py, train_baselines_comparison.py,
train_classical.py, +2 archived).
"""

import numpy as np
import pytest
import sys
from pathlib import Path

# Add sudoku/core to sys.path
_sudoku_core = str(Path(__file__).resolve().parent.parent / "sudoku" / "core")
if _sudoku_core not in sys.path:
    sys.path.insert(0, _sudoku_core)

from generation import generate_complete_grid, generate_puzzles
from solvers import is_valid_puzzle


# ─── generate_complete_grid ──────────────────────────────────────────


class TestGenerateCompleteGrid:
    def test_shape(self):
        grid = generate_complete_grid()
        assert grid.shape == (9, 9)

    def test_dtype(self):
        grid = generate_complete_grid()
        assert grid.dtype == np.int64

    def test_values_in_range(self):
        grid = generate_complete_grid()
        assert grid.min() >= 1
        assert grid.max() <= 9

    def test_no_zeros(self):
        grid = generate_complete_grid()
        assert np.all(grid > 0)

    def test_rows_valid(self):
        """Each row contains digits 1-9 exactly once."""
        grid = generate_complete_grid()
        for r in range(9):
            assert set(grid[r]) == set(range(1, 10))

    def test_cols_valid(self):
        """Each column contains digits 1-9 exactly once."""
        grid = generate_complete_grid()
        for c in range(9):
            assert set(grid[:, c]) == set(range(1, 10))

    def test_boxes_valid(self):
        """Each 3x3 box contains digits 1-9 exactly once."""
        grid = generate_complete_grid()
        for br in range(3):
            for bc in range(3):
                box = grid[br*3:br*3+3, bc*3:bc*3+3].flatten()
                assert set(box) == set(range(1, 10))

    def test_deterministic_with_seed(self):
        """Same seed produces same grid."""
        rng1 = np.random.RandomState(42)
        rng2 = np.random.RandomState(42)
        g1 = generate_complete_grid(rng1)
        g2 = generate_complete_grid(rng2)
        assert np.array_equal(g1, g2)

    def test_different_seeds_different_grids(self):
        """Different seeds produce different grids."""
        g1 = generate_complete_grid(np.random.RandomState(1))
        g2 = generate_complete_grid(np.random.RandomState(2))
        assert not np.array_equal(g1, g2)

    def test_no_seed_produces_grid(self):
        """Calling without seed still works (uses default RandomState)."""
        grid = generate_complete_grid()
        assert grid.shape == (9, 9)
        assert np.all(grid > 0)

    def test_is_valid_sudoku(self):
        """Generated grid is a valid solved Sudoku."""
        grid = generate_complete_grid()
        flat = grid.flatten()
        assert is_valid_puzzle(flat)


# ─── generate_puzzles ────────────────────────────────────────────────


class TestGeneratePuzzles:
    def test_shape(self):
        puzzles, solutions = generate_puzzles(5, seed=42)
        assert puzzles.shape == (5, 81)
        assert solutions.shape == (5, 81)

    def test_dtype(self):
        puzzles, solutions = generate_puzzles(3, seed=42)
        assert puzzles.dtype == np.int64
        assert solutions.dtype == np.int64

    def test_solutions_complete(self):
        """Solutions should have no zeros."""
        _, solutions = generate_puzzles(5, seed=42)
        assert np.all(solutions > 0)

    def test_solutions_valid(self):
        """Each solution should be a valid Sudoku."""
        _, solutions = generate_puzzles(5, seed=42)
        for i in range(5):
            assert is_valid_puzzle(solutions[i])

    def test_puzzles_have_zeros(self):
        """Puzzles should have empty cells (zeros)."""
        puzzles, _ = generate_puzzles(5, n_empty_range=(30, 55), seed=42)
        for i in range(5):
            assert np.sum(puzzles[i] == 0) >= 30

    def test_puzzles_values_in_range(self):
        """Non-zero puzzle values must be 1-9."""
        puzzles, _ = generate_puzzles(5, seed=42)
        non_zero = puzzles[puzzles > 0]
        assert non_zero.min() >= 1
        assert non_zero.max() <= 9

    def test_given_cells_match_solution(self):
        """Non-zero cells in puzzle should match solution."""
        puzzles, solutions = generate_puzzles(10, seed=42)
        for i in range(10):
            mask = puzzles[i] > 0
            assert np.all(puzzles[i][mask] == solutions[i][mask])

    def test_empty_count_in_range(self):
        """Number of empty cells should be within specified range."""
        puzzles, _ = generate_puzzles(20, n_empty_range=(35, 45), seed=42)
        for i in range(20):
            n_empty = np.sum(puzzles[i] == 0)
            assert 35 <= n_empty <= 45

    def test_reproducible(self):
        """Same seed produces same puzzles."""
        p1, s1 = generate_puzzles(5, seed=99)
        p2, s2 = generate_puzzles(5, seed=99)
        assert np.array_equal(p1, p2)
        assert np.array_equal(s1, s2)

    def test_single_puzzle(self):
        puzzles, solutions = generate_puzzles(1, seed=42)
        assert puzzles.shape[0] == 1
        assert solutions.shape[0] == 1

    def test_custom_empty_range(self):
        """Minimal empty range."""
        puzzles, _ = generate_puzzles(5, n_empty_range=(20, 20), seed=42)
        for i in range(5):
            assert np.sum(puzzles[i] == 0) == 20


# ─── Cross-invariants ────────────────────────────────────────────────


class TestCrossInvariants:
    def test_generated_puzzle_solvable(self):
        """Generated puzzles should be solvable (valid solution, not necessarily unique)."""
        from solvers import solve_sudoku
        puzzles, _ = generate_puzzles(5, n_empty_range=(30, 40), seed=42)
        for i in range(5):
            result = solve_sudoku(puzzles[i])
            assert result is not None, f"Puzzle {i} not solvable"
            assert np.all(result > 0), f"Puzzle {i} solution has zeros"
            assert np.all(result <= 9), f"Puzzle {i} solution has values > 9"
            # Verify given cells preserved
            mask = puzzles[i] > 0
            assert np.all(result[mask] == puzzles[i][mask]), \
                f"Puzzle {i} solution changes given cells"

    def test_grid_flat_compatible_with_solver(self):
        """Flat grid is compatible with solver (81-element array)."""
        from solvers import solve_sudoku
        grid = generate_complete_grid(np.random.RandomState(7))
        flat = grid.flatten()
        assert len(flat) == 81
        assert is_valid_puzzle(flat)

    def test_puzzles_compatible_with_graph(self):
        """Generated puzzles should be compatible with graph edge construction."""
        from graph import build_sudoku_edge_index
        puzzles, _ = generate_puzzles(3, seed=42)
        edges = build_sudoku_edge_index()
        assert edges.shape[0] == 2
        # Each puzzle has 81 cells matching edge index nodes
        for i in range(3):
            assert len(puzzles[i]) == 81

    def test_generate_then_solve_hard(self):
        """Harder puzzles (more empties) still solvable."""
        from solvers import solve_sudoku
        puzzles, _ = generate_puzzles(3, n_empty_range=(50, 55), seed=123)
        for i in range(3):
            result = solve_sudoku(puzzles[i])
            assert result is not None, f"Hard puzzle {i} not solvable"
            assert np.all(result > 0), f"Hard puzzle {i} solution has zeros"
            mask = puzzles[i] > 0
            assert np.all(result[mask] == puzzles[i][mask]), \
                f"Hard puzzle {i} solution changes given cells"


# ─── Degenerate-input guard (bug-class #7554/#7551) ──────────────────


class TestGeneratePuzzlesGuard:
    """generate_puzzles must reject degenerate inputs explicitly.

    Without the guards, degenerate inputs produce silent wrong results or
    crash far from the call site:
      - n=0           -> np.zeros((0,81)) allocated, range(0) body skipped,
                         returns empty arrays shape (0,81) silently (no error).
      - n=-2          -> np.zeros((-2,81)) raises opaque numpy
                         ``negative dimensions are not allowed``.
      - n_empty_range=(50,30) (inverted) -> rng.randint(50,31) raises opaque
                         numpy ``low >= high`` once the loop reaches it.

    Same degenerate-input bug-class as make_batch_edge_index batch_size<=0
    (#7554), WFC rows<=0 (#7551), Tournament repetitions<=0 (#7544)."""

    def test_n_zero_raises(self):
        with pytest.raises(ValueError, match="n must be positive"):
            generate_puzzles(0)

    def test_n_negative_raises(self):
        with pytest.raises(ValueError, match="n must be positive"):
            generate_puzzles(-5)

    def test_inverted_empty_range_raises(self):
        with pytest.raises(ValueError, match="n_empty_range must be non-decreasing"):
            generate_puzzles(5, n_empty_range=(50, 30))

    def test_equal_bounds_allowed(self):
        """Equal lo==hi is valid (randint(a, a+1) == a always) and must NOT raise."""
        puzzles, _ = generate_puzzles(3, n_empty_range=(40, 40), seed=7)
        for i in range(3):
            assert np.sum(puzzles[i] == 0) == 40

    def test_positive_n_unaffected(self):
        """The guard does not impact the normal path (shape + reproducibility)."""
        puzzles, solutions = generate_puzzles(4, seed=42)
        assert puzzles.shape == (4, 81)
        assert solutions.shape == (4, 81)
