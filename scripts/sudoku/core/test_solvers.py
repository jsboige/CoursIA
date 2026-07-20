"""Tests for the Norvig constraint-propagation solver (scripts/sudoku/core/solvers.py).

Covers the two public symbols exported by ``sudoku.core``: ``solve_sudoku`` and
``is_valid_puzzle``. The solver was previously untested at unit level (only
``_archived/test_student.py`` exists, which exercises a different path); these
tests pin the behaviour the package exposes to callers:

- ``solve_sudoku`` returns a fully solved grid that preserves every given clue,
  rejects unsolvable inputs (direct conflicts) with ``None``, and handles the
  fully-empty grid.
- ``is_valid_puzzle`` detects a duplicate non-zero value in a row, a column, or
  a 3x3 box, and accepts the valid puzzle plus the all-empty grid.

Run with: pytest scripts/sudoku/core/test_solvers.py -v
"""

import sys
from pathlib import Path

import numpy as np
import pytest

# Insert this module's own directory (scripts/sudoku/core/) so ``from solvers
# import ...`` resolves without requiring scripts/sudoku/__init__.py (which does
# not exist; only core/ is a package).
sys.path.insert(0, str(Path(__file__).parent))

from solvers import solve_sudoku, is_valid_puzzle  # noqa: E402


# A standard easy puzzle (0 = empty). Used as the canonical valid fixture.
_PUZZLE = np.array([
    5, 3, 0, 0, 7, 0, 0, 0, 0,
    6, 0, 0, 1, 9, 5, 0, 0, 0,
    0, 9, 8, 0, 0, 0, 0, 6, 0,
    8, 0, 0, 0, 6, 0, 0, 0, 3,
    4, 0, 0, 8, 0, 3, 0, 0, 1,
    7, 0, 0, 0, 2, 0, 0, 0, 6,
    0, 6, 0, 0, 0, 0, 2, 8, 0,
    0, 0, 0, 4, 1, 9, 0, 0, 5,
    0, 0, 0, 0, 8, 0, 0, 7, 9,
], dtype=np.int64)


def _is_solved(grid):
    """A solved grid has every row, column, and 3x3 box filled with 1-9 exactly."""
    g = grid.reshape(9, 9)
    target = set(range(1, 10))
    for r in range(9):
        if set(g[r].tolist()) != target:
            return False
    for c in range(9):
        if set(g[:, c].tolist()) != target:
            return False
    for br in range(0, 9, 3):
        for bc in range(0, 9, 3):
            if set(g[br:br + 3, bc:bc + 3].flatten().tolist()) != target:
                return False
    return True


class TestSolveSudoku:
    """solve_sudoku: constraint propagation + MRV backtracking."""

    def test_returns_valid_solution(self):
        """The returned grid is a complete, consistent Sudoku solution."""
        sol = solve_sudoku(_PUZZLE)
        assert sol is not None
        assert _is_solved(sol)

    def test_preserves_given_clues(self):
        """Every non-zero clue must be unchanged in the solution."""
        sol = solve_sudoku(_PUZZLE)
        clues = _PUZZLE != 0
        np.testing.assert_array_equal(sol[clues], _PUZZLE[clues])

    def test_shape_and_dtype(self):
        """Contract: returns an (81,) int64 array (np.int64), per docstring."""
        sol = solve_sudoku(_PUZZLE)
        assert sol.shape == (81,)
        assert sol.dtype == np.int64

    def test_unsolvable_returns_none(self):
        """Two identical non-zero values in the same unit -> None (no solution)."""
        unsolvable = np.zeros(81, dtype=np.int64)
        unsolvable[0] = 1
        unsolvable[1] = 1  # both in row 0
        assert solve_sudoku(unsolvable) is None

    def test_empty_grid_solvable(self):
        """A fully empty grid has many solutions; the solver returns one of them."""
        sol = solve_sudoku(np.zeros(81, dtype=np.int64))
        assert sol is not None
        assert _is_solved(sol)


class TestIsValidPuzzle:
    """is_valid_puzzle: fast pre-check for duplicate non-zero values."""

    def test_valid_puzzle_true(self):
        assert is_valid_puzzle(_PUZZLE) is True

    def test_all_empty_true(self):
        assert is_valid_puzzle(np.zeros(81, dtype=np.int64)) is True

    def test_duplicate_in_row_false(self):
        p = _PUZZLE.copy()
        p[0] = 5
        p[1] = 5  # cells 0 and 1 are both in row 0
        assert is_valid_puzzle(p) is False

    def test_duplicate_in_col_false(self):
        p = _PUZZLE.copy()
        p[0] = 5
        p[9] = 5  # cells 0 and 9 are both in column 0
        assert is_valid_puzzle(p) is False

    def test_duplicate_in_box_false(self):
        p = _PUZZLE.copy()
        p[0] = 5
        p[10] = 5  # cells 0 and 10 are both in the top-left 3x3 box
        assert is_valid_puzzle(p) is False


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
