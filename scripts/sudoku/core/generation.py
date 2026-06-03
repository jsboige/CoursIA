"""Puzzle generation utilities."""

import numpy as np


def generate_complete_grid(rng=None):
    """Generate a complete valid Sudoku grid via backtracking with randomization."""
    if rng is None:
        rng = np.random.RandomState()

    def solve(grid, pos=0):
        if pos == 81:
            return True
        r, c = divmod(pos, 9)
        nums = list(range(1, 10))
        rng.shuffle(nums)
        for n in nums:
            if _can_place(grid, r, c, n):
                grid[r][c] = n
                if solve(grid, pos + 1):
                    return True
                grid[r][c] = 0
        return False

    grid = np.zeros((9, 9), dtype=np.int64)
    solve(grid)
    return grid


def _can_place(grid, r, c, num):
    if num in grid[r]:
        return False
    if num in grid[:, c]:
        return False
    br, bc = (r // 3) * 3, (c // 3) * 3
    if num in grid[br:br+3, bc:bc+3]:
        return False
    return True


def generate_puzzles(n, n_empty_range=(30, 55), seed=42):
    """Generate n puzzles with controlled difficulty (number of empty cells)."""
    rng = np.random.RandomState(seed)
    puzzles = np.zeros((n, 81), dtype=np.int64)
    solutions = np.zeros((n, 81), dtype=np.int64)

    for i in range(n):
        grid = generate_complete_grid(rng)
        solutions[i] = grid.flatten()
        n_empty = rng.randint(n_empty_range[0], n_empty_range[1] + 1)
        mask = rng.choice(81, n_empty, replace=False)
        puzzle = grid.flatten().copy()
        puzzle[mask] = 0
        puzzles[i] = puzzle
        if (i + 1) % 1000 == 0:
            print(f"  Generated {i+1}/{n} puzzles")

    return puzzles, solutions
