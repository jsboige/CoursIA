"""Constraint-propagation solvers for Sudoku (Norvig-style)."""

import numpy as np

_DIGITS = '123456789'


def _build_units_peers():
    units = [[] for _ in range(81)]
    peers = [None] * 81
    all_units = []
    for r in range(9):
        all_units.append([r * 9 + c for c in range(9)])
    for c in range(9):
        all_units.append([r * 9 + c for r in range(9)])
    for br in range(0, 9, 3):
        for bc in range(0, 9, 3):
            all_units.append([(br + dr) * 9 + (bc + dc) for dr in range(3) for dc in range(3)])
    for i in range(81):
        units[i] = [u for u in all_units if i in u]
        peer_set = set()
        for u in units[i]:
            peer_set.update(u)
        peer_set.discard(i)
        peers[i] = tuple(peer_set)
    return all_units, units, peers


_UNITS, _CELL_UNITS, _PEERS = _build_units_peers()


def _fill(grid, s, d):
    """Eliminate all digits except d from grid[s]."""
    if grid[s] == d:
        return grid
    other = grid[s].replace(d, '')
    for d2 in other:
        grid = _eliminate(grid, s, d2)
        if grid is None:
            return None
    return grid


def _eliminate(grid, s, d):
    """Eliminate d from grid[s]; propagate naked singles + hidden singles."""
    if d not in grid[s]:
        return grid
    grid[s] = grid[s].replace(d, '')
    val = grid[s]
    if len(val) == 0:
        return None
    if len(val) == 1:
        for p in _PEERS[s]:
            grid = _eliminate(grid, p, val)
            if grid is None:
                return None
    for u in _CELL_UNITS[s]:
        dplaces = [sq for sq in u if d in grid[sq]]
        if len(dplaces) == 0:
            return None
        if len(dplaces) == 1:
            grid = _fill(grid, dplaces[0], d)
            if grid is None:
                return None
    return grid


def _search(grid):
    """MRV backtracking search."""
    if grid is None:
        return None
    min_len, best = 10, -1
    for s in range(81):
        n = len(grid[s])
        if 1 < n < min_len:
            min_len, best = n, s
    if best == -1:
        return grid
    for d in grid[best]:
        result = _search(_fill(grid.copy(), best, d))
        if result is not None:
            return result
    return None


def solve_sudoku(puzzle_81):
    """Norvig solver: constraint propagation + MRV backtracking. ~3ms/puzzle.

    Args:
        puzzle_81: (81,) int array, 0 = empty cell.

    Returns:
        (81,) int array with solution, or None if unsolvable.
    """
    grid = {i: _DIGITS for i in range(81)}
    for i in range(81):
        if puzzle_81[i] != 0:
            d = str(puzzle_81[i])
            grid = _fill(grid, i, d)
            if grid is None:
                return None
    result = _search(grid)
    if result is None:
        return None
    return np.array([int(result[i]) for i in range(81)], dtype=np.int64)


def is_valid_puzzle(puzzle_81):
    """Quick check: no duplicate non-zero values in any row/col/box."""
    for i in range(81):
        if puzzle_81[i] == 0:
            continue
        val = puzzle_81[i]
        r, c = divmod(i, 9)
        br, bc = (r // 3) * 3, (c // 3) * 3
        for cc in range(9):
            if cc != c and puzzle_81[r * 9 + cc] == val:
                return False
        for rr in range(9):
            if rr != r and puzzle_81[rr * 9 + c] == val:
                return False
        for dr in range(3):
            for dc in range(3):
                j = (br + dr) * 9 + (bc + dc)
                if j != i and puzzle_81[j] == val:
                    return False
    return True
