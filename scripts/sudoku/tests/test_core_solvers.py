#!/usr/bin/env python3
"""Tests pour scripts/sudoku/core/solvers.py + generation.py — le moteur de
resolution CSP Sudoku (Norvig constraint-propagation + MRV backtracking).

Couvre solve_sudoku (resolution + clue-consistency + unsolvable), is_valid_puzzle
(duplicates row/col/box), _build_units_peers (structure 27 units / 20 peers),
generate_complete_grid (grille valide + reproductibilite), _can_place (conflits),
generate_puzzles (shapes + reproductibilite + pin lo==hi + 3 ValueErrors) et le
round-trip generate -> solve (integration hermetique).

Import direct par chemin (sys.path.insert sur core/) pour contourner le
core/__init__.py qui force-importe torch (models/graph/dataset) : ces tests
restent numpy-only, hermetiques, sans torch.
"""

import sys
from pathlib import Path

import numpy as np
import pytest

HERE = Path(__file__).resolve().parent
CORE_DIR = HERE.parent / "core"
sys.path.insert(0, str(CORE_DIR))

import solvers  # noqa: E402  (numpy-only, __init__.py torch chain bypassed)
import generation  # noqa: E402

np = pytest.importorskip("numpy")


# --------------------------------------------------------------------------
# Helpers — validity of a complete 9x9 Sudoku grid
# --------------------------------------------------------------------------

def _is_complete_valid(arr81):
    """True si la grille 81 est complete ET valide (lignes/colonnes/box = 1..9)."""
    if arr81 is None:
        return False
    g = np.asarray(arr81).reshape(9, 9)
    full = set(range(1, 10))
    for r in range(9):
        if set(g[r]) != full:
            return False
    for c in range(9):
        if set(g[:, c]) != full:
            return False
    for br in range(0, 9, 3):
        for bc in range(0, 9, 3):
            if set(g[br:br + 3, bc:bc + 3].flatten()) != full:
                return False
    return True


# Wikipedia Sudoku (exemple canonique) + sa solution unique.
_WIKI_PUZZLE = np.array([
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


# --------------------------------------------------------------------------
# solve_sudoku — resolution, clue-consistency, unsolvable, empty, ValueError
# --------------------------------------------------------------------------

def test_solve_sudoku_returns_complete_valid_grid():
    sol = solvers.solve_sudoku(_WIKI_PUZZLE)
    assert sol is not None
    assert sol.shape == (81,)
    assert _is_complete_valid(sol)


def test_solve_sudoku_solution_consistent_with_clues():
    """La solution respecte les indices non-nuls du puzzle de depart."""
    sol = solvers.solve_sudoku(_WIKI_PUZZLE)
    clues = _WIKI_PUZZLE != 0
    assert np.all(sol[clues] == _WIKI_PUZZLE[clues])


def test_solve_sudoku_unsolvable_conflict_returns_none():
    """Deux 5 dans la ligne 0 -> propagation echoue -> None."""
    bad = np.zeros(81, dtype=np.int64)
    bad[0] = 5
    bad[1] = 5  # meme ligne, meme chiffre
    assert solvers.solve_sudoku(bad) is None


def test_solve_sudoku_empty_grid_returns_valid_complete():
    """Grille entierement vide -> une solution complete valide (le solveur
    backtracks jusqu'a une grille valide)."""
    sol = solvers.solve_sudoku(np.zeros(81, dtype=np.int64))
    assert sol is not None
    assert _is_complete_valid(sol)


def test_solve_sudoku_wrong_length_raises():
    with pytest.raises(ValueError, match="81 cells"):
        solvers.solve_sudoku(np.zeros(80, dtype=np.int64))
    with pytest.raises(ValueError, match="81 cells"):
        solvers.solve_sudoku(np.zeros(82, dtype=np.int64))


# --------------------------------------------------------------------------
# is_valid_puzzle — duplicates row/col/box, zeros ok, ValueError
# --------------------------------------------------------------------------

def test_is_valid_puzzle_accepts_clean_puzzle():
    assert solvers.is_valid_puzzle(_WIKI_PUZZLE) is True


def test_is_valid_puzzle_rejects_row_duplicate():
    # Grille vide + un seul doublon dans la ligne 0 (cells (0,0) et (0,5)),
    # sans conflit de colonne ni de box -> echec imputable uniquement a la ligne.
    bad = np.zeros(81, dtype=np.int64)
    bad[0] = 5   # cell (0,0) box top-left
    bad[5] = 5   # cell (0,5) meme ligne 0, box top-mid (box differente)
    assert solvers.is_valid_puzzle(bad) is False


def test_is_valid_puzzle_rejects_col_duplicate():
    bad = np.zeros(81, dtype=np.int64)
    bad[0] = 9    # cell (0,0)
    bad[72] = 9   # cell (8,0) meme colonne
    assert solvers.is_valid_puzzle(bad) is False


def test_is_valid_puzzle_rejects_box_duplicate():
    bad = np.zeros(81, dtype=np.int64)
    bad[0] = 4    # cell (0,0) box top-left
    bad[20] = 4   # cell (2,2) meme box top-left
    assert solvers.is_valid_puzzle(bad) is False


def test_is_valid_puzzle_all_zeros_is_valid():
    assert solvers.is_valid_puzzle(np.zeros(81, dtype=np.int64)) is True


def test_is_valid_puzzle_wrong_length_raises():
    with pytest.raises(ValueError, match="81 cells"):
        solvers.is_valid_puzzle(np.zeros(10, dtype=np.int64))


# --------------------------------------------------------------------------
# _build_units_peers — structure (27 units, 3 units/cell, 20 peers/cell)
# --------------------------------------------------------------------------

def test_build_units_peers_structure():
    all_units, units, peers = solvers._build_units_peers()
    assert len(all_units) == 27  # 9 rows + 9 cols + 9 boxes
    assert all(len(u) == 81 for u in [units])  # units indexed by 81 cells
    assert len(units) == 81
    assert len(peers) == 81
    # Chaque cellule appartient a exactement 3 unites (sa ligne, sa colonne, sa box).
    assert all(len(units[i]) == 3 for i in range(81))
    # Chaque cellule a exactement 20 peers (8 row + 8 col + 4 box-only).
    assert all(len(peers[i]) == 20 for i in range(81))


def test_build_units_peers_cell0_peers():
    """Peers de la cellule 0 = voisins ligne0 (1-8) + col0 + box0-only."""
    _, _, peers = solvers._build_units_peers()
    p0 = set(peers[0])
    assert 0 not in p0
    # Ligne 0 : cells 1..8.
    assert {1, 2, 3, 4, 5, 6, 7, 8} <= p0
    # Colonne 0 : cells 9,18,...,72.
    assert {9, 18, 27, 36, 45, 54, 63, 72} <= p0
    # Box top-left only (hors ligne0/col0) : 10,11,19,20.
    assert {10, 11, 19, 20} <= p0
    assert len(p0) == 20


# --------------------------------------------------------------------------
# generate_complete_grid — grille valide + reproductibilite
# --------------------------------------------------------------------------

def test_generate_complete_grid_returns_valid_grid():
    rng = np.random.RandomState(0)
    g = generation.generate_complete_grid(rng)
    assert g.shape == (9, 9)
    assert _is_complete_valid(g.flatten())


def test_generate_complete_grid_reproducible_with_seed():
    g1 = generation.generate_complete_grid(np.random.RandomState(123))
    g2 = generation.generate_complete_grid(np.random.RandomState(123))
    assert np.array_equal(g1, g2)


# --------------------------------------------------------------------------
# _can_place — conflits row/col/box
# --------------------------------------------------------------------------

def _empty_grid():
    return np.zeros((9, 9), dtype=np.int64)


def test_can_place_empty_cell_accepts_digit():
    g = _empty_grid()
    assert generation._can_place(g, 0, 0, 5) is True


def test_can_place_rejects_row_conflict():
    g = _empty_grid()
    g[0][3] = 5  # meme ligne que (0,0)
    assert generation._can_place(g, 0, 0, 5) is False


def test_can_place_rejects_col_conflict():
    g = _empty_grid()
    g[4][0] = 5  # meme colonne que (0,0)
    assert generation._can_place(g, 0, 0, 5) is False


def test_can_place_rejects_box_conflict():
    g = _empty_grid()
    g[2][2] = 5  # meme box top-left que (0,0)
    assert generation._can_place(g, 0, 0, 5) is False


# --------------------------------------------------------------------------
# generate_puzzles — shapes, reproductibilite, pin lo==hi, 3 ValueErrors
# --------------------------------------------------------------------------

def test_generate_puzzles_shapes():
    puzzles, solutions = generation.generate_puzzles(5, seed=42)
    assert puzzles.shape == (5, 81)
    assert solutions.shape == (5, 81)
    # Les solutions sont des grilles completes valides.
    assert all(_is_complete_valid(s) for s in solutions)


def test_generate_puzzles_reproducible():
    p1, s1 = generation.generate_puzzles(3, seed=7)
    p2, s2 = generation.generate_puzzles(3, seed=7)
    assert np.array_equal(p1, p2)
    assert np.array_equal(s1, s2)


def test_generate_puzzles_puzzle_is_solution_with_holes():
    """puzzle[i] vaut 0 (trou) ou solutions[i] (indice conserve)."""
    puzzles, solutions = generation.generate_puzzles(4, seed=99)
    for p, s in zip(puzzles, solutions):
        # La ou puzzle != 0, il doit egaler la solution.
        keep = p != 0
        assert np.all(p[keep] == s[keep])
        # La ou puzzle == 0, la solution est non-nulle (grille complete).
        assert np.all(s[p == 0] != 0)


def test_generate_puzzles_pin_difficulty_lo_eq_hi():
    """lo == hi epingle la difficulte : exactement 'lo' trous par puzzle."""
    pinned = 40
    puzzles, _ = generation.generate_puzzles(
        6, n_empty_range=(pinned, pinned), seed=3)
    for p in puzzles:
        assert int(np.sum(p == 0)) == pinned


def test_generate_puzzles_n_empty_within_range():
    lo, hi = 30, 50
    puzzles, _ = generation.generate_puzzles(8, n_empty_range=(lo, hi), seed=5)
    for p in puzzles:
        n_empty = int(np.sum(p == 0))
        assert lo <= n_empty <= hi


def test_generate_puzzles_n_le_zero_raises():
    with pytest.raises(ValueError, match="must be positive"):
        generation.generate_puzzles(0)
    with pytest.raises(ValueError, match="must be positive"):
        generation.generate_puzzles(-3)


def test_generate_puzzles_inverted_range_raises():
    with pytest.raises(ValueError, match="non-decreasing"):
        generation.generate_puzzles(2, n_empty_range=(50, 30))


def test_generate_puzzles_bounds_out_of_range_raises():
    with pytest.raises(ValueError, match="0 <= lo <= hi <= 81"):
        generation.generate_puzzles(2, n_empty_range=(-5, 30))
    with pytest.raises(ValueError, match="0 <= lo <= hi <= 81"):
        generation.generate_puzzles(2, n_empty_range=(30, 90))


# --------------------------------------------------------------------------
# Integration round-trip — generate -> solve (hermetique, haute valeur)
# --------------------------------------------------------------------------

def test_round_trip_generated_puzzles_solvable_by_solver():
    """Les puzzles generes sont resolus par le solveur Norvig : resultat
    non-None, grille complete valide, et coherent avec les indices du puzzle."""
    puzzles, solutions = generation.generate_puzzles(5, seed=42)
    for p, s in zip(puzzles, solutions):
        solved = solvers.solve_sudoku(p)
        assert solved is not None
        assert _is_complete_valid(solved)
        # Le resultat du solveur respecte les indices (clues) du puzzle.
        clues = p != 0
        assert np.all(solved[clues] == p[clues])


def test_round_trip_generated_solution_passes_validity_check():
    """Les solutions completes generees passent is_valid_puzzle (pas de doublon)."""
    _, solutions = generation.generate_puzzles(5, seed=11)
    for s in solutions:
        assert solvers.is_valid_puzzle(s) is True
