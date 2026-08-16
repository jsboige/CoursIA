"""Tests du substrat Jeu de la Vie (phase-zero #5726).

Verifient la regle B3/S23 (naissance, survie, mort), les proprietes de trajectoire
et surtout la **calibration canonique** : chaque pattern (glider, blinker, pulsar,
LWSS, block) doit reproduire sa periode et son deplacement documentes. C'est le
certificat qui fonde l'usage de ce substrat comme source de trajectoires calibrees
pour la batterie ICT.

Numpy + pytest."""

import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ict.life import (  # noqa: E402
    CALIBRATION,
    calibrate_all,
    canonical_pattern,
    embed,
    live_cells,
    next_generation,
    period_and_displacement,
    trajectory,
)


# --------------------------------------------------------------- regle B3/S23
def test_lone_cell_dies():
    grid = np.zeros((8, 8), dtype=np.uint8)
    grid[4, 4] = 1
    assert next_generation(grid).sum() == 0


def test_block_is_still_life():
    block = embed(canonical_pattern("block"), 8)
    nxt = next_generation(block)
    assert nxt.sum() == 4
    assert live_cells(nxt) == live_cells(block)


def test_birth_on_three_neighbors():
    grid = np.zeros((8, 8), dtype=np.uint8)
    grid[3, 3] = grid[4, 3] = grid[5, 3] = 1  # blinker vertical
    nxt = next_generation(grid)
    # le centre (4,3) survit ; (4,2) et (4,4) naissent ; les extremites meurent
    assert live_cells(nxt) == [(4, 2), (4, 3), (4, 4)]


def test_overpopulation_death():
    grid = np.zeros((8, 8), dtype=np.uint8)
    grid[3, 3] = grid[3, 4] = grid[4, 3] = grid[4, 4] = grid[5, 4] = 1  # centre (4,4) a 4 voisins
    nxt = next_generation(grid)
    assert nxt[4, 4] == 0


def test_toroidal_wrap():
    # blinker a cheval sur le bord : les voisins viennent du cote oppose
    grid = np.zeros((6, 6), dtype=np.uint8)
    grid[0, 0] = grid[0, 5] = grid[0, 1] = 1  # ligne 0, colonnes -1, 0, 1 (wrap)
    nxt = next_generation(grid)
    assert sorted(live_cells(nxt)) == [(0, 0), (1, 0), (5, 0)]


# --------------------------------------------------------------- trajectoire et export
def test_trajectory_length_and_types():
    grid = embed(canonical_pattern("blinker"), 8)
    film = trajectory(grid, 3)
    assert len(film) == 4
    assert all(g.shape == (8, 8) and g.dtype == np.uint8 for g in film)
    # la trajectoire ne modifie pas la grille d'entree
    assert (film[0] == grid).all()
    assert film[1].sum() == 3  # un blinker reste 3 cellules


def test_live_cells_export_format():
    block = embed(canonical_pattern("block"), 6, top=2, left=3)
    assert sorted(live_cells(block)) == [(2, 3), (2, 4), (3, 3), (3, 4)]


# --------------------------------------------------------------- calibration canonique
def test_calibration_all_patterns():
    """Certificat : chaque pattern canonique reproduit periode et deplacement."""
    results = calibrate_all()
    assert results == {name: True for name in results}, results


def test_glider_period_and_displacement():
    period, disp = period_and_displacement(embed(canonical_pattern("glider"), 32))
    assert period == CALIBRATION["glider"]["period"] == 4
    assert disp is not None and abs(disp[0]) == abs(disp[1]) == 1


def test_pulsar_period_three_stationary():
    period, disp = period_and_displacement(embed(canonical_pattern("pulsar"), 32))
    assert period == 3
    assert disp == (0, 0)


def test_lwss_period_and_orthogonal_displacement():
    period, disp = period_and_displacement(embed(canonical_pattern("lwss"), 32))
    assert period == 4
    assert disp is not None
    dr, dc = disp
    assert (abs(dr) == 0 and abs(dc) == 2) or (abs(dr) == 2 and abs(dc) == 0)


def test_blinker_period_two():
    period, disp = period_and_displacement(embed(canonical_pattern("blinker"), 8))
    assert period == 2
    assert disp == (0, 0)


def test_dying_pattern_reports_none():
    grid = np.zeros((8, 8), dtype=np.uint8)
    grid[4, 4] = 1
    period, disp = period_and_displacement(grid)
    assert period is None and disp is None


def test_embed_rejects_oversized_pattern():
    import pytest

    with pytest.raises(ValueError):
        embed(canonical_pattern("pulsar"), 4)


# ------------------------------------------------- pont batterie ICT (#5726)
def test_trajectory_symbols_blinker_alternates():
    from ict.life import trajectory_symbols

    traj = trajectory(embed(canonical_pattern("blinker"), 8), 6)
    symbols, states = trajectory_symbols(traj)
    assert symbols == ["e0", "e1", "e0", "e1", "e0", "e1", "e0"]
    assert len(states) == 2


def test_trajectory_symbols_block_single_state():
    from ict.life import trajectory_symbols

    traj = trajectory(embed(canonical_pattern("block"), 8), 10)
    symbols, states = trajectory_symbols(traj)
    assert symbols == ["e0"] * 11
    assert len(states) == 1


def test_trajectory_symbols_glider_cycle_length():
    # Glider sur tore 16x16 : deplacement (1, 1) par periode de 4, retour a
    # l'etat initial apres 16 pas de deplacement = 64 generations.
    from ict.life import trajectory_symbols

    traj = trajectory(embed(canonical_pattern("glider"), 16), 64)
    symbols, states = trajectory_symbols(traj)
    assert len(states) == 64
    assert symbols[0] == symbols[-1]  # la fenetre referme le cycle
