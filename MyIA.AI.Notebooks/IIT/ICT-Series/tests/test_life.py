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
import pytest

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


# ------------------------------------------- ensemble des graines (phase narrative #5726)
def test_torus_ensemble_tpm_deterministic_and_degenerate():
    from ict.life import torus_ensemble_tpm

    tpm, succ = torus_ensemble_tpm(2)
    assert tpm.shape == (16, 16)
    # determinisme : chaque ligne est un one-hot
    assert np.allclose(tpm.sum(axis=1), 1.0)
    assert np.all((tpm == 0.0) | (tpm == 1.0))
    # degenerescence mesuree de B3/S23 sur le tore 2x2 : 5 successeurs distincts
    assert len(set(succ.tolist())) == 5
    # k hors cap -> erreur explicite (jamais de TPM 65536x65536 silencieuse)
    with pytest.raises(ValueError):
        torus_ensemble_tpm(4)


def test_fate_and_population_strata_partition_exhaustive():
    from ict.life import fate_strata, live_count_strata, torus_ensemble_tpm

    _, succ = torus_ensemble_tpm(2)
    fate = fate_strata(succ)
    flat = [s for g in fate for s in g]
    assert sorted(flat) == list(range(16))
    # les strates de destin sont les fibres : une strate = un seul successeur
    assert all(len(set(succ[g].tolist())) == 1 for g in fate)

    pop = live_count_strata(2, succ)
    flat = [s for g in pop for s in g]
    assert sorted(flat) == list(range(16))
    # strates de population d'un tore 2x2 : tailles du triangle de Pascal
    assert [len(g) for g in pop] == [1, 4, 6, 4, 1]


# ------------------------------------- cas ouvert : soups et collisions (ICT-33)
def test_random_soup_reproductible_et_densite():
    from ict.life import random_soup

    rng1 = np.random.default_rng(7)
    rng2 = np.random.default_rng(7)
    g1, g2 = random_soup(16, 0.3, rng1), random_soup(16, 0.3, rng2)
    assert np.array_equal(g1, g2)
    # densite empirique proche de la cible (16x16 = 256 cellules, tolerance 5 pts)
    assert abs(g1.mean() - 0.3) < 0.05
    with pytest.raises(ValueError):
        random_soup(16, 0.0, np.random.default_rng(0))


def test_empirical_tpm_live_count_stochastique():
    """Le cas ouvert : la TPM macro sur ensemble conditionne n'est PAS one-hot.

    Mesure (seed 42, 8x8, densite 0.3, 200 echantillons) : la strate 12 cellules
    se repartit sur TROIS destins (11/12/13) -- le complement exact du tore
    exhaustif d'ICT-32 dont toutes les lignes sont one-hot.
    """
    from ict.life import empirical_tpm_live_count, random_soup

    rng = np.random.default_rng(42)
    soups = [random_soup(8, 0.3, rng) for _ in range(200)]
    tpm, axis = empirical_tpm_live_count(soups)
    # lignes sources somment a 1
    for row in tpm:
        if row.any():
            assert abs(row.sum() - 1.0) < 1e-9
    # au moins une strate a destins multiples : le cas ouvert, mesure
    multi = [i for i, row in enumerate(tpm) if np.count_nonzero(row) > 1]
    assert multi, "TPM soup totalement deterministe -- le temoin du cas ouvert a disparu"
    # constante mesuree : strate 12 -> trois destins
    i = axis.index(12)
    assert np.count_nonzero(tpm[i]) == 3
    assert abs(tpm[i, axis.index(13)] - 0.6) < 0.05


def test_glider_collision_parametres_valides():
    from ict.life import glider_collision

    g = glider_collision(32, 0, 0)
    assert g.shape == (32, 32)
    assert g.sum() == 10  # deux gliders de 5 cellules
    # phase hors domaine -> erreur explicite
    with pytest.raises(ValueError):
        glider_collision(32, 4, 0)


def test_collision_outcome_deterministe_par_parametres():
    from ict.life import collision_outcome, glider_collision

    # mesure : (phase=0, offset=8) = frôlement, un glider sur deux survit
    r1 = collision_outcome(glider_collision(32, 0, 8))
    r2 = collision_outcome(glider_collision(32, 0, 8))
    assert r1 == r2  # B3/S23 deterministe : meme entree, meme issue
    assert r1["class"] == "1-glider"
    # mesure : (phase=0, offset=0) = collision frontale, annihilation
    assert collision_outcome(glider_collision(32, 0, 0))["class"] == "annihilation"


def test_batterie_collision_plusieurs_destins():
    """Le banc discriminant : la batterie phase x offset produit AU MOINS trois
    classes d'issue distinctes (mesure : 21 annihilation / 7 1-glider / 20 debris)."""
    from collections import Counter

    from ict.life import collision_outcome, glider_collision

    classes = Counter(
        collision_outcome(glider_collision(32, p, off))["class"]
        for p in range(4)
        for off in range(-3, 9)
    )
    assert set(classes) == {"annihilation", "1-glider", "debris"}
    assert classes["annihilation"] == 21
    assert classes["1-glider"] == 7


def test_connected_components_glider_isole():
    from ict.life import canonical_pattern, connected_components, embed, is_glider

    g = embed(canonical_pattern("glider"), 16)
    comps = connected_components(g)
    assert len(comps) == 1
    assert is_glider(comps[0])
    # un bloc n'est pas un glider
    block = embed(canonical_pattern("block"), 16)
    assert not is_glider(connected_components(block)[0])
