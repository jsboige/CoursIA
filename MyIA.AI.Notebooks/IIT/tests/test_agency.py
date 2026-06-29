"""Tests des mesures d'agence morphologique (module ICT-9).

Verifient les masques d'ablation, l'intervention ``do(ablation)``, les mesures de
structure / distance / similarite spectrale, et surtout le coeur conceptuel : la
reaction-diffusion **repare** (gain de reparation > 0) la ou la diffusion pure
echoue, sur le **meme** champ ablate.

Numpy + pytest. Les modules ne dependent que de numpy."""

import os
import sys

import numpy as np
import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ict import agency  # noqa: E402
from ict import reaction_diffusion as rd  # noqa: E402


def test_quadrant_mask_covers_quarter():
    m = agency.quadrant_mask(8, quadrant=0)
    assert m.shape == (8, 8)
    assert m.sum() == 16  # un quart de 64
    assert m[0, 0] and not m[7, 7]
    assert agency.quadrant_mask(8, 3)[7, 7]


def test_disk_mask():
    m = agency.disk_mask(21, cx=10, cy=10, radius=3)
    assert m[10, 10]
    assert not m[0, 0]
    # tous les pixels du masque sont dans le rayon
    yy, xx = np.mgrid[0:21, 0:21]
    assert ((xx[m] - 10) ** 2 + (yy[m] - 10) ** 2 <= 9).all()


def test_ablate_resets_region_and_is_pure():
    U = np.full((8, 8), 0.5)
    V = np.full((8, 8), 0.3)
    mask = agency.quadrant_mask(8, 0)
    U2, V2 = agency.ablate(U, V, mask)
    # region ablatee remise a l'etat nu
    assert (U2[mask] == 1.0).all()
    assert (V2[mask] == 0.0).all()
    # hors region : inchange
    assert (U2[~mask] == 0.5).all()
    assert (V2[~mask] == 0.3).all()
    # entrees non mutees
    assert (U == 0.5).all() and (V == 0.3).all()


def test_structure_uniform_is_zero():
    assert agency.structure(np.full((10, 10), 0.42)) == pytest.approx(0.0)


def test_structure_increases_with_contrast():
    flat = np.full((10, 10), 0.5)
    contrasted = np.zeros((10, 10))
    contrasted[:5] = 1.0
    assert agency.structure(contrasted) > agency.structure(flat)


def test_pattern_distance_zero_for_identical():
    a = np.random.default_rng(0).standard_normal((12, 12))
    assert agency.pattern_distance(a, a) == pytest.approx(0.0)


def test_pattern_distance_positive_for_different():
    a = np.zeros((12, 12))
    b = np.ones((12, 12))
    assert agency.pattern_distance(a, b) == pytest.approx(1.0)


def test_spectral_similarity_identical_is_one():
    a = np.random.default_rng(1).standard_normal((32, 32))
    assert agency.spectral_similarity(a, a) == pytest.approx(1.0, abs=1e-6)


def test_spectral_similarity_translation_invariant():
    # deux motifs identiques mais decales ont des spectres tres proches
    base = np.zeros((40, 40))
    base[10:14, 10:14] = 1.0
    base[26:30, 26:30] = 1.0
    shifted = np.roll(np.roll(base, 5, axis=0), 7, axis=1)
    assert agency.spectral_similarity(base, shifted) > 0.95


def test_recovery_score_full_and_none():
    ref = np.zeros((8, 8))
    ref[:4] = 1.0          # structure presente (variance > 0)
    ablated = np.full((8, 8), 1.0)   # uniforme -> variance nulle
    # repare = identique a la reference -> recuperation ~1
    assert agency.recovery_score(ref, ablated, ref) == pytest.approx(1.0, abs=1e-6)
    # repare = reste uniforme -> recuperation ~0
    assert agency.recovery_score(ref, ablated, ablated) == pytest.approx(0.0, abs=1e-6)


def test_repair_gain_sign():
    assert agency.repair_gain(0.9, 0.1) == pytest.approx(0.8)
    assert agency.repair_gain(0.1, 0.9) < 0


def test_time_to_recover():
    structures = [0.0, 0.2, 0.5, 0.9, 1.0]  # monte vers la cible 1.0
    # seuil 0.9*1.0 = 0.9 atteint a l'indice 3
    assert agency.time_to_recover(structures, target=1.0, tol=0.1, record_every=10) == 30
    # cible inatteignable
    assert agency.time_to_recover(structures, target=100.0, tol=0.1) is None


def test_reaction_diffusion_repairs_diffusion_does_not():
    """Coeur ICT-9 : sur le meme champ ablate, RD repare, la diffusion dissout.

    Test integratif (court mais reel) : on forme un motif, on ablate un quadrant,
    puis on compare la recuperation sous reaction-diffusion vs diffusion pure.
    Le gain de reparation doit etre nettement positif.
    """
    gs = rd.GrayScott()
    U, V = gs.seed(n=64, rng=np.random.default_rng(11))
    U, V, _ = gs.run(U, V, steps=3000)          # forme un motif
    V_ref = V.copy()
    mask = agency.quadrant_mask(64, quadrant=3)

    U_abl, V_abl = agency.ablate(U, V, mask)

    # monde 1 : reaction-diffusion
    _, V_rd, _ = gs.run(U_abl.copy(), V_abl.copy(), steps=4000)
    # monde 2 : diffusion pure (meme operateur diffusif, sans reaction)
    V_diff = rd.run_pure_diffusion(V_abl.copy(), D=gs.Dv, steps=4000)

    rec_rd = agency.recovery_score(V_ref, V_abl, V_rd, mask)
    rec_diff = agency.recovery_score(V_ref, V_abl, V_diff, mask)
    gain = agency.repair_gain(rec_rd, rec_diff)

    assert rec_rd > 0.3          # la RD reconstruit une part substantielle
    assert rec_diff < rec_rd     # la diffusion fait moins bien
    assert gain > 0.2            # agence mesuree, pas declaree
