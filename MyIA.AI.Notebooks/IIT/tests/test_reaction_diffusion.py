"""Tests du simulateur de reaction-diffusion Gray-Scott (module ICT-9).

Verifient les proprietes structurelles du Laplacien periodique, la conservation
de masse de la diffusion pure, la stabilite numerique de l'integration, et le
fait fondateur du notebook : la reaction-diffusion **engendre** un motif structure
la ou la diffusion pure **dissout** tout vers l'uniforme.

Numpy + pytest. Le module ne depend que de numpy."""

import os
import sys

import numpy as np
import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ict import reaction_diffusion as rd  # noqa: E402


def test_laplacian_constant_field_is_zero():
    # un champ uniforme a un Laplacien nul partout
    f = np.full((16, 16), 3.7)
    assert np.allclose(rd.laplacian(f), 0.0)


def test_laplacian_periodic_boundary():
    # bords periodiques : la somme du Laplacien sur tout le tore est nulle
    f = np.random.default_rng(0).standard_normal((20, 20))
    assert abs(rd.laplacian(f).sum()) < 1e-9


def test_laplacian_known_peak():
    # un seul pixel a 1 entoure de 0 : centre -> -4, chaque voisin -> +1
    f = np.zeros((9, 9))
    f[4, 4] = 1.0
    lap = rd.laplacian(f)
    assert lap[4, 4] == pytest.approx(-4.0)
    assert lap[3, 4] == pytest.approx(1.0)
    assert lap[5, 4] == pytest.approx(1.0)
    assert lap[4, 3] == pytest.approx(1.0)
    assert lap[4, 5] == pytest.approx(1.0)


def test_seed_shapes_and_bounds():
    gs = rd.GrayScott()
    U, V = gs.seed(n=48, rng=np.random.default_rng(1))
    assert U.shape == (48, 48) and V.shape == (48, 48)
    assert U.min() >= 0.0 and U.max() <= 1.0
    assert V.min() >= 0.0 and V.max() <= 1.0
    # le germe central injecte du V ; le fond reste majoritairement U~1, V~0
    assert V[24, 24] > 0.0
    assert V.mean() < 0.1


def test_seed_reproducible():
    gs = rd.GrayScott()
    U1, V1 = gs.seed(n=32, rng=np.random.default_rng(7))
    U2, V2 = gs.seed(n=32, rng=np.random.default_rng(7))
    assert np.array_equal(U1, U2) and np.array_equal(V1, V2)


def test_step_stays_bounded():
    # l'integration reste dans [0, 1] (stabilite + clip)
    gs = rd.GrayScott()
    U, V = gs.seed(n=48, rng=np.random.default_rng(2))
    U, V, _ = gs.run(U, V, steps=500)
    assert np.isfinite(U).all() and np.isfinite(V).all()
    assert U.min() >= 0.0 and U.max() <= 1.0
    assert V.min() >= 0.0 and V.max() <= 1.0


def test_reaction_diffusion_generates_structure():
    # apres assez de pas, le motif est nettement plus structure que le germe initial
    gs = rd.GrayScott()
    U, V = gs.seed(n=64, rng=np.random.default_rng(3))
    v0 = np.var(V)
    U, V, _ = gs.run(U, V, steps=3000)
    assert np.var(V) > v0
    assert np.var(V) > 1e-4  # un vrai motif, pas du bruit residuel


def test_run_records_snapshots():
    gs = rd.GrayScott()
    U, V = gs.seed(n=32, rng=np.random.default_rng(4))
    _, _, snaps = gs.run(U, V, steps=100, record_every=20)
    assert snaps is not None
    assert len(snaps) == 5
    assert all(s.shape == (32, 32) for s in snaps)


def test_run_include_initial_prepends_t0():
    gs = rd.GrayScott()
    U, V = gs.seed(n=32, rng=np.random.default_rng(4))
    V0 = V.copy()
    _, _, snaps = gs.run(U.copy(), V.copy(), steps=100, record_every=20)
    _, _, snaps_i = gs.run(
        U.copy(), V.copy(), steps=100, record_every=20, include_initial=True
    )
    # une capture de plus, et la premiere est l'etat initial exact (t = 0)
    assert len(snaps_i) == len(snaps) + 1
    assert np.array_equal(snaps_i[0], V0)
    # include_initial sans capture active reste sans effet
    _, _, none_snaps = gs.run(U.copy(), V.copy(), steps=10, include_initial=True)
    assert none_snaps is None


def test_pure_diffusion_conserves_mass():
    # la diffusion pure (bords periodiques) conserve la masse totale
    f = np.random.default_rng(5).standard_normal((24, 24)) + 5.0
    out = rd.run_pure_diffusion(f, D=0.2, steps=200)
    assert out.sum() == pytest.approx(f.sum(), rel=1e-6)


def test_pure_diffusion_dissolves_structure():
    # la diffusion pure lisse : la variance decroit vers l'uniforme
    f = np.zeros((32, 32))
    f[8:16, 8:16] = 1.0  # bloc structure
    v0 = np.var(f)
    out = rd.run_pure_diffusion(f, D=0.2, steps=1000)
    assert np.var(out) < 0.05 * v0
