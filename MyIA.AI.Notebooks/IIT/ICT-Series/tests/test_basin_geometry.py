"""Tests du module : profil geometrique de bassin substrate-agnostic (#9531 L1).

Couvrent les 4 axes du livrable :

1. **Derivees numeriques** -- gradient et Hessien centraux, accuracy ``O(h^2)``
   vs formes analytiques connues.
2. **Coherence fronce (S1)** -- le profil generic reproduit
   :func:`ict.bridge_testing.basin_geometry` (cas algebrique de reference).
3. **Coherence double-puits** -- reproduit :func:`ict.basin_family.basin_profile`
   (sigma=4b, width=sqrt(b/(2a)), barrier=b^2/(4a)).
4. **Nouvelle capability 2D** -- Hessien, valeurs propres, anisotropie le long
   des directions principales (impossible en 1D algebrique).
5. **Cas limites** -- region monostable (pas de col), bassin infini, bornes
   invalides.

numpy + pytest, CPU uniquement.
"""

from __future__ import annotations

import numpy as np
import pytest

from ict.basin_geometry import (
    BasinProfile,
    basin_geometry,
    equilibria_1d,
    equilibria_2d,
    numeric_gradient,
    numeric_hessian,
    profile_cusp,
    profile_double_well,
)
from ict.bridge_testing import basin_geometry as cusp_algebraic
from ict.basin_family import basin_profile as dw_algebraic


# --------------------------------------------------------------------------- #
#  1. Derivees numeriques : accuracy O(h^2)                                   #
# --------------------------------------------------------------------------- #


def test_numeric_gradient_accuracy():
    """Gradient central vs analytique sur V = sin(x) + x^2 (V' = cos(x)+2x)."""
    f = lambda x: np.sin(float(x[0])) + float(x[0]) ** 2
    for x0 in (0.0, 0.7, -1.3, 2.5):
        gn = numeric_gradient(f, np.array([x0]))[0]
        ga = np.cos(x0) + 2.0 * x0
        assert abs(gn - ga) < 1e-7, f"x={x0}: grad num={gn} vs ana={ga}"


def test_numeric_hessian_accuracy():
    """Hessien vs analytique sur V = sin(x) + x^2 (V'' = -sin(x)+2)."""
    f = lambda x: np.sin(float(x[0])) + float(x[0]) ** 2
    for x0 in (0.0, 0.7, -1.3, 2.5):
        Hn = numeric_hessian(f, np.array([x0]))[0, 0]
        Ha = -np.sin(x0) + 2.0
        assert abs(Hn - Ha) < 1e-5, f"x={x0}: Hess num={Hn} vs ana={Ha}"


def test_numeric_hessian_2d_cross_terms():
    """Hessien 2D : termes croises sur V = x^2 + 3xy + 2y^2 (H = [[2,3],[3,4]])."""
    f = lambda x: float(x[0]) ** 2 + 3.0 * float(x[0]) * float(x[1]) + 2.0 * float(x[1]) ** 2
    H = numeric_hessian(f, np.array([0.0, 0.0]))
    assert abs(H[0, 0] - 2.0) < 1e-3
    assert abs(H[1, 1] - 4.0) < 1e-3
    assert abs(H[0, 1] - 3.0) < 1e-3
    assert abs(H[1, 0] - 3.0) < 1e-3


# --------------------------------------------------------------------------- #
#  2. Coherence FRONCE (S1) : generic == bridge_testing.basin_geometry         #
# --------------------------------------------------------------------------- #


@pytest.mark.parametrize("a,b", [(-1.0, 0.0), (-1.0, 0.1), (-2.0, 0.0), (-3.0, -0.05)])
def test_profile_cusp_matches_algebraic(a, b):
    """Le profil generic de la fronce reproduit le cas algebrique de reference."""
    gen = profile_cusp(a, b)
    alg = cusp_algebraic(a, b)
    assert len(gen) == len(alg)
    for bp, (xs, sigma, width, col) in zip(gen, alg):
        assert abs(float(bp.xstar[0]) - xs) < 1e-3
        assert abs(bp.curvature[0] - sigma) < 1e-2
        assert abs(bp.width - width) < 1e-2
        assert abs(float(bp.col[0]) - col) < 1e-2


def test_profile_cusp_barrier_positive():
    """La hauteur de barriere V(col)-V(x*) >= 0 sur la fronce bistable."""
    for bp in profile_cusp(-1.0, 0.0):
        assert bp.barrier >= -1e-9


def test_profile_cusp_monostable_returns_empty():
    """Region MONOSTABLE de la fronce (a > 0) : pas de col -> profil vide."""
    # a > 0 : V'' = 3x^2 + a > 0 partout -> un seul minimum, pas de col
    assert profile_cusp(1.0, 0.0) == []


# --------------------------------------------------------------------------- #
#  3. Coherence DOUBLE-PUITS : generic == basin_family.basin_profile           #
# --------------------------------------------------------------------------- #


@pytest.mark.parametrize("a,b", [(1.0, 1.0), (1.0, 2.0), (2.0, 1.0), (0.5, 3.0)])
def test_profile_double_well_matches_algebraic(a, b):
    """Le profil generic du double-puits reproduit le cas algebrique."""
    gen = profile_double_well(a, b)
    alg = dw_algebraic(a, b)
    assert len(gen) == len(alg)
    for bp, (xs, sigma, width, col, barrier) in zip(gen, alg):
        assert abs(float(bp.xstar[0]) - xs) < 1e-3
        assert abs(bp.curvature[0] - sigma) < 1e-2     # sigma = 4b
        assert abs(bp.width - width) < 1e-2             # width = sqrt(b/(2a))
        assert abs(float(bp.col[0]) - col) < 1e-2
        assert abs(bp.barrier - barrier) < 1e-3         # barrier = b^2/(4a)


@pytest.mark.parametrize("a,b", [(1.0, 1.0), (1.0, 2.0), (2.0, 1.0)])
def test_double_well_analytic_formulas(a, b):
    """Les formules fermees sigma=4b, width=sqrt(b/2a), barrier=b^2/(4a)."""
    for bp in profile_double_well(a, b):
        assert abs(bp.curvature[0] - 4.0 * b) < 1e-2
        assert abs(bp.width - np.sqrt(b / (2.0 * a))) < 1e-2
        assert abs(bp.barrier - (b ** 2) / (4.0 * a)) < 1e-3


# --------------------------------------------------------------------------- #
#  4. NOUVELLE CAPABILITY 2D : Hessien, valeurs propres, anisotropie           #
# --------------------------------------------------------------------------- #


def test_basin_geometry_2d_anisotropic_double_well():
    """V(x,y)=(x^2-1)^2 + 0.1 y^2 : minima (±1,0), curvature (8, 0.2), aniso 40."""
    V2d = lambda x: (float(x[0]) ** 2 - 1) ** 2 + 0.1 * float(x[1]) ** 2
    basins = basin_geometry(V2d, bounds=(-2.0, 2.0, -2.0, 2.0), n_grid=25)
    assert len(basins) == 2
    # positions des minima : ±1 en x, 0 en y
    xs = sorted(float(b.xstar[0]) for b in basins)
    assert abs(xs[0] + 1.0) < 1e-2
    assert abs(xs[1] - 1.0) < 1e-2
    for b in basins:
        assert abs(float(b.xstar[1])) < 1e-2            # y ~ 0
        curv = np.sort(b.curvature)[::-1]
        assert abs(curv[0] - 8.0) < 0.2                 # courbure x ~ 8
        assert abs(curv[1] - 0.2) < 0.05                # courbure y ~ 0.2
        assert abs(b.anisotropy - 40.0) < 2.0           # 8 / 0.2 = 40
        assert abs(b.width - 1.0) < 1e-2                # distance au col (0,0)
        assert abs(b.barrier - 1.0) < 1e-2              # V(0,0) - V(1,0) = 1


def test_anisotropy_isotropic_basin():
    """Un bassin rond (Hessien isotrope) -> anisotropy ~ 1."""
    # V = x^2 + y^2 : Hessien diag(2,2) -> anisotropy 1. Mais pas de col ->
    # on teste la property directement via BasinProfile.
    bp = BasinProfile(xstar=np.array([0.0, 0.0]),
                      curvature=np.array([2.0, 2.0]),
                      col=None, width=np.inf, barrier=np.inf)
    assert abs(bp.anisotropy - 1.0) < 1e-9


def test_anisotropy_1d_is_one():
    """En 1D, une seule valeur propre -> anisotropy = 1 (pas de direction comparee)."""
    bp = BasinProfile(xstar=np.array([1.0]),
                      curvature=np.array([4.0]),
                      col=np.array([0.0]), width=1.0, barrier=0.5)
    assert abs(bp.anisotropy - 1.0) < 1e-9


def test_equilibria_2d_classifies_minimum_and_saddle():
    """equilibria_2d classifie minima (2 evals > 0) et selles (1+ 1-)."""
    V2d = lambda x: (float(x[0]) ** 2 - 1) ** 2 + 0.1 * float(x[1]) ** 2
    eqs = equilibria_2d(V2d, -2.0, 2.0, -2.0, 2.0, n=25)
    types = {t for _, t in eqs}
    assert "minimum" in types
    assert "saddle" in types


# --------------------------------------------------------------------------- #
#  5. Cas limites                                                              #
# --------------------------------------------------------------------------- #


def test_basin_geometry_1d_pure_quadratic_monostable():
    """V = x^2 : un minimum, aucun col -> profil vide (bassin infini)."""
    f = lambda x: float(x[0]) ** 2
    assert basin_geometry(f, bounds=(-3.0, 3.0)) == []


def test_basin_geometry_invalid_bounds_raises():
    """bounds de taille invalide -> ValueError."""
    with pytest.raises(ValueError):
        basin_geometry(lambda x: 0.0, bounds=(1.0, 2.0, 3.0))


def test_equilibria_1d_finds_cusp_roots():
    """equilibria_1d localise les 3 racines de la fronce bistable (2 minima + 1 col)."""
    V = lambda x: float(x[0]) ** 4 / 4.0 - float(x[0]) ** 2 / 2.0  # double-puits a=1,b=1
    eqs = equilibria_1d(V, -3.0, 3.0, n=400)
    xs = [x for x, _ in eqs]
    # 3 equilibres : 2 minima (±1) + 1 col (0)
    assert len(eqs) == 3
    assert any(abs(x) < 1e-3 for x in xs)         # col en 0
    assert any(abs(x + 1.0) < 1e-2 for x in xs)   # minimum -1
    assert any(abs(x - 1.0) < 1e-2 for x in xs)   # minimum +1


def test_basinprofile_dim_property():
    """BasinProfile.dim retourne la dimension (1 ou 2)."""
    bp1 = BasinProfile(np.array([0.0]), np.array([1.0]), None, np.inf, np.inf)
    bp2 = BasinProfile(np.array([0.0, 0.0]), np.array([1.0, 1.0]), None, np.inf, np.inf)
    assert bp1.dim == 1
    assert bp2.dim == 2
