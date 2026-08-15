"""Profil geometrique de bassin -- substrate-agnostic (Case #9531, deliverable 1).

La serie ICT profite la geometrie des bassins d'un potentiel sur plusieurs
substrats : la fronce de Thom (S1, ``ict.catastrophe``), le double-puits
symetrique (Pont #1-bis, ``ict.basin_family``), et a venir le potentiel de May
(S2) et l'espace de champ de Gray-Scott (S4, cf ICT-19b). Chaque substrat avait
sa propre fonction de geometrie, **couplee a sa forme algebrique** :

* :func:`ict.bridge_testing.basin_geometry` : fronce, via ``cat.cusp_equilibria``
  + ``cat.cusp_curvature`` -> 4-tuple ``(x*, sigma, width, col)``.
* :func:`ict.basin_family.basin_profile` : double-puits, via
  ``double_well_equilibria`` + courbure algebrique ``4b`` -> 5-tuple
  ``(x*, sigma, width, col, barrier)``.

Ce module fournit un **profileur substrate-agnostic** : il prend un potentiel
``V(x)`` arbitraire (1D scalaire ou 2D vecteur), calcule gradient et Hessien
**numeriquement**, localise les equilibres (minima stables + cols/selles
instables), et renvoie pour chaque bassin un :class:`BasinProfile` uniforme :

    * ``curvature`` : **valeurs propres** du Hessien au minimum (>= 0, triees
      decroissant) -- la stabilite le long des directions principales ;
    * ``col`` : equilibre instable le plus proche (frontiere de bassin) ;
    * ``width`` : distance ``|x* - col|`` (portee du bassin vers la frontiere) ;
    * ``barrier`` : hauteur ``V(col) - V(x*) >= 0`` (seuil de bascule) ;
    * ``anisotropy`` : ``lambda_max / lambda_min`` des valeurs propres (1 en 1D ;
      >= 1 en 2D -- 1 = bassin rond, grand = cuvette allongee/creux).

La genericalite a un cout : numerique (erreur ~ ``h^2``), a valider par les
tests de coherence qui **reproduisent** les cas algebriques (fonce, double-puits)
la ou la forme fermee existe. Substrat : numpy uniquement, CPU.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Callable, List, Optional, Sequence, Tuple

import numpy as np

Potential = Callable[[np.ndarray], float]
"""Potentiel ``V(x) -> float``. ``x`` est scalaire (1D) ou vecteur (ND)."""


# --------------------------------------------------------------------------- #
#  Derivees numeriques (central differences, erreur O(h^2))                    #
# --------------------------------------------------------------------------- #


def numeric_gradient(V: Potential, x: np.ndarray, h: float = 1e-5) -> np.ndarray:
    """Gradient de ``V`` en ``x`` par differences centrales (vecteur ND)."""
    x = np.atleast_1d(np.asarray(x, dtype=float))
    n = x.size
    grad = np.zeros(n, dtype=float)
    for i in range(n):
        xp = x.copy(); xp[i] += h
        xm = x.copy(); xm[i] -= h
        grad[i] = (float(V(xp)) - float(V(xm))) / (2.0 * h)
    return grad


def numeric_hessian(V: Potential, x: np.ndarray, h: float = 1e-4) -> np.ndarray:
    """Hessien de ``V`` en ``x`` par differences finies (matrice ND x ND).

    Diagonale : differences centrales d'ordre 2. Hors-diagonale : melange
    central symetrique. Erreur global ``O(h^2)``.
    """
    x = np.atleast_1d(np.asarray(x, dtype=float))
    n = x.size
    H = np.zeros((n, n), dtype=float)
    f0 = float(V(x))
    # Diagonale
    for i in range(n):
        xp = x.copy(); xp[i] += h
        xm = x.copy(); xm[i] -= h
        H[i, i] = (float(V(xp)) - 2.0 * f0 + float(V(xm))) / (h * h)
    # Hors-diagonale (symetrique)
    for i in range(n):
        for j in range(i + 1, n):
            xpp = x.copy(); xpp[i] += h; xpp[j] += h
            xpm = x.copy(); xpm[i] += h; xpm[j] -= h
            xmp = x.copy(); xmp[i] -= h; xmp[j] += h
            xmm = x.copy(); xmm[i] -= h; xmm[j] -= h
            val = (float(V(xpp)) - float(V(xpm)) - float(V(xmp)) + float(V(xmm))) / (4.0 * h * h)
            H[i, j] = val
            H[j, i] = val
    return H


# --------------------------------------------------------------------------- #
#  Localisation des equilibres                                                 #
# --------------------------------------------------------------------------- #


def equilibria_1d(
    V: Potential,
    x_min: float,
    x_max: float,
    n: int = 400,
) -> List[Tuple[float, bool]]:
    """Equilibres 1D ``(x*, stable)`` d'un potentiel ``V`` arbitraire.

    Localise les zeros du gradient par **changement de signe** sur une grille
    reguliere de ``n`` points, raffines par bissection. ``stable`` ssi le
    Hessien (courbure) ``V''(x*) > 0`` (minimum). Renvoie la liste triee par
    ``x`` croissant. Substrate-agnostic (pas de forme fermee requise).
    """
    if n < 4:
        n = 4
    xs = np.linspace(float(x_min), float(x_max), int(n))
    g = np.array([numeric_gradient(V, np.array([xi]))[0] for xi in xs])
    eqs: List[Tuple[float, bool]] = []
    for k in range(len(xs) - 1):
        if g[k] == 0.0:
            stab = float(numeric_hessian(V, np.array([xs[k]]))[0, 0]) > 0.0
            eqs.append((float(xs[k]), stab))
        elif g[k] * g[k + 1] < 0.0:
            root = _bissect_zero(V, xs[k], xs[k + 1])
            stab = float(numeric_hessian(V, np.array([root]))[0, 0]) > 0.0
            eqs.append((float(root), stab))
    # dedup + sort
    eqs.sort(key=lambda t: t[0])
    out: List[Tuple[float, bool]] = []
    for x, st in eqs:
        if not out or abs(x - out[-1][0]) > 1e-6:
            out.append((x, st))
    return out


def _bissect_zero(V: Potential, a: float, b: float, tol: float = 1e-10,
                  max_iter: int = 100) -> float:
    """Raffine un zero du gradient entre ``a`` et ``b`` (g(a)*g(b)<0)."""
    ga = numeric_gradient(V, np.array([a]))[0]
    for _ in range(max_iter):
        m = 0.5 * (a + b)
        gm = numeric_gradient(V, np.array([m]))[0]
        if abs(gm) < tol or (b - a) < tol:
            return float(m)
        if ga * gm < 0.0:
            b = m
        else:
            a = m
            ga = gm
    return float(0.5 * (a + b))


def equilibria_2d(
    V: Potential,
    x_min: float, x_max: float,
    y_min: float, y_max: float,
    n: int = 40,
) -> List[Tuple[np.ndarray, str]]:
    """Equilibres 2D ``(xy, type)`` d'un potentiel ``V`` a 2 variables.

    Cherche les zeros du gradient (``grad V = 0``) par balayage grille + descente
    de Newton raffinant, puis classifie via le Hessien (valeurs propres) :

    * ``minimum`` : 2 valeurs propres > 0 (bassin, stable) ;
    * ``saddle``  : 1 positive, 1 negative (col/selle, frontiere instable) ;
    * ``maximum`` : 2 valeurs propres < 0 (instable, hors-scope ici).

    Renvoie une liste ``[(xy_array, type_str), ...]``. Le parametre ``n`` pilote
    la grille d'initialisation (croissance quadratique en n^2 -> garder modere).
    """
    pts: List[Tuple[np.ndarray, str]] = []
    found: List[np.ndarray] = []
    gx = np.linspace(x_min, x_max, int(n))
    gy = np.linspace(y_min, y_max, int(n))
    for xi in gx:
        for yj in gy:
            root = _newton_root_2d(V, np.array([float(xi), float(yj)]))
            if root is None:
                continue
            if any(np.linalg.norm(root - f) < 1e-3 for f in found):
                continue
            found.append(root)
            evals = np.linalg.eigvalsh(numeric_hessian(V, root))
            if evals.min() > 0.0:
                pts.append((root, "minimum"))
            elif evals.max() < 0.0:
                pts.append((root, "maximum"))
            else:
                pts.append((root, "saddle"))
    return pts


def _newton_root_2d(V: Potential, x0: np.ndarray,
                    tol: float = 1e-9, max_iter: int = 50,
                    box: Optional[Tuple[float, float, float, float]] = None
                    ) -> Optional[np.ndarray]:
    """Newton-Raphson pour ``grad V = 0`` en 2D (sortie ``xy`` ou ``None``)."""
    x = np.asarray(x0, dtype=float).copy()
    for _ in range(max_iter):
        g = numeric_gradient(V, x)
        if np.linalg.norm(g) < tol:
            return x
        H = numeric_hessian(V, x)
        try:
            step = np.linalg.solve(H, g)
        except np.linalg.LinAlgError:
            return None
        x = x - step
        if not np.all(np.isfinite(x)):
            return None
        if box is not None and not (box[0] <= x[0] <= box[1] and box[2] <= x[1] <= box[3]):
            return None
    return None


# --------------------------------------------------------------------------- #
#  Profil de bassin uniforme (1D et 2D)                                        #
# --------------------------------------------------------------------------- #


@dataclass
class BasinProfile:
    """Profil geometrique d'un bassin (autour d'un minimum stable ``xstar``).

    * ``curvature`` : valeurs propres du Hessien en ``xstar`` (>= 0, triees
      decroissant) -- stabilite le long des directions principales ;
    * ``col`` : equilibre instable le plus proche (``None`` si aucun col, bassin
      infini -> monostable) ;
    * ``width`` : distance ``|xstar - col|`` (``np.inf`` si pas de col) ;
    * ``barrier`` : hauteur ``V(col) - V(xstar) >= 0`` (``np.inf`` si pas de col) ;
    * ``anisotropy`` : ``lambda_max / lambda_min`` des valeurs propres (= 1.0 en
      1D ou pour un bassin rond 2D ; >> 1 = cuvette allongee / creux directional).
    """
    xstar: np.ndarray
    curvature: np.ndarray
    col: Optional[np.ndarray]
    width: float
    barrier: float

    @property
    def anisotropy(self) -> float:
        curv = np.asarray(self.curvature, dtype=float)
        pos = curv[curv > 1e-12]
        if pos.size == 0:
            return 1.0
        return float(pos.max() / pos.min())

    @property
    def dim(self) -> int:
        return int(np.asarray(self.xstar).size)


def basin_geometry(
    V: Potential,
    bounds: Sequence,
    n_grid: int = 400,
) -> List[BasinProfile]:
    """Profil geometrique de tous les bassins de ``V`` dans ``bounds``.

    Parameters
    ----------
    V : potentiel ``V(x) -> float``, ``x`` scalaire (1D) ou vecteur 2D.
    bounds : ``(x_min, x_max)`` en 1D, ou ``(x_min, x_max, y_min, y_max)`` en 2D.
    n_grid : resolution de la grille de localisation des equilibres.

    Returns
    -------
    list[BasinProfile]
        Un profil par minimum stable ayant un col voisin (les minima sans col
        -- bassin infini -- sont omis : cas trivial ou toute perturbation est
        recuperee, hors-scope du pont). Vide hors region multistable.
    """
    if len(bounds) == 2:
        return _basin_geometry_1d(V, float(bounds[0]), float(bounds[1]), n_grid)
    elif len(bounds) == 4:
        return _basin_geometry_2d(V, *map(float, bounds), n_grid)
    raise ValueError(f"bounds doit etre 2-tuple (1D) ou 4-tuple (2D), recut {len(bounds)}")


def _basin_geometry_1d(V: Potential, x_min: float, x_max: float,
                       n_grid: int) -> List[BasinProfile]:
    eqs = equilibria_1d(V, x_min, x_max, n=n_grid)
    stables = [x for x, st in eqs if st]
    unstables = [x for x, st in eqs if not st]
    out: List[BasinProfile] = []
    for xstar in stables:
        xs = np.array([float(xstar)])
        curv = np.array([float(numeric_hessian(V, xs)[0, 0])])
        col = min(unstables, key=lambda c: abs(c - xstar)) if unstables else None
        if col is None:
            continue  # bassin infini (monostable) -> hors-scope
        col_arr = np.array([float(col)])
        width = float(abs(xstar - col))
        barrier = float(V(col_arr) - V(xs))
        out.append(BasinProfile(xs, curv, col_arr, width, barrier))
    return out


def _basin_geometry_2d(V: Potential, x_min: float, x_max: float,
                       y_min: float, y_max: float,
                       n_grid: int) -> List[BasinProfile]:
    eqs = equilibria_2d(V, x_min, x_max, y_min, y_max, n=n_grid)
    minima = [xy for xy, t in eqs if t == "minimum"]
    saddles = [xy for xy, t in eqs if t == "saddle"]
    out: List[BasinProfile] = []
    for xstar in minima:
        H = numeric_hessian(V, xstar)
        evals = np.linalg.eigvalsh(H)
        curv = np.sort(evals)[::-1]  # decroissant
        if not saddles:
            continue
        col = min(saddles, key=lambda c: float(np.linalg.norm(c - xstar)))
        width = float(np.linalg.norm(xstar - col))
        barrier = float(V(col) - V(xstar))
        out.append(BasinProfile(xstar, curv, col, width, barrier))
    return out


# --------------------------------------------------------------------------- #
#  Adaptateurs substrat -> profil uniforme (reutilisabilite S1/S2/S4)          #
# --------------------------------------------------------------------------- #


def profile_cusp(a: float, b: float, n_grid: int = 400) -> List[BasinProfile]:
    """Profil de la fronce de Thom ``V(x) = x^4/4 + a x^2/2 + b x`` (S1).

    Equivalent substrate-agnostic de
    :func:`ict.bridge_testing.basin_geometry` (4-tuple) -- valide par test de
    coherence : reproduit les memes ``(x*, sigma, width, col)``.
    """
    return basin_geometry(lambda x: float(x[0]) ** 4 / 4.0 + a * float(x[0]) ** 2 / 2.0 + b * float(x[0]),
                          bounds=(-3.0, 3.0), n_grid=n_grid)


def profile_double_well(a: float, b: float, n_grid: int = 400) -> List[BasinProfile]:
    """Profil du double-puits symetrique ``V(x) = a x^4 - b x^2`` (Pont #1-bis).

    Equivalent substrate-agnostic de :func:`ict.basin_family.basin_profile`
    (5-tuple) -- valide par test de coherence : reproduit sigma=4b,
    width=sqrt(b/(2a)), barrier=b^2/(4a).
    """
    return basin_geometry(lambda x: a * float(x[0]) ** 4 - b * float(x[0]) ** 2,
                          bounds=(-3.0, 3.0), n_grid=n_grid)
