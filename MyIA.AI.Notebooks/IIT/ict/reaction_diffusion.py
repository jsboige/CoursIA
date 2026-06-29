"""Morphogenese par reaction-diffusion (modele de Gray-Scott).

Outille le notebook **ICT-9** (strate 2 de la serie ICT). Le substrat est le
systeme de **Gray-Scott** (P. Gray & S. K. Scott, 1983-84 ; J. E. Pearson,
*Complex Patterns in a Simple System*, Science 1993) — un couple de deux
especes chimiques ``U`` et ``V`` qui diffusent et reagissent :

    dU/dt = Du * Lap(U)  -  U * V^2  +  F * (1 - U)
    dV/dt = Dv * Lap(V)  +  U * V^2  -  (F + k) * V

* ``U`` : substrat, reapprovisionne au taux ``F`` (terme ``F * (1 - U)``) ;
* ``V`` : activateur autocatalytique (le terme ``U * V^2`` consomme ``U`` et
  produit ``V``), retire au taux ``F + k`` ;
* ``Du``, ``Dv`` : coefficients de diffusion (``Du > Dv`` : l'inhibiteur diffuse
  plus vite que l'activateur — la condition de Turing) ;
* ``F`` : *feed rate* ; ``k`` : *kill rate* — les deux **parametres de controle**
  qui selectionnent le regime morphologique (taches, rayures, vers, chaos...).

C'est une **vraie morphogenese generative** : a partir d'un germe localise, le
systeme **engendre** spontanement un motif spatial structure et **auto-entretenu**
(un attracteur de forme), la ou une simple diffusion ne ferait que tout lisser
vers l'etat uniforme. C'est cette difference qui fonde la mesure d'agence du
notebook ICT-9 (cf. :mod:`ict.agency`).

Le regime par defaut (``F = 0.0367``, ``k = 0.0649``, ``Du = 0.16``,
``Dv = 0.08``) est le regime **taches mitotiques** (*spots* qui se divisent) de
Pearson, robuste et lisible. Le pas de temps ``dt = 1.0`` respecte la condition
de stabilite explicite en 2D (``Du * dt / dx^2 = 0.16 <= 0.25``, ``dx = 1``).

Numpy uniquement (Laplacien 5 points vectorise via ``numpy.roll``, bords
periodiques), comme le reste du package leger ``ict``.
"""

from __future__ import annotations

from typing import List, Optional, Tuple

import numpy as np


def laplacian(field: np.ndarray) -> np.ndarray:
    """Laplacien discret 5 points a bords periodiques (vectorise via ``roll``).

    Stencil orthogonal standard ``[[0,1,0],[1,-4,1],[0,1,0]]`` avec ``dx = 1`` :
    somme des quatre voisins moins quatre fois le centre. Les bords periodiques
    (tore) evitent les artefacts de bord et conservent la masse globale du terme
    diffusif.
    """
    return (
        np.roll(field, 1, axis=0)
        + np.roll(field, -1, axis=0)
        + np.roll(field, 1, axis=1)
        + np.roll(field, -1, axis=1)
        - 4.0 * field
    )


class GrayScott:
    """Systeme de reaction-diffusion de Gray-Scott sur une grille periodique.

    Parameters
    ----------
    F : float
        *Feed rate* (reapprovisionnement de ``U``). Defaut ``0.0367``.
    k : float
        *Kill rate* (retrait de ``V``). Defaut ``0.0649``.
    Du, Dv : float
        Coefficients de diffusion de ``U`` et ``V``. Defauts ``0.16`` / ``0.08``.
    dt : float
        Pas de temps explicite (Euler). Defaut ``1.0`` (stable pour ces ``Du``).
    """

    def __init__(
        self,
        F: float = 0.0367,
        k: float = 0.0649,
        Du: float = 0.16,
        Dv: float = 0.08,
        dt: float = 1.0,
    ):
        self.F = float(F)
        self.k = float(k)
        self.Du = float(Du)
        self.Dv = float(Dv)
        self.dt = float(dt)

    # -- initialisation --------------------------------------------------- #
    def seed(
        self,
        n: int = 96,
        block: int = 12,
        noise: float = 0.02,
        rng: Optional[np.random.Generator] = None,
    ) -> Tuple[np.ndarray, np.ndarray]:
        """Etat initial : substrat sature (``U = 1``, ``V = 0``) avec un germe.

        Un petit bloc central est ensemence (``U = 0.5``, ``V = 0.25``) plus un
        bruit faible ``noise`` qui brise la symetrie et amorce la morphogenese.
        Le bruit est seede via ``rng`` pour une sortie reproductible.
        """
        if rng is None:
            rng = np.random.default_rng(0)
        U = np.ones((n, n), dtype=float)
        V = np.zeros((n, n), dtype=float)
        lo = n // 2 - block // 2
        hi = lo + block
        U[lo:hi, lo:hi] = 0.50
        V[lo:hi, lo:hi] = 0.25
        if noise > 0.0:
            U += noise * rng.standard_normal((n, n))
            V += noise * rng.standard_normal((n, n))
        np.clip(U, 0.0, 1.0, out=U)
        np.clip(V, 0.0, 1.0, out=V)
        return U, V

    # -- dynamique -------------------------------------------------------- #
    def step(self, U: np.ndarray, V: np.ndarray) -> Tuple[np.ndarray, np.ndarray]:
        """Un pas d'Euler explicite du couple reaction-diffusion."""
        reaction = U * V * V
        U_new = U + self.dt * (self.Du * laplacian(U) - reaction + self.F * (1.0 - U))
        V_new = V + self.dt * (self.Dv * laplacian(V) + reaction - (self.F + self.k) * V)
        np.clip(U_new, 0.0, 1.0, out=U_new)
        np.clip(V_new, 0.0, 1.0, out=V_new)
        return U_new, V_new

    def run(
        self,
        U: np.ndarray,
        V: np.ndarray,
        steps: int,
        record_every: int = 0,
        include_initial: bool = False,
    ) -> Tuple[np.ndarray, np.ndarray, Optional[List[np.ndarray]]]:
        """Integre ``steps`` pas. Retourne ``(U, V, snapshots)``.

        Si ``record_every > 0``, ``snapshots`` est la liste des champs ``V``
        captures tous les ``record_every`` pas (pour les courbes temporelles et
        les animations) ; sinon ``snapshots`` vaut ``None``.

        Si ``include_initial`` est vrai (et ``record_every > 0``), l'etat ``V``
        **avant le premier pas** (t = 0) est insere en tete de ``snapshots``. Par
        defaut la capture commence apres le premier pas : pour une courbe de
        recuperation qui part de l'etat ablate exact, passer ``include_initial=True``
        garantit que le point de depart de la trajectoire est bien l'instant 0.
        """
        snapshots: Optional[List[np.ndarray]] = [] if record_every > 0 else None
        if snapshots is not None and include_initial:
            snapshots.append(V.copy())
        for t in range(steps):
            U, V = self.step(U, V)
            if snapshots is not None and (t % record_every == 0):
                snapshots.append(V.copy())
        return U, V, snapshots


def pure_diffusion_step(field: np.ndarray, D: float, dt: float = 1.0) -> np.ndarray:
    """Un pas de **diffusion pure** (l'equation de la chaleur, sans reaction).

    Sert de **controle degrade** dans ICT-9 : meme operateur de diffusion, mais
    prive du couplage reactif autocatalytique. Une forme soumise a la seule
    diffusion se **dissout** vers l'uniforme — elle ne se reconstruit jamais.
    """
    return field + dt * D * laplacian(field)


def run_pure_diffusion(
    field: np.ndarray, D: float, steps: int, dt: float = 1.0
) -> np.ndarray:
    """Integre ``steps`` pas de diffusion pure sur ``field``."""
    out = field.copy()
    for _ in range(steps):
        out = pure_diffusion_step(out, D, dt)
    return out
