"""Modele bistable a bifurcation pli (*fold*) et paysage d'attracteurs.

Outille le notebook **ICT-8**. Le substrat est le **modele de paturage de May**
(R. M. May, *Thresholds and breakpoints in ecosystems...*, Nature 1977), le
systeme canonique sur lequel la litterature des *early-warning signals* a ete
batie (Scheffer et al. 2009 ; Dakos et al. 2012) :

    dx/dt = r * x * (1 - x / K)  -  c * x^2 / (x^2 + h^2)

* ``x`` : biomasse de vegetation (paramètre d'ordre, mesurable) ;
* ``r``, ``K`` : croissance logistique (taux, capacite de charge) ;
* ``c`` : pression de broutage (le **paramètre de controle** qu'on fait varier) ;
* ``h`` : demi-saturation du broutage (réponse fonctionnelle de type II).

C'est un **vrai modele a bifurcation pli**, pas un potentiel-jouet ajuste a la
main : pour ``c`` faible le systeme presente **deux etats stables alternatifs**
(Scheffer) — un etat **vegetalise haut** (``x`` eleve) et un etat **surpature
bas** (``x`` faible) — separes par un equilibre instable. (L'etat vraiment vide
``x = 0`` est, lui, *instable* : la reponse de broutage de type III s'annule en
``x^2`` pres de zero, donc la vegetation repart toujours du quasi-neant.) Quand
``c`` franchit ``c_fold``, l'equilibre haut et l'instable **fusionnent et
disparaissent** (le pli) : le systeme bascule alors **catastrophiquement** vers
l'etat surpature bas — un *changement de regime*, non une extinction. Le paysage
d'attracteurs se lit sur le **potentiel effectif** ``V(x)`` defini par
``dx/dt = -dV/dx`` : ses minima sont les attracteurs, et le puits haut
**s'aplatit** a l'approche du pli — ce qui *est* le ralentissement critique.

Numpy uniquement (racines de polynome via ``numpy.roots``), comme le package
leger ``ict``.
"""

from __future__ import annotations

from typing import List, Tuple

import numpy as np


class GrazingModel:
    """Modele de paturage de May : bistabilite, pli, paysage d'attracteurs."""

    def __init__(self, r: float = 1.0, K: float = 10.0, h: float = 1.0):
        self.r = float(r)
        self.K = float(K)
        self.h = float(h)

    # -- champ de vitesse et derivees ------------------------------------- #
    def rate(self, x, c: float):
        """dx/dt au point ``x`` pour une pression de broutage ``c``."""
        x = np.asarray(x, dtype=float)
        return self.r * x * (1 - x / self.K) - c * x * x / (x * x + self.h ** 2)

    def rate_prime(self, x, c: float):
        """Derivee df/dx (valeur propre locale ; < 0 => equilibre stable)."""
        x = np.asarray(x, dtype=float)
        graze = 2 * x * self.h ** 2 / (x * x + self.h ** 2) ** 2
        return self.r * (1 - 2 * x / self.K) - c * graze

    def potential(self, x, c: float):
        """Potentiel effectif ``V(x)`` tel que ``dx/dt = -dV/dx``.

        ``V(x) = -r x^2/2 + r x^3/(3K) + c x - c h arctan(x/h)``.
        Derive analytiquement du modele (aucun ajustement) : ses minima sont les
        attracteurs, le puits haut s'aplatit a l'approche du pli.
        """
        x = np.asarray(x, dtype=float)
        return (-self.r * x ** 2 / 2
                + self.r * x ** 3 / (3 * self.K)
                + c * x
                - c * self.h * np.arctan(x / self.h))

    # -- equilibres et bifurcation ---------------------------------------- #
    def _positive_roots(self, c: float) -> List[float]:
        # equilibres non nuls : racines du cubique
        #   x^3 - K x^2 + (h^2 + cK/r) x - K h^2 = 0
        coeffs = [1.0, -self.K, self.h ** 2 + c * self.K / self.r, -self.K * self.h ** 2]
        roots = np.roots(coeffs)
        real = roots[np.abs(roots.imag) < 1e-9].real
        return sorted(float(x) for x in real if x > 1e-9)

    def equilibria(self, c: float) -> List[Tuple[float, bool]]:
        """Liste ``(x*, stable)`` des equilibres (l'etat nu ``x=0`` inclus)."""
        xs = [0.0] + self._positive_roots(c)
        return [(x, bool(self.rate_prime(x, c) < 0)) for x in xs]

    def find_fold(self, c_lo: float = 1.5, c_hi: float = 3.5, n: int = 4000) -> float:
        """Localise ``c_fold`` : plus grand ``c`` ou subsiste un equilibre haut.

        Au-dela, le cubique n'a plus de racine positive (le pli a eu lieu).
        """
        cs = np.linspace(c_lo, c_hi, n)
        last = float("nan")
        for c in cs:
            if len(self._positive_roots(c)) >= 2:
                last = float(c)
        return last

    def bifurcation_branches(self, c_grid):
        """Pour chaque ``c``, renvoie ``(c, x*, stable)`` pour tout equilibre.

        Pratique pour tracer le diagramme de bifurcation (branches stables vs
        instable). Renvoie trois listes plates ``cs, xs, stables``.
        """
        cs, xs, stables = [], [], []
        for c in np.asarray(c_grid, dtype=float):
            for x, st in self.equilibria(c):
                cs.append(float(c)); xs.append(x); stables.append(st)
        return np.array(cs), np.array(xs), np.array(stables, dtype=bool)

    # -- integration ------------------------------------------------------ #
    def relax(self, x0: float, c: float, dt: float = 0.01, steps: int = 20000) -> float:
        """Relaxe deterministe depuis ``x0`` vers l'equilibre atteint (Euler)."""
        x = float(x0)
        for _ in range(steps):
            x = max(0.0, x + dt * float(self.rate(x, c)))
        return x

    def simulate_sde(self, c: float, x0: float, sigma: float, dt: float,
                     T: int, seed: int) -> np.ndarray:
        """Trajectoire stochastique (Euler-Maruyama), bruit additif ``sigma``.

        Reflexion a 0 (une biomasse ne peut etre negative). ``c`` constant :
        regime quasi-stationnaire pour mesurer les EWS a distance fixe du pli.
        """
        g = np.random.default_rng(seed)
        sq = float(np.sqrt(dt))
        x = float(x0)
        xs = np.empty(int(T))
        for t in range(int(T)):
            x = x + dt * float(self.rate(x, c)) + sigma * sq * g.standard_normal()
            if x < 0.0:
                x = 0.0
            xs[t] = x
        return xs

    def simulate_ramp(self, c0: float, c1: float, x0: float, sigma: float,
                      dt: float, T: int, seed: int):
        """Trajectoire ou ``c`` glisse lineairement de ``c0`` a ``c1`` (rampe).

        Renvoie ``(xs, cs)`` — la version non-stationnaire qui traverse le pli.
        """
        g = np.random.default_rng(seed)
        sq = float(np.sqrt(dt))
        x = float(x0)
        T = int(T)
        xs = np.empty(T); cs = np.empty(T)
        for t in range(T):
            c = c0 + (c1 - c0) * t / T
            x = x + dt * float(self.rate(x, c)) + sigma * sq * g.standard_normal()
            if x < 0.0:
                x = 0.0
            xs[t] = x; cs[t] = c
        return xs, cs
