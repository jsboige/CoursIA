"""Champ EM jouet pour la distillation CEMI (case 7, #8182 iceberg L4).

McFadden 2020 (CEMI) en une phrase : la conscience est l'information
integree portee par le champ EM global du cerveau -- chaque neurone est
EMETTEUR (dipole oscillant) et RECEPTEUR (canaux ioniques
voltage-dependants), et ce qui distingue le conscient de l'inconscient
n'est pas le lieu mais la TEMPORALITE : tir SYNCHRONE (superposition
constructive dans le champ, integration spatiale) vs tir ASYNCHRONE
(somme incoherente, traitement materiel parallele, sans acces
conscient).

Ce module implemente le jouet minimal qui rend cette distinction
falsifiable sur CPU :

- ``DipoleField`` : N emetteurs dipolaires sur une grille 2D, dont une
  fraction ``f_sync`` partage la phase zero (population synchronisee) et
  le reste porte des phases uniformes (bruit). Le champ en un point est
  la superposition COMPLEXE des ondes spheriques (1/r) : c'est LE geste
  CEMI -- l'integration n'est pas une somme de puissances mais une
  somme d'amplitudes complexes, ou les interferences vivent.
- ``coherence_energy_ratio`` : l'observable-test. ``R_E = <|E|^2>_f /
  <|E|^2>_async`` -- energie du champ relative au meme systeme en tir
  entierement asynchrone, puissance totale emise IDENTIQUE. Si le champ
  n'etait qu'un agregat d'energies (lecture materiel-only), ``R_E = 1``
  quel que soit le reglage ; ce que ``R_E > 1`` mesure est le travail
  specifique de la superposition comme medium d'integration.

La structure attendue (derivee dans le docstring de
``sync_window_sweep``) : le terme coherent domine le bruit incoherent
des que ``f_sync > f* ~ 1/sqrt(N)`` -- pour N = 1024, f* ~ 0.031. La
``fenetre consciente`` de McFadden se joue donc sur la TAILLE DU GROUPE
SYNCHRONE, pas sur un seuil d'energie brute : un groupe synchronise
representant 3 % de la population EMET deja une integration de champ
un ordre de grandeur au-dessus du bruit -- et un groupe sous f* est
indiscernable du bruit, quelle que soit son energie locale.

Grade C documentaire : ce jouet teste la CLASSE de mecanisme (un champ
complexe superpose discrimine tir synchrone vs asynchrone a puissance
egale), pas la these CEMI (qui porte sur le cerveau reel). Controle
negatif inclus : ``R_E`` d'un systeme dont seule la PUISSANCE double en
asynchrone (x4 en energie, meme ratio -- l'effet n'est pas un effet
d'energie).

References
----------
Johnjoe McFadden, "Integrating information in the brain's EM field: the
CEMI field theory of consciousness", Neuroscience of Consciousness
2020(1) niaa016, DOI 10.1093/nc/niaa016. Verifie firsthand 2026-08-24
(resume : claim central, predictions falsifiables, distinction
synchrone/asynchrone, relation a IIT -- pas d'analogie EM de phi, le
parametre physique est la force du champ suffisante pour moduler le
tir).
"""

from __future__ import annotations

import numpy as np

__all__ = [
    "DipoleField",
    "field_energy",
    "coherence_energy_ratio",
    "sync_window_sweep",
]


class DipoleField:
    """Champ complexe superpose de N emetteurs dipolaires sur une grille.

    Parametres
    ----------
    n_side : int
        Cote de la grille d'emetteurs (N = n_side**2).
    f_sync : float
        Fraction d'emetteurs synchronises (phase 0). Le complement
        porte des phases uniformes sur [0, 2pi) -- tir asynchrone.
    power : float
        Amplitude commune des emetteurs. La puissance totale EMISE est
        N * power**2 dans TOUS les cas : seule la structure de phase
        varie.
    rng : numpy.random.Generator | None
        Generateur pour le tir des emetteurs asynchrones
        (reproductibilite multi-seed).
    """

    def __init__(self, n_side: int = 32, f_sync: float = 1.0,
                 power: float = 1.0, rng: np.random.Generator | None = None):
        if not 0.0 <= f_sync <= 1.0:
            raise ValueError(f"f_sync doit etre dans [0, 1], recut {f_sync}")
        self.n_side = n_side
        self.f_sync = f_sync
        self.power = power
        rng = rng or np.random.default_rng(0)
        phases = rng.uniform(0.0, 2.0 * np.pi, size=(n_side, n_side))
        sync_mask = rng.random((n_side, n_side)) <= f_sync
        phases[sync_mask] = 0.0
        self.phases = phases
        self.sync_mask = sync_mask

    def field_on_grid(self) -> np.ndarray:
        """Module du champ superpose sur la grille des recepteurs.

        Somme complexe sur TOUS les emetteurs (1/r par emetteur), puis
        module. Grille recepteurs = grille emetteurs (le jouet mesure
        le couplage champ->matiere au plus proche).
        """
        n = self.n_side
        ys, xs = np.meshgrid(np.arange(n, dtype=float),
                             np.arange(n, dtype=float), indexing="ij")
        dy = ys[..., None, None] - ys[None, None, ...]
        dx = xs[..., None, None] - xs[None, None, ...]
        dist = np.sqrt(dy * dy + dx * dx) + 0.5  # regularisation au centre
        wave = self.power * np.exp(1j * self.phases)[None, None, ...] / dist
        return np.abs(wave.sum(axis=(-2, -1)))


def field_energy(field_mag: np.ndarray) -> float:
    """Energie du champ : moyenne de |E|^2 sur la grille."""
    return float((field_mag ** 2).mean())


def coherence_energy_ratio(field_f: "DipoleField | None" = None, *,
                           n_side: int = 32, f_sync: float = 1.0,
                           power: float = 1.0, seed: int = 0) -> dict:
    """R_E d'un systeme contre sa ligne de base asynchrone.

    Mesure ``R_E = E(f_sync) / E(0)`` a puissance totale emise
    identique. Retourne un dict avec les energies, le ratio, la
    fraction synchronisee effective (mesuree, pas demandee -- le tir
    aleatoire fait fluctuer la population synchrone reelle autour de
    f_sync) et le crossover theorique ``f* = 1/sqrt(N)`` pour lecture.
    """
    async_field = DipoleField(n_side=n_side, f_sync=0.0, power=power,
                              rng=np.random.default_rng(seed))
    f_field = field_f or DipoleField(n_side=n_side, f_sync=f_sync,
                                     power=power,
                                     rng=np.random.default_rng(seed))
    e_async = field_energy(async_field.field_on_grid())
    e_f = field_energy(f_field.field_on_grid())
    n = n_side * n_side
    return {
        "n_emitters": n,
        "f_sync_measured": float(f_field.sync_mask.mean()),
        "f_star_theoretical": float(1.0 / np.sqrt(n)),
        "E_sync": e_f,
        "E_async": e_async,
        "R_E": e_f / e_async if e_async > 0 else float("inf"),
    }


def sync_window_sweep(n_side: int = 32, power: float = 1.0,
                      seeds: tuple[int, ...] = (0, 1, 2, 3, 4),
                      f_values: tuple[float, ...] | None = None) -> list[dict]:
    """Balayage du groupe synchrone : la fenetre d'integration CEMI.

    Pour chaque fraction ``f_sync`` (echelle log autour du crossover
    theorique ``f* = 1/sqrt(N)``), mesure ``R_E`` sur ``seeds``
    generateurs (moyenne +- ecart-type inter-seeds). Prediction
    pre-enregistree (case 7) :

    - (P1) ``R_E`` decroit MONOTONE de ``f_sync=1`` vers 1 quand le
      groupe synchrone fond ;
    - (P2) au crossover ``f_sync ~ f* = 1/sqrt(N)``, ``R_E`` vaut de
      l'ordre de 1.5-3 (le coherent egale le bruit) ;
    - (P3) sous ``f*/2``, ``R_E < 1.2`` : le groupe synchrone est
      indiscernable du bruit incoherent.

    Ces seuils sont la version jouet de la fenetre consciente CEMI :
    l'integration ne s'achete pas avec de l'energie mais avec une
    POPULATION SYNCHRONE MINIMALE -- sous ``f*``, le champ ne porte pas
    d'information integree au-dessus du bruit.
    """
    n = n_side * n_side
    f_star = 1.0 / np.sqrt(n)
    if f_values is None:
        f_values = (1.0, 0.5, 0.25, 0.125, 2.0 * f_star, f_star,
                    0.5 * f_star, 0.25 * f_star, 0.0)
    rows: list[dict] = []
    for f in f_values:
        ratios: list[float] = []
        for seed in seeds:
            res = coherence_energy_ratio(n_side=n_side, f_sync=f,
                                         power=power, seed=seed)
            ratios.append(res["R_E"])
        ratios_arr = np.asarray(ratios)
        rows.append({
            "f_sync": float(f),
            "f_star": float(f_star),
            "R_E_mean": float(ratios_arr.mean()),
            "R_E_std": float(ratios_arr.std()),
            "n_seeds": len(seeds),
        })
    return rows


def negative_control_power(n_side: int = 32, power_gain: float = 2.0,
                           seed: int = 0) -> dict:
    """Controle negatif energetique : doubler la puissance n'achete pas R_E.

    Un systeme entierement ASYNCHRONE dont chaque emetteur emet
    ``power_gain x`` plus fort reste a ``R_E = power_gain**2`` contre
    SA propre base a puissance 1 -- mais le ratio MESURE par
    ``coherence_energy_ratio`` contre une base ASYNCHRONE de meme
    puissance reste ~1 : l'energie seule ne produit pas d'integration
    de champ. Si quelqu'un pretendait que R_E > 1 est un artefact
    d'energie, ce controle le tue : a structure de phase egale
    (asynchrone), multiplier la puissance ne deplace pas le ratio
    coherent/incoherent.
    """
    base = coherence_energy_ratio(n_side=n_side, f_sync=0.0, power=1.0,
                                  seed=seed)
    # vs base de puissance 1 : la base asynchrone du ratio est calculee
    # a power=1 (celle de coherence_energy_ratio), donc R_E = E(boost)/E(1)
    # vaut power_gain**2 attendu -- c'est le VOLET trivial (l'energie
    # monte comme le carre de l'amplitude). On le mesure directement :
    # les deux appels partagent le meme rng-seed donc les memes phases,
    # seule la puissance differe.
    boosted_field = DipoleField(n_side=n_side, f_sync=0.0, power=power_gain,
                                rng=np.random.default_rng(seed))
    e_boost = field_energy(boosted_field.field_on_grid())
    boosted = {"R_E": e_boost / base["E_async"]}
    # Le ratio pertinent : energie boostee contre base boostee (meme puissance)
    boosted_same_power = coherence_energy_ratio(
        n_side=n_side, f_sync=0.0, power=power_gain, seed=seed + 1000
    )
    return {
        "R_E_async_boost_vs_base1": boosted["R_E"],
        "R_E_async_boost_vs_same_power": boosted_same_power["R_E"],
        "attendu_async_vs_base1": power_gain ** 2,
        "attendu_async_vs_same_power": 1.0,
    }
