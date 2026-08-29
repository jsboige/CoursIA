# -*- coding: utf-8 -*-
"""Tests du module limit_sets.py (GameTheory-26, Poincare-Bendixson).

Backing notebook : GameTheory-26-Ensembles-Limites-Poincare-Bendixson.ipynb.

Ces tests assertent des **invariants de theorie connus**, pas seulement
l'absence de crash :

1. Dilemme du Prisonnier 2 populations -> convergence au sommet (D, D) :
   l'equilibre strict est un point fixe attracteur (regime POINT_FIXE).
2. Matching Pennies 2 populations -> orbites fermees : premier retour au
   point initial ET conservation exacte de l'invariant x(1-x)y(1-y)
   (c'est la preuve numerique de la fermeture des orbites).
3. RPS w > l -> le barycentre attire (POINT_FIXE) ; RPS w < l -> omega-limite
   = cycle heteroclinique de la frontiere (CYCLE_HETEROCLINIQUE), avec temps
   de sejour par sommet croissants (ralentissement heteroclinique).
4. RPS w = l (mur antisymetrique) -> orbites periodiques neutres.
5. Le verdict ne depend ni du pas d'integration (dt vs dt/2) ni de la
   condition initiale dans le bassin.
6. RK4 conserve exactement les invariants lineaires (sommes des deux
   populations a 1, sommes du simplexe a 1).
7. Regression anti-faux-positif : une rampe heteroclinique profonde (drift
   terminal ~ 1e-17) ne doit PAS etre classee point fixe — chaque depart
   d'un sommet refute la convergence vers ce sommet.
"""

import sys
from pathlib import Path

import numpy as np
import pytest

sys.path.insert(0, str(Path(__file__).parent.parent))

import limit_sets as ls  # noqa: E402


# =============================================================================
# Parametres canoniques des trois regimes (partages avec le notebook)
# =============================================================================

def run_pd(t_max=30.0, dt=1e-3, x0=(0.6, 0.4)):
    A, B = ls.prisoner_dilemma_matrices()
    rhs = lambda z: ls.replicator_2pop_rhs(A, B, z)
    return ls.integrate_rk4(rhs, ls.make_state_2pop(*x0), t_max, dt)


def run_mp(t_max=20.0, dt=1e-3, x0=(0.35, 0.6)):
    A, B = ls.matching_pennies_matrices()
    rhs = lambda z: ls.replicator_2pop_rhs(A, B, z)
    return ls.integrate_rk4(rhs, ls.make_state_2pop(*x0), t_max, dt)


def run_rps(w, l, t_max=120.0, dt=1e-3, x0=(0.4, 0.35, 0.25)):
    A = ls.rps_matrix(w, l)
    rhs = lambda x: ls.replicator_1pop_rhs(A, x)
    return ls.integrate_rk4(rhs, np.array(x0, dtype=float), t_max, dt)


# =============================================================================
# 1-2-3 : les trois regimes
# =============================================================================

def test_pd_point_fixe_au_sommet_dd():
    t, tr = run_pd()
    regime, info = ls.detect_regime(t, tr)
    assert regime == ls.POINT_FIXE
    # l'etat final est le sommet (D, D) : action 2 dominante chez les deux
    # populations (x -> 0, y -> 0).
    x, y = ls.unpack_2pop(tr[-1])
    assert x == pytest.approx(0.0, abs=1e-6)
    assert y == pytest.approx(0.0, abs=1e-6)


def test_matching_pennies_orbites_fermees():
    t, tr = run_mp()
    regime, info = ls.detect_regime(t, tr)
    assert regime == ls.ORBITE_PERIODIQUE
    # preuve de fermeture : l'invariant x(1-x)y(1-y) est conserve
    inv = np.array([ls.mp_invariant(z) for z in tr])
    assert np.ptp(inv) < 1e-12 * inv[0]
    # et la trajectoire revient pres de son point de depart
    assert info["premier_retour"] is not None


def test_rps_perdant_cycle_heteroclinique_avec_ralentissement():
    t, tr = run_rps(w=1.0, l=2.0, t_max=120.0)
    regime, info = ls.detect_regime(t, tr)
    assert regime == ls.CYCLE_HETEROCLINIQUE
    # signature du ralentissement : les temps de sejour par sommet croissent
    # (chaque tour de cycle prend plus longtemps que le precedent).
    gaps = np.array(info["temps_de_sejour"])
    assert len(gaps) >= 4
    assert gaps[-1] > gaps[1]
    assert gaps[-1] >= 2.0 * gaps[len(gaps) // 2]


# =============================================================================
# Les deux cotes du mur w = l
# =============================================================================

def test_rps_gagnant_barycentre_attracteur():
    t, tr = run_rps(w=2.0, l=1.0)
    regime, _ = ls.detect_regime(t, tr)
    assert regime == ls.POINT_FIXE
    assert np.allclose(tr[-1], np.full(3, 1.0 / 3.0), atol=1e-4)


def test_rps_mur_antisymetrique_orbites_neutres():
    t, tr = run_rps(w=1.0, l=1.0, t_max=40.0)
    regime, info = ls.detect_regime(t, tr)
    assert regime == ls.ORBITE_PERIODIQUE
    # sur le mur, l'amplitude ne derive pas : la distance au barycentre
    # oscille au sein d'une periode (la boucle n'est pas un cercle) mais son
    # max sur la premiere moitie egale celui sur la seconde (orbite fermee,
    # ni spirale rentrante ni sortante).
    bary = np.full(3, 1.0 / 3.0)
    r = np.linalg.norm(tr - bary, axis=1)
    assert abs(r[:len(r) // 2].max() - r[len(r) // 2:].max()) < 1e-3 * r.max()


# =============================================================================
# Stabilite du verdict
# =============================================================================

@pytest.mark.parametrize("runner", [run_pd, run_mp,
                                    lambda **kw: run_rps(1.0, 2.0, **kw)],
                         ids=["pd", "mp", "rps-perdant"])
def test_regime_stable_au_pas(runner):
    ref = ls.detect_regime(*runner(dt=1e-3))[0]
    demi = ls.detect_regime(*runner(dt=5e-4))[0]
    assert ref == demi


@pytest.mark.parametrize("runner,x0_alt", [
    (run_pd, (0.63, 0.37)),
    (run_mp, (0.42, 0.55)),
    (lambda **kw: run_rps(1.0, 2.0, **kw), (0.38, 0.34, 0.28)),
], ids=["pd", "mp", "rps-perdant"])
def test_regime_stable_a_la_condition_initiale(runner, x0_alt):
    ref = ls.detect_regime(*runner())[0]
    alt = ls.detect_regime(*runner(x0=x0_alt))[0]
    assert ref == alt


# =============================================================================
# Invariants numeriques de l'integrateur
# =============================================================================

def test_rk4_conserve_les_sommes_exactement():
    t, tr = run_mp()
    assert np.allclose(tr[:, 0] + tr[:, 1], 1.0, atol=1e-14)
    assert np.allclose(tr[:, 2] + tr[:, 3], 1.0, atol=1e-14)
    t3, tr3 = run_rps(1.0, 1.0, t_max=40.0)
    assert np.allclose(tr3.sum(axis=1), 1.0, atol=1e-14)


def test_simplexe_invariant_interieur_reste_interieur():
    # une trajectoire interieure ne quitte jamais le simplexe (positivite)
    t, tr = run_rps(1.0, 2.0, t_max=60.0)
    assert np.min(tr) >= 0.0


# =============================================================================
# Chasse au Cerf : point fixe, mais transit pre-selle (anti-faux-positif)
# =============================================================================

def _run_stag_hunt(x0, t_max=60.0, dt=1e-3):
    A, B = ls.stag_hunt_matrices()
    rhs = lambda z: ls.replicator_2pop_rhs(A, B, z)
    return ls.integrate_rk4(rhs, ls.make_state_2pop(*x0), t_max, dt)


def test_cerf_transit_pre_selle_pas_un_cycle():
    # (0.45, 0.6) passe pres de la selle interieure avant de converger vers
    # (Cerf, Cerf). Un argmax sur le 4-uple entier y produisait un
    # clignotement de dominance 2 pops aux gaps ~0.03 s, lu a tort comme un
    # ralentissement heteroclinique. La dominance par simplexe + le plancher
    # absolu (sejour >= 1) doivent laisser passer le regime POINT_FIXE.
    t, tr = _run_stag_hunt((0.45, 0.6))
    regime, info = ls.detect_regime(t, tr)
    assert regime == ls.POINT_FIXE
    x, y = ls.unpack_2pop(tr[-1])
    assert x > 0.99 and y > 0.99


def test_cerf_bassins_des_deux_attracteurs():
    # la variete stable x + y = 1 separe les bassins : au-dessus -> Cerf,
    # en dessous -> Lievre. Le regime est POINT_FIXE des deux cotes.
    for x0, attends_cerf in [((0.6, 0.6), True), ((0.3, 0.3), False)]:
        t, tr = _run_stag_hunt(x0)
        regime, _ = ls.detect_regime(t, tr)
        assert regime == ls.POINT_FIXE
        x, y = ls.unpack_2pop(tr[-1])
        assert (x > 0.99 and y > 0.99) == attends_cerf


# =============================================================================
# Regression : la rampe heteroclinique profonde n'est pas un point fixe
# =============================================================================

def test_rampe_profonde_pas_un_point_fixe():
    # a t_max=200, la fenetre terminale est immobile (drift ~ 1e-17) alors
    # que l'ensemble omega-limite est le cycle, pas un sommet. Chaque depart
    # de dominance observe dans la trajectoire refute la convergence.
    t, tr = run_rps(1.0, 2.0, t_max=200.0)
    regime, info = ls.detect_regime(t, tr)
    assert regime == ls.CYCLE_HETEROCLINIQUE
    assert info["drift_final"] < 1e-3  # la fenetre terminale est bien immobile
