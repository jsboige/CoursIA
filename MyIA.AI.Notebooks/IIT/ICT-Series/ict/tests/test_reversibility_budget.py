"""Tests du module :mod:`ict.reversibility_budget` (ICT-18b, Epic #4588).

Chaque test valide une propriete falsifiable du budget de reversibilite,
numerotee par *gate* pour le cross-reference avec les predictions P1/P2/P3
du notebook ICT-18b. Pattern herite de ``test_time_arrow.py`` : bootstrap
``sys.path`` module-level, sans fixtures, tolerances commentees.
"""

from __future__ import annotations

import os
import sys

import numpy as np
import pytest

_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

from ict import reversibility_budget as rb  # noqa: E402
from ict import time_arrow  # noqa: E402


def _rng_for(seed: int) -> np.random.Generator:
    return np.random.default_rng(seed)


# --------------------------------------------------------------------------- #
#  Gate 1 : sample_ball est uniforme dans le volume                            #
# --------------------------------------------------------------------------- #


def test_sample_ball_uniform_in_volume():
    """L'echantillonnage est uniforme dans la boule (pas concentre au centre).

    Pour une boule 2-D de rayon 1, la fraction de points dans le disque
    interieur de rayon 0.5 doit valoir ``0.5**2 = 0.25`` (les volumes vont
    comme r^n). Une concentration au centre donnerait >> 0.25 ; une
    concentration sur la surface donnerait ~ 0.
    """
    rng = _rng_for(1)
    pts = rb.sample_ball(radius=1.0, n_dims=2, n_samples=20000, rng=rng)
    assert pts.shape == (20000, 2)
    norms = np.linalg.norm(pts, axis=1)
    # Tous dans la boule de rayon 1.
    assert norms.max() <= 1.0 + 1e-9
    # Fraction dans le disque interieur de rayon 0.5 ~= 0.25 (a l'echantillonnage).
    frac_inner = float(np.mean(norms <= 0.5))
    assert abs(frac_inner - 0.25) < 0.02, (
        f"uniformite volumique attendue (frac_inner ~= 0.25), recu {frac_inner}"
    )


def test_sample_ball_1d_is_uniform():
    """En dimension 1, sample_ball = uniforme sur [-radius, radius]."""
    rng = _rng_for(2)
    pts = rb.sample_ball(radius=3.0, n_dims=1, n_samples=10000, rng=rng)
    # Moyenne ~= 0, |max| <= 3.
    assert abs(float(pts.mean())) < 0.2
    assert float(np.abs(pts).max()) <= 3.0 + 1e-9


# --------------------------------------------------------------------------- #
#  Gate 2 : B_state = 1 sur un attracteur stable, 0 sur un etat perdu          #
# --------------------------------------------------------------------------- #


def test_state_space_budget_stable_attractor_returns_one():
    """Un attracteur stable lineaire renvoie un budget maximal.

    Dynamique : ``x_{t+1} = 0.5 * x`` (contraction vers 0). Toute perturbation
    dans une boule finie revient a l'origine. ``B_state(r, tau)`` doit etre
    ~1.0 des que ``tau`` est assez grand pour que la contraction ramene l'etat
    dans la consigne.
    """
    rng = _rng_for(3)

    def contract(x: np.ndarray) -> np.ndarray:
        return 0.5 * x

    anchor = np.array([0.0])
    B = rb.state_space_budget(
        contract, anchor, radius=1.0, tau=8, n_samples=300, rng=rng,
        consigne_radius=0.1,
    )
    # Apres 8 pas de facteur 0.5, |x0| <= 1 => |x_tau| <= 1/256 ~= 4e-3 < 0.1.
    assert B >= 0.98, f"attracteur stable : B devrait etre ~1.0, recu {B}"


def test_state_space_budget_lost_attractor_returns_zero():
    """Une dynamique qui fuit l'ancre renvoie un budget nul.

    Dynamique : ``x_{t+1} = x + 1`` (translation). Toute perturbation est
    poussee vers le grand ``+infty`` ; aucun retour a l'ancre.
    """
    rng = _rng_for(4)

    def diverge(x: np.ndarray) -> np.ndarray:
        return x + 1.0

    anchor = np.array([0.0])
    B = rb.state_space_budget(
        diverge, anchor, radius=0.5, tau=5, n_samples=300, rng=rng,
        consigne_radius=0.2,
    )
    assert B <= 0.02, f"etat perdu : B devrait etre ~0.0, recu {B}"


def test_state_space_budget_decreases_with_perturbation_size():
    """Plus la perturbation est grande, plus le budget s'epuise (sur seuil).

    Dynamique : ``x_{t+1} = clip(x, -1, 1)`` (le seuil a +/- 1 est l'attracteur
    plat ; au-dela l'etat est clippe). Une petite perturbation autour de 0 est
    dans la zone de retour ; une perturbation >= 1 part d'un bord clippe.
    Le budget (taux de retour dans la consigne) decroit avec le rayon.
    """
    rng = _rng_for(5)

    def threshold(x: np.ndarray) -> np.ndarray:
        return np.clip(x, -1.0, 1.0)

    anchor = np.array([0.0])
    radii = [0.2, 0.5, 1.0, 2.0, 5.0]
    curve = rb.budget_curve(
        threshold, anchor, radii=radii, tau=3, n_samples=400, rng=rng,
        consigne_radius=0.2,
    )
    # Monotone decroissant (a la tolerance d'echantillonnage pres).
    for a, b in zip(curve[:-1], curve[1:]):
        assert b <= a + 0.05, (
            f"budget doit decroitre avec le rayon, recu {curve}"
        )


# --------------------------------------------------------------------------- #
#  Gate 3 : B_work = 0 sur une chaine reversible, > 0 sinon                    #
# --------------------------------------------------------------------------- #


def test_work_budget_reversible_chain_is_zero():
    """Une chaine symetrique (detailed balance par construction) : B_work ~ 0."""
    P = np.array([[0.5, 0.5], [0.5, 0.5]])
    pi = np.array([0.5, 0.5])
    bw = rb.work_budget(P, pi)
    assert bw < 1e-9, f"chaine reversible : B_work ~= 0, recu {bw}"


def test_work_budget_irreversible_chain_positive():
    """Un cycle dirige 3-etats : B_work strictement positif."""
    P = np.array([[0.0, 1.0, 0.0], [0.0, 0.0, 1.0], [1.0, 0.0, 0.0]])
    pi = np.array([1 / 3, 1 / 3, 1 / 3])
    bw = rb.work_budget(P, pi)
    # La chaine est completement irreversible (P_rev la moyennise) -> distance
    # maximale pour k=3. L1/2 ~= somme des |1 - 1/3| / 2 sur 6 hors-diagonaux.
    assert bw > 1.0, f"cycle dirige : B_work eleve attendu, recu {bw}"


def test_work_budget_normalized_in_unit_interval():
    """B_work normalise reste dans [0, 1]."""
    P = np.array([[0.1, 0.9], [0.4, 0.6]])
    pi = time_arrow.stationary_distribution(P)
    bwn = rb.work_budget_normalized(P, pi)
    assert 0.0 <= bwn <= 1.0


# --------------------------------------------------------------------------- #
#  Gate 4 : co-variation budget <-> EWS (lecture-ressource, P1)               #
# --------------------------------------------------------------------------- #


def test_covariation_contract_valid_on_synthetic_collapse():
    """Le contrat lecture-ressource se valide sur une donnee synthetique.

    On simule l'approche d'un pli : le parametre croit, le budget decroit
    (le bassin se retracte) et l'EWS croit (critical slowing down). Le contrat
    ``tau_budget_vs_ews <= -0.5`` doit etre valide.
    """
    param = np.arange(1, 11, dtype=float)  # parametre croissant vers le pli
    budgets = 1.0 / param  # budget decroissant (retraction du bassin)
    ews = param.astype(float) ** 2  # EWS croissant (variance qui explose)
    diag = rb.covariation_with_ews(param, budgets, ews)
    assert diag["contract_valid"], (
        f"contrat lecture-ressource devrait etre valide, diag={diag}"
    )
    assert diag["tau_budget"] <= -0.5
    assert diag["tau_ews"] >= 0.5
