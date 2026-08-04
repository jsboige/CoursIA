"""Tests unitaires pour ``ict.bistable`` (ICT-8 / strate 2, Epic #4588).

Le module ``ict.bistable.GrazingModel`` est le substrat canonique des
*early-warning signals* (Scheffer et al. 2009) : le **modele de paturage de
May** (Nature 1977), systeme a bifurcation pli (*fold*). C'est le point
d'ancrage d'ICT-8 et le banc d'essai de la theorie des catastrophes de la
serie ICT. Ces gates falsifient ses proprietes physiques/maths (cadre des
**bifurcations et dynamique non-lineaire** -- distinct de l'algebre lineaire
de ``ict.spectral``) :

  1. (Gate equilibria = racines de rate) pour tout equilibre ``x*`` retourne
     par ``equilibria(c)``, ``rate(x*, c) ~= 0`` (definition d'un point fixe).

  2. (Gate stabilite vs signe de rate_prime) un equilibre est stable ssi
     ``rate_prime(x*, c) < 0`` (puits = minimum du potentiel V), instable ssi
     ``> 0`` (col = maximum de V). La signature de la derivee seconde du
     potentiel ``-rate_prime`` discrimine puits/col.

  3. (Gate potentiel = primitive de -rate) ``V`` est defini par
     ``dV/dx = -rate`` ; verifie numeriquement (gradient de V ~= -rate).

  4. (Gate x=0 instable) l'etat nu ``x=0`` a ``rate_prime(0, c) > 0`` : la
     response de broutage type III s'annule en ``x^2`` pres de zero, donc la
     vegetation repart toujours du quasi-neant (point documente docstring).

  5. (Gate bistabilite sous c_fold) pour ``c`` nettement sous le pli, le
     cubique a >= 2 racines positives (etat haut vegetalise + etat bas
     surpature + instable entre) ; au-dela de ``c_fold``, < 2 (bascule
     monostable sur l'etat bas). C'est la signature de la bifurcation pli.

  6. (Gate relax converge vers stable) ``relax(x0, c)`` atteint un etat
     proche d'un equilibre **stable** (Euler deterministe suit le gradient
     de V vers un minimum, jamais un col).

  7. (Gate reflexion SDE) ``simulate_sde`` ne produit jamais de valeurs
     negatives (biomasse reflechie a 0).

  8. (Gate determinisme) meme seed => trajectoire SDE identique (Euler-Maruyama
     deterministe pour un generateur fixe).

Implementation : numpy seul + import du package ``ict``. Le modele est
construit avec ses valeurs canoniques (r=1, K=10, h=1) sauf indication.
"""

from __future__ import annotations

import sys
import os

# Permettre l'import direct depuis ict package (sans installer en mode develop).
_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

import numpy as np
import pytest

from ict.bistable import GrazingModel


# --------------------------------------------------------------------------- #
#  Modele canonique (May 1977, valeurs par defaut r=1, K=10, h=1)              #
# --------------------------------------------------------------------------- #
@pytest.fixture
def model():
    return GrazingModel(r=1.0, K=10.0, h=1.0)


# --------------------------------------------------------------------------- #
#  Gate 1 : equilibria = racines de rate                                       #
# --------------------------------------------------------------------------- #
def test_equilibria_are_roots_of_rate(model):
    """Tout equilibre x* verifie rate(x*, c) ~= 0 (point fixe du flot)."""
    for c in [1.0, 2.0, 2.5, 3.0]:
        for x_star, _stable in model.equilibria(c):
            assert abs(model.rate(x_star, c)) < 1e-6, (
                f"rate({x_star}, c={c}) ~= 0 attendu (equilibre), got {model.rate(x_star, c)}"
            )


def test_equilibria_includes_origin(model):
    """L'etat nu x=0 est toujours un equilibre (retourne en premiere position)."""
    eqs = model.equilibria(2.0)
    assert eqs[0][0] == 0.0, f"x=0 doit etre equilibre (biomasse nulle), got {eqs[0]}"


# --------------------------------------------------------------------------- #
#  Gate 2 : stabilite vs signe de rate_prime (puits vs col)                    #
# --------------------------------------------------------------------------- #
def test_stability_matches_rate_prime_sign(model):
    """stable ssi rate_prime(x*, c) < 0 (puits), instable ssi > 0 (col)."""
    for c in [1.5, 2.0, 2.5]:
        for x_star, stable in model.equilibria(c):
            rp = model.rate_prime(x_star, c)
            if stable:
                assert rp < 0, (
                    f"equilibre stable {x_star} (c={c}) doit avoir rate_prime < 0, got {rp}"
                )
            else:
                assert rp >= 0, (
                    f"equilibre instable {x_star} (c={c}) doit avoir rate_prime >= 0, got {rp}"
                )


# --------------------------------------------------------------------------- #
#  Gate 3 : potentiel V = primitive de -rate                                   #
# --------------------------------------------------------------------------- #
def test_potential_is_antiderivative_of_negative_rate(model):
    """dV/dx = -rate (relation de definition du potentiel effectif).

    Verifie numeriquement (gradient central dense). On exclut les bords du
    domaine car ``np.gradient`` y utilise des differences avancees moins
    precises ; l'interieur (slice [20:-20]) est compare a ``atol=5e-3``.
    Verifie au prealable que la derivee analytique coincide a la precision
    machine (1e-15) -- garantie que le module est correct, le test ne mesure
    que la precision du gradient numerique.
    """
    c = 2.0
    xs = np.linspace(0.3, 11.0, 2000)
    V = model.potential(xs, c)
    dVdx = np.gradient(V, xs)
    neg_rate = -model.rate(xs, c)
    # Garantie analytique : -rate est bien la derivee de V (precision machine).
    r, K, h = model.r, model.K, model.h
    dVdx_ana = -r * xs + r * xs ** 2 / K + c - c * h ** 2 / (xs ** 2 + h ** 2)
    assert np.allclose(dVdx_ana, neg_rate, atol=1e-12), (
        "garantie analytique : dV/dx analytique = -rate a la precision machine"
    )
    # Gradient numerique (interieur seulement, bord exclu).
    assert np.allclose(dVdx[20:-20], neg_rate[20:-20], atol=5e-3), (
        f"dV/dx numerique ~= -rate sur l'interieur, ecart max = "
        f"{np.max(np.abs(dVdx[20:-20] - neg_rate[20:-20]))}"
    )


def test_stable_equilibrium_is_potential_minimum(model):
    """Un equilibre stable correspond a un minimum local de V (puits)."""
    c = 2.0
    eqs = model.equilibria(c)
    stable_xs = [x for x, s in eqs if s and x > 1e-6]
    assert len(stable_xs) >= 1, "sous c_fold, au moins un equilibre haut stable"
    x_high = max(stable_xs)
    V_around = model.potential(
        np.array([x_high - 0.5, x_high, x_high + 0.5]), c
    )
    # Le puits : V au centre < V des deux cotes (minimum local).
    assert V_around[1] < V_around[0] and V_around[1] < V_around[2], (
        f"equilibre stable haut {x_high} doit etre un min de V, got V={V_around}"
    )


# --------------------------------------------------------------------------- #
#  Gate 4 : x=0 instable (la vegetation repart du quasi-neant)                 #
# --------------------------------------------------------------------------- #
def test_origin_is_unstable(model):
    """rate_prime(0, c) > 0 : l'etat nu est instable (response type III en x^2)."""
    for c in [1.0, 2.0, 3.0]:
        rp0 = model.rate_prime(0.0, c)
        assert rp0 > 0, (
            f"x=0 instable (rate_prime(0,c)>0), got {rp0} pour c={c}"
        )


# --------------------------------------------------------------------------- #
#  Gate 5 : bistabilite sous c_fold vs monostabilite au-dela                   #
# --------------------------------------------------------------------------- #
def test_fold_separates_bistable_and_monostable(model):
    """c_fold = borne ou l'etat haut disparait : sous, >=2 racines ; au-dela, <2."""
    c_fold = model.find_fold()
    assert 1.5 < c_fold < 3.5, f"c_fold dans [1.5, 3.5] attendu, got {c_fold}"
    # Nettement sous le pli : bistable (>= 2 racines positives).
    n_below = len(model._positive_roots(c_fold - 0.3))
    assert n_below >= 2, (
        f"sous c_fold (bistable), >=2 racines positives attendues, got {n_below}"
    )
    # Au-dela du pli : monostable (< 2 racines positives = bascule sur l'etat bas).
    n_above = len(model._positive_roots(c_fold + 0.3))
    assert n_above < 2, (
        f"au-dela c_fold (monostable), <2 racines positives attendues, got {n_above}"
    )


# --------------------------------------------------------------------------- #
#  Gate 6 : relax converge vers un equilibre stable                            #
# --------------------------------------------------------------------------- #
def test_relax_converges_to_stable_equilibrium(model):
    """relax(x0, c) atteint un etat proche d'un equilibre stable (jamais un col)."""
    c = 2.0
    stable_xs = [x for x, s in model.equilibria(c) if s]
    # Depuis une condition initiale haute, on tombe sur l'etat haut stable.
    x_final = model.relax(x0=8.0, c=c, dt=0.01, steps=20000)
    assert any(abs(x_final - xs) < 0.5 for xs in stable_xs), (
        f"relax(8.0, c={c})={x_final} doit atteindre un equilibre stable parmi {stable_xs}"
    )


# --------------------------------------------------------------------------- #
#  Gate 7 : reflexion SDE (biomasse non negative)                              #
# --------------------------------------------------------------------------- #
def test_simulate_sde_never_negative(model):
    """La trajectoire stochastique ne produit jamais x < 0 (reflexion a 0)."""
    traj = model.simulate_sde(c=2.0, x0=5.0, sigma=2.0, dt=0.05, T=500, seed=42)
    assert np.all(traj >= 0.0), (
        f"biomasse reflechie a 0, min observe = {traj.min()}"
    )


def test_simulate_sde_shape_and_finite(model):
    """La trajectoire a la bonne taille et reste finie (pas d'explosion numerique)."""
    traj = model.simulate_sde(c=2.0, x0=5.0, sigma=0.5, dt=0.05, T=1000, seed=7)
    assert traj.shape == (1000,)
    assert np.all(np.isfinite(traj)), "trajectoire doit rester finie"


# --------------------------------------------------------------------------- #
#  Gate 8 : determinisme (meme seed => meme trajectoire)                       #
# --------------------------------------------------------------------------- #
def test_simulate_sde_deterministic_for_fixed_seed(model):
    """Deux runs avec le meme seed donnent des trajectoires identiques."""
    t1 = model.simulate_sde(c=2.0, x0=5.0, sigma=0.5, dt=0.05, T=500, seed=99)
    t2 = model.simulate_sde(c=2.0, x0=5.0, sigma=0.5, dt=0.05, T=500, seed=99)
    assert np.array_equal(t1, t2), "meme seed => trajectoires identiques (Euler-Maruyama)"


def test_simulate_ramp_returns_states_and_control(model):
    """simulate_ramp renvoie (xs, cs) avec c glissant lineairement de c0 vers c1.

    NB : ``range(T)`` discrétise t=0..T-1, donc le dernier pas atteint
    ``c0 + (c1-c0)*(T-1)/T`` (pas c1 exactement) — comportement standard
    d'une rampe discrétisée. On vérifie le démarrage exact (c0) et la fin
    approchée (dernier pas ~= c1 à un incrément près).
    """
    c0, c1, T = 1.5, 3.5, 500
    xs, cs = model.simulate_ramp(c0=c0, c1=c1, x0=8.0, sigma=0.3, dt=0.05, T=T, seed=1)
    assert xs.shape == cs.shape == (T,)
    assert np.isclose(cs[0], c0), f"c commence a c0={c0}, got {cs[0]}"
    expected_last = c0 + (c1 - c0) * (T - 1) / T
    assert np.isclose(cs[-1], expected_last), (
        f"dernier pas c ~= {expected_last} (c0+(c1-c0)*(T-1)/T), got {cs[-1]}"
    )
    # Monotonie : c croit strictement (rampe montante).
    assert np.all(np.diff(cs) > 0), "c doit croitre strictement (rampe montante)"
    assert np.all(xs >= 0.0), "biomasse reflechie a 0 pendant la rampe"
