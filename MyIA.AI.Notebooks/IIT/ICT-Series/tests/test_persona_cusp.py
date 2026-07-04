"""Tests du module ``ict.persona_cusp`` -- EPIC #4588 / #5104 (ICT-23).

Couvre les 3 predictions de l'Epic #5104 traduites en jumeau cusp de
Thom :

* **P0** (aplatissement par inoculation) : ``charge -> 0`` doit faire
  sortir la persona de la region bistable, meme a transgression forte.
* **P1** (hysteresis conditionnelle) : sous ``charge > 0``, un balayage
  aller-retour de la recompense doit montrer **deux sauts** ; sous
  inoculation (``charge ~ 0``), le suivi doit etre **continu**.
* **P2** (EWS Wissel/Scheffer) : variance et AR1 doivent monter avant
  la bascule (ralentissement critique), et rester plats sous inoculation.

Toutes les fonctions sont numpy-only et deterministes (graine fixee pour
les SDE). Cf. ``tests/test_catastrophe.py`` pour le pattern de tests de
la primitive cusp partagee.
"""

from __future__ import annotations

import numpy as np
import pytest

from ict.persona_cusp import (
    ews_summary_persona,
    inoculation_check,
    inoculation_signature,
    in_persona_bistable_region,
    persona_a_factor,
    persona_catastrophe_indices,
    persona_force,
    persona_hysteresis_loop,
    persona_potential,
    persona_sde,
    relax_persona,
)


# --------------------------------------------------------------------------- #
#  P0 -- bistabilite conditionnelle a la charge semantique                     #
# --------------------------------------------------------------------------- #


def test_a_factor_sign():
    """``a = -transgression * charge`` : negatif si les deux positifs."""
    assert persona_a_factor(2.0, 0.5) == pytest.approx(-1.0)
    assert persona_a_factor(0.0, 0.5) == 0.0
    assert persona_a_factor(2.0, 0.0) == 0.0
    assert persona_a_factor(2.0, -0.5) == pytest.approx(1.0)


def test_inoculation_zero_flattens_bistability():
    """P0 : charge=0 => plus de bistabilite, meme a transgression forte."""
    # charge = 0 => a = 0 => monostable (un seul bassin)
    assert not in_persona_bistable_region(transgression=5.0, charge=0.0, reward=0.0)
    assert not in_persona_bistable_region(transgression=5.0, charge=0.0, reward=1.0)
    # charge > 0 + transgression suffisante => bistable
    assert in_persona_bistable_region(transgression=2.0, charge=1.0, reward=0.0)


def test_inoculation_check_threshold():
    """Le predicat ``inoculation_check`` est vrai sous le seuil 1e-3."""
    assert inoculation_check(0.0)
    assert inoculation_check(1e-4)
    assert not inoculation_check(1e-2)
    assert not inoculation_check(0.5)


def test_potential_equals_cusp_at_zero_charge():
    """Charge nulle => ``V(p) = p^4/4 + b p`` (pas de terme quadratique)."""
    p = np.linspace(-2.0, 2.0, 5)
    v_charge0 = persona_potential(p, transgression=3.0, charge=0.0, reward=0.5)
    v_ref = p ** 4 / 4 + 0.5 * p
    assert np.allclose(v_charge0, v_ref)


def test_force_is_negative_gradient_of_potential():
    """Cohence ``dp/dt = -dV/dp`` sur une grille de points."""
    p = np.linspace(-1.5, 1.5, 7)
    h = 1e-4
    for tr, ch, rw in [(2.0, 0.8, 0.0), (1.0, 0.5, 0.2), (0.0, 0.0, 0.5)]:
        v_plus = persona_potential(p + h, tr, ch, rw)
        v_minus = persona_potential(p - h, tr, ch, rw)
        grad_num = (v_plus - v_minus) / (2 * h)
        f = persona_force(p, tr, ch, rw)
        assert np.allclose(f, -grad_num, atol=1e-6), (tr, ch, rw)


# --------------------------------------------------------------------------- #
#  P1 -- hysteresis conditionnelle : 2 catastrophes sans inoculation, 0 avec  #
# --------------------------------------------------------------------------- #


def _rampe_recompenses(sym_max: float = 2.0, n_up: int = 60) -> np.ndarray:
    """Rampe symetrique aller-retour comme ICT-10 (perception + capture)."""
    up = np.linspace(-sym_max, sym_max, n_up)
    down = np.linspace(sym_max, -sym_max, n_up)
    return np.concatenate([up, down])


def test_hysteresis_loop_two_catastrophes_without_inoculation():
    """P1 : sous charge semantique forte, 2 catastrophes sur le lacet."""
    rewards = _rampe_recompenses(sym_max=1.5, n_up=80)
    ps = persona_hysteresis_loop(
        transgression=2.0,
        charge=0.8,  # inoculation absente
        rewards=rewards,
        dt=0.01,
        relax_steps=400,
    )
    n_cat = len(persona_catastrophe_indices(rewards, ps, threshold=0.5))
    assert n_cat == 2, f"Attendu 2 catastrophes, vu {n_cat}"


def test_hysteresis_loop_continuous_with_full_inoculation():
    """P0 dynamique : sous charge=0, suivi continu, 0 saut."""
    rewards = _rampe_recompenses(sym_max=1.5, n_up=80)
    ps = persona_hysteresis_loop(
        transgression=2.0,
        charge=0.0,  # inoculation totale
        rewards=rewards,
        dt=0.01,
        relax_steps=400,
    )
    n_cat = len(persona_catastrophe_indices(rewards, ps, threshold=0.5))
    assert n_cat == 0, f"Attendu 0 catastrophe (inoculation), vu {n_cat}"


def test_hysteresis_loop_range_monotone_when_monostable():
    """Monostable => ``p`` reste dans un intervalle borne par le balayage."""
    rewards = _rampe_recompenses(sym_max=2.0, n_up=50)
    ps = persona_hysteresis_loop(
        transgression=2.0,
        charge=0.0,  # inoculation => monostable
        rewards=rewards,
        dt=0.01,
        relax_steps=300,
    )
    # Sous monostabilite, p doit rester proche du minimum unique (p ~ -b).
    # La plage ne doit pas montrer le saut caracteristique des 2 bassins.
    assert ps.max() - ps.min() < 3.0, (
        f"Plage inattendue sous monostabilite : "
        f"min={ps.min():.3f}, max={ps.max():.3f}"
    )


def test_relax_converges_to_equilibrium():
    """La relaxation aboutit a un zero de la force (equilibre cusp)."""
    # Demarre loin du minimum attendu
    p_final = relax_persona(
        p0=2.0,
        transgression=2.0,
        charge=0.8,
        reward=0.0,
        dt=0.01,
        steps=5000,
    )
    f_final = persona_force(p_final, 2.0, 0.8, 0.0)
    assert abs(f_final) < 1e-3, f"Force residuelle {f_final}"


# --------------------------------------------------------------------------- #
#  P2 -- EWS Wissel/Scheffer avant le pli                                       #
# --------------------------------------------------------------------------- #


def test_ews_distinguish_bistable_vs_monostable():
    """P2 : les EWS (variance, AR1) sont plus eleves en regime bistable
    qu'en regime monostable (inoculation). C'est la **signature**
    Wissel/Scheffer (cf ICT-8 / ICT-20) : le ralentissement critique
    n'apparait que quand la bifurcation est proche.

    Note : on ne teste PAS ``tau > 0`` directement sur une seule
    trajectoire (signe depend de la graine + seed) ; on teste que la
    **difference** bistable - monostable est positive et marquee.
    C'est le diagnostic haut-niveau de P2.
    """
    T = 20000
    # Regime bistable (charge forte -> a < 0)
    ps_bi = persona_sde(
        transgression=2.0, charge=0.8, reward=0.05,
        p0=0.0, sigma=0.05, dt=0.01, T=T, seed=20260704,
    )
    # Regime monostable par inoculation (charge = 0 -> a = 0)
    ps_mono = persona_sde(
        transgression=2.0, charge=0.0, reward=0.05,
        p0=0.0, sigma=0.05, dt=0.01, T=T, seed=20260704,
    )
    sum_bi = ews_summary_persona(ps_bi, window=500, thin_factor=5, detrend_sigma=2.0)
    sum_mono = ews_summary_persona(ps_mono, window=500, thin_factor=5, detrend_sigma=2.0)
    # La variance moyenne est plus elevee en bistable (le systeme
    # "hesite" entre les 2 bassins) qu'en monostable (autour d'un seul).
    assert sum_bi["variance_mean"] > sum_mono["variance_mean"], (
        f"variance bistable {sum_bi['variance_mean']:.4f} doit etre > "
        f"variance monostable {sum_mono['variance_mean']:.4f}"
    )


def test_ews_ar1_higher_in_bistable_regime():
    """P2 (variante) : l'AR1 (autocorrelation lag-1) est plus eleve en
    regime bistable qu'en monostable -- le systeme "hesite" et la
    dynamique presente une memoire courte plus marquee."""
    T = 20000
    ps_bi = persona_sde(
        transgression=2.0, charge=0.8, reward=0.05,
        p0=0.0, sigma=0.05, dt=0.01, T=T, seed=20260704,
    )
    ps_mono = persona_sde(
        transgression=2.0, charge=0.0, reward=0.05,
        p0=0.0, sigma=0.05, dt=0.01, T=T, seed=20260704,
    )
    sum_bi = ews_summary_persona(ps_bi, window=500, thin_factor=5, detrend_sigma=2.0)
    sum_mono = ews_summary_persona(ps_mono, window=500, thin_factor=5, detrend_sigma=2.0)
    # AR1 plus grand en bistable (le "bruit" est plus correle).
    assert sum_bi["ar1_mean"] > sum_mono["ar1_mean"], (
        f"AR1 bistable {sum_bi['ar1_mean']:.4f} doit etre > "
        f"AR1 monostable {sum_mono['ar1_mean']:.4f}"
    )


# --------------------------------------------------------------------------- #
#  Signature d'inoculation : courbe N_catastrophes(charge) decroissante        #
# --------------------------------------------------------------------------- #


def test_inoculation_signature_monotone_decreasing():
    """La signature ``N_catastrophes(charge)`` est decroissante : 2 sous
    charge forte, 0 sous inoculation totale. Le **diagnostic haut niveau**
    de P0/P1 d'#5104."""
    rewards = _rampe_recompenses(sym_max=1.5, n_up=60)
    sig = inoculation_signature(
        transgression=2.0,
        rewards=rewards,
        charges=(0.0, 0.3, 0.6, 0.9),
    )
    n_cat_by_charge = [sig[c]["n_catastrophes"] for c in sorted(sig)]
    # 0 sous inoculation totale, >=1 sous forte charge.
    assert n_cat_by_charge[0] == 0.0
    assert n_cat_by_charge[-1] >= 1.0
    # Monotone non-croissant.
    for i in range(len(n_cat_by_charge) - 1):
        assert n_cat_by_charge[i + 1] >= n_cat_by_charge[i], n_cat_by_charge