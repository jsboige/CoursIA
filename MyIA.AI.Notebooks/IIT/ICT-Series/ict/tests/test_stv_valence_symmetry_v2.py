"""Tests instrument - case 17bis (STV v2, structure du lock).

Chaque test cible une piece scellee du protocole : detecteur m:n + classe
(pas de double compte), reconstruction de u, Spearman partiel par decile,
exclusions NaN de S, null a3, controle mecanique (irrationnelles libres,
exactes = plafond cinematique DECLARE), determinisme de la jambe, echelle
du null b, et gel des bandes du scelle.
"""

from __future__ import annotations

import numpy as np
import pytest

from ict import stv_valence_symmetry as v1
from ict import stv_valence_symmetry_v2 as stv2

K = v1.K
N_TIMES = 1200   # fenetre analysee : seconde moitie, 1 point sur 4


def _synth_phases(omegas, n_conf=1, seed=0):
    """Phases (N_TIMES, n_conf, K) de rotations libres aux frequences donnees."""
    rng = np.random.default_rng(seed)
    dt = stv2.DT * stv2.SUBSAMPLE
    t = np.arange(N_TIMES) * dt
    ph = omegas[None, None, :] * t[:, None, None]
    ph = ph + rng.uniform(0, 2 * np.pi, size=(1, n_conf, K))
    return np.broadcast_to(ph, (N_TIMES, n_conf, K)).copy()


# --- Detecteur m:n + classes ---

def test_lock_unison_all_1_1():
    v, s, counts = stv2.lock_analysis(_synth_phases(np.ones(K)))
    assert v[0] == pytest.approx(1.0)
    assert counts[0, 0] == K * (K - 1) // 2   # toutes en classe 1:1
    assert s[0] == pytest.approx(0.0, abs=1e-12)


def test_lock_mixed_1_1_and_2_1():
    # 4 lentes (indice bas) puis 4 rapides : croisees -> 2:1 classees.
    omegas = np.array([1.0] * 4 + [2.0] * 4)
    v, s, counts = stv2.lock_analysis(_synth_phases(omegas))
    assert v[0] == pytest.approx(1.0)
    assert counts[0, 0] == 12 and counts[0, 3] == 16  # 1:1 et 2:1
    assert s[0] == pytest.approx(
        -(12 / 28 * np.log(12 / 28) + 16 / 28 * np.log(16 / 28))
        / np.log(6), rel=1e-6)


def test_lock_reversed_order_unclassed_counts_in_v():
    # Rapides en indice bas : croisees -> ratio 1:2, HORS des 6 classes.
    # Elles comptent dans v mais pas dans S (comportement declare).
    omegas = np.array([2.0] * 4 + [1.0] * 4)
    v, s, counts = stv2.lock_analysis(_synth_phases(omegas))
    assert v[0] == pytest.approx(1.0)
    assert counts.sum(axis=1)[0] == 12            # seules les 1:1 classees
    assert 0.0 < s[0] < 1e-12 or s[0] == 0.0      # distribution uniforme


def test_lock_free_incommensurate():
    # Racines de premiers distincts : aucun |a*om_i - b*om_j| < SLOPE_TOL
    # (min mesure ~ 0.096), aucune paire ne verrouille.
    omegas = np.sqrt(np.array([1.0, 2.0, 3.0, 5.0, 7.0, 11.0, 13.0, 17.0]))
    v, s, _c = stv2.lock_analysis(_synth_phases(omegas))
    assert v[0] < 0.05
    assert not np.isfinite(s[0])


# --- Reconstruction de u ---

def test_u_hat_full_ladder_exact():
    assert stv2.u_hat(np.array(v1.HARMONIC_LADDER)) == pytest.approx(1.0)


def test_u_hat_one_member_shifted():
    row = np.array(v1.HARMONIC_LADDER, dtype=float)
    row[3] *= 1.05
    assert stv2.u_hat(row) == pytest.approx((K - 1) / K)


def test_gate_pools_available_sealed_semantics():
    """Portes scellees : pools u_hat = 1 (echelle exacte) et u_hat = 1/8
    (echelle entierement decalee -- ancre seule exacte) non vides aux
    graines test. Un filtre a u_hat <= 0 serait toujours vide : l'ancre
    1.0 est toujours presente dans le tirage v1."""
    for seed in stv2.SEEDS_TEST:
        cfg = v1.draw_configs(seed, stv2.M_CONFIGS, n_pairs=stv2.M_PAIRS)
        u_arr = np.array([stv2.u_hat(rr)
                          for rr in cfg["ratios"][:cfg["n_ladder"]]])
        assert u_arr.min() == pytest.approx(1 / 8)
        assert (u_arr >= 0.999).sum() >= 5          # pool porte plancher
        assert (u_arr <= 1 / 8 + 1e-9).sum() >= 5   # pool porte plafond


# --- Spearman partiel par deciles de sigma ---

def test_partial_spearman_independent_eps():
    rng = np.random.default_rng(7)
    sigma0 = rng.uniform(0.2, 0.9, 120)
    v_base = rng.normal(0.5, 0.1, 120)
    v_eps = {str(e): v_base.tolist() for e in stv2.EPS_GRID}
    assert abs(stv2._decile_partial_spearman(v_eps, sigma0)) < 0.25


def test_partial_spearman_driven_eps():
    rng = np.random.default_rng(7)
    sigma0 = rng.uniform(0.2, 0.9, 120)
    v_eps = {str(e): (0.5 + 3.0 * e + 0.01 * rng.normal(size=120)).tolist()
             for e in stv2.EPS_GRID}
    # Rangs globaux aux ex aequo d'eps pres : 0.85, tres au-dela du cas
    # independant (< 0.25 ci-dessus).
    assert stv2._decile_partial_spearman(v_eps, sigma0) > 0.85


# --- Moyennes S avec exclusions, null a3 ---

def test_mean_s_excluding_nan():
    mean, excl = stv2._mean_s_excluding_nan([0.5, float("nan"), 0.7])
    assert mean == pytest.approx(0.6)
    assert excl == 1
    mean0, excl0 = stv2._mean_s_excluding_nan([float("nan")])
    assert not np.isfinite(mean0) and excl0 == 1


def test_perm_null_a3_identical_pools_zero():
    d = {"s_pairs": [0.5] * 40, "m": 20}
    assert stv2._perm_null_a3(d, draws=50) == pytest.approx(0.0)


def test_perm_null_a3_below_true_contrast():
    rng = np.random.default_rng(1)
    h = rng.uniform(0.7, 0.9, 20).tolist()
    n = rng.uniform(0.1, 0.3, 20).tolist()
    d = {"s_pairs": h + n, "m": 20}
    null = stv2._perm_null_a3(d, draws=200)
    assert 0.0 <= null < 0.4            # tres en deca du contraste vrai ~0.6


# --- Controle mecanique ---

def test_mechanical_control_irr_free_exact_kinematic_5_seeds():
    """Controle mecanique scelle « sur 5/5 graines » (§3) : chaque graine
    porte sa propre instance du controle (irrationnelles libres -> porte ;
    membres exacts -> plafond cinematique DECLARE, diagnostic)."""
    for seed in stv2.SEEDS_TEST:
        ctrl = stv2._mechanical_control_v2(seed)
        assert ctrl["seed"] == seed
        assert ctrl["v0_irr_mean"] <= stv2.CTRL_V0_MAX   # porte scellee
        assert ctrl["v0_exact_mean"] > 0.4               # plafond DECLARE (diag)


# --- Jambe complete (short) + determinisme ---

def test_run_seed_v2_smoke_deterministic(monkeypatch):
    monkeypatch.setattr(stv2, "T_TOTAL", 3.0)
    a = stv2.run_seed_v2(0, 8.0, m_configs=4, n_pairs=2, eps_grid=(0.0,))
    b = stv2.run_seed_v2(0, 8.0, m_configs=4, n_pairs=2, eps_grid=(0.0,))
    # Comparaison par JSON : l'egalite flottante directe est muette sur les
    # nan (S des configurations sans paire classee), presents ici.
    import json
    assert json.dumps(a) == json.dumps(b)
    for key in ("v_eps", "v_pairs", "s_pairs", "r_bar_pairs",
                "sigma_ladder", "u_ladder"):
        assert key in a
    assert len(a["v_pairs"]) == 4 and len(a["u_ladder"]) == 4


def test_strong_null_uses_x8_scale(monkeypatch):
    captured = {}

    def fake_run(seed, k2_c, **kw):
        captured["seed"], captured["k2_c"] = seed, k2_c
        return {"v_eps": {"0.0": [0.1, 0.4]},
                "sigma_ladder": [0.3, 0.5]}

    monkeypatch.setattr(stv2, "run_seed_v2", fake_run)
    stv2._strong_result_v2(10.0)
    assert captured["k2_c"] == pytest.approx(10.0 * stv2.NULL_B_SCALE)
    assert captured["seed"] == v1.SEEDS_TEST[0]


# --- Gel des bandes scellees ---

def test_sealed_bands_frozen():
    assert stv2.BAND_P1 == 0.6 and stv2.BAND_P1_FAIL == 0.2
    assert stv2.BAND_P2 == 0.2
    assert stv2.BAND_P3 == 0.25 and stv2.BAND_P2_FAIL == 0.5
    assert stv2.BAND_P3_FAIL == 0.10
    assert stv2.GATE_V_U1 == 0.3 and stv2.GATE_V_U0 == 0.7
    assert stv2.GATE_MATCH_RB == 0.15 and stv2.CTRL_V0_MAX == 0.05
    assert stv2.NULL_B_SCALE == 8.0
    assert stv2.RATIO_CLASSES == (1.0, 4 / 3, 1.5, 2.0, 3.0, 4.0)
