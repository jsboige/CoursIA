"""Tests du banc case 17 — STV : valence comme symetrie (iceberg #8182).

Ces tests valident l'INSTRUMENT (mecanique du banc), pas la these :
chaque prediction P1/P2/P3 est portee par le run principal
(``stv_valence_symmetry.py --json``), jamais par ces tests. Deux tests
portent les premisses des amendements pre-execution : le couplage sin pur
ne produit que des locks 1:1 (amendement v2), et la stationnarite seule
compte les paires libres (amendement v3, detecteur m:n).
"""

from __future__ import annotations

import pickle

import numpy as np
import pytest

from ict import stv_valence_symmetry as stv


# --- Consonance : harmonicite octave-repliee (amendement v3) ---

def test_sigma_ladder_perfect_octave_repliee():
    assert stv.sigma_config(np.array(stv.HARMONIC_LADDER)) == pytest.approx(1.0)


def test_sigma_inharmonic_shift_reduces_harmonicite():
    rng = np.random.default_rng(7)
    ladder = np.array(stv.HARMONIC_LADDER)
    shifted = ladder.copy()
    shifted[1:] = [stv._inharmonic_shift(rng, b) for b in ladder[1:]]
    assert stv.sigma_config(shifted) < 0.5 * stv.sigma_config(ladder)


def test_sigma_monotone_en_decalage():
    base = np.array([1.0, 2.0, 3.0, 4.0, 6.0, 8.0, 12.0, 16.0])
    eps = [0.0, 0.02, 0.05, 0.10]
    sig = []
    for e in eps:
        cfg = base * np.concatenate([[1.0], np.full(7, np.exp(e))])
        sig.append(stv.sigma_config(cfg))
    assert all(s1 > s2 for s1, s2 in zip(sig, sig[1:]))


def test_dissident_ratio_hors_jeu_farey8():
    rng = np.random.default_rng(3)
    for _ in range(200):
        r = stv._dissident_ratio(rng)
        assert 1.0 <= r <= 2.0
        assert np.min(np.abs(np.log(r) - stv.LN_FOLD_SET)) >= stv.DISSIDENT_DIST


# --- Dynamique ---

def test_free_integration_recovers_natural_frequencies():
    """Controle mecanique du scelle : K_c = 0 => phases libres exactes."""
    assert stv._mechanical_control(seed=42)


def test_amendment_premise_harmonic_coupling_needed():
    """Premisse de l'amendement v2 : sans contenu harmonique du couplage,
    les rapports m:n ne se verrouillent pas ; avec H(phi) = 1/h, l'echelle
    octave s'installe partiellement au regime m:n (kc = 32, en deca du
    collapse 1:1 de kc >= 48 — ou les deux bras convergent)."""
    rng = np.random.default_rng(5)
    ratios = np.array([stv.HARMONIC_LADDER])
    ph0 = rng.uniform(0, 2 * np.pi, size=(1, stv.K))
    amps = np.ones((1, stv.K))
    ph_harm = stv.integrate(ratios, ph0, amps, 32.0, t_total=40.0)
    ph_sin = stv.integrate(ratios, ph0, amps, 32.0, t_total=40.0,
                           coupling_harmonics=(1.0,))
    assert stv.v_settling(ph_harm)[0] > 0.2
    assert stv.v_settling(ph_sin)[0] < 0.05


# --- Observables ---

def _synthetic_locks(ratios_list):
    """Phases libres exactes (n_temps, n_configs, K) pour des rapports donnes."""
    n_pts = 800
    t = np.arange(n_pts) * (stv.DT * stv.SUBSAMPLE)
    return np.stack([np.outer(t, np.asarray(r, dtype=float))
                     for r in ratios_list], axis=1)


def test_v_blind_to_ratio_values_and_free_pairs_not_counted():
    """Aveuglement aux VALEURS : locks parfaits 2:1, 3:2 et 4:3 donnent le
    meme v = 1. Et une paire LIBRE stationnaire (sqrt(2), m/n indisponible
    pour m, n <= 4) n'est pas comptee — la degenerescence v2 corrigee."""
    ratios = [(2.0, 1, 1, 1, 1, 1, 1, 1),
              (1.5, 1, 1, 1, 1, 1, 1, 1),
              (4.0 / 3.0, 1, 1, 1, 1, 1, 1, 1),
              (np.sqrt(2.0), 1, 1, 1, 1, 1, 1, 1)]
    v = stv.v_settling(_synthetic_locks(ratios))
    assert v[0] == pytest.approx(1.0, abs=1e-9)
    assert v[1] == pytest.approx(1.0, abs=1e-9)
    assert v[2] == pytest.approx(1.0, abs=1e-9)
    # 28 paires dont 21 locks 1:1 (les sept unisons croises) — les 7 paires
    # portant sqrt(2) echappent a tout (m, n) <= 4 : v = 21/28, PAS 1.
    assert v[3] == pytest.approx(21.0 / 28.0, abs=1e-9)


def test_order_parameter_unison_is_one():
    phases = np.zeros((10, 1, stv.K))
    assert np.allclose(stv.order_parameter(phases), 1.0)


def test_order_parameter_blind_to_mn_lock():
    """r est aveugle aux locks m:n : une paire 2:1 verrouillee ne fait PAS
    converger r vers 1 (il pulse au rythme du repliement), alors qu'un lock
    1:1 exact donne r = 1. Motivation documentee de l'observable v."""
    n_pts = 400
    t = np.arange(n_pts) * 0.01
    theta21 = np.stack([2.0 * t, 1.0 * t])          # paire lockee 2:1
    theta11 = np.stack([1.0 * t, 1.0 * t])          # paire lockee 1:1
    r21 = stv.order_parameter(theta21.T[None, :, :])[0]
    r11 = stv.order_parameter(theta11.T[None, :, :])[0]
    assert np.mean(r11) == pytest.approx(1.0, abs=1e-9)
    assert np.mean(r21) < 0.8


def test_spearman_montone_and_antimonotone():
    a = np.arange(10.0)
    assert stv._spearman(a, a * 2.0 + 1.0) == pytest.approx(1.0)
    assert stv._spearman(a, -a) == pytest.approx(-1.0)


# --- Protocol (instrument seulement) ---

def test_run_seed_shapes_and_slices():
    d = stv.run_seed(0, m_configs=4, k_c=1.0, n_pairs=3, t_total=6.0)
    n_total = 4 + 2 * 3
    assert d["v"].shape == (n_total,)
    assert d["sigma"].shape == (n_total,)
    assert d["slice_ladder"].indices(n_total) == (0, 4, 1)
    assert d["slice_h"].indices(n_total) == (4, 7, 1)
    assert d["slice_n"].indices(n_total) == (7, 10, 1)
    assert d["e"].shape == (n_total,)
    assert np.all((d["sigma"][d["slice_ladder"]] > 0)
                  & (d["sigma"][d["slice_ladder"]] <= 1.0))


def test_run_seed_deterministic():
    kw = dict(m_configs=3, k_c=1.5, n_pairs=2, t_total=4.0)
    a = stv.run_seed(9, **kw)
    b = stv.run_seed(9, **kw)
    assert np.array_equal(a["v"], b["v"])
    assert np.array_equal(a["sigma"], b["sigma"])


def test_p2_perturbation_varies_energy():
    """La perturbation P2 doit faire VARIER E entre configurations (sinon
    rho(v, E) serait NaN par variance nulle)."""
    kw = dict(m_configs=6, k_c=1.5, n_pairs=0, t_total=4.0)
    base = stv.run_seed(0, **kw)
    pert = 1.0 + np.random.default_rng(1000).uniform(
        -0.1, 0.1, size=(base["v"].shape[0], stv.K))
    perturbed = stv.run_seed(0, perturb=pert, **kw)
    assert np.std(perturbed["e"]) > 0
    assert np.std(base["e"]) == pytest.approx(0.0)
    assert np.all(perturbed["e"] > 0.8 * base["e"].mean())
    assert np.all(perturbed["e"] < 1.2 * base["e"].mean())


def test_pool_entrypoints_picklable():
    """Entrees du Pool (spawn Windows) : picklables par reference. Une
    fonction locale ou un lambda ferait echouer le chemin parallele au
    premier run — et le run sequentiel ne le verrait pas."""
    for fn in (stv._seed_result, stv._strong_result):
        assert pickle.loads(pickle.dumps(fn)) is fn


def test_bands_frozen_against_seal():
    """Les bandes implementees sont celles du scelle section 4."""
    assert stv.BAND_P1 == 0.6
    assert stv.BAND_P2 == 0.2
    assert stv.BAND_P3 == 2.0
    assert stv.GATE_RBAR == (0.3, 0.95)
    assert stv.SEEDS_TEST == (0, 1, 7, 42, 99)
    assert stv.SEEDS_CALIB == (11, 22, 33)
    assert set(stv.SEEDS_CALIB).isdisjoint(stv.SEEDS_TEST)
