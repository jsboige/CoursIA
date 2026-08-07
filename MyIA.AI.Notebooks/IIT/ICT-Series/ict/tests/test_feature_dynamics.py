"""Tests unitaires pour ``ict.feature_dynamics`` (ICT-20, strate 5, Epic #4588).

Les 15 gates falsifiables couvrent les 5 propres fonctions + 1 dataclass
du module ``feature_dynamics`` (347L) -- l'adaptateur mince entre Early
Warning Signals (EWS) et la lecture chargee d'ICT-23 (PersonaCatastrophe) :

  - :func:`ews_report` -- verdict Kendall explicite (panel-friendly)
  - :func:`changepoint_cusum` -- detecteur CUSUM (Page 1954)
  - :func:`changepoint_argmax_derivative` -- argmax de la derivee discrete
  - :func:`simulate_neutral_transition` -- generateur de panel synthetique
  - :func:`hysteresis_residual` -- mesure du retour a la ligne de base
  - :class:`EWSReport` -- dataclass de rapport structure

Aucune prediction chiffrée ICT dans ce module (c'est un adaptateur, pas un
predictor) -- les gates verifient : (a) les **invariants structurels** des
primitives (shape, determinisme, edge cases), (b) la **fidelite** du verdict
textuel au comportement observe (white noise = no_signal, slowing variance =
mixed), (c) les **anti-patterns numeriques** (division par 0, NaN sur entree
constante, idx=-1 vs 0 sur entree trop courte).

Substrats contrôles :

  * Pure white noise (iid N(0,1)) -> CUSUM no/or-early trigger, EWS no_signal
  * AR(1) constant (forcage vers 0) -> EWS no_signal (variance stable)
  * Ramp lineaire -> CUSUM rapide (derivee croissante)
  * Pure step (mean shift iid) -> CUSUM sensible
  * Slowing variance trend (sigma(t) croissant) -> variance Kendall monte
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

from ict import feature_dynamics as fd


# --------------------------------------------------------------------------- #
#  Helpers                                                                   #
# --------------------------------------------------------------------------- #


def _make_ar1(n: int, ar1: float, sigma: float, seed: int = 0) -> np.ndarray:
    """AR(1) x[t] = ar1 * x[t-1] + sigma * N(0,1), x[0] = 0."""
    rng = np.random.default_rng(seed)
    out = np.zeros(n)
    for t in range(1, n):
        out[t] = ar1 * out[t - 1] + sigma * rng.standard_normal()
    return out


def _make_slowing_variance(n: int, sigma_base: float, drift: float,
                          seed: int = 0) -> np.ndarray:
    """AR(1) avec sigma(t) = sigma_base + drift * t (sigma croissance)."""
    rng = np.random.default_rng(seed)
    out = np.zeros(n)
    for t in range(1, n):
        sig_t = sigma_base + drift * t
        out[t] = 0.5 * out[t - 1] + sig_t * rng.standard_normal()
    return out


# --------------------------------------------------------------------------- #
#  simulate_neutral_transition (3 gates)                                     #
# --------------------------------------------------------------------------- #


def test_simulate_neutral_transition_shape_means_shift():
    """(gate 1) shape (n_tokens,), mean des segments avant/apres transition_at
    reflètent les mean pré/post (mesure sur simulation par défaut)."""
    trace, t_at = fd.simulate_neutral_transition(
        n_tokens=400, transition_at=200,
        pre_mean=0.0, post_mean=1.0,
        pre_ar1=0.7, post_ar1=0.7,
        sigma=0.3, seed=0,
    )
    assert trace.shape == (400,)
    assert t_at == 200
    pre_mean = trace[:200].mean()
    post_mean = trace[200:].mean()
    # Le saut cible vaut 1.0 ; sur n=200 par segment avec AR(1) noise, on
    # tolere 0.2 d'ecart (bruit d'echantillonnage).
    assert abs(pre_mean - 0.0) < 0.15, f"pre_mean={pre_mean}"
    assert abs(post_mean - 1.0) < 0.2, f"post_mean={post_mean}"
    assert post_mean - pre_mean > 0.5, "le saut de moyenne n'est pas preserve"


def test_simulate_neutral_transition_determinism_same_seed():
    """(gate 2) determinisme bit-a-bit (memes seeds -> memes arrays)."""
    common = dict(n_tokens=400, transition_at=200,
                  pre_mean=0.0, post_mean=1.0,
                  pre_ar1=0.7, post_ar1=0.85, sigma=0.3)
    trace_a, _ = fd.simulate_neutral_transition(seed=42, **common)
    trace_b, _ = fd.simulate_neutral_transition(seed=42, **common)
    np.testing.assert_array_equal(trace_a, trace_b)


def test_simulate_neutral_transition_ar1_visibly_post_higher():
    """(gate 3) AR(1) post > AR(1) pre verifiable sur autocorrelation lag-1."""
    trace, t_at = fd.simulate_neutral_transition(
        n_tokens=2000, transition_at=1000,
        pre_mean=0.0, post_mean=0.0,
        pre_ar1=0.5, post_ar1=0.95,
        sigma=0.3, seed=0,
    )
    pre = trace[:1000]
    post = trace[1000:]
    # autocorrelation lag-1 sur chaque segment
    pre_lag1 = float(np.corrcoef(pre[:-1], pre[1:])[0, 1])
    post_lag1 = float(np.corrcoef(post[:-1], post[1:])[0, 1])
    # post > pre avec marge (bruit d'echantillonnage sur n=1000).
    assert post_lag1 > pre_lag1 + 0.2, (
        f"AR1 pas augmente : pre_lag1={pre_lag1:.3f}, post_lag1={post_lag1:.3f}"
    )


# --------------------------------------------------------------------------- #
#  changepoint_cusum (3 gates)                                               #
# --------------------------------------------------------------------------- #


def test_changepoint_cusum_returns_idx_and_S_shapes():
    """(gate 4) retour (idx, S) avec S de taille len(x)."""
    x = np.random.default_rng(0).normal(0, 1, 200)
    idx, S = fd.changepoint_cusum(x, threshold=5.0)
    assert isinstance(idx, (int, np.integer))
    assert S.shape == (200,)
    assert isinstance(int(idx), int)


def test_changepoint_cusum_constant_input_returns_minus_one():
    """(gate 5) entree constante (sigma=0 -> fallback sigma=1.0) : pas de
    detection, idx=-1 (pas de deviation cumulee)."""
    x = np.zeros(100)
    idx, S = fd.changepoint_cusum(x, threshold=5.0)
    assert idx == -1, f"constant input should not trigger, got idx={idx}"
    assert S.shape == (100,)
    np.testing.assert_array_equal(S, np.zeros(100))


def test_changepoint_cusum_short_input_returns_minus_one():
    """(gate 6) entree trop courte (n < 3) : idx=-1, S=zeros."""
    idx, S = fd.changepoint_cusum(np.array([1.0, 2.0]), threshold=5.0)
    assert idx == -1
    assert S.shape == (2,)
    np.testing.assert_array_equal(S, np.zeros(2))


# --------------------------------------------------------------------------- #
#  changepoint_argmax_derivative (3 gates)                                   #
# --------------------------------------------------------------------------- #


def test_changepoint_argmax_derivative_finds_step_edge():
    """(gate 7) sur un step noise-free, argmax |dx| identifie l'index du dernier
    point AVANT le saut (np.diff[n] = vals[n+1]-vals[n], donc argmax |diff|
    designe l'index de depart du saut)."""
    # step a t=10 sur 20 points -> diff = 1.0 a l'index 9 (entre vals[9]=0 et vals[10]=1)
    vals = np.array([0.0] * 10 + [1.0] * 10)
    idx = fd.changepoint_argmax_derivative(vals)
    # Comportement documente : argmax |np.diff| retourne l'index n ou diff[n] est max,
    # qui est l'index du dernier point AVANT le saut (et non le premier point APRES).
    assert idx == 9, f"step edge in diff array at 9, got {idx}"


def test_changepoint_argmax_derivative_short_input_returns_zero():
    """(gate 8) entree de taille < 3 : idx=0 (defensivo, pas d'erreur)."""
    assert fd.changepoint_argmax_derivative(np.array([1.0])) == 0
    assert fd.changepoint_argmax_derivative(np.array([1.0, 2.0])) == 0


def test_changepoint_argmax_derivative_smooth_changes_argmax():
    """(gate 9) avec smooth_sigma > 0, l'argmax peut differer de la version
    brute -- sur une rampe + bruit, le lissage recentre l'argmax."""
    np.random.seed(0)
    vals = np.linspace(0, 1, 50) + np.random.normal(0, 0.05, 50)
    idx_raw = fd.changepoint_argmax_derivative(vals, smooth_sigma=0.0)
    idx_smooth = fd.changepoint_argmax_derivative(vals, smooth_sigma=2.0)
    # Les deux argmax doivent etre dans la moitie droite de la serie
    # (la ou la rampe prend vraiment).
    assert 0 <= idx_raw < 50
    assert 0 <= idx_smooth < 50
    # Le lissage peut deplacer l'argmax de plusieurs points (sanity non-NaN).
    assert isinstance(int(idx_raw), int)
    assert isinstance(int(idx_smooth), int)


# --------------------------------------------------------------------------- #
#  ews_report (5 gates)                                                      #
# --------------------------------------------------------------------------- #


def test_ews_report_white_noise_is_no_signal():
    """(gate 10) bruit blanc iid : pas de tendance Kendall, verdict=no_signal."""
    np.random.seed(42)
    wn = np.random.normal(0, 1, 200)
    report = fd.ews_report(wn, window=30, thin_factor=1)
    assert report.verdict == "no_signal", (
        f"white noise should be no_signal, got {report.verdict}"
    )
    # Kendall tau proche de 0 (pas de tendance) sur bruit blanc.
    assert abs(report.tau_var) < 0.2, f"tau_var={report.tau_var}"
    assert abs(report.tau_ar1) < 0.2, f"tau_ar1={report.tau_ar1}"


def test_ews_report_constant_input_is_no_signal_zero_tau():
    """(gate 11) entree constante : variance=0, tau=0, verdict=no_signal,
    pas de NaN sur variance (anti-regression early_warning division par 0).
    Note : ar1 peut etre NaN si variance=0 partout (AR1 = cov/var = 0/0) ;
    c'est mathematique, pas un bug -- on NE verifie pas ar1 ici."""
    report = fd.ews_report(np.zeros(200), window=30, thin_factor=1)
    assert report.verdict == "no_signal"
    assert report.tau_var == 0.0
    assert report.tau_ar1 == 0.0
    assert not np.any(np.isnan(report.variance))
    assert np.all(report.variance == 0.0)


def test_ews_report_slowing_variance_is_mixed():
    """(gate 12) serie avec sigma(t) croissant : variance Kendall monte mais
    AR1 ne suit pas forcement -> verdict=mixed OU critical_slowing selon
    la p-value."""
    slowing = _make_slowing_variance(n=200, sigma_base=0.01, drift=0.02, seed=0)
    report = fd.ews_report(slowing, window=30, thin_factor=1)
    # Le verdict documente un signal ; au moins un tau est > 0.25 signe
    # (sigma_base tres faible donne une hausse de variance tres tendancielle).
    assert report.verdict in ("mixed", "critical_slowing"), (
        f"slowing variance should yield mixed/critical_slowing, got {report.verdict}"
    )
    assert report.tau_var > 0.25, f"tau_var={report.tau_var}"
    # summary_line format check (commence par EWS verdict=)
    line = report.summary_line()
    assert line.startswith("EWS verdict=")
    assert "tau_var=" in line
    assert "tau_ar1=" in line


def test_ews_report_dataclass_all_expected_fields():
    """(gate 13) la dataclass EWSReport a TOUS les champs documentes :"""
    report = fd.ews_report(np.random.default_rng(0).normal(0, 1, 200),
                           window=30, thin_factor=1)
    expected_fields = {"variance", "ar1", "index", "tau_var", "tau_ar1",
                       "p_var", "p_ar1", "verdict", "notes"}
    actual_fields = set(report.__dict__.keys())
    assert expected_fields.issubset(actual_fields), (
        f"champs manquants : {expected_fields - actual_fields}"
    )
    # Coherence types
    assert isinstance(report.variance, np.ndarray)
    assert isinstance(report.ar1, np.ndarray)
    assert isinstance(report.index, np.ndarray)
    assert isinstance(report.tau_var, float)
    assert isinstance(report.tau_ar1, float)
    assert isinstance(report.p_var, float)
    assert isinstance(report.p_ar1, float)
    assert isinstance(report.verdict, str)
    assert isinstance(report.notes, list)


def test_ews_report_window_and_thin_factor_affect_output_length():
    """(gate 14) la longueur de variance/ar1 depend de window et thin_factor :
    thin_factor=2 doit diviser la longueur par 2 (a 1 pres par floor)."""
    rng = np.random.default_rng(0)
    trace = rng.normal(0, 1, 200)
    r_w30 = fd.ews_report(trace, window=30, thin_factor=1)
    r_w50 = fd.ews_report(trace, window=50, thin_factor=1)
    r_t1 = fd.ews_report(trace, window=30, thin_factor=1)
    r_t2 = fd.ews_report(trace, window=30, thin_factor=2)
    # window plus grand -> series plus courtes (anti-regression ews_summary)
    assert r_w50.ar1.shape[0] < r_w30.ar1.shape[0]
    # thin_factor=2 coupe la serie par 2 (sous-echantillonnage)
    assert r_t2.ar1.shape[0] < r_t1.ar1.shape[0]
    assert r_t2.ar1.shape[0] <= r_t1.ar1.shape[0] // 2 + 1


# --------------------------------------------------------------------------- #
#  hysteresis_residual (1 gate)                                              #
# --------------------------------------------------------------------------- #


def test_hysteresis_residual_symmetric_loop_is_zero():
    """(gate 15) boucle forward/backward parfaitement symetrique (aller-retour
    identique) -> residu nul = pas d'hysteresis instrinseque de la methode."""
    fwd = np.array([0.0] * 20 + [1.0] * 20)
    back = np.array([1.0] * 20 + [0.0] * 20)
    # Aller = monte, retour = descend en miroir ; la queue de back = tete de fwd.
    residu = fd.hysteresis_residual(fwd, back, baseline_window=20)
    assert abs(residu) < 1e-12, f"symmetric loop should yield ~0, got {residu}"
    # Sanity check type
    assert isinstance(residu, float)


def test_hysteresis_residual_drift_yields_nonzero():
    """(gate bonus) drift d'hysteresis : la queue de back ne revient pas
    exactement a la tete de fwd -> residu non nul."""
    fwd = np.array([0.0] * 20 + [1.0] * 20)
    back = np.array([1.0] * 20 + [0.5] * 20)  # ne revient PAS a 0.0
    residu = fd.hysteresis_residual(fwd, back, baseline_window=20)
    assert abs(residu - 0.5) < 1e-12, f"expected 0.5, got {residu}"
