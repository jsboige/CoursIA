"""Tests de la boite a outils des signaux precurseurs (module ICT-8).

Verifient que les indicateurs (variance roulante, AR1 roulante, tau de Kendall)
et le pretraitement (amincissement, detrendage) se comportent correctement sur
des cas de reference connus, et que la chaine ``ews_summary`` detecte un
ralentissement critique synthetique.

Numpy + pytest. Le module ne depend que de numpy."""

import os
import sys

import numpy as np
import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ict import early_warning as ew  # noqa: E402


def _ar1_process(phi, n, sigma=1.0, seed=0):
    """Genere un AR(1) : x[t] = phi x[t-1] + bruit. AR1 theorique = phi."""
    g = np.random.default_rng(seed)
    x = np.empty(n)
    x[0] = 0.0
    for t in range(1, n):
        x[t] = phi * x[t - 1] + sigma * g.standard_normal()
    return x


def test_thin():
    x = np.arange(100)
    assert np.array_equal(ew.thin(x, 10), np.arange(0, 100, 10))
    with pytest.raises(ValueError):
        ew.thin(x, 0)


def test_lag1_autocorr_white_noise_near_zero():
    x = np.random.default_rng(1).standard_normal(20000)
    assert abs(ew.lag1_autocorr(x)) < 0.05


def test_lag1_autocorr_recovers_phi():
    # un AR(1) fortement autocorrele doit retrouver phi
    x = _ar1_process(0.9, 50000, seed=2)
    assert ew.lag1_autocorr(x) == pytest.approx(0.9, abs=0.03)


def test_rolling_variance_matches_numpy():
    x = np.random.default_rng(3).standard_normal(200)
    rv = ew.rolling_variance(x, 50)
    assert len(rv) == 200 - 50 + 1
    assert rv[0] == pytest.approx(x[:50].var())
    assert rv[-1] == pytest.approx(x[-50:].var())


def test_rolling_variance_constant_is_zero():
    rv = ew.rolling_variance(np.ones(100), 20)
    assert np.allclose(rv, 0.0)


def test_kendall_tau_monotone():
    t = np.arange(40)
    tau_up, p_up = ew.kendall_tau(t, t.astype(float))
    assert tau_up == pytest.approx(1.0)
    assert p_up < 1e-6
    tau_dn, _ = ew.kendall_tau(t, -t.astype(float))
    assert tau_dn == pytest.approx(-1.0)


def test_kendall_tau_no_trend():
    g = np.random.default_rng(4)
    t = np.arange(200)
    y = g.standard_normal(200)
    tau, p = ew.kendall_tau(t, y)
    assert abs(tau) < 0.15
    assert p > 0.05


def test_detrend_removes_linear_trend():
    t = np.linspace(0, 10, 500)
    noise = 0.1 * np.random.default_rng(5).standard_normal(500)
    x = 3.0 * t + noise  # forte tendance lineaire
    res = ew.detrend(x, sigma=20)
    # la variance des residus doit etre tres inferieure a celle du signal brut
    assert res.var() < 0.05 * x.var()
    assert abs(res.mean()) < 0.5


def test_oversampling_masks_signal_thinning_reveals_it():
    """La lecon ICT-8 : sur-echantillonner sature l'AR1 ; amincir revele le signal."""
    # serie tres correlee (pas fin) -> AR1 brute ~1, sans contraste
    x = _ar1_process(0.995, 40000, seed=6)
    ar1_dense = ew.lag1_autocorr(x)
    ar1_thin = ew.lag1_autocorr(ew.thin(x, 50))
    assert ar1_dense > 0.97              # sature pres de 1
    assert ar1_thin < ar1_dense - 0.1    # l'amincissement degage de la marge


def test_ews_summary_detects_rising_autocorrelation():
    # serie dont l'autocorrelation augmente par blocs (ralentissement critique synthetique)
    g = np.random.default_rng(7)
    seg = []
    for phi in np.linspace(0.5, 0.95, 6):
        s = np.empty(4000); s[0] = 0.0
        for t in range(1, 4000):
            s[t] = phi * s[t - 1] + g.standard_normal()
        seg.append(s)
    x = np.concatenate(seg)
    out = ew.ews_summary(x, window=2000, thin_factor=1, detrend_sigma=0.0)
    assert out["tau_ar1"] > 0.3
    assert out["tau_var"] > 0.3


def test_recovery_time():
    traj = np.array([5.0, 4.0, 3.0, 2.1, 2.0, 2.0])
    # 2.1 est deja dans la tolerance 0.15 autour de 2.0 -> premier retour a l'indice 3
    assert ew.recovery_time(traj, baseline=2.0, tol=0.15) == 3
    # tolerance plus serree : il faut atteindre 2.0 exactement -> indice 4
    assert ew.recovery_time(traj, baseline=2.0, tol=0.05) == 4
    assert ew.recovery_time(traj, baseline=-100.0, tol=0.1) is None
