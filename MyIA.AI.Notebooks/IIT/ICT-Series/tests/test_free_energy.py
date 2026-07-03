"""Tests de la jambe energie-libre du representant interne (module ICT-14).

Verifient la surprise gaussienne (forme fermee, minimum, plancher numerique),
la precision adaptive (causalite EMA, convergence, plancher), la decomposition
free energy = accuracy + complexity, et surtout les **deux gates
falsifiables** de la strate 4 :

* **Gate 1** : a precision **fixe**, ``F_bar`` est une transformation monotone
  du MSE -> le classement des estimateurs par ``F`` coincide exactement avec le
  classement par ``lead_error`` (l'energie libre n'est qu'un habillage du MSE).
* coherence interne : ``free_energy_trajectory`` et ``gaussian_surprise``
  calculent la meme quantite.

Numpy + pytest. Le module ne depend que de numpy (+ ``catastrophe`` du package).
"""

import os
import sys

import numpy as np
import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ict import free_energy as fe  # noqa: E402
from ict import catastrophe as cat  # noqa: E402


# --------------------------------------------------------------------------- #
#  Surprise gaussienne : forme fermee, minimum, plancher                      #
# --------------------------------------------------------------------------- #


def test_gaussian_surprise_closed_form_at_unit_sigma():
    # a sigma=1 : S_t = 0.5 * [err^2 + ln(2 pi)]
    rng = np.random.default_rng(0)
    obs = rng.standard_normal(200)
    pred = rng.standard_normal(200)
    expected = 0.5 * ((obs - pred) ** 2 + np.log(2.0 * np.pi))
    got = fe.gaussian_surprise(obs, pred, sigma=1.0)
    assert np.allclose(got, expected)


def test_gaussian_surprise_minimum_at_zero_error():
    # surprise minimale quand pred == obs ; croit avec |err|
    obs = np.array([1.0, 1.0, 1.0])
    sigma = 0.7
    s0 = fe.gaussian_surprise(np.array([1.0, 1.0, 1.0]), obs, sigma=sigma)
    s1 = fe.gaussian_surprise(np.array([1.5, 1.0, 1.0]), obs, sigma=sigma)
    s2 = fe.gaussian_surprise(np.array([2.0, 1.0, 1.0]), obs, sigma=sigma)
    assert s0[0] < s1[0] < s2[0]
    # minimum theorique = 0.5 * ln(2 pi sigma^2)
    assert s0[0] == pytest.approx(0.5 * np.log(2.0 * np.pi * sigma * sigma))


def test_gaussian_surprise_precision_floor_avoids_infinity():
    # sigma = 0 ne doit ni diviser par zero ni log(0) : plancher applique
    s = fe.gaussian_surprise(np.array([1.0]), np.array([0.0]), sigma=0.0)
    assert np.isfinite(s).all()


def test_gaussian_surprise_array_sigma_broadcasts():
    # sigma tableau (precision adaptive) : broadcast elementaire
    obs = np.array([0.0, 0.0, 0.0])
    pred = np.array([1.0, 1.0, 1.0])
    sigma = np.array([1.0, 2.0, 4.0])
    s = fe.gaussian_surprise(obs, pred, sigma=sigma)
    # a err=1 fixe, la surprise est minimale a sigma=|err|=1 ; sur sigma>1 le
    # complexity term (ln sigma) domine -> surprise croissante sur [1,2,4]
    assert s[0] < s[1] < s[2]


def test_gaussian_surprise_minimum_at_sigma_matches_error():
    # le modele minimisant la surprise s'accorde a l'erreur : sigma* = |err|
    err = 0.6
    obs = np.array([0.0])
    pred = np.array([err])
    sigmas = np.linspace(0.15, 2.0, 50)
    s = np.array([fe.gaussian_surprise(obs, pred, sigma=sig)[0] for sig in sigmas])
    assert sigmas[int(np.argmin(s))] == pytest.approx(err, abs=0.1)


# --------------------------------------------------------------------------- #
#  Precision adaptive : causalite, convergence, plancher                      #
# --------------------------------------------------------------------------- #


def test_adaptive_precision_is_causal():
    # var[0] = var0 (independant de err[0]) ; var[1] ne depend que de err[0]
    e = np.array([3.0, -2.0, 5.0, 1.0])
    alpha, var0 = 0.4, 0.5
    var = fe.adaptive_precision(e, alpha=alpha, var0=var0)
    assert var[0] == pytest.approx(var0)
    assert var[1] == pytest.approx(alpha * e[0] ** 2 + (1 - alpha) * var0)
    # var[2] ne depend que de err[0..1]
    assert var[2] == pytest.approx(
        alpha * e[1] ** 2 + (1 - alpha) * var[1]
    )


def test_adaptive_precision_converges_to_constant_squared():
    # erreurs constantes c -> sigma^2 converge vers c^2 (suite geometrique)
    c = 2.5
    e = np.full(400, c)
    var = fe.adaptive_precision(e, alpha=0.2, var0=10.0)
    assert var[-1] == pytest.approx(c * c, rel=1e-3)


def test_adaptive_precision_floor_on_zero_errors():
    # erreurs nulles -> variance converge vers le plancher (pas de log(0))
    e = np.zeros(200)
    var = fe.adaptive_precision(e, alpha=0.3, var0=1.0)
    assert np.all(np.isfinite(var))
    assert var[-1] >= 1e-6


def test_adaptive_precision_rejects_bad_alpha():
    for bad in (0.0, -0.1, 1.7):
        with pytest.raises(ValueError):
            fe.adaptive_precision(np.zeros(5), alpha=bad)


# --------------------------------------------------------------------------- #
#  Free energy : decomposition + coherence interne                            #
# --------------------------------------------------------------------------- #


def test_free_energy_decomposes_into_accuracy_plus_complexity():
    rng = np.random.default_rng(7)
    obs = rng.standard_normal(100)
    pred = rng.standard_normal(100)
    traj = fe.free_energy_trajectory(obs, pred, sigma=0.8, mode="fixed")
    assert np.allclose(traj["F"], traj["accuracy"] + traj["complexity"])
    # complexite constante en mode fixe (sigma constant)
    assert np.allclose(traj["complexity"], traj["complexity"][0])


def test_free_energy_equals_gaussian_surprise():
    # coherence interne : free_energy_trajectory["F"] == gaussian_surprise
    rng = np.random.default_rng(42)
    obs = rng.standard_normal(50)
    pred = rng.standard_normal(50)
    traj = fe.free_energy_trajectory(obs, pred, sigma=1.3, mode="fixed")
    gs = fe.gaussian_surprise(obs, pred, sigma=1.3)
    assert np.allclose(traj["F"], gs)


def test_free_energy_adaptive_complexity_varies():
    # en mode adaptatif, la complexite n'est PAS constante (sigma^2 varie)
    rng = np.random.default_rng(1)
    obs = np.concatenate([np.zeros(30), np.full(30, 5.0)])  # un saut
    pred = np.zeros(60)
    traj = fe.free_energy_trajectory(obs, pred, mode="adaptive", alpha=0.4)
    assert not np.allclose(traj["complexity"], traj["complexity"][0])


def test_free_energy_rejects_unknown_mode():
    with pytest.raises(ValueError):
        fe.free_energy_trajectory(np.zeros(5), np.zeros(5), mode="nonsense")


# --------------------------------------------------------------------------- #
#  GATE 1 (falsifiable) : a precision fixe, F_bar monotone en MSE            #
# --------------------------------------------------------------------------- #


def test_gate1_fixed_precision_F_monotone_in_mse():
    # deux predictions sur la meme cible : MSE plus faible => F_bar plus faible
    rng = np.random.default_rng(99)
    target = np.sin(np.linspace(0, 6, 200))
    good = target + 0.05 * rng.standard_normal(200)     # faible erreur
    bad = target + 0.8 * rng.standard_normal(200)       # forte erreur
    sigma = 0.5
    mse_good, mse_bad = (
        np.mean((good - target) ** 2),
        np.mean((bad - target) ** 2),
    )
    f_good = np.mean(fe.free_energy_trajectory(target, good, sigma=sigma)["F"])
    f_bad = np.mean(fe.free_energy_trajectory(target, bad, sigma=sigma)["F"])
    assert mse_good < mse_bad          # sanity
    assert f_good < f_bad              # gate 1 : meme ordre que le MSE


def test_gate1_fe_report_ranks_match_mse():
    # sur une trajectoire sinus, a sigma fixe, argmin(F) == argmin(erreur)
    rng = np.random.default_rng(7)
    obs = cat.prey_trajectory("sinus", n_steps=300, noise=0.10, rng=rng)
    rapport = fe.fe_anticipation_report(obs, lead=4, sigma=1.0, mode="fixed")
    by_F = sorted(rapport, key=lambda k: rapport[k]["F"])
    by_err = sorted(rapport, key=lambda k: rapport[k]["erreur"])
    assert by_F == by_err               # gate 1 : rangs identiques


# --------------------------------------------------------------------------- #
#  Report complet : 4 estimateurs, mode adaptatif s'execute                   #
# --------------------------------------------------------------------------- #


def test_fe_report_returns_four_estimators_with_metrics():
    rng = np.random.default_rng(3)
    obs = cat.prey_trajectory("derive", n_steps=200, noise=0.15, rng=rng)
    rapport = fe.fe_anticipation_report(obs, lead=3, sigma=1.0, mode="fixed")
    assert set(rapport) == {"p_hat", "persistance", "moyenne_mobile", "ar1"}
    for nom, m in rapport.items():
        assert set(m) == {"F", "erreur", "pic_lag"}
        assert np.isfinite(m["F"]) and np.isfinite(m["erreur"])
        assert isinstance(m["pic_lag"], float)


def test_fe_report_adaptive_mode_runs_and_is_finite():
    # mode adaptatif : s'execute, F fini (gate 2 se teste empiriquement en nb)
    rng = np.random.default_rng(11)
    obs = cat.prey_trajectory("creneau", n_steps=300, noise=0.10, rng=rng)
    rapport = fe.fe_anticipation_report(obs, lead=4, mode="adaptive", alpha_prec=0.3)
    for m in rapport.values():
        assert np.isfinite(m["F"])
