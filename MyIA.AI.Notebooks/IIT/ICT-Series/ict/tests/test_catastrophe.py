"""Tests du module :mod:`ict.catastrophe` (ICT-10 prélude Thom, Epic #4588).

La grammaire des catastrophes élémentaires de Rene Thom outille ICT-10 : le
**cusp** (fronce), potentiel ``V(x;a,b) = x^4/4 + a x^2/2 + b x``. Dans la région
``4 a^3 + 27 b^2 < 0`` (donc ``a < 0``) le cubique ``x^3 + a x + b = 0`` a trois
racines réelles — deux minima stables séparés par un col instable (bistable,
deux bassins/actants). Ailleurs, une seule racine. La courbe de bifurcation
``4 a^3 + 27 b^2 = 0`` est le lieu des **plis** (fusion min+col, disparition).

Ces tests verrouillent les invariants falsifiables du squelette morphodynamique :

  * **Identités analytiques** du potentiel/force/courbure (dérivées exactes).
  * **Géométrie du cusp** : nombre d'équilibres (1 vs 3), stabilité (V''>0),
    discriminant (signe = région bistable), courbe de bifurcation (NaN hors ``a<0``).
  * **Relaxation + lacet d'hystérésis** : descente de gradient converge vers le
    minimum du bassin de départ ; le lacet adiabatique suit une branche puis
    saute au pli (``loop_jumps`` localise les catastrophes).
  * **Représentant interne p_hat** : extrapolation à vitesse constante
    (``p_hat ≈ obs + lead·v`` après warmup EMA), persistance (retard d'un pas),
    corrélation croisée normalisée (lags + pic), erreur d'anticipation, baselines
    adverses (moyenne mobile causale = retard sur rampe, AR(1) d'une rampe ~1).

Numpy uniquement, comme le reste du package léger ``ict``. Pattern hérité de
``test_compression.py`` : bootstrap ``sys.path`` module-level, sans fixtures.
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

from ict import catastrophe as c  # noqa: E402


def _rng(seed: int) -> np.random.Generator:
    return np.random.default_rng(seed)


# --------------------------------------------------------------------------- #
#  Identités analytiques : potentiel, force (gradient), courbure
# --------------------------------------------------------------------------- #


class TestCuspIdentities:
    def test_potential_zero_at_origin(self):
        # V(0; a, b) = 0 pour tout (a, b).
        assert c.cusp_potential(0.0, 1.0, 2.0) == 0.0
        assert c.cusp_potential(np.zeros(3), -1.0, 0.5).tolist() == [0.0, 0.0, 0.0]

    def test_force_is_negative_gradient(self):
        # dx/dt = -dV/dx = -(x^3 + a x + b). En x=1, a=1, b=1 => -(1+1+1) = -3.
        assert c.cusp_force(1.0, 1.0, 1.0) == pytest.approx(-3.0)
        # Vectorisé : force(array) = -(x^3 + a x + b) élément par élément.
        xs = np.array([-1.0, 0.0, 2.0])
        got = c.cusp_force(xs, 1.0, 0.0)
        assert np.allclose(got, -(xs ** 3 + xs))

    def test_curvature_signs_distinguish_min_and_col(self):
        # V''(x) = 3 x^2 + a. En a=-1 : V''(0) = -1 (col), V''(1) = 2 (min).
        assert c.cusp_curvature(0.0, -1.0) == pytest.approx(-1.0)
        assert c.cusp_curvature(1.0, -1.0) == pytest.approx(2.0)


# --------------------------------------------------------------------------- #
#  Géométrie du cusp : équilibres, discriminant, bistable, plis
# --------------------------------------------------------------------------- #


class TestCuspGeometry:
    def test_equilibria_bistable_three_real_two_stable(self):
        # a=-1, b=0 : cubique x^3 - x = 0 => racines {-1, 0, 1}.
        # Stables : V''(-1)=2>0, V''(0)=-1<0 (col), V''(1)=2>0.
        eq = c.cusp_equilibria(-1.0, 0.0)
        xs = [round(x, 9) for x, _ in eq]
        stable = [s for _, s in eq]
        assert xs == [-1.0, 0.0, 1.0]
        assert stable == [True, False, True]

    def test_equilibria_sorted_by_x(self):
        # Le contrat documente un tri par x croissant.
        eq = c.cusp_equilibria(-2.0, 0.7)
        xs = [x for x, _ in eq]
        assert xs == sorted(xs)

    def test_equilibria_monostable_single_real(self):
        # a>0 (hors bistable) : une seule racine réelle, stable.
        eq = c.cusp_equilibria(1.0, 0.0)
        assert len(eq) == 1
        assert eq[0][1] is True  # stable

    def test_discriminant_sign_encodes_region(self):
        # Delta = -(4 a^3 + 27 b^2). Delta>0 => bistable.
        assert c.cusp_discriminant(-1.0, 0.0) == pytest.approx(4.0)  # >0
        assert c.cusp_discriminant(1.0, 0.0) == pytest.approx(-4.0)  # <0
        # Sur le pli (a=0, b=0) : Delta = 0 (frontière).
        assert c.cusp_discriminant(0.0, 0.0) == 0.0

    def test_in_bistable_region_matches_discriminant(self):
        assert c.in_bistable_region(-1.0, 0.0) is True
        assert c.in_bistable_region(1.0, 0.0) is False
        assert c.in_bistable_region(0.0, 0.0) is False  # Delta=0, strictement >

    def test_count_equilibria_and_stable(self):
        # Bistable : 3 équilibres dont 2 stables.
        assert c.count_equilibria(-1.0, 0.0) == 3
        assert c.count_stable(-1.0, 0.0) == 2
        # Monostable : 1 équilibre, 1 stable.
        assert c.count_equilibria(1.0, 0.0) == 1
        assert c.count_stable(1.0, 0.0) == 1

    def test_fold_lines_none_when_not_bistable(self):
        # Pas de pli si a >= 0 (région monostable).
        assert c.fold_lines(0.0) is None
        assert c.fold_lines(1.5) is None

    def test_fold_lines_symmetric_when_bistable(self):
        # b = +/- sqrt(-4 a^3 / 27), symétrique en 0.
        lo, hi = c.fold_lines(-3.0)
        assert lo < 0.0 < hi
        assert abs(lo + hi) < 1e-12  # symétrie ±
        # Valeur exacte pour a=-3 : sqrt(-4*(-27)/27) = sqrt(4) = 2.
        assert hi == pytest.approx(2.0)

    def test_bifurcation_curve_nan_outside_bistable(self):
        grid = np.array([-1.0, 0.0, 1.0])
        b_inf, b_sup = c.bifurcation_curve(grid)
        # a<0 : branches réelles ; a>=0 : NaN.
        assert np.isfinite(b_inf[0]) and np.isfinite(b_sup[0])
        assert np.isnan(b_inf[1]) and np.isnan(b_sup[1])
        assert np.isnan(b_inf[2]) and np.isnan(b_sup[2])
        # Symétrie ± sur la branche finie.
        assert abs(b_inf[0] + b_sup[0]) < 1e-12


# --------------------------------------------------------------------------- #
#  Relaxation gradient + lacet d'hystérésis (lacet de prédation)
# --------------------------------------------------------------------------- #


class TestRelaxationAndHysteresis:
    def test_relax_converges_to_basin_minimum(self):
        # a=-1, b=0 : minima en ±1. x0>0 => converge vers +1, x0<0 => vers -1.
        assert c.relax_to_equilibrium(0.5, -1.0, 0.0) == pytest.approx(1.0, abs=1e-3)
        assert c.relax_to_equilibrium(-0.5, -1.0, 0.0) == pytest.approx(-1.0, abs=1e-3)

    def test_relax_monostable_single_minimum(self):
        # a>0 : un seul minimum global ; la convergence est indépendante de x0.
        xstar = c.relax_to_equilibrium(3.0, 1.0, 0.0)
        assert xstar == pytest.approx(0.0, abs=1e-3)

    def test_hysteresis_loop_returns_aligned_array(self):
        # xs a la même forme que b_values (suivi pas-à-pas).
        b = np.linspace(-0.5, 0.5, 30)
        xs = c.hysteresis_loop(-1.0, b, x_start=-1.0, relax_steps=100)
        assert xs.shape == b.shape

    def test_loop_jumps_detects_branch_switches(self):
        # Un aller-retour en b à a<0 traverse deux plis : loop_jumps doit
        # localiser au moins les sauts catastrophiques (threshold large pour
        # tolérer la résolution numérique).
        b = np.concatenate([
            np.linspace(-0.6, 0.6, 60),
            np.linspace(0.6, -0.6, 60),
        ])
        xs = c.hysteresis_loop(-1.0, b, x_start=-1.0, relax_steps=150)
        jumps = c.loop_jumps(b, xs, threshold=0.5)
        # Au moins un saut détecté (la fonctionnalité = localiser les plis).
        assert len(jumps) >= 1
        # Tous les indices dans la plage valide de xs.
        assert all(1 <= j < len(xs) for j in jumps)

    def test_loop_jumps_empty_on_monotone_stable_path(self):
        # Sur un chemin monostable (a>0, pas de pli), pas de saut > threshold.
        b = np.linspace(-0.5, 0.5, 40)
        xs = c.hysteresis_loop(1.0, b, x_start=0.0, relax_steps=100)
        assert c.loop_jumps(b, xs, threshold=0.5) == []


# --------------------------------------------------------------------------- #
#  Représentant interne p_hat et baselines adverses
# --------------------------------------------------------------------------- #


class TestInternalRepresentation:
    def test_constant_velocity_tracker_anticipates_ramp(self):
        # Rampe linéaire de pente 1 : la vitesse EMA converge vers 1, donc
        # p_hat[t] -> obs[t] + lead après warmup.
        obs = np.arange(60, dtype=float)
        ph = c.constant_velocity_tracker(obs, lead=2, alpha=0.3)
        # En queue (warmup terminé), p_hat ≈ obs + lead*1.
        assert ph[-1] == pytest.approx(obs[-1] + 2.0, abs=0.5)

    def test_constant_velocity_tracker_aligned_shape(self):
        obs = _rng(0).standard_normal(25)
        ph = c.constant_velocity_tracker(obs, lead=1, alpha=0.4)
        assert ph.shape == obs.shape

    def test_persistence_tracker_lags_by_one(self):
        obs = np.arange(10, dtype=float)
        pt = c.persistence_tracker(obs)
        # p_hat[t] = obs[t-1] ; p_hat[0] = obs[0] (initialisation causale).
        assert pt[0] == obs[0]
        assert np.array_equal(pt[1:], obs[:-1])

    def test_cross_correlation_returns_symmetric_lag_range(self):
        rng = _rng(1)
        p = rng.standard_normal(40)
        t = rng.standard_normal(40)
        lags, corr = c.cross_correlation(p, t, max_lag=5)
        assert lags.tolist() == list(range(-5, 6))
        assert corr.shape == lags.shape
        # Corrélations normalisées : amplitude bornée autour de [-1, 1].
        assert np.all(np.abs(corr) <= 1.0 + 1e-9)

    def test_cross_correlation_self_peak_at_zero(self):
        # Auto-corrélation d'un signal avec lui-même : pic au lag 0.
        sig = _rng(2).standard_normal(50)
        lags, corr = c.cross_correlation(sig, sig, max_lag=6)
        assert c.peak_lag(lags, corr) == 0
        # Et la valeur au lag 0 est ~1 (corrélation parfaite normalisée).
        assert corr[6] == pytest.approx(1.0, abs=1e-6)

    def test_peak_lag_is_int_in_range(self):
        lags = np.arange(-4, 5)
        corr = _rng(3).standard_normal(9)
        pl = c.peak_lag(lags, corr)
        assert isinstance(pl, int)
        assert -4 <= pl <= 4

    def test_lead_error_positive_and_decreases_with_good_forecast(self):
        # lead_error(p_hat, target, lead) : MSE de p_hat[t] vs target[t+lead].
        target = np.arange(30, dtype=float)
        # Un « forecast » parfait = target lui-même (décalé) : erreur faible.
        perfect = target.copy()
        good = c.lead_error(perfect, target, lead=1)
        # Un forecast bruité : erreur plus forte.
        noisy = target + _rng(4).standard_normal(30) * 5
        bad = c.lead_error(noisy, target, lead=1)
        assert good >= 0.0
        assert bad > good

    def test_lead_error_zero_lag_is_plain_mse(self):
        # lead<=0 : MSE directe p_hat vs target (pas de décalage).
        p = np.array([1.0, 2.0, 3.0])
        t = np.array([1.0, 0.0, 3.0])
        # MSE = (0 + 4 + 0)/3.
        assert c.lead_error(p, t, lead=0) == pytest.approx(4.0 / 3.0)

    def test_moving_average_tracker_causal_and_lagging_on_ramp(self):
        # MA causale : sur une rampe, elle est systématiquement en dessous
        # (retard) après le warmup — l'adversaire « lisse » que p_hat doit battre.
        obs = np.arange(20, dtype=float)
        ma = c.moving_average_tracker(obs, window=5)
        assert ma.shape == obs.shape
        assert ma[-1] < obs[-1]  # retard

    def test_moving_average_tracker_window_one_equals_obs(self):
        # window=1 : la MA est l'observation elle-même (pas de lissage).
        obs = _rng(5).standard_normal(15)
        ma = c.moving_average_tracker(obs, window=1)
        assert np.allclose(ma, obs)

    def test_ar1_coefficient_ramp_approaches_one(self):
        # Une rampe pure (tendance déterministe) : AR(1) -> phi ~ 1.
        obs = np.arange(100, dtype=float)
        assert c.ar1_coefficient(obs) == pytest.approx(1.0, abs=1e-2)

    def test_ar1_coefficient_white_noise_below_one(self):
        # Bruit blanc iid : phi ~ 0 (pas d'autocorrélation).
        obs = _rng(6).standard_normal(2000)
        phi = c.ar1_coefficient(obs)
        assert abs(phi) < 0.1
