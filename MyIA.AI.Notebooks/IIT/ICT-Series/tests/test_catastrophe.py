"""Tests de la grammaire des catastrophes elementaires (module ICT-10).

Verifient le squelette de la catastrophe fronce (potentiel, force, equilibres,
courbe de bifurcation, plis), le lacet d'hysteresis a deux catastrophes (le
*lacet de predation* de Thom), et le contenu predictif **mesure** du representant
interne ``p_hat`` (il anticipe, et bat la persistance sur un horizon ``lead``).

Numpy + pytest. Le module ne depend que de numpy."""

import os
import sys

import numpy as np
import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ict import catastrophe as cat  # noqa: E402


# --------------------------------------------------------------------------- #
#  Catastrophe fronce : potentiel, force, equilibres                           #
# --------------------------------------------------------------------------- #


def test_force_is_negative_gradient_of_potential():
    # cusp_force doit etre -dV/dx (verification par differences finies)
    a, b = -1.0, 0.2
    x = np.linspace(-2, 2, 401)
    dx = x[1] - x[0]
    V = cat.cusp_potential(x, a, b)
    num_force = -(np.gradient(V, dx))
    ana_force = cat.cusp_force(x, a, b)
    # bords exclus (gradient moins precis)
    assert np.allclose(num_force[5:-5], ana_force[5:-5], atol=1e-2)


def test_equilibria_are_force_zeros():
    a, b = -1.0, 0.3
    for x, _ in cat.cusp_equilibria(a, b):
        assert cat.cusp_force(x, a, b) == pytest.approx(0.0, abs=1e-9)


def test_bistable_region_has_three_equilibria_two_stable():
    eq = cat.cusp_equilibria(-1.0, 0.0)
    assert len(eq) == 3
    assert sum(1 for _, st in eq if st) == 2          # deux minima
    assert sum(1 for _, st in eq if not st) == 1       # un col instable


def test_monostable_region_has_one_equilibrium():
    assert cat.count_equilibria(1.0, 0.0) == 1         # a > 0 : un seul
    assert cat.count_equilibria(-1.0, 1.0) == 1        # b hors region bistable
    assert cat.count_stable(1.0, 0.0) == 1


def test_discriminant_sign_matches_region():
    assert cat.cusp_discriminant(-1.0, 0.0) > 0        # bistable
    assert cat.in_bistable_region(-1.0, 0.0)
    assert cat.cusp_discriminant(-1.0, 1.0) < 0        # monostable
    assert not cat.in_bistable_region(-1.0, 1.0)


def test_discriminant_zero_on_fold():
    a = -1.0
    b_lo, b_hi = cat.fold_lines(a)
    assert cat.cusp_discriminant(a, b_hi) == pytest.approx(0.0, abs=1e-9)
    assert cat.cusp_discriminant(a, b_lo) == pytest.approx(0.0, abs=1e-9)


def test_fold_lines_value():
    # a = -1 : b_fold = +/- sqrt(4/27)
    b_lo, b_hi = cat.fold_lines(-1.0)
    assert b_hi == pytest.approx(np.sqrt(4.0 / 27.0))
    assert b_lo == pytest.approx(-np.sqrt(4.0 / 27.0))


def test_fold_lines_none_when_no_bistability():
    assert cat.fold_lines(0.0) is None
    assert cat.fold_lines(0.5) is None


def test_count_equilibria_changes_only_at_fold():
    # le long d'un balayage de b a a<0, le nombre d'equilibres ne saute qu'aux
    # plis : 1 -> 3 (naissance d'une paire) -> 1 (disparition) -- le metatheoreme
    a = -1.0
    b_lo, b_hi = cat.fold_lines(a)
    bs = np.linspace(b_lo - 0.3, b_hi + 0.3, 200)
    counts = np.array([cat.count_equilibria(a, float(b)) for b in bs])
    assert set(np.unique(counts)).issubset({1, 3})
    assert counts[0] == 1 and counts[-1] == 1          # monostable aux extremites
    assert (counts == 3).any()                          # bistable au milieu
    # exactement deux transitions de comptage (les deux plis)
    assert int((np.diff(counts) != 0).sum()) == 2


def test_bifurcation_curve_branches_symmetric():
    a_grid = np.linspace(-2.0, 0.5, 50)
    b_inf, b_sup = cat.bifurcation_curve(a_grid)
    neg = a_grid < 0
    assert np.allclose(b_inf[neg], -b_sup[neg])
    assert np.all(np.isnan(b_sup[~neg]))               # pas de pli pour a >= 0


# --------------------------------------------------------------------------- #
#  Relaxation et lacet de predation (hysteresis a deux catastrophes)           #
# --------------------------------------------------------------------------- #


def test_relax_converges_to_an_equilibrium():
    a, b = -1.0, 0.2
    x_star = cat.relax_to_equilibrium(2.0, a, b)
    assert cat.cusp_force(x_star, a, b) == pytest.approx(0.0, abs=1e-4)
    # 3x^2 + a > 0 : c'est bien un minimum
    assert cat.cusp_curvature(x_star, a) > 0


def test_relax_basin_dependence():
    # deux conditions initiales de part et d'autre du col -> deux minima
    a, b = -1.0, 0.0
    x_low = cat.relax_to_equilibrium(-2.0, a, b)
    x_high = cat.relax_to_equilibrium(2.0, a, b)
    assert x_low < 0 < x_high


def test_hysteresis_loop_has_two_catastrophes():
    a = -1.0
    b_up = np.linspace(-0.7, 0.7, 80)
    b_path = np.concatenate([b_up, b_up[::-1]])
    x0 = cat.cusp_equilibria(a, float(b_path[0]))[0][0]
    xs = cat.hysteresis_loop(a, b_path, x_start=x0)
    jumps = cat.loop_jumps(b_path, xs, threshold=0.5)
    assert len(jumps) == 2                              # perception J + capture K


def test_hysteresis_loop_is_open():
    # l'aire signee du lacet est non nulle (memoire de branche = hysteresis)
    a = -1.0
    b_up = np.linspace(-0.7, 0.7, 80)
    b_path = np.concatenate([b_up, b_up[::-1]])
    x0 = cat.cusp_equilibria(a, float(b_path[0]))[0][0]
    xs = cat.hysteresis_loop(a, b_path, x_start=x0)
    trapz = getattr(np, "trapezoid", None) or np.trapz
    area = float(trapz(xs, b_path))
    assert abs(area) > 0.5


def test_no_hysteresis_outside_bistable_axis():
    # a > 0 : pas de bistabilite, donc pas de saut, le suivi est continu
    a = 0.5
    b_up = np.linspace(-0.7, 0.7, 80)
    b_path = np.concatenate([b_up, b_up[::-1]])
    xs = cat.hysteresis_loop(a, b_path, x_start=cat.cusp_equilibria(a, -0.7)[0][0])
    assert cat.loop_jumps(b_path, xs, threshold=0.5) == []


# --------------------------------------------------------------------------- #
#  Representant interne p_hat : contenu predictif mesure                        #
# --------------------------------------------------------------------------- #


def _prey(seed=7, npts=300, span=8, noise=0.10):
    rng = np.random.default_rng(seed)
    t = np.linspace(0, span * np.pi, npts)
    return np.sin(t) + noise * rng.standard_normal(npts)


def test_persistence_tracker_lags_by_one():
    prey = _prey()
    base = cat.persistence_tracker(prey)
    lags, corr = cat.cross_correlation(base, prey, max_lag=8)
    assert cat.peak_lag(lags, corr) <= 0                # un suiveur est en retard


def test_anticipatory_tracker_leads():
    prey = _prey()
    lead = 4
    phat = cat.constant_velocity_tracker(prey, lead=lead, alpha=0.25)
    lags, corr = cat.cross_correlation(phat, prey, max_lag=10)
    # le pic de correlation est a un lag strictement positif : p_hat anticipe
    assert cat.peak_lag(lags, corr) > 0


def test_anticipatory_beats_persistence_on_lead_horizon():
    prey = _prey()
    lead = 4
    phat = cat.constant_velocity_tracker(prey, lead=lead, alpha=0.25)
    base = cat.persistence_tracker(prey)
    assert cat.lead_error(phat, prey, lead) < cat.lead_error(base, prey, lead)


def test_raw_velocity_amplifies_noise():
    # caveat mesure : alpha=1 (vitesse brute) est plus bruite que alpha lisse
    prey = _prey(noise=0.15)
    lead = 4
    raw = cat.constant_velocity_tracker(prey, lead=lead, alpha=1.0)
    smooth = cat.constant_velocity_tracker(prey, lead=lead, alpha=0.25)
    assert cat.lead_error(raw, prey, lead) > cat.lead_error(smooth, prey, lead)


def test_cross_correlation_symmetric_lags():
    prey = _prey()
    lags, corr = cat.cross_correlation(prey, prey, max_lag=6)
    assert lags[0] == -6 and lags[-1] == 6
    assert cat.peak_lag(lags, corr) == 0                # autocorrelation pique a 0
    assert corr[np.argmax(corr)] == pytest.approx(1.0, abs=1e-6)


# --------------------------------------------------------------------------- #
#  Durcissement p_hat (cran 10.1, #4588) : baselines adverses, familles,       #
#  banc aux deux metriques separees                                            #
# --------------------------------------------------------------------------- #


def test_moving_average_tracker_constant_and_lag():
    const = np.full(50, 3.0)
    assert np.allclose(cat.moving_average_tracker(const, window=5), 3.0)
    ramp = np.arange(50, dtype=float)
    ma = cat.moving_average_tracker(ramp, window=5)
    assert np.all(ma[5:] < ramp[5:])                    # lisser retarde une rampe


def test_ar1_coefficient_recovers_generating_phi():
    rng = np.random.default_rng(0)
    phi_true = 0.8
    x = np.zeros(4000)
    for k in range(1, x.shape[0]):
        x[k] = phi_true * x[k - 1] + rng.standard_normal()
    assert abs(cat.ar1_coefficient(x) - phi_true) < 0.05


def test_ar1_tracker_shrinks_toward_mean():
    prey = _prey()
    pred = cat.ar1_tracker(prey, lead=4)
    mu = prey.mean()
    # phi < 1 sur une serie stationnaire : la prediction se contracte vers mu
    assert np.all(np.abs(pred - mu) <= np.abs(prey - mu) + 1e-9)


def test_prey_trajectory_families_distinct():
    kinds = ["sinus", "derive", "creneau"]
    trajs = {
        k: cat.prey_trajectory(k, n_steps=200, noise=0.1,
                               rng=np.random.default_rng(7))
        for k in kinds
    }
    for k in kinds:
        assert trajs[k].shape == (200,)
    assert not np.allclose(trajs["sinus"], trajs["derive"])
    assert not np.allclose(trajs["sinus"], trajs["creneau"])
    with pytest.raises(ValueError):
        cat.prey_trajectory("inconnue")


def test_anticipation_report_both_metrics_all_estimators():
    rep = cat.anticipation_report(_prey(), lead=4)
    assert set(rep) == {"p_hat", "persistance", "moyenne_mobile", "ar1"}
    for valeurs in rep.values():
        assert set(valeurs) == {"erreur", "pic_lag"}
        assert valeurs["erreur"] >= 0.0


def test_phat_advantage_is_regime_dependent():
    # Gate du cran 10.1 (#4588) : p_hat bat les 3 baselines sur trajectoire
    # lisse (sinus, inertie exploitable) mais PERD sur le creneau (la vitesse
    # EMA sur-reagit au saut). L'avantage est regime-dependant, et le banc
    # doit rendre cet echec visible plutot que l'agreger.
    lead = 4

    def meilleure_baseline(rep):
        return min(v["erreur"] for k, v in rep.items() if k != "p_hat")

    rep_sin = cat.anticipation_report(
        cat.prey_trajectory("sinus", rng=np.random.default_rng(7)), lead=lead)
    rep_cre = cat.anticipation_report(
        cat.prey_trajectory("creneau", rng=np.random.default_rng(7)), lead=lead)
    assert rep_sin["p_hat"]["erreur"] < meilleure_baseline(rep_sin)
    assert rep_cre["p_hat"]["erreur"] > meilleure_baseline(rep_cre)
