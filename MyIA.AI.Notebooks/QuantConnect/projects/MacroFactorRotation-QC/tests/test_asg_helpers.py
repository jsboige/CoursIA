"""Tests locaux des helpers purs du bras ASG (issue #14722).

Couvre : winsorisation 1/99, ponderation par capitalisation, lag d'un
mois de la regression OLS a fenetre croissante, variance 120 mois et
bornes du poids clip(., 0, 1.5).

Execute avec : python -m pytest tests/test_asg_helpers.py
(depuis MyIA.AI.Notebooks/QuantConnect/projects/MacroFactorRotation-QC)
"""

import sys
from pathlib import Path

import numpy as np
import pandas as pd

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import asg_helpers  # noqa: E402


def _cross_section(n_half: int = 50) -> pd.Series:
    """Coupe a 2*n_half valeurs dupliquees (quantiles 1/99 exacts)."""
    return pd.Series([0.10] * n_half + [0.20] * n_half)


def test_winsorize_clips_at_quantiles():
    values = pd.Series(np.arange(1, 101, dtype=float))
    clipped = asg_helpers.winsorize(values)
    lo, hi = values.quantile([0.01, 0.99])
    assert clipped.min() == lo
    assert clipped.max() == hi
    # Les valeurs interieures ne bougent pas.
    assert clipped.iloc[50] == values.iloc[50]


def test_aggregate_sales_growth_cap_weighting_exact():
    growth = _cross_section()
    caps = pd.Series(1.0, index=growth.index)
    # Quantiles exactement 0.10/0.20 (valeurs dupliquees) -> winsorisation
    # identite, moyenne ponderee attendue = 0.15.
    assert abs(asg_helpers.aggregate_sales_growth(growth, caps) - 0.15) < 1e-12
    # La ponderation par cap respecte les proportions.
    caps = pd.Series([3.0] + [1.0] * (len(growth) - 1), index=growth.index)
    growth_all_010 = pd.Series(0.10, index=growth.index)
    value = asg_helpers.aggregate_sales_growth(growth_all_010, caps)
    assert abs(value - 0.10) < 1e-12


def test_aggregate_sales_growth_winsorizes_outliers():
    # Une firme extreme (croissance 100) avec cap ecrasante : sans
    # winsorisation l'ASG serait proche de 100 ; winsorisee au quantile
    # 99 % elle est contenue juste au-dessus de la masse des valeurs.
    growth = pd.Series([0.10] * 50 + [0.20] * 49 + [100.0])
    caps = pd.Series([1.0] * 99 + [1e12])
    value = asg_helpers.aggregate_sales_growth(growth, caps)
    assert value is not None
    assert 1.0 < value < 2.0


def test_aggregate_sales_growth_excludes_nonpositive_caps():
    # 101 valeurs : 50 x 0.10, 50 x 0.20, 1 extreme a 100.0. Les quantiles
    # 1/99 tombent exactement sur 0.10/0.20 (positions 1 et 99), donc la
    # winsorisation ne touche pas les 100 valeurs retenues.
    growth = pd.Series([0.10] * 50 + [0.20] * 50 + [100.0])
    caps = pd.Series([1.0] * 100 + [0.0])  # firme extreme sans cap
    value = asg_helpers.aggregate_sales_growth(growth, caps)
    assert abs(value - 0.15) < 1e-12
    # Cap NaN : meme exclusion.
    caps_nan = pd.Series([1.0] * 100 + [np.nan])
    value = asg_helpers.aggregate_sales_growth(growth, caps_nan)
    assert abs(value - 0.15) < 1e-12
    # Aucune observation exploitable -> None.
    assert asg_helpers.aggregate_sales_growth(pd.Series(dtype=float), pd.Series(dtype=float)) is None
    assert asg_helpers.aggregate_sales_growth(growth, pd.Series(0.0, index=growth.index)) is None


def test_fit_expanding_ols_recovers_relationship_with_one_month_lag():
    # Serie ASG aleatoire (autocorrelation nulle) : seul l'appariement
    # retarde d'un mois peut retrouver exactement (alpha, beta).
    rng = np.random.default_rng(42)
    months = pd.period_range("2015-01", "2019-12", freq="M")
    asg = pd.Series(rng.normal(0.05, 0.02, len(months)), index=months)
    alpha_true, beta_true = 0.001, 0.75
    excess = (alpha_true + beta_true * asg.shift(1)).dropna()
    fit = asg_helpers.fit_expanding_ols(asg, excess)
    assert fit is not None
    alpha_hat, beta_hat = fit
    assert abs(alpha_hat - alpha_true) < 1e-8
    assert abs(beta_hat - beta_true) < 1e-8
    # Un appariement concurrent (sans lag) ne retrouverait pas beta :
    # l'ASG n'est pas autocorrelee, la regression serait degénérée en pente 0.
    concurrent = asg.align(excess, join="inner")[0]
    a2, b2 = np.polynomial.polynomial.polyfit(concurrent, excess, 1)
    assert abs(b2 - beta_true) > 0.1


def test_fit_expanding_ols_requires_min_observations():
    months = pd.period_range("2015-01", "2016-06", freq="M")
    asg = pd.Series(np.linspace(0.01, 0.09, len(months)), index=months)
    excess = pd.Series(np.linspace(0.0, 0.02, len(months)), index=months)
    assert asg_helpers.fit_expanding_ols(asg, excess, min_observations=60) is None
    assert asg_helpers.fit_expanding_ols(asg, excess, min_observations=2) is not None


def test_trailing_variance_uses_last_window_months():
    rng = np.random.default_rng(7)
    months = pd.period_range("2005-01", "2020-12", freq="M")
    excess = pd.Series(rng.normal(0.005, 0.04, len(months)), index=months)
    value = asg_helpers.trailing_variance(excess, window=120, min_observations=60)
    assert value is not None
    assert abs(value - excess.tail(120).var()) < 1e-15
    # 59 mois < seuil minimal de 60 -> None ; 100 mois disponibles ->
    # variance portee par les 100 mois (fenetre 120 non remplie).
    assert asg_helpers.trailing_variance(excess.tail(59), window=120, min_observations=60) is None
    short = excess.tail(100)
    value_100 = asg_helpers.trailing_variance(short, window=120, min_observations=60)
    assert value_100 is not None
    assert abs(value_100 - short.var()) < 1e-15
    # Fenetre plus courte respectee.
    value_50 = asg_helpers.trailing_variance(short, window=50, min_observations=50)
    assert value_50 is not None
    assert abs(value_50 - short.tail(50).var()) < 1e-15


def test_solve_exposure_formula_and_clips():
    # w = forecast / (gamma * variance) : 0.10 / (3 * 0.04) = 0.8333...
    assert abs(asg_helpers.solve_exposure(0.10, 0.04) - 0.10 / 0.12) < 1e-12
    # Prevision negative -> jamais short -> 0.
    assert asg_helpers.solve_exposure(-0.10, 0.04) == 0.0
    # Prevision extreme -> plafond 1.5.
    assert asg_helpers.solve_exposure(10.0, 0.001) == 1.5
    # Entrees invalides -> 100 % BIL (garde-fou #14722).
    assert asg_helpers.solve_exposure(None, 0.04) == 0.0
    assert asg_helpers.solve_exposure(0.10, None) == 0.0
    assert asg_helpers.solve_exposure(0.10, 0.0) == 0.0
    assert asg_helpers.solve_exposure(float("nan"), 0.04) == 0.0
    assert asg_helpers.solve_exposure(0.10, float("nan")) == 0.0


def test_forecast_excess_return():
    assert asg_helpers.forecast_excess_return(None, 0.05) is None
    assert asg_helpers.forecast_excess_return((0.001, 0.75), None) is None
    value = asg_helpers.forecast_excess_return((0.001, 0.75), 0.05)
    assert abs(value - (0.001 + 0.75 * 0.05)) < 1e-15
