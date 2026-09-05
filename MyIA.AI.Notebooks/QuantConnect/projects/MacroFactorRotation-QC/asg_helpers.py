"""Fonctions pures du bras ASG (Aggregate Sales Growth) - MacroFactorRotation-QC.

Extraites de main.py pour etre testees localement sans aucune dependance
LEAN/QuantConnect. Mecaniques conformes a l'article QC research #21132
"Sizing Market Exposure With Aggregate Sales Growth" (Derek Melchin,
juillet 2026), lui-meme fonde sur Garfinkel, Hribar & Hsiao (2025),
"Aggregate Sales Growth and Stock Market Returns" (SSRN 5066654) :

- croissance annuelle du chiffre d'affaires, winsorisee 1 % / 99 % en
  coupe transversale, agregee par pondération de capitalisation ;
- regression OLS a fenetre croissante du rendement excédentaire mensuel
  de SPY sur l'ASG retardée d'un mois (convention shift(1, freq="M") ;
- exposition clip(forecast / (gamma * variance), 0, 1.5) avec gamma = 3
  et variance des 120 derniers rendements excédentaires mensuels.
"""

from typing import Optional, Tuple

import numpy as np
import pandas as pd

# Constantes de l'article #21132 (garde-fous decrits dans l'issue #14722).
WINSOR_LOWER_Q = 0.01
WINSOR_UPPER_Q = 0.99
GAMMA = 3.0
VARIANCE_WINDOW = 120  # mois (10 ans)
MIN_WEIGHT = 0.0
MAX_WEIGHT = 1.5

# Garde-fous robustesse (choix #14722, l'article n'en fixe pas) :
# nombre minimal d'observations appariees / de mois de variance avant
# qu'un poids autre que 100 % BIL puisse etre emis.
MIN_FIT_OBSERVATIONS = 60
MIN_VARIANCE_OBSERVATIONS = 60


def winsorize(
    values: pd.Series,
    lower_q: float = WINSOR_LOWER_Q,
    upper_q: float = WINSOR_UPPER_Q,
) -> pd.Series:
    """Ecrete la coupe transversale aux quantiles lower_q / upper_q."""
    if values.empty:
        return values
    lower, upper = values.quantile([lower_q, upper_q])
    return values.clip(lower, upper)


def aggregate_sales_growth(
    growth: pd.Series, market_cap: pd.Series
) -> Optional[float]:
    """ASG mensuelle : moyenne des croissances winsorisees, ponderee par cap.

    Ne contribuent que les firmes avec capitalisation positive non nulle
    et croissance observee (mecanique de l'article #21132). Renvoie None
    si aucune observation exploitable.
    """
    firms = pd.concat(
        [growth.rename("growth"), market_cap.rename("market_cap")], axis=1
    ).dropna(subset=["growth"])
    if firms.empty:
        return None
    firms["growth"] = winsorize(firms["growth"])
    usable = firms["market_cap"].notna() & (firms["market_cap"] > 0)
    firms = firms[usable]
    if firms.empty:
        return None
    total_cap = firms["market_cap"].sum()
    if not np.isfinite(total_cap) or total_cap <= 0:
        return None
    return float(np.average(firms["growth"], weights=firms["market_cap"]))


def fit_expanding_ols(
    asg: pd.Series,
    excess_returns: pd.Series,
    min_observations: int = 2,
) -> Optional[Tuple[float, float]]:
    """OLS fenetre croissante du rendement excédentaire sur l'ASG retardée.

    Reproduit la construction de l'article : X = asg.shift(1, freq="M")
    aligne (jointure interne) sur la serie des rendements excédentaires
    mensuels realises, puis ajustement polynomial de degre 1 via
    np.polynomial.polynomial.polyfit (coefficient en degre croissant :
    renvoie (alpha, beta)).

    Renvoie None si moins de min_observations paires exploitables ou si
    l'ajustement echoue / diverge.
    """
    if asg.empty or excess_returns.empty:
        return None
    x, y = asg.shift(1, freq="M").align(excess_returns, join="inner")
    paired = pd.concat([x.rename("x"), y.rename("y")], axis=1).dropna()
    if len(paired) < max(2, min_observations):
        return None
    try:
        alpha, beta = np.polynomial.polynomial.polyfit(
            paired["x"], paired["y"], 1
        )
    except Exception:
        return None
    if not (np.isfinite(alpha) and np.isfinite(beta)):
        return None
    return float(alpha), float(beta)


def trailing_variance(
    excess_returns: pd.Series,
    window: int = VARIANCE_WINDOW,
    min_observations: int = MIN_VARIANCE_OBSERVATIONS,
) -> Optional[float]:
    """Variance echantillon (ddof=1) des derniers `window` mois.

    Equivalent pandas de l'indicateur Variance(10*12) de l'article une
    fois la fenetre remplie. Renvoie None sous le seuil minimal
    d'observations ou si la variance est non finie / nulle.
    """
    if excess_returns.empty:
        return None
    tail = excess_returns.dropna().tail(window)
    if len(tail) < min_observations:
        return None
    variance = float(tail.var())
    if not np.isfinite(variance) or variance <= 0:
        return None
    return variance


def forecast_excess_return(
    fit: Optional[Tuple[float, float]], current_asg: Optional[float]
) -> Optional[float]:
    """Prevision alpha + beta * ASG courante (entree de l'article #21132)."""
    if fit is None or current_asg is None:
        return None
    if not np.isfinite(current_asg):
        return None
    alpha, beta = fit
    value = alpha + beta * float(current_asg)
    return float(value) if np.isfinite(value) else None


def solve_exposure(
    forecast: Optional[float],
    variance: Optional[float],
    gamma: float = GAMMA,
    min_weight: float = MIN_WEIGHT,
    max_weight: float = MAX_WEIGHT,
) -> float:
    """Poids SPY w = clip(forecast / (gamma * variance), min, max).

    Entrees invalides (None, variance <= 0, NaN) -> min_weight (100 % BIL),
    garde-fou #14722 : l'article diviserait par une variance d'indicateur
    non prete (division par zero), on reste ici entierement en T-bills.
    """
    if forecast is None or variance is None:
        return min_weight
    if not (np.isfinite(forecast) and np.isfinite(variance)):
        return min_weight
    if variance <= 0:
        return min_weight
    w_star = forecast / (gamma * variance)
    return float(np.clip(w_star, min_weight, max_weight))
