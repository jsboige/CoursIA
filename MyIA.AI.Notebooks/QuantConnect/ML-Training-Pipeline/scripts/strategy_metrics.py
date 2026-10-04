"""Métriques de stratégie partagées : Sharpe, CAGR, pire baisse.

Une seule définition pour les scripts qui comparent leurs chiffres entre eux : le
verdict de l'expérience 5a (`voltarget_strategy_verdict.py`, #18921) et le rejeu des
candidates en ombre (`shadow_replay.py`, #18923). Une candidate suivie en ombre se
compare directement aux chiffres du verdict, ce qui n'a de sens que si les deux
scripts calculent la même chose sous le même nom.

- Sharpe = moyenne / écart-type (ddof=1) * sqrt(252) des rendements journaliers
  nets, taux sans risque nul. Le Sharpe affiché par QuantConnect retranche un taux
  sans risque : il ne se compare pas directement.
- CAGR = patrimoine final ** (1 / années) - 1, le patrimoine étant le produit
  cumulé de (1 + r) ; les années sont fournies par l'appelant (jours calendaires
  divisés par 365,25 dans les deux scripts).
- Pire baisse = minimum de patrimoine / maximum courant - 1 (nombre négatif).

Un écart-type nul n'est pas traité ici : le Sharpe vaut alors inf ou nan, et c'est
à l'appelant de décider ce qu'il en fait (le rejeu en ombre laisse la case vide).
"""

from __future__ import annotations

import math

import numpy as np

TRADING_DAYS = 252


def sharpe(returns, axis: int | None = None):
    """Sharpe annualisé, taux sans risque nul ; `axis` sert au bootstrap (une ligne par tirage)."""
    r = np.asarray(returns, dtype=float)
    return r.mean(axis=axis) / r.std(axis=axis, ddof=1) * math.sqrt(TRADING_DAYS)


def wealth(returns) -> np.ndarray:
    """Patrimoine après chaque rendement, en partant de 1."""
    return np.cumprod(1.0 + np.asarray(returns, dtype=float))


def cagr(returns, years: float) -> float:
    """Taux de croissance annuel composé sur `years` années."""
    if years <= 0:
        raise ValueError("years must be positive")
    return float(wealth(returns)[-1] ** (1.0 / years) - 1.0)


def max_drawdown(returns) -> float:
    """Pire baisse depuis un sommet, en fraction (négative ou nulle)."""
    w = wealth(returns)
    return float((w / np.maximum.accumulate(w) - 1.0).min())
