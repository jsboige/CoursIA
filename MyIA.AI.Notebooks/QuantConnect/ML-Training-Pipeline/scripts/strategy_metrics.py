"""Métriques de stratégie partagées : Sharpe, CAGR, pire baisse.

Une seule définition pour les scripts qui comparent leurs chiffres entre eux : le
verdict de l'expérience 5a (`voltarget_strategy_verdict.py`, #18921) et le rejeu des
candidates en ombre (`shadow_replay.py`, #18923). Une candidate suivie en ombre se
compare directement aux chiffres du verdict, ce qui n'a de sens que si les deux
scripts calculent la même chose sous le même nom.

- Sharpe = moyenne / écart-type (ddof=1) * sqrt(périodes par an) des rendements
  nets, taux sans risque nul. 252 périodes par défaut (séances boursières) ; un
  marché ouvert tous les jours passe 365. Le Sharpe affiché par QuantConnect
  retranche un taux sans risque : il ne se compare pas directement.
- CAGR = patrimoine final / patrimoine initial ** (1 / années) - 1, le patrimoine
  étant le produit cumulé de (1 + r) à partir de 1.
- Pire baisse = minimum de patrimoine / maximum courant - 1 (nombre négatif), le
  capital de départ compté comme premier sommet : une baisse dès le premier
  rendement est une baisse.

Conventions communes au pipeline (#19016) — ce module les porte, les autres
modules l'importent :

- **Années du CAGR** : fournies par l'appelant. Quand les rendements sont datés,
  jours calendaires entre le premier et le dernier point divisés par 365,25 (verdict
  de la 5a, rejeu en ombre). Un appelant qui ne reçoit qu'un tableau sans dates
  (`wf_framework/metrics.py`) compte des séances divisées par les périodes par an,
  et l'écrit dans sa docstring.
- **Sharpe non défini** (écart-type nul) : ce module ne le remplace pas. Il rend la
  valeur de la division (inf ou nan), et l'appelant laisse la case vide plutôt que
  d'afficher un 0,0 qui se lirait comme un Sharpe mesuré. Les fonctions plus
  anciennes qui rendent 0,0 le disent dans leur docstring.
"""

from __future__ import annotations

import math

import numpy as np

TRADING_DAYS = 252


def sharpe(returns, axis: int | None = None, periods_per_year: int = TRADING_DAYS):
    """Sharpe annualisé, taux sans risque nul ; `axis` sert au bootstrap (une ligne par tirage).

    `periods_per_year=1` rend le Sharpe par période, sans annualisation.
    """
    r = np.asarray(returns, dtype=float)
    return r.mean(axis=axis) / r.std(axis=axis, ddof=1) * math.sqrt(periods_per_year)


def wealth(returns) -> np.ndarray:
    """Patrimoine après chaque rendement, en partant de 1 (le 1 initial n'est pas rendu)."""
    return np.cumprod(1.0 + np.asarray(returns, dtype=float))


def _with_start(returns) -> np.ndarray:
    """Patrimoine capital de départ compris : 1, puis un point par rendement."""
    return np.concatenate(([1.0], wealth(returns)))


def cagr_of_equity(equity, years: float) -> float:
    """Taux de croissance annuel composé d'une courbe d'équité sur `years` années."""
    if years <= 0:
        raise ValueError("years must be positive")
    e = np.asarray(equity, dtype=float)
    return float((e[-1] / e[0]) ** (1.0 / years) - 1.0)


def cagr(returns, years: float) -> float:
    """Taux de croissance annuel composé des rendements sur `years` années."""
    return cagr_of_equity(_with_start(returns), years)


def max_drawdown_of_equity(equity) -> float:
    """Pire baisse d'une courbe d'équité depuis un sommet, en fraction (négative ou nulle)."""
    e = np.asarray(equity, dtype=float)
    return float((e / np.maximum.accumulate(e) - 1.0).min())


def max_drawdown(returns) -> float:
    """Pire baisse des rendements depuis un sommet, capital de départ compris."""
    return max_drawdown_of_equity(_with_start(returns))
