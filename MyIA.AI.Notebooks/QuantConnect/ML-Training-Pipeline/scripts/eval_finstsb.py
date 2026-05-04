"""
FinTSB-style evaluation with regime detection for financial ML models.

Evaluates model performance across 4 market regimes (uptrend, downtrend,
volatility, black_swan) to ensure strategies don't just work in one regime.

References:
    - FinTSB: TongjiFinLab/FinTSB (https://github.com/TongjiFinLab/FinTSB, 2025)
    - Hands-On AI Trading with Python, Pik et al., Wiley 2025
"""

from __future__ import annotations

import numpy as np
import pandas as pd
from typing import Protocol


class DirectionModel(Protocol):
    """Protocol for models that predict price direction."""

    def predict(self, X: np.ndarray) -> np.ndarray: ...


def detect_regimes(
    prices: pd.Series | np.ndarray,
    lookback_days: int = 60,
    uptrend_threshold: float = 0.10,
    downtrend_threshold: float = -0.10,
    volatility_percentile: float = 75,
    black_swan_drawdown: float = -0.20,
    black_swan_window: int = 30,
) -> pd.Series:
    """Classify each date into a market regime.

    Parameters
    ----------
    prices : array-like
        Daily price series.
    lookback_days : int
        Rolling window for regime detection.
    uptrend_threshold : float
        Minimum rolling return to classify as uptrend (annualized ~10%).
    downtrend_threshold : float
        Maximum rolling return to classify as downtrend.
    volatility_percentile : float
        Percentile threshold for high-volatility regime (0-100).
    black_swan_drawdown : float
        Drawdown threshold for black swan (e.g. -0.20 = -20%).
    black_swan_window : int
        Window for drawdown calculation.

    Returns
    -------
    pd.Series of regime labels: "uptrend", "downtrend", "volatility", "black_swan".
    """
    prices = pd.Series(prices).reset_index(drop=True)
    returns = prices.pct_change()

    # Rolling return over lookback
    rolling_return = prices.pct_change(lookback_days)

    # Rolling volatility (annualized)
    rolling_std = returns.rolling(lookback_days).std() * np.sqrt(252)
    vol_threshold = rolling_std.quantile(volatility_percentile / 100)

    # Rolling drawdown
    rolling_max = prices.rolling(black_swan_window, min_periods=1).max()
    drawdown = (prices - rolling_max) / rolling_max

    regimes = pd.Series("normal", index=prices.index, dtype="object")

    # Black swan first (highest priority)
    black_swan_mask = drawdown <= black_swan_drawdown
    regimes[black_swan_mask] = "black_swan"

    # Uptrend: strong positive returns
    uptrend_mask = (rolling_return >= uptrend_threshold) & (regimes == "normal")
    regimes[uptrend_mask] = "uptrend"

    # Downtrend: strong negative returns
    downtrend_mask = (rolling_return <= downtrend_threshold) & (regimes == "normal")
    regimes[downtrend_mask] = "downtrend"

    # Volatility: high std (remaining non-classified)
    vol_mask = (rolling_std >= vol_threshold) & (regimes == "normal")
    regimes[vol_mask] = "volatility"

    # Remaining = normal (subset of uptrend or quiet market)
    # For evaluation purposes, fold "normal" into closest regime
    normal_mask = regimes == "normal"
    # If positive return and not classified, treat as mild uptrend
    mild_up = normal_mask & (rolling_return > 0)
    regimes[mild_up] = "uptrend"
    # If negative return and not classified, treat as mild downtrend
    mild_down = normal_mask & (rolling_return <= 0)
    regimes[mild_down] = "downtrend"

    # Fill NaN from rolling calculations
    regimes[:lookback_days] = "normal"

    return regimes


def eval_per_regime(
    model: DirectionModel,
    X: np.ndarray,
    y: np.ndarray,
    prices: pd.Series | np.ndarray,
    regimes: pd.Series | None = None,
) -> dict:
    """Evaluate model performance per market regime.

    Parameters
    ----------
    model : DirectionModel
        Model with a predict() method.
    X : np.ndarray
        Feature matrix.
    y : np.ndarray
        True labels (0=down, 1=up).
    prices : array-like
        Price series for regime detection.
    regimes : pd.Series or None
        Pre-computed regime labels. If None, computed from prices.

    Returns
    -------
    dict with per-regime metrics and weighted average.
    """
    prices = pd.Series(prices).reset_index(drop=True)
    n = min(len(X), len(y), len(prices))
    X = X[:n]
    y = y[:n]
    prices = prices[:n]

    if regimes is None:
        regimes = detect_regimes(prices)
    regimes = regimes.iloc[:n].reset_index(drop=True)

    predictions = model.predict(X)
    returns = prices.pct_change().fillna(0).values[:n]

    results = {}
    regime_counts = {}

    for regime in ["uptrend", "downtrend", "volatility", "black_swan"]:
        mask = regimes.values == regime
        n_samples = int(mask.sum())

        if n_samples < 5:
            results[regime] = {
                "diracc": float("nan"),
                "sharpe": float("nan"),
                "n_samples": n_samples,
            }
            regime_counts[regime] = 0
            continue

        regime_y = y[mask]
        regime_pred = predictions[mask]
        regime_returns = returns[mask]

        diracc = float(np.mean(regime_pred == regime_y))

        # Strategy returns: long if predict up, short if predict down
        strategy_returns = regime_returns * (2 * regime_pred - 1)
        sharpe = _sharpe(strategy_returns)

        results[regime] = {
            "diracc": diracc,
            "sharpe": sharpe,
            "n_samples": n_samples,
        }
        regime_counts[regime] = n_samples

    # Weighted average Sharpe
    total = sum(regime_counts.values())
    if total > 0:
        weights = {r: c / total for r, c in regime_counts.items() if c > 0}
        weighted_sharpe = sum(
            weights.get(r, 0) * results[r]["sharpe"]
            for r in weights
            if not np.isnan(results[r].get("sharpe", float("nan")))
        )
        weighted_diracc = sum(
            weights.get(r, 0) * results[r]["diracc"]
            for r in weights
            if not np.isnan(results[r].get("diracc", float("nan")))
        )
    else:
        weighted_sharpe = float("nan")
        weighted_diracc = float("nan")

    results["weighted_avg"] = {
        "diracc": weighted_diracc,
        "sharpe": weighted_sharpe,
        "n_samples": total,
    }

    return results


def validate_no_regime_failure(eval_results: dict, min_sharpe: float = 0.0) -> tuple[bool, list[str]]:
    """Check that no regime has Sharpe below minimum threshold.

    A strategy that only works in one regime (e.g. uptrend) is fragile.

    Parameters
    ----------
    eval_results : dict
        Output from eval_per_regime().
    min_sharpe : float
        Minimum acceptable Sharpe per regime.

    Returns
    -------
    (passed, failures) : tuple of bool and list of regime names that failed.
    """
    failures = []
    for regime in ["uptrend", "downtrend", "volatility", "black_swan"]:
        if regime not in eval_results:
            continue
        regime_data = eval_results[regime]
        if regime_data["n_samples"] < 5:
            continue
        sharpe = regime_data.get("sharpe", float("nan"))
        if np.isnan(sharpe):
            failures.append(f"{regime}: insufficient data (Sharpe=NaN)")
        elif sharpe < min_sharpe:
            failures.append(f"{regime}: Sharpe={sharpe:.3f} < {min_sharpe}")

    return len(failures) == 0, failures


def _sharpe(returns: np.ndarray, annualize: bool = True) -> float:
    """Compute Sharpe ratio from returns array."""
    if len(returns) == 0 or np.std(returns) < 1e-12:
        return 0.0
    sharpe = np.mean(returns) / np.std(returns)
    if annualize:
        sharpe *= np.sqrt(252)
    return float(sharpe)
