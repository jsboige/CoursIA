"""
Baseline models for financial direction prediction evaluation.

Every ML model must beat these baselines to be considered useful.
If your model's DirAcc <= majority_class or Sharpe <= random_walk,
it is not adding value.

References:
    - Hands-On AI Trading with Python, Pik et al., Wiley 2025
    - Lopez de Prado, "Advances in Financial Machine Learning" (AFML)
"""

from __future__ import annotations

import numpy as np
import pandas as pd


def majority_class_baseline(y_train: np.ndarray | pd.Series, y_test: np.ndarray | pd.Series) -> dict:
    """Predict the most frequent class from training data for all test samples.

    This is the absolute floor for direction accuracy. Any model with
    DirAcc <= this baseline is a majority class predictor and adds no value.

    Parameters
    ----------
    y_train : array-like
        Training labels (0=down, 1=up or -1/1).
    y_test : array-like
        Test labels.

    Returns
    -------
    dict with keys: accuracy, majority_class, majority_freq, n_train, n_test.
    """
    y_train = np.asarray(y_train)
    y_test = np.asarray(y_test)

    classes, counts = np.unique(y_train, return_counts=True)
    majority_idx = np.argmax(counts)
    majority = classes[majority_idx]
    freq = counts[majority_idx] / len(y_train)

    predictions = np.full(len(y_test), majority)
    accuracy = np.mean(predictions == y_test)

    return {
        "accuracy": float(accuracy),
        "majority_class": int(majority),
        "majority_freq": float(freq),
        "n_train": len(y_train),
        "n_test": len(y_test),
    }


def naive_momentum_baseline(
    prices: pd.Series | np.ndarray,
    lookback: int = 20,
    test_start: int | None = None,
) -> dict:
    """Simple moving average crossover: buy if price > MA(lookback), else sell.

    Industry-standard naive baseline for direction prediction.

    Parameters
    ----------
    prices : array-like
        Price series.
    lookback : int
        Moving average window.
    test_start : int or None
        Index at which evaluation begins. If None, evaluates on all data
        after the first lookback period.

    Returns
    -------
    dict with keys: accuracy, sharpe, returns, n_signals, lookback.
    """
    prices = pd.Series(prices).reset_index(drop=True)
    ma = prices.rolling(lookback).mean()
    direction = (prices > ma).astype(int)

    # Shift to avoid look-ahead: predict tomorrow's direction from today's signal
    forward_return = prices.pct_change().shift(-1)
    predicted_up = direction

    start = test_start if test_start is not None else lookback
    valid = slice(start, len(prices) - 1)

    actual_up = (forward_return[valid] > 0).astype(int)
    predicted = predicted_up[valid]

    accuracy = float(np.mean(predicted.values == actual_up.values))

    # Calculate Sharpe from strategy returns
    strategy_returns = forward_return[valid] * (2 * predicted.values - 1)
    sharpe = _sharpe_from_returns(strategy_returns.dropna())

    return {
        "accuracy": accuracy,
        "sharpe": float(sharpe),
        "lookback": lookback,
        "n_signals": int(len(predicted)),
        "start": start,
    }


def random_walk_baseline(
    prices: pd.Series | np.ndarray,
    n_simulations: int = 1000,
    seed: int = 42,
    test_start: int | None = None,
) -> dict:
    """Distribution of Sharpe ratios under the null hypothesis of random trading.

    Generates random long/short signals and computes the distribution of
    resulting Sharpe ratios. Used for deflated Sharpe ratio testing
    (AFML Chapter 14) to account for multiple testing.

    Parameters
    ----------
    prices : array-like
        Price series.
    n_simulations : int
        Number of random strategy simulations.
    seed : int
        Random seed for reproducibility.
    test_start : int or None
        Index at which evaluation begins.

    Returns
    -------
    dict with keys: sharpe_mean, sharpe_std, sharpe_p95, diracc_mean,
                    diracc_std, n_simulations, observed_sharpes.
    """
    prices = pd.Series(prices).reset_index(drop=True)
    returns = prices.pct_change().dropna()

    start = test_start if test_start is not None else 0
    test_returns = returns.iloc[start:]

    rng = np.random.default_rng(seed)
    sharpes = []
    diraccs = []

    for _ in range(n_simulations):
        # Random long/short with 50/50 probability
        signals = rng.choice([-1, 1], size=len(test_returns))
        strategy_returns = test_returns.values * signals
        sharpe = _sharpe_from_returns(pd.Series(strategy_returns))
        sharpes.append(sharpe)

        # Direction accuracy
        predicted_up = (signals == 1).astype(int)
        actual_up = (test_returns.values > 0).astype(int)
        diraccs.append(np.mean(predicted_up == actual_up))

    sharpes = np.array(sharpes)
    diraccs = np.array(diraccs)

    return {
        "sharpe_mean": float(np.mean(sharpes)),
        "sharpe_std": float(np.std(sharpes)),
        "sharpe_p95": float(np.percentile(sharpes, 95)),
        "diracc_mean": float(np.mean(diraccs)),
        "diracc_std": float(np.std(diraccs)),
        "n_simulations": n_simulations,
        "n_test_samples": len(test_returns),
    }


def buy_and_hold_baseline(
    prices: pd.Series | np.ndarray,
    test_start: int | None = None,
) -> dict:
    """Buy-and-hold reference. Every long-only strategy must beat this.

    Parameters
    ----------
    prices : array-like
        Price series.
    test_start : int or None
        Index at which evaluation begins.

    Returns
    -------
    dict with keys: total_return, cagr, sharpe, max_drawdown, volatility,
                    n_days, start_price, end_price.
    """
    prices = pd.Series(prices).reset_index(drop=True)
    returns = prices.pct_change().dropna()

    start = test_start if test_start is not None else 0
    test_returns = returns.iloc[start:]
    test_prices = prices.iloc[start:]

    if len(test_returns) == 0:
        return {
            "total_return": 0.0,
            "cagr": 0.0,
            "sharpe": 0.0,
            "max_drawdown": 0.0,
            "volatility": 0.0,
            "n_days": 0,
        }

    total_return = float(test_prices.iloc[-1] / test_prices.iloc[0] - 1)
    n_years = len(test_returns) / 252
    cagr = float((1 + total_return) ** (1 / max(n_years, 1e-6)) - 1) if total_return > -1 else -1.0

    sharpe = _sharpe_from_returns(test_returns)

    # Max drawdown
    cummax = test_prices.cummax()
    drawdown = (test_prices - cummax) / cummax
    max_dd = float(drawdown.min())

    volatility = float(test_returns.std() * np.sqrt(252))

    return {
        "total_return": total_return,
        "cagr": cagr,
        "sharpe": float(sharpe),
        "max_drawdown": max_dd,
        "volatility": volatility,
        "n_days": len(test_returns),
        "start_price": float(test_prices.iloc[0]),
        "end_price": float(test_prices.iloc[-1]),
    }


def _sharpe_from_returns(returns: pd.Series, annualize: bool = True, risk_free: float = 0.0) -> float:
    """Compute Sharpe ratio from a returns series.

    Parameters
    ----------
    returns : pd.Series
        Strategy or asset returns.
    annualize : bool
        Annualize using sqrt(252).
    risk_free : float
        Risk-free rate (annualized).

    Returns
    -------
    float : Sharpe ratio.
    """
    if len(returns) == 0:
        return 0.0

    mean_ret = returns.mean()
    std_ret = returns.std()

    if std_ret < 1e-12 or np.isnan(std_ret):
        return 0.0

    daily_rf = risk_free / 252
    sharpe = (mean_ret - daily_rf) / std_ret

    if annualize:
        sharpe *= np.sqrt(252)

    return float(sharpe)
