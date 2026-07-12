"""Production portfolio metrics for walk-forward backtesting.

Computes Sharpe, MaxDD, CAGR, HitRate, Calmar, and related statistics
from equity curves or return series. Designed for direct consumption
by backtest_walk_forward.py and the validation pipeline.
"""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np


@dataclass
class PortfolioMetrics:
    """Production metrics from a portfolio simulation."""
    sharpe: float
    max_drawdown: float
    cagr: float
    hit_rate: float
    calmar: float
    total_return: float
    volatility: float
    n_periods: int
    gross_sharpe: float = 0.0
    net_sharpe: float = 0.0
    cost_drag_bps: float = 0.0

    def to_dict(self) -> dict:
        return {
            "sharpe": round(self.sharpe, 4),
            "max_drawdown": round(self.max_drawdown, 4),
            "cagr": round(self.cagr, 4),
            "hit_rate": round(self.hit_rate, 4),
            "calmar": round(self.calmar, 4),
            "total_return": round(self.total_return, 6),
            "volatility": round(self.volatility, 4),
            "n_periods": self.n_periods,
            "gross_sharpe": round(self.gross_sharpe, 4),
            "net_sharpe": round(self.net_sharpe, 4),
            "cost_drag_bps": round(self.cost_drag_bps, 2),
        }


def compute_sharpe(
    returns: np.ndarray,
    annualize: bool = True,
    periods_per_year: int = 252,
    risk_free: float = 0.0,
) -> float:
    """Annualized Sharpe ratio from return series."""
    returns = np.asarray(returns, dtype=float)
    if len(returns) < 2:
        return 0.0

    mean_r = np.mean(returns)
    std_r = np.std(returns, ddof=1)

    if std_r < 1e-12:
        return 0.0

    daily_rf = risk_free / periods_per_year
    sharpe = (mean_r - daily_rf) / std_r

    if annualize:
        sharpe *= np.sqrt(periods_per_year)

    return float(sharpe)


def compute_max_drawdown(equity_curve: np.ndarray) -> float:
    """Maximum drawdown from equity curve. Returns negative value."""
    equity = np.asarray(equity_curve, dtype=float)
    if len(equity) < 2:
        return 0.0

    peak = np.maximum.accumulate(equity)
    drawdown = (equity - peak) / peak
    return float(np.min(drawdown))


def compute_cagr(
    equity_curve: np.ndarray,
    periods_per_year: int = 252,
) -> float:
    """Compound Annual Growth Rate from equity curve."""
    equity = np.asarray(equity_curve, dtype=float)
    if len(equity) < 2 or equity[0] <= 0:
        return 0.0

    total_return = equity[-1] / equity[0]
    n_years = (len(equity) - 1) / periods_per_year

    if n_years <= 0 or total_return <= 0:
        return -1.0 if total_return < 1.0 else 0.0

    return float(total_return ** (1.0 / n_years) - 1)


def compute_hit_rate(returns: np.ndarray) -> float:
    """Fraction of periods with positive returns."""
    r = np.asarray(returns, dtype=float)
    if len(r) == 0:
        return 0.0
    return float(np.mean(r > 0))


def compute_volatility(
    returns: np.ndarray,
    annualize: bool = True,
    periods_per_year: int = 252,
) -> float:
    """Annualized volatility."""
    r = np.asarray(returns, dtype=float)
    if len(r) < 2:
        return 0.0
    vol = float(np.std(r, ddof=1))
    if annualize:
        vol *= np.sqrt(periods_per_year)
    return vol


def compute_portfolio_metrics(
    net_returns: np.ndarray,
    equity_curve: np.ndarray | None = None,
    gross_returns: np.ndarray | None = None,
    initial_capital: float = 100_000.0,
    periods_per_year: int = 252,
) -> PortfolioMetrics:
    """Compute full production metrics from portfolio simulation.

    Parameters
    ----------
    net_returns : array
        Returns after transaction costs.
    equity_curve : array or None
        Equity curve. Built from net_returns if not provided.
    gross_returns : array or None
        Returns before costs (for gross vs net comparison).
    initial_capital : float
        Starting capital.
    periods_per_year : int
        Annualization factor (252 for daily, 52 for weekly).

    Returns
    -------
    PortfolioMetrics with all computed statistics.
    """
    net_returns = np.asarray(net_returns, dtype=float)

    if equity_curve is None:
        equity = np.zeros(len(net_returns) + 1)
        equity[0] = initial_capital
        for t in range(len(net_returns)):
            equity[t + 1] = equity[t] * (1 + net_returns[t])
    else:
        equity = np.asarray(equity_curve, dtype=float)

    sharpe = compute_sharpe(net_returns, periods_per_year=periods_per_year)
    max_dd = compute_max_drawdown(equity)
    cagr = compute_cagr(equity, periods_per_year=periods_per_year)
    hit_rate = compute_hit_rate(net_returns)
    vol = compute_volatility(net_returns, periods_per_year=periods_per_year)
    total_return = float(equity[-1] / equity[0] - 1)

    calmar = cagr / abs(max_dd) if abs(max_dd) > 1e-8 else 0.0

    metrics = PortfolioMetrics(
        sharpe=sharpe,
        max_drawdown=max_dd,
        cagr=cagr,
        hit_rate=hit_rate,
        calmar=float(calmar),
        total_return=total_return,
        volatility=vol,
        n_periods=len(net_returns),
    )

    if gross_returns is not None:
        gross_returns = np.asarray(gross_returns, dtype=float)
        metrics.gross_sharpe = compute_sharpe(gross_returns, periods_per_year=periods_per_year)
        metrics.net_sharpe = sharpe
        gross_total = float(np.prod(1 + gross_returns) - 1)
        metrics.cost_drag_bps = (gross_total - total_return) * 10_000

    return metrics


def aggregate_fold_metrics(
    fold_metrics: list[PortfolioMetrics],
) -> dict[str, float]:
    """Aggregate metrics across walk-forward folds.

    Returns mean and std for each metric across folds.
    """
    if not fold_metrics:
        return {}

    keys = ["sharpe", "max_drawdown", "cagr", "hit_rate", "calmar",
            "total_return", "volatility", "cost_drag_bps"]

    result = {"n_folds": len(fold_metrics)}
    for key in keys:
        values = [getattr(m, key) for m in fold_metrics]
        result[f"mean_{key}"] = float(np.mean(values))
        result[f"std_{key}"] = float(np.std(values, ddof=1)) if len(values) > 1 else 0.0

    return result
