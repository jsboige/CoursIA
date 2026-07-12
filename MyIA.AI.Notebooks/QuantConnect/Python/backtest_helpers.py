"""Standardized backtest performance metrics and formatting.

Shared helper module for QC-Py notebooks (QC-Py-12, QC-Py-15, etc.).
Provides consistent metric calculation across all backtest analyses.
"""

import numpy as np
import pandas as pd
from typing import Dict, Optional, Union


def calculate_metrics(
    equity: pd.Series,
    benchmark: Optional[pd.Series] = None,
    risk_free_rate: float = 0.02,
) -> Dict[str, float]:
    """Compute standard backtest performance metrics from an equity curve.

    Args:
        equity: Equity curve (ascending dates).
        benchmark: Optional benchmark equity curve for alpha/beta calculation.
        risk_free_rate: Annual risk-free rate (default 2%).

    Returns:
        Dictionary with keys: total_return, cagr, annual_vol, sharpe,
        sortino, max_drawdown, calmar, win_rate, num_trades.
    """
    if len(equity) < 2:
        return {k: 0.0 for k in [
            "total_return", "cagr", "annual_vol", "sharpe", "sortino",
            "max_drawdown", "calmar", "win_rate", "num_trades",
        ]}

    returns = equity.pct_change().dropna()
    total_days = (equity.index[-1] - equity.index[0]).days
    years = max(total_days / 365.25, 1e-6)

    total_return = (equity.iloc[-1] / equity.iloc[0]) - 1
    cagr = (1 + total_return) ** (1 / years) - 1
    annual_vol = returns.std() * np.sqrt(252)
    sharpe = ((cagr - risk_free_rate) / annual_vol) if annual_vol > 0 else 0.0

    downside = returns[returns < 0]
    downside_vol = downside.std() * np.sqrt(252) if len(downside) > 0 else annual_vol
    sortino = ((cagr - risk_free_rate) / downside_vol) if downside_vol > 0 else 0.0

    running_max = equity.cummax()
    drawdown = (equity - running_max) / running_max
    max_drawdown = drawdown.min()
    calmar = (cagr / abs(max_drawdown)) if max_drawdown != 0 else 0.0

    win_rate = (returns > 0).mean()

    metrics = {
        "total_return": total_return,
        "cagr": cagr,
        "annual_vol": annual_vol,
        "sharpe": sharpe,
        "sortino": sortino,
        "max_drawdown": max_drawdown,
        "calmar": calmar,
        "win_rate": win_rate,
        "num_trades": len(returns),
    }

    if benchmark is not None and len(benchmark) >= len(equity):
        bench_returns = benchmark.pct_change().dropna()
        bench_returns = bench_returns.reindex(returns.index).dropna()
        aligned_returns = returns.reindex(bench_returns.index).dropna()
        if len(aligned_returns) > 1 and bench_returns.std() > 0:
            beta = aligned_returns.cov(bench_returns) / bench_returns.var()
            alpha = cagr - (risk_free_rate + beta * (
                ((1 + benchmark.iloc[-1] / benchmark.iloc[0]) ** (1 / years) - 1)
                - risk_free_rate
            ))
            metrics["alpha"] = alpha
            metrics["beta"] = beta

    return metrics


def format_backtest_summary(
    metrics: Dict[str, float],
    strategy_name: str = "Strategy",
) -> str:
    """Format metrics dictionary into a readable summary string.

    Args:
        metrics: Output of calculate_metrics().
        strategy_name: Display name for the strategy.

    Returns:
        Formatted multi-line string.
    """
    pct = lambda v: f"{v * 100:.2f}%"
    dec = lambda v: f"{v:.4f}"

    lines = [
        "=" * 60,
        f"  Backtest Summary: {strategy_name}",
        "=" * 60,
        f"  Total Return:      {pct(metrics.get('total_return', 0))}",
        f"  CAGR:              {pct(metrics.get('cagr', 0))}",
        f"  Annual Volatility: {pct(metrics.get('annual_vol', 0))}",
        f"  Sharpe Ratio:      {dec(metrics.get('sharpe', 0))}",
        f"  Sortino Ratio:     {dec(metrics.get('sortino', 0))}",
        f"  Max Drawdown:      {pct(metrics.get('max_drawdown', 0))}",
        f"  Calmar Ratio:      {dec(metrics.get('calmar', 0))}",
        f"  Win Rate:          {pct(metrics.get('win_rate', 0))}",
        f"  Num Periods:       {int(metrics.get('num_trades', 0))}",
    ]
    if "alpha" in metrics:
        lines.append(f"  Alpha:             {dec(metrics['alpha'])}")
    if "beta" in metrics:
        lines.append(f"  Beta:              {dec(metrics['beta'])}")
    lines.append("=" * 60)
    return "\n".join(lines)


def compare_strategies(
    strategies: Dict[str, pd.Series],
    risk_free_rate: float = 0.02,
) -> pd.DataFrame:
    """Compare multiple strategy equity curves side-by-side.

    Args:
        strategies: Mapping of strategy name -> equity Series.
        risk_free_rate: Annual risk-free rate.

    Returns:
        DataFrame with one row per strategy and metrics as columns.
    """
    rows = []
    for name, equity in strategies.items():
        m = calculate_metrics(equity, risk_free_rate=risk_free_rate)
        rows.append({
            "Strategy": name,
            "Total Return": m["total_return"],
            "CAGR": m["cagr"],
            "Sharpe": m["sharpe"],
            "Sortino": m["sortino"],
            "Max DD": m["max_drawdown"],
            "Calmar": m["calmar"],
            "Win Rate": m["win_rate"],
        })
    return pd.DataFrame(rows).set_index("Strategy")
