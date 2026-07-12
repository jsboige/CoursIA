"""Standardized backtest plotting functions.

Shared helper module for QC-Py notebooks.
Provides consistent visualization of backtest results.
"""

import numpy as np
import pandas as pd
import matplotlib.pyplot as plt
from typing import Optional


def plot_backtest_results(
    results_df: pd.DataFrame,
    benchmark: Optional[pd.Series] = None,
    title: str = "Backtest Results",
) -> None:
    """Plot equity curve, drawdown, and daily returns.

    Args:
        results_df: DataFrame with columns: equity, daily_returns, drawdown.
        benchmark: Optional benchmark equity series.
        title: Plot title.
    """
    fig, axes = plt.subplots(3, 1, figsize=(14, 10), sharex=True)

    ax1 = axes[0]
    ax1.plot(results_df.index, results_df["equity"], label="Strategy", linewidth=1.5)
    if benchmark is not None:
        bench_aligned = benchmark.reindex(results_df.index).dropna()
        if len(bench_aligned) > 0:
            ax1.plot(bench_aligned.index, bench_aligned, label="Benchmark",
                     linewidth=1, alpha=0.7, linestyle="--")
    ax1.set_title(title)
    ax1.set_ylabel("Equity")
    ax1.legend()
    ax1.grid(True, alpha=0.3)

    ax2 = axes[1]
    ax2.fill_between(results_df.index, results_df["drawdown"], 0,
                     color="red", alpha=0.3)
    ax2.set_ylabel("Drawdown (%)")
    ax2.grid(True, alpha=0.3)

    ax3 = axes[2]
    ax3.bar(results_df.index, results_df["daily_returns"],
            width=1, color="steelblue", alpha=0.6)
    ax3.set_ylabel("Daily Returns")
    ax3.set_xlabel("Date")
    ax3.grid(True, alpha=0.3)

    plt.tight_layout()
    plt.show()


def plot_returns_distribution(
    returns: pd.Series,
    title: str = "Returns Distribution",
) -> None:
    """Plot histogram of returns with normal overlay.

    Args:
        returns: Series of daily returns.
        title: Plot title.
    """
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 5))

    ax1.hist(returns.dropna(), bins=50, density=True, color="steelblue",
             edgecolor="black", alpha=0.7)
    mu, sigma = returns.mean(), returns.std()
    x = np.linspace(returns.min(), returns.max(), 100)
    ax1.plot(x, 1 / (sigma * np.sqrt(2 * np.pi)) *
             np.exp(-0.5 * ((x - mu) / sigma) ** 2),
             "r--", linewidth=2, label=f"Normal (mu={mu:.4f}, sigma={sigma:.4f})")
    ax1.set_title(title)
    ax1.set_xlabel("Return")
    ax1.set_ylabel("Density")
    ax1.legend()
    ax1.grid(True, alpha=0.3)

    from scipy import stats
    stats.probplot(returns.dropna(), dist="norm", plot=ax2)
    ax2.set_title("Q-Q Plot")
    ax2.grid(True, alpha=0.3)

    plt.tight_layout()
    plt.show()
