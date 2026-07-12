"""Portfolio simulation with position tracking and transaction costs.

Integrates with WalkForwardBacktest to convert model predictions into
portfolio-level P&L. Each fold produces equity curves and trade logs
suitable for production metrics (Sharpe, MaxDD, CAGR, HitRate).
"""

from __future__ import annotations

from dataclasses import dataclass, field

import numpy as np
import pandas as pd

from transaction_costs import TransactionCostModel


@dataclass
class PortfolioState:
    """State snapshot for a single period."""
    position: int  # -1, 0, +1
    equity: float
    cash: float
    trade_cost: float


@dataclass
class PortfolioResult:
    """Result of portfolio simulation over a walk-forward fold."""
    positions: np.ndarray
    equity_curve: np.ndarray
    gross_returns: np.ndarray
    net_returns: np.ndarray
    trade_costs: np.ndarray
    n_trades: int
    initial_capital: float
    final_equity: float

    @property
    def total_return(self) -> float:
        return float(self.final_equity / self.initial_capital - 1)

    @property
    def total_cost_bps(self) -> float:
        if len(self.trade_costs) == 0:
            return 0.0
        return float(np.sum(self.trade_costs) / self.initial_capital * 10_000)

    def to_dict(self) -> dict:
        return {
            "n_trades": self.n_trades,
            "initial_capital": self.initial_capital,
            "final_equity": round(self.final_equity, 2),
            "total_return": round(self.total_return, 6),
            "total_cost_bps": round(self.total_cost_bps, 2),
        }


# Preset cost models for common asset classes
SPY_COST_MODEL = TransactionCostModel(
    commission_bps=0.5,
    bid_ask_spread_bps=0.5,
    market_impact_coeff=0.05,
    daily_volume=50_000_000,
    slippage_bps=0.0,
)

CRYPTO_COST_MODEL = TransactionCostModel(
    commission_bps=5.0,
    bid_ask_spread_bps=2.0,
    market_impact_coeff=0.1,
    daily_volume=5_000_000,
    slippage_bps=3.0,
)

COST_PRESETS = {
    "spy": SPY_COST_MODEL,
    "equity": SPY_COST_MODEL,
    "crypto": CRYPTO_COST_MODEL,
    "default": TransactionCostModel(),
}


def simulate_fold(
    y_true: np.ndarray,
    y_pred: np.ndarray,
    prices: np.ndarray | None = None,
    returns: np.ndarray | None = None,
    cost_model: TransactionCostModel | str = "spy",
    initial_capital: float = 100_000.0,
    order_size: float = 100.0,
) -> PortfolioResult:
    """Simulate portfolio P&L for a single walk-forward fold.

    Converts classification predictions (0/1 or -1/+1) into positions,
    applies transaction costs on position changes, and tracks equity.

    Parameters
    ----------
    y_true : array, shape (T,)
        True labels (0=down, 1=up or -1/+1).
    y_pred : array, shape (T,)
        Predicted labels (same encoding as y_true).
    prices : array or None
        Price series for the fold. Used to compute returns if not provided.
    returns : array or None
        Pre-computed returns. If None, derived from prices.
    cost_model : TransactionCostModel or str
        Cost model or preset name ("spy", "crypto", "default").
    initial_capital : float
        Starting capital.
    order_size : float
        Shares per trade (for market impact).

    Returns
    -------
    PortfolioResult with equity curve, returns, and trade statistics.
    """
    y_pred = np.asarray(y_pred)
    y_true = np.asarray(y_true)
    n = len(y_pred)

    if isinstance(cost_model, str):
        cost_model = COST_PRESETS.get(cost_model, TransactionCostModel())

    # Compute returns
    if returns is not None:
        asset_returns = np.asarray(returns, dtype=float)
    elif prices is not None:
        prices = np.asarray(prices, dtype=float)
        asset_returns = np.diff(prices, prepend=prices[0]) / prices
    else:
        # Use sign-based proxy: +1 if predicted up, -1 if down
        asset_returns = np.where(y_true > 0, 1.0, -1.0) * 0.01

    asset_returns = asset_returns[:n]

    # Convert predictions to positions: pred=1 -> long (+1), pred=0/-1 -> short (-1)
    # Binary classification (0/1): 1=up -> long, 0=down -> short
    positions = np.where(y_pred >= 0.5, 1.0, -1.0)
    # Handle (-1/+1) encoding
    if np.min(y_pred) < 0:
        positions = np.where(y_pred > 0, 1.0, -1.0)

    # Strategy gross returns: position * asset return
    gross_returns = positions * asset_returns

    # Detect position changes (trades)
    pos_changes = np.diff(positions, prepend=0.0)
    trades = (pos_changes != 0).astype(float)

    # Apply transaction costs
    trade_costs = trades * 2 * cost_model.cost_per_trade(order_size)
    net_returns = gross_returns - trade_costs

    # Build equity curve
    equity = np.zeros(n + 1)
    equity[0] = initial_capital
    for t in range(n):
        equity[t + 1] = equity[t] * (1 + net_returns[t])

    return PortfolioResult(
        positions=positions,
        equity_curve=equity,
        gross_returns=gross_returns,
        net_returns=net_returns,
        trade_costs=trade_costs,
        n_trades=int(np.sum(trades)),
        initial_capital=initial_capital,
        final_equity=float(equity[-1]),
    )


def simulate_walk_forward(
    fold_predictions: list[tuple[np.ndarray, np.ndarray]],
    prices_per_fold: list[np.ndarray] | None = None,
    returns_per_fold: list[np.ndarray] | None = None,
    cost_model: TransactionCostModel | str = "spy",
    initial_capital: float = 100_000.0,
) -> list[PortfolioResult]:
    """Simulate portfolio across all walk-forward folds.

    Parameters
    ----------
    fold_predictions : list of (y_true, y_pred) tuples per fold.
    prices_per_fold : list of price arrays per fold (optional).
    returns_per_fold : list of return arrays per fold (optional).
    cost_model : cost model or preset name.
    initial_capital : starting capital.

    Returns
    -------
    list of PortfolioResult, one per fold.
    """
    results = []
    for i, (y_true, y_pred) in enumerate(fold_predictions):
        prices = prices_per_fold[i] if prices_per_fold else None
        returns = returns_per_fold[i] if returns_per_fold else None
        result = simulate_fold(
            y_true, y_pred,
            prices=prices, returns=returns,
            cost_model=cost_model,
            initial_capital=initial_capital,
        )
        results.append(result)
    return results
