"""
Transaction cost modeling for realistic backtest evaluation.

Every backtest must account for costs to avoid inflated performance.
A strategy that is profitable gross but unprofitable net is not viable.

Components:
    - Commission: broker fee per trade (basis points of notional)
    - Slippage: execution price vs mid-price (bid-ask spread + market impact)
    - Market impact: price movement caused by our own order (square-root model)

References:
    - Almgren & Chriss (2001), "Optimal Execution of Portfolio Transactions"
    - Kissell (2013), "The Science of Algorithmic Trading and Portfolio Management"
    - Lopez de Prado, "Advances in Financial Machine Learning" (AFML)
"""

from __future__ import annotations

import numpy as np
import pandas as pd
from dataclasses import dataclass

from baselines import sharpe_from_returns


@dataclass
class TransactionCostModel:
    """Configurable transaction cost model.

    Parameters
    ----------
    commission_bps : float
        Commission in basis points of notional traded (e.g. 1.0 = 0.01%).
    bid_ask_spread_bps : float
        Average bid-ask spread in basis points (e.g. 1.0 = 0.01%).
    market_impact_coeff : float
        Market impact coefficient for square-root model.
        impact = coeff * sqrt(order_size / daily_volume).
    daily_volume : float
        Average daily trading volume (shares). Used for market impact.
    slippage_bps : float
        Additional fixed slippage in basis points (default 0).
    """

    commission_bps: float = 1.0
    bid_ask_spread_bps: float = 1.0
    market_impact_coeff: float = 0.1
    daily_volume: float = 1_000_000.0
    slippage_bps: float = 0.0

    def cost_per_trade(self, order_size: float) -> float:
        """Compute total transaction cost as fraction of notional.

        Parameters
        ----------
        order_size : float
            Number of shares traded.

        Returns
        -------
        float : Total cost as fraction of notional (e.g. 0.0005 = 5bps).
        """
        commission = self.commission_bps / 10_000
        spread = self.bid_ask_spread_bps / 10_000
        slippage = self.slippage_bps / 10_000

        # Square-root market impact model (Almgren-Chriss)
        participation = order_size / max(self.daily_volume, 1.0)
        impact = self.market_impact_coeff * np.sqrt(participation)

        return commission + spread + slippage + impact

    def apply_to_returns(
        self,
        strategy_returns: np.ndarray | pd.Series,
        trades: np.ndarray | pd.Series,
        order_size: float = 100.0,
    ) -> np.ndarray:
        """Apply transaction costs to strategy returns.

        Each trade incurs a round-trip cost (buy + sell), deducted from returns.

        Parameters
        ----------
        strategy_returns : array-like
            Strategy returns series (gross of costs).
        trades : array-like
            Binary array: 1 = trade occurred (position change), 0 = hold.
        order_size : float
            Number of shares per trade.

        Returns
        -------
        np.ndarray : Net returns after transaction costs.
        """
        strategy_returns = np.asarray(strategy_returns, dtype=float)
        trades = np.asarray(trades, dtype=float)

        cost_frac = self.cost_per_trade(order_size)
        # Round-trip cost: each position change requires buy AND sell
        trade_costs = trades * 2 * cost_frac

        net_returns = strategy_returns - trade_costs
        return net_returns


def compare_gross_vs_net(
    gross_returns: np.ndarray | pd.Series,
    positions: np.ndarray | pd.Series,
    cost_model: TransactionCostModel | None = None,
    order_size: float = 100.0,
) -> dict:
    """Compare gross vs net strategy performance.

    Parameters
    ----------
    gross_returns : array-like
        Strategy returns before transaction costs.
    positions : array-like
        Position sizes or signals. Trade occurs when position changes.
    cost_model : TransactionCostModel or None
        Cost model. Default: institutional equity model (1bp commission, 1bp spread).
    order_size : float
        Number of shares per trade.

    Returns
    -------
    dict with keys: gross_sharpe, net_sharpe, total_costs_bps,
                    n_trades, cost_drag_bps, net_total_return.
    """
    if cost_model is None:
        cost_model = TransactionCostModel()

    gross_returns = np.asarray(gross_returns, dtype=float)
    positions = np.asarray(positions, dtype=float)

    n = len(gross_returns)
    gross_returns = gross_returns[:n]
    positions = positions[:n]

    # Detect trades: position change from one period to next
    pos_changes = np.diff(positions, prepend=positions[0])
    trades = (pos_changes != 0).astype(float)

    net_returns = cost_model.apply_to_returns(gross_returns, trades, order_size)

    gross_sharpe = sharpe_from_returns(gross_returns)
    net_sharpe = sharpe_from_returns(net_returns)

    total_costs = np.sum(trades) * 2 * cost_model.cost_per_trade(order_size)
    n_trades = int(np.sum(trades))

    gross_total = float(np.prod(1 + gross_returns) - 1)
    net_total = float(np.prod(1 + net_returns) - 1)

    cost_drag = gross_total - net_total

    return {
        "gross_sharpe": gross_sharpe,
        "net_sharpe": net_sharpe,
        "gross_total_return": gross_total,
        "net_total_return": net_total,
        "total_costs_bps": total_costs * 10_000,
        "n_trades": n_trades,
        "cost_drag_bps": cost_drag * 10_000,
        "trade_frequency": n_trades / max(n, 1),
    }
