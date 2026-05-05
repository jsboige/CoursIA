"""Tests for transaction_costs.py -- TransactionCostModel and cost evaluation."""

import sys
from pathlib import Path

import numpy as np
import pandas as pd
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))

from transaction_costs import TransactionCostModel, compare_gross_vs_net


class TestTransactionCostModel:
    def test_default_costs(self):
        model = TransactionCostModel()
        cost = model.cost_per_trade(order_size=100)
        assert cost > 0
        # Default: 1bp commission + 1bp spread + market impact
        assert cost < 0.01  # Less than 1% per trade

    def test_zero_impact(self):
        model = TransactionCostModel(
            commission_bps=0, bid_ask_spread_bps=0,
            slippage_bps=0, market_impact_coeff=0,
        )
        cost = model.cost_per_trade(order_size=100)
        assert cost == 0.0

    def test_commission_only(self):
        model = TransactionCostModel(
            commission_bps=10, bid_ask_spread_bps=0,
            slippage_bps=0, market_impact_coeff=0,
        )
        cost = model.cost_per_trade(order_size=100)
        assert abs(cost - 10 / 10_000) < 1e-10

    def test_larger_order_more_impact(self):
        model = TransactionCostModel(market_impact_coeff=0.1)
        cost_small = model.cost_per_trade(order_size=10)
        cost_large = model.cost_per_trade(order_size=10000)
        assert cost_large > cost_small

    def test_apply_to_returns(self):
        model = TransactionCostModel(
            commission_bps=10, bid_ask_spread_bps=0,
            slippage_bps=0, market_impact_coeff=0,
        )
        returns = np.array([0.01, 0.02, -0.01])
        trades = np.array([1, 0, 1])
        net = model.apply_to_returns(returns, trades)
        assert net[0] < returns[0]  # Trade cost deducted
        assert net[1] == returns[1]  # No trade, no cost
        assert net[2] < returns[2]  # Trade cost deducted

    def test_apply_to_returns_series(self):
        model = TransactionCostModel()
        returns = pd.Series([0.01, 0.02, -0.01])
        trades = pd.Series([1, 0, 1])
        net = model.apply_to_returns(returns, trades)
        assert isinstance(net, np.ndarray)
        assert len(net) == 3


class TestCompareGrossVsNet:
    def test_basic_output(self):
        gross = np.array([0.01, -0.005, 0.02, -0.01, 0.005])
        positions = np.array([1, 1, -1, 1, 1])
        result = compare_gross_vs_net(gross, positions)
        assert "gross_sharpe" in result
        assert "net_sharpe" in result
        assert "n_trades" in result
        assert "cost_drag_bps" in result

    def test_no_trades_no_cost(self):
        returns = np.array([0.01, 0.02, -0.01] * 10)
        positions = np.ones(30)  # Always long, no position change
        result = compare_gross_vs_net(returns, positions)
        assert result["n_trades"] == 0
        assert result["cost_drag_bps"] == 0

    def test_net_lower_than_gross(self):
        np.random.seed(42)
        gross = np.random.randn(100) * 0.01
        positions = np.random.choice([-1, 0, 1], size=100).astype(float)
        result = compare_gross_vs_net(gross, positions)
        if result["n_trades"] > 0:
            assert result["net_total_return"] <= result["gross_total_return"]

    def test_custom_model(self):
        model = TransactionCostModel(commission_bps=50)
        returns = np.array([0.01, -0.005, 0.02])
        positions = np.array([1, -1, 1])
        result = compare_gross_vs_net(returns, positions, cost_model=model)
        assert result["n_trades"] > 0
