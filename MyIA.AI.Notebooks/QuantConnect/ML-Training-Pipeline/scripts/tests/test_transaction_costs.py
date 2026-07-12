"""Tests for transaction_costs.py — transaction cost modeling."""

from __future__ import annotations

import numpy as np
import pandas as pd
import pytest

from transaction_costs import (
    TransactionCostModel,
    compare_gross_vs_net,
)
from baselines import sharpe_from_returns


class TestTransactionCostModel:
    """TransactionCostModel unit tests."""

    def test_default_cost_positive(self):
        model = TransactionCostModel()
        cost = model.cost_per_trade(order_size=100)
        assert cost > 0

    def test_commission_only(self):
        model = TransactionCostModel(
            commission_bps=5.0,
            bid_ask_spread_bps=0.0,
            market_impact_coeff=0.0,
            slippage_bps=0.0,
        )
        cost = model.cost_per_trade(order_size=100)
        assert cost == pytest.approx(5.0 / 10_000)

    def test_spread_only(self):
        model = TransactionCostModel(
            commission_bps=0.0,
            bid_ask_spread_bps=3.0,
            market_impact_coeff=0.0,
            slippage_bps=0.0,
        )
        cost = model.cost_per_trade(order_size=100)
        assert cost == pytest.approx(3.0 / 10_000)

    def test_market_impact_increases_with_size(self):
        model = TransactionCostModel(
            commission_bps=0.0,
            bid_ask_spread_bps=0.0,
            market_impact_coeff=0.1,
            daily_volume=10_000,
        )
        cost_small = model.cost_per_trade(order_size=10)
        cost_large = model.cost_per_trade(order_size=1000)
        assert cost_large > cost_small

    def test_zero_volume_handled(self):
        """Zero daily volume should not crash."""
        model = TransactionCostModel(daily_volume=0.0)
        cost = model.cost_per_trade(order_size=100)
        assert np.isfinite(cost)

    def test_apply_to_returns_reduces_performance(self):
        model = TransactionCostModel(commission_bps=5.0)
        gross = np.array([0.01, -0.005, 0.02, 0.005, -0.01])
        trades = np.array([1, 0, 1, 0, 1])
        net = model.apply_to_returns(gross, trades, order_size=100)
        assert net.sum() < gross.sum()

    def test_no_trades_no_cost(self):
        model = TransactionCostModel(commission_bps=5.0)
        gross = np.array([0.01, 0.02, 0.01])
        trades = np.array([0, 0, 0])
        net = model.apply_to_returns(gross, trades, order_size=100)
        np.testing.assert_array_equal(net, gross)

    def test_round_trip_cost(self):
        """Each trade incurs round-trip cost (buy + sell), deducted twice."""
        model = TransactionCostModel(
            commission_bps=2.0,
            bid_ask_spread_bps=2.0,
            market_impact_coeff=0.0,
            slippage_bps=0.0,
        )
        gross = np.array([0.0, 0.0, 0.0])
        trades = np.array([1.0, 0.0, 1.0])
        net = model.apply_to_returns(gross, trades, order_size=100)
        expected_cost = 2 * 4.0 / 10_000  # round-trip: 2x (commission + spread)
        assert net[0] == pytest.approx(-expected_cost)
        assert net[1] == pytest.approx(0.0)
        assert net[2] == pytest.approx(-expected_cost)


class TestCompareGrossVsNet:
    """compare_gross_vs_net integration tests."""

    @pytest.fixture
    def sample_strategy(self):
        """Generate a simple long/short strategy."""
        rng = np.random.default_rng(42)
        n = 252
        gross = rng.normal(0.001, 0.01, n)
        positions = np.ones(n)
        # Flip positions occasionally
        flip_indices = rng.choice(range(10, n), size=20, replace=False)
        for idx in flip_indices:
            positions[idx:] *= -1
        return gross, positions

    def test_net_sharpe_lower(self, sample_strategy):
        gross, positions = sample_strategy
        result = compare_gross_vs_net(gross, positions)
        assert result["net_sharpe"] < result["gross_sharpe"]

    def test_net_return_lower(self, sample_strategy):
        gross, positions = sample_strategy
        result = compare_gross_vs_net(gross, positions)
        assert result["net_total_return"] < result["gross_total_return"]

    def test_trade_count_positive(self, sample_strategy):
        gross, positions = sample_strategy
        result = compare_gross_vs_net(gross, positions)
        assert result["n_trades"] > 0

    def test_cost_drag_positive(self, sample_strategy):
        gross, positions = sample_strategy
        result = compare_gross_vs_net(gross, positions)
        assert result["cost_drag_bps"] > 0

    def test_frequency_between_zero_one(self, sample_strategy):
        gross, positions = sample_strategy
        result = compare_gross_vs_net(gross, positions)
        assert 0 < result["trade_frequency"] < 1

    def test_default_model(self):
        """Without explicit model, default institutional model is used."""
        gross = np.array([0.01, -0.005, 0.02])
        positions = np.array([1, -1, 1])
        result = compare_gross_vs_net(gross, positions)
        assert "gross_sharpe" in result
        assert "net_sharpe" in result

    def test_custom_model(self):
        """High-cost model should have larger drag."""
        gross = np.array([0.01, -0.005, 0.02, 0.01, -0.01])
        positions = np.array([1, -1, 1, -1, 1])

        cheap = TransactionCostModel(commission_bps=0.5, bid_ask_spread_bps=0.5)
        expensive = TransactionCostModel(commission_bps=10.0, bid_ask_spread_bps=10.0)

        r_cheap = compare_gross_vs_net(gross, positions, cost_model=cheap)
        r_expensive = compare_gross_vs_net(gross, positions, cost_model=expensive)

        assert r_expensive["cost_drag_bps"] > r_cheap["cost_drag_bps"]


class TestSharpeFromArray:
    """Internal Sharpe helper tests."""

    def test_empty(self):
        assert sharpe_from_returns(np.array([])) == 0.0

    def test_constant(self):
        assert sharpe_from_returns(np.full(100, 0.01)) == 0.0

    def test_positive(self):
        rng = np.random.default_rng(42)
        r = rng.normal(0.001, 0.01, 252)
        assert sharpe_from_returns(r) > 0

    def test_negative(self):
        rng = np.random.default_rng(99)
        r = rng.normal(-0.005, 0.01, 252)
        assert sharpe_from_returns(r) < 0

    def test_no_annualize(self):
        rng = np.random.default_rng(42)
        r = rng.normal(0.001, 0.01, 252)
        s_ann = sharpe_from_returns(r, annualize=True)
        s_raw = sharpe_from_returns(r, annualize=False)
        assert abs(s_ann) > abs(s_raw)
