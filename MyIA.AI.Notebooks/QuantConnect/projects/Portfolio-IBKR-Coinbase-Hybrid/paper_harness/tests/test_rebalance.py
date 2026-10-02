import math

import numpy as np
import pandas as pd
import pytest

from paper_harness.rebalance import inverse_vol_weights, plan_orders, realized_vol


def _series(daily_returns, start=100.0):
    closes = [start]
    for r in daily_returns:
        closes.append(closes[-1] * (1.0 + r))
    return closes


def test_realized_vol_needs_lookback_plus_one_closes():
    assert realized_vol([100.0] * 21, lookback=21) is None
    assert realized_vol([100.0] * 22, lookback=21) == 0.0


def test_realized_vol_rejects_non_positive_prices():
    closes = _series([0.01, -0.01] * 11)
    closes[5] = 0.0
    assert realized_vol(closes) is None


def test_realized_vol_uses_only_the_last_window():
    calm = _series([0.001] * 100)
    wild = _series([0.05, -0.05] * 50)
    assert realized_vol(wild[:50] + calm[-22:]) == pytest.approx(realized_vol(calm), abs=1e-12)


def test_weights_match_the_pandas_convention_of_the_selection_backtest():
    rng = np.random.default_rng(7)
    vols = {"SPY": 0.012, "QQQ": 0.016, "IEF": 0.004, "GLD": 0.009}
    closes = {s: list(100 * np.cumprod(1 + rng.normal(0, v, 300))) for s, v in vols.items()}
    expected = {}
    for s, c in closes.items():
        r = pd.Series(c).pct_change().iloc[-21:]
        expected[s] = min(0.025 / (r.std() * math.sqrt(252)), 0.5)
    total = sum(expected.values())
    if total > 1:
        expected = {s: w / total for s, w in expected.items()}
    got = inverse_vol_weights(closes, budget_per_line=0.025)
    assert got.keys() == expected.keys()
    for s in expected:
        assert got[s] == pytest.approx(expected[s], rel=1e-10)


def test_weights_are_capped_per_line_and_scaled_to_one():
    calm = _series([0.0005, -0.0005] * 15)  # very low vol: capped at max_weight
    w = inverse_vol_weights({"A": calm, "B": calm, "C": calm}, budget_per_line=0.025, max_weight=0.5)
    assert sum(w.values()) == pytest.approx(1.0)
    assert all(v == pytest.approx(1 / 3) for v in w.values())


def test_weights_leave_unmeasurable_lines_in_cash():
    w = inverse_vol_weights({"A": _series([0.01, -0.01] * 15), "B": [100.0] * 5}, budget_per_line=0.025)
    assert set(w) == {"A"}
    assert w["A"] < 1.0


def test_plan_rounds_targets_down_to_whole_shares():
    orders = plan_orders({"A": 0.5}, {}, {"A": 30.0}, equity=1000.0)
    assert [(o.symbol, o.quantity) for o in orders] == [("A", 16)]  # 500 / 30 = 16.7


def test_plan_lists_sells_before_buys_and_closes_dropped_lines():
    orders = plan_orders(
        {"A": 0.6}, {"A": 10, "B": 5}, {"A": 50.0, "B": 20.0}, equity=1100.0
    )
    assert [(o.symbol, o.side, o.quantity) for o in orders] == [("B", "SELL", -5), ("A", "BUY", 3)]


def test_plan_skips_trades_inside_the_band():
    # Target 13 shares of A, hold 12: one share = 1 % of equity, under a 3 % band.
    assert plan_orders({"A": 0.13}, {"A": 12}, {"A": 10.0}, equity=1000.0, band=0.03) == []
    # Holding 10 instead: three shares = 3 %, at the band, so the trade goes through.
    orders = plan_orders({"A": 0.13}, {"A": 10}, {"A": 10.0}, equity=1000.0, band=0.03)
    assert [o.quantity for o in orders] == [3]


def test_plan_skips_orders_below_the_minimum_notional():
    assert plan_orders({"A": 0.02}, {}, {"A": 5.0}, equity=1000.0, min_notional=25.0) == []


def test_plan_keeps_a_cash_reserve_for_fees():
    orders = plan_orders({"A": 1.0}, {}, {"A": 10.0}, equity=1000.0, cash_reserve=0.01)
    assert orders[0].quantity == 99
    assert orders[0].notional <= 1000.0 * 0.99


def test_plan_refuses_to_plan_without_a_price():
    with pytest.raises(ValueError, match="no usable price for B"):
        plan_orders({"A": 0.5}, {"B": 3}, {"A": 10.0}, equity=1000.0)
