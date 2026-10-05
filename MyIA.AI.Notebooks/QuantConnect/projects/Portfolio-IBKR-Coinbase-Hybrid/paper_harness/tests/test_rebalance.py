import math

import numpy as np
import pandas as pd
import pytest

from paper_harness.rebalance import fit_to_cash, inverse_vol_weights, plan_orders, realized_vol


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


def test_a_zero_target_sells_the_whole_holding_whatever_its_size():
    # 1 share = 1 % of equity: a rebalance would skip it, an exit must not.
    orders = plan_orders({"A": 0.0}, {"A": 1}, {"A": 100.0}, 10_000.0, band=0.03, min_notional=500.0)
    assert [(o.symbol, o.quantity) for o in orders] == [("A", -1)]
    # A line held but absent from the targets is an exit too.
    orders = plan_orders({}, {"B": 2}, {"B": 10.0}, 10_000.0, band=0.03)
    assert [(o.symbol, o.quantity) for o in orders] == [("B", -2)]


def test_plan_keeps_a_cash_reserve_for_fees():
    orders = plan_orders({"A": 1.0}, {}, {"A": 10.0}, equity=1000.0, cash_reserve=0.01)
    assert orders[0].quantity == 99
    assert orders[0].notional <= 1000.0 * 0.99


def test_plan_refuses_to_plan_without_a_price():
    with pytest.raises(ValueError, match="no usable price for B"):
        plan_orders({"A": 0.5}, {"B": 3}, {"A": 10.0}, equity=1000.0)


# -- cash feasibility (#19113) ------------------------------------------------

# A is held above its target by less than the 5 % band: its sell is skipped,
# while C, absent, is bought. Without the cash, the plan buys more than it has.
OVER = dict(target_weights={"A": 0.45, "B": 0.25, "C": 0.30}, positions={"A": 48, "B": 48},
            prices={"A": 100.0, "B": 100.0, "C": 100.0}, equity=10_000.0)
OVER_CASH = 10_000.0 - 96 * 100.0  # 400


def _spend(orders):
    buys = sum(o.notional for o in orders if o.quantity > 0)
    sells = sum(o.notional for o in orders if o.quantity < 0)
    return buys - sells


def test_the_band_alone_lets_the_buys_exceed_the_cash():
    orders = plan_orders(**OVER, band=0.05, cash_reserve=0.002)
    assert [(o.symbol, o.quantity) for o in orders] == [("B", -24), ("C", 29)]
    assert _spend(orders) == pytest.approx(500.0)  # 100 more than the 400 of cash


def test_cash_releases_the_skipped_sell_before_touching_the_buys():
    orders = plan_orders(**OVER, band=0.05, cash_reserve=0.002, cash=OVER_CASH)
    assert [(o.symbol, o.quantity) for o in orders] == [("A", -4), ("B", -24), ("C", 29)]
    assert _spend(orders) <= OVER_CASH - 0.002 * 10_000.0


def test_cash_scales_the_buys_when_no_sell_is_released():
    orders = plan_orders(**OVER, band=0.05, cash_reserve=0.002, cash=OVER_CASH,
                         release_skipped_sells=False)
    # 2 400 of sells + 400 of cash - 20 of reserve = 2 780: 27 shares of C
    assert [(o.symbol, o.quantity) for o in orders] == [("B", -24), ("C", 27)]
    assert _spend(orders) <= OVER_CASH - 20.0


def test_a_plan_that_fits_is_left_unchanged_by_the_cash():
    kw = dict(target_weights={"A": 0.5, "B": 0.3}, positions={"A": 10}, prices={"A": 50.0, "B": 20.0},
              equity=1_000.0, band=0.03, cash_reserve=0.01)
    assert plan_orders(**kw, cash=500.0) == plan_orders(**kw)


def test_a_sell_under_the_minimum_notional_is_not_released():
    # A's skipped sell is worth 400, under a 500 minimum: only the scaling is left.
    orders = plan_orders(**OVER, band=0.05, min_notional=500.0, cash_reserve=0.002, cash=OVER_CASH)
    assert [o.symbol for o in orders if o.quantity < 0] == ["B"]
    assert _spend(orders) <= OVER_CASH - 20.0


def test_scaled_buys_are_rounded_down_and_tiny_ones_dropped():
    from paper_harness.rebalance import OrderIntent
    buys = [OrderIntent("X", 10, 100.0, 0.0, 0.1), OrderIntent("Y", 3, 30.0, 0.0, 0.01)]
    # 1 090 of buys for 545 available: factor 0.5 -> X 5, Y 1 (45 < 50, dropped)
    kept = fit_to_cash(buys, available=545.0, min_notional=50.0)
    assert [(o.symbol, o.quantity) for o in kept] == [("X", 5)]


def test_no_cash_left_keeps_the_sells_and_drops_every_buy():
    orders = plan_orders(**OVER, band=0.0, cash_reserve=0.002, cash=-3_000.0)
    assert all(o.quantity < 0 for o in orders)
