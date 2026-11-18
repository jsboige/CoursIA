"""Tests for plan_cash_feasibility.py (#19113) on synthetic series."""

from __future__ import annotations

import math

import numpy as np
import pandas as pd
import pytest

import plan_cash_feasibility as pcf


@pytest.fixture(scope="module")
def harness():
    return pcf.load_harness()


def _panel(n: int = 400, seed: int = 0) -> pd.DataFrame:
    rng = np.random.default_rng(seed)
    days = pd.bdate_range("2020-01-01", periods=n)
    vols = {"SPY": 0.18, "QQQ": 0.24, "IEF": 0.06, "GLD": 0.15}
    return pd.DataFrame(
        {s: 100.0 * np.cumprod(1.0 + rng.normal(0.0, v / math.sqrt(252), n)) for s, v in vols.items()},
        index=days,
    )


def test_cycle_defaults_are_read_from_the_orchestrator():
    cfg = pcf.cycle_defaults()
    assert cfg["band"] == pytest.approx(0.03)
    assert cfg["cash_reserve"] == pytest.approx(0.002)
    assert cfg["lookback"] == 21 and isinstance(cfg["lookback"], int)


def test_rebalance_dates_are_the_last_session_of_each_month_in_range():
    days = pd.bdate_range("2020-01-01", "2020-04-30")
    dates = pcf.rebalance_dates(days, "2020-02", "2020-03")
    assert [pd.Timestamp(d).strftime("%Y-%m-%d") for d in dates] == ["2020-02-28", "2020-03-31"]


def test_execute_stops_at_the_first_buy_above_the_cash(harness):
    book = pcf.Book(cash=100.0, shares={"A": 10})
    orders = [harness.OrderIntent("A", -5, 10.0, 0.5, 0.0),   # +50 of cash
              harness.OrderIntent("B", 10, 20.0, 0.0, 0.5),   # 200 > 150: refused
              harness.OrderIntent("C", 1, 1.0, 0.0, 0.1)]
    run = pcf.execute(book, orders, {"A": 10.0, "B": 20.0, "C": 1.0}, fee=0.0)
    assert run == {"filled": 1, "stopped": True}
    assert book.shares == {"A": 5} and book.cash == pytest.approx(150.0)


def test_distance_to_targets_counts_lines_held_without_a_target():
    book = pcf.Book(cash=0.0, shares={"A": 6, "B": 4})
    d = pcf.distance_to_targets(book, {"A": 0.5}, {"A": 10.0, "B": 10.0})
    assert d == pytest.approx(0.1 + 0.4)


def test_constrained_policies_never_stop_and_keep_the_cash_positive(harness):
    closes = _panel()
    dates = pcf.rebalance_dates(closes.index, "2020-03", "2021-06")
    cfg = {**pcf.cycle_defaults(), "budget_per_line": 1.0}  # fully invested: the case that overdraws
    unchecked = pcf.summarize(pcf.simulate(harness, closes, dates, 10_000.0, "N", cfg))
    assert unchecked["stopped_cycles"] >= 1  # the panel does reach the defect
    for policy in ("S", "R"):
        m = pcf.summarize(pcf.simulate(harness, closes, dates, 10_000.0, policy, cfg))
        assert m["stopped_cycles"] == 0
        assert m["min_cash_after_pct"] >= 0.0


def _row(n_stop, s_dist, r_dist, s_cash=0.001, r_cash=0.001):
    return {"N": {"stopped_cycles": n_stop, "overdrawing_plans": n_stop},
            "S": {"stopped_cycles": 0, "min_cash_after_pct": s_cash, "mean_distance_binding": s_dist},
            "R": {"stopped_cycles": 0, "min_cash_after_pct": r_cash, "mean_distance_binding": r_dist}}


def test_verdict_prefers_R_only_when_closer_at_every_capital():
    assert pcf.verdict({"a": _row(1, 0.05, 0.01), "b": _row(0, 0.04, 0.02)}) == {
        "defect": "CONFIRME", "eligible": {"S": True, "R": True}, "default_policy": "R"}
    assert pcf.verdict({"a": _row(1, 0.05, 0.01), "b": _row(0, 0.02, 0.03)})["default_policy"] == "S"


def test_verdict_without_overdraw_and_with_a_negative_cash():
    v = pcf.verdict({"a": _row(0, None, None), "b": _row(0, None, None)})
    assert v["defect"] == "NON REPRODUIT" and v["default_policy"] == "S"
    v = pcf.verdict({"a": _row(2, 0.05, 0.01, r_cash=-0.001)})
    assert v["eligible"]["R"] is False and v["default_policy"] == "S"
