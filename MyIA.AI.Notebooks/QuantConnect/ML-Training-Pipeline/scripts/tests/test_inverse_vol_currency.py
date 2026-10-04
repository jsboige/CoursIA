"""Tests for inverse_vol_currency.py (#19072) on synthetic series."""

from __future__ import annotations

import math

import numpy as np
import pandas as pd
import pytest

import inverse_vol_currency as ivc


@pytest.fixture(scope="module")
def harness():
    return ivc.load_harness()


def _days(n: int, start: str = "2020-01-01") -> pd.DatetimeIndex:
    return pd.bdate_range(start, periods=n)


def _walk(n: int, vol: float, seed: int, start: float = 100.0) -> np.ndarray:
    rng = np.random.default_rng(seed)
    return start * np.cumprod(1.0 + rng.normal(0.0, vol / math.sqrt(252), n))


def test_harness_is_imported_not_copied(harness):
    assert harness.__file__.replace("\\", "/").endswith("paper_harness/rebalance.py")
    assert harness.realized_vol([1.0] * 5, 21) is None


def test_constant_fx_gives_identical_forecasts_and_weights(harness):
    idx = _days(60)
    usd = pd.DataFrame({"SPY": _walk(60, 0.2, 0), "IEF": _walk(60, 0.06, 1)}, index=idx)
    panel = ivc.build_panel({c: usd[c] for c in usd}, pd.Series(1.25, index=idx))
    date = idx[-1]
    fu = ivc.forecasts(harness, panel["usd"], date)
    ff = ivc.forecasts(harness, panel["eur"], date)
    for c in usd:
        assert ff[c] == pytest.approx(fu[c], rel=1e-12)
    assert ivc.target_weights(harness, panel["eur"], date, 0.025) == pytest.approx(
        ivc.target_weights(harness, panel["usd"], date, 0.025))


def test_eur_price_divides_by_usd_per_eur():
    idx = _days(3)
    fx = pd.Series([1.10, 1.12, 1.13], index=idx)
    panel = ivc.build_panel({"SPY": pd.Series([100.0, 103.0, 101.0], index=idx)}, fx)
    eur = panel["eur"]["SPY"]
    assert eur.iloc[1] == pytest.approx(103.0 / 1.12)
    # the EUR return is the USD return deflated by the move of the USD-per-EUR quote
    assert eur.iloc[1] / eur.iloc[0] - 1 == pytest.approx(1.03 / (1.12 / 1.10) - 1)


def test_fx_quote_direction_guard():
    idx = _days(5)
    with pytest.raises(RuntimeError, match="USD per EUR"):
        ivc.build_panel({"SPY": pd.Series(100.0, index=idx)}, pd.Series(0.9, index=idx))


def test_fx_error_rule_drops_an_isolated_bad_print_only():
    idx = _days(6)
    fx = pd.Series([1.10, 1.11, 1.60, 1.12, 1.13, 1.14], index=idx)
    clean, dropped = ivc.drop_fx_errors(fx)
    assert dropped == [idx[2].strftime("%Y-%m-%d")]
    assert list(clean.index) == [d for d in idx if d != idx[2]]


def test_fx_error_rule_refuses_a_run_of_large_moves():
    # every move is 5 %: dropping date after date would eat the series, so it stops
    idx = _days(30)
    fx = pd.Series(1.1 * 1.05 ** np.arange(30), index=idx)
    with pytest.raises(RuntimeError):
        ivc.drop_fx_errors(fx, max_drops=3)


def test_month_ends_are_last_sessions():
    idx = pd.DatetimeIndex(["2024-01-30", "2024-01-31", "2024-02-01", "2024-02-28", "2024-03-01"])
    assert list(ivc.month_ends(idx)) == [pd.Timestamp("2024-01-31"), pd.Timestamp("2024-02-28"),
                                         pd.Timestamp("2024-03-01")]


def test_window_bounds():
    assert ivc.first_rebalance_month("2005-01-01") == pd.Timestamp("2004-12-01")
    assert ivc.last_holding_month() == pd.Timestamp("2026-09-01")


def test_simulate_band_fee_and_drift():
    idx = _days(4)
    rets = pd.DataFrame({"A": [0.0, 0.10, 0.0, 0.0], "B": [0.0, 0.0, 0.0, 0.0]}, index=idx)
    schedule = {idx[0]: {"A": 0.5, "B": 0.5}, idx[2]: {"A": 0.5, "B": 0.5}}
    sim = ivc.simulate(rets, schedule, band=0.03, fee=0.001)
    # first rebalance buys 100 % of the book: fee 0.001
    assert sim["returns"].iloc[0] == pytest.approx(-0.001)
    # day 2: half the book gains 10 %
    assert sim["returns"].iloc[1] == pytest.approx(0.05)
    # day 3: A drifted to 0.55/1.05 = 0.5238, gap 0.0238 < band: no trade, no fee
    assert sim["returns"].iloc[2] == pytest.approx(0.0)
    assert sim["traded"] == pytest.approx(1.0)
    assert sim["fees"] == pytest.approx(0.001)


def test_simulate_trades_when_gap_reaches_band():
    idx = _days(2)
    rets = pd.DataFrame({"A": [0.0, 0.0]}, index=idx)
    sim = ivc.simulate(rets, {idx[0]: {"A": 0.5}, idx[1]: {"A": 0.75}}, band=0.25, fee=0.0)
    assert sim["traded"] == pytest.approx(0.5 + 0.25)


def test_simulate_exit_ignores_the_band():
    idx = _days(3)
    rets = pd.DataFrame({"A": [0.0, 0.0, 0.0], "B": [0.0, -0.9, 0.0]}, index=idx)
    schedule = {idx[0]: {"A": 0.5, "B": 0.2}, idx[2]: {"A": 0.6, "B": 0.0}}
    sim = ivc.simulate(rets, schedule, band=0.03, fee=0.0)
    w_b = 0.02 / 0.82  # B lost 90 %, the book 18 %: below the band, sold anyway
    assert w_b < 0.03
    # A drifted to 0.5 / 0.82 = 0.6098, gap to 0.6 below the band: kept
    assert sim["traded"] == pytest.approx(0.7 + w_b)


def test_block_bootstrap_mean_signs():
    rng = np.random.default_rng(3)
    up = rng.normal(0.5, 1.0, 240)
    assert ivc.block_bootstrap_mean(up, 6, 2000, 0)["p_one_sided"] < 0.01
    down = -up
    assert ivc.block_bootstrap_mean(down, 6, 2000, 0)["p_one_sided"] > 0.99
    with pytest.raises(ValueError):
        ivc.block_bootstrap_mean(up[:4], 6, 10, 0)


def test_verdict_rule():
    assert ivc.verdict(-0.1, 0.001, [0.1, 0.1]) == "NO BEATS"
    assert ivc.verdict(0.0, 0.001, [0.1, 0.1]) == "NO BEATS"
    assert ivc.verdict(0.1, 0.01, [0.1, 0.2]) == "BEATS"
    assert ivc.verdict(0.1, 0.01, [0.1, -0.01]) == "INCONCLUSIVE"
    assert ivc.verdict(0.1, 0.06, [0.1, 0.2]) == "INCONCLUSIVE"


def test_forecast_losses_scores_the_next_month(harness):
    # constant daily moves: forecast and realised volatility are equal, loss 0
    idx = pd.bdate_range("2024-01-01", "2024-03-31")
    signs = np.where(np.arange(len(idx)) % 2 == 0, 1.01, 1 / 1.01)
    prices = pd.DataFrame({"X": 100 * np.cumprod(signs)}, index=idx)
    rebal = ivc.month_ends(idx)[:2]
    table = ivc.forecast_losses(harness, {"U": prices}, prices, rebal)
    assert list(table["month"]) == ["2024-02", "2024-03"]
    assert (table["loss_U"] < 1e-3).all()


def test_forecast_losses_prefers_the_matching_currency(harness):
    # the EUR line is twice as volatile as the USD one: F forecasts it, U does not
    idx = pd.bdate_range("2023-01-01", "2024-12-31")
    usd = pd.DataFrame({"X": _walk(len(idx), 0.05, 4)}, index=idx)
    eur = pd.DataFrame({"X": _walk(len(idx), 0.10, 5)}, index=idx)
    table = ivc.forecast_losses(harness, {"U": usd, "F": eur}, eur, ivc.month_ends(idx)[3:-1])
    d = ivc.monthly_diff(table, "U", "F")
    assert d.mean() > 0
    summary = ivc.loss_summary(table, ["U", "F"])
    # U under-forecasts the EUR volatility: positive bias of about ln 2
    assert summary["X"]["U"]["bias_log"] == pytest.approx(math.log(2), abs=0.25)
    assert abs(summary["X"]["F"]["bias_log"]) < 0.25
