"""Tests for shadow_inverse_vol.py (#18923, step 2) on synthetic series, without network."""

from __future__ import annotations

import math

import numpy as np
import pandas as pd
import pytest

import inverse_vol_currency as ivc
import shadow_inverse_vol as siv
import shadow_replay


@pytest.fixture(scope="module")
def harness():
    return ivc.load_harness()


def _walk(idx: pd.DatetimeIndex, vol: float, seed: int, start: float = 100.0) -> pd.Series:
    rng = np.random.default_rng(seed)
    return pd.Series(start * np.cumprod(1.0 + rng.normal(0.0, vol / math.sqrt(252), len(idx))),
                     index=idx)


def _market(start: str = "2026-01-01", end: str = "2026-12-31", fx: pd.Series | None = None):
    idx = pd.bdate_range(start, end)
    closes = {s: _walk(idx, v, k) for k, (s, v) in enumerate(
        [("SPY", 0.18), ("QQQ", 0.24), ("IEF", 0.07), ("GLD", 0.15)])}
    if fx is None:
        fx = _walk(idx, 0.08, 9, start=1.15)
    return closes, fx


def test_schedule_opens_on_start_then_complete_month_ends():
    idx = pd.bdate_range("2026-08-03", "2026-11-06")
    # 2026-10-03 is a Saturday: the first session is Monday 2026-10-05
    got = siv.schedule_dates(idx, "2026-10-03", "2026-11-02")
    assert [d.strftime("%Y-%m-%d") for d in got] == ["2026-10-05", "2026-10-30"]


def test_schedule_skips_the_month_of_end():
    idx = pd.bdate_range("2026-08-03", "2026-11-30")
    # the pass runs mid-November: 2026-11-13 is the last known session, not a month-end
    got = siv.schedule_dates(idx, "2026-10-05", "2026-11-16")
    assert [d.strftime("%Y-%m-%d") for d in got] == ["2026-10-05", "2026-10-30"]


def test_schedule_counts_a_start_on_a_month_end_once():
    idx = pd.bdate_range("2026-08-03", "2026-11-30")
    got = siv.schedule_dates(idx, "2026-09-30", "2026-11-02")
    assert [d.strftime("%Y-%m-%d") for d in got] == ["2026-09-30", "2026-10-30"]


def test_schedule_without_session_raises():
    idx = pd.bdate_range("2026-08-03", "2026-10-02")
    with pytest.raises(ValueError):
        siv.schedule_dates(idx, "2026-10-03", "2026-10-05")


def test_window_is_half_open_and_opens_with_the_allocation_fee(harness):
    closes, fx = _market()
    out = siv.replay(closes, fx, "2026-06-03", "2026-09-01", "U", 0.025, harness)
    assert out["dates"][0] == "2026-06-03"
    assert out["dates"][-1] == "2026-08-31"
    assert all("2026-06-03" <= d < "2026-09-01" for d in out["dates"])
    assert len(out["dates"]) == len(out["net_returns"]) == len(out["turnover"])
    # nothing held before the first close: its return is the fee of the opening allocation
    gross = sum(ivc.target_weights(harness, ivc.build_panel(closes, fx)["usd"],
                                   pd.Timestamp("2026-06-03"), 0.025).values())
    assert out["turnover"][0] == pytest.approx(gross)
    assert out["net_returns"][0] == pytest.approx(-ivc.FEE * gross)
    # trades only on the opening close and on month-ends; August is over when the pass runs on 09-01
    traded = {d for d, t in zip(out["dates"], out["turnover"]) if t > 0}
    assert traded <= {"2026-06-03", "2026-06-30", "2026-07-31", "2026-08-31"}
    assert "2026-06-03" in traded


def test_fees_are_measured_on_the_starting_equity(harness):
    closes, fx = _market()
    # one rebalance only: the window ends before the first month-end
    out = siv.replay(closes, fx, "2026-06-03", "2026-06-20", "F", 0.025, harness)
    assert out["fees"] == pytest.approx(ivc.FEE * out["turnover"][0])
    assert sum(t > 0 for t in out["turnover"]) == 1
    # several rebalances: the fee of each one is paid on the equity of that day
    out = siv.replay(closes, fx, "2026-02-02", "2026-12-01", "F", 0.025, harness)
    equity = np.cumprod(1.0 + np.asarray(out["net_returns"]))
    rate = np.asarray(out["turnover"]) * ivc.FEE
    assert out["fees"] == pytest.approx(float((equity / (1.0 - rate) * rate).sum()))
    assert out["fees"] > ivc.FEE * out["turnover"][0]


def test_constant_fx_makes_both_conventions_identical(harness):
    closes, _ = _market()
    fx = pd.Series(1.20, index=closes["SPY"].index)
    u = siv.replay(closes, fx, "2026-03-02", "2026-12-01", "U", 0.025, harness)
    f = siv.replay(closes, fx, "2026-03-02", "2026-12-01", "F", 0.025, harness)
    assert f["net_returns"] == pytest.approx(u["net_returns"], rel=1e-12, abs=1e-15)


def test_returns_are_those_of_a_euro_investor(harness):
    closes, _ = _market()
    idx = closes["SPY"].index
    flat = {s: pd.Series(100.0, index=idx) for s in closes}
    # flat USD prices would give no volatility at all: give them a little, then move the FX alone
    flat = {s: c * (1.0 + 1e-4 * np.sin(np.arange(len(idx)) + k)) for k, (s, c) in enumerate(flat.items())}
    fx = pd.Series(np.linspace(1.10, 1.30, len(idx)), index=idx)
    out = siv.replay(flat, fx, "2026-03-02", "2026-12-01", "U", 0.025, harness)
    # the euro rises against the dollar: a euro investor in US assets loses on the conversion
    assert float(np.prod(1.0 + np.asarray(out["net_returns"]))) < 0.99


def test_conventions_differ_when_the_fx_moves(harness):
    closes, fx = _market()
    u = siv.replay(closes, fx, "2026-03-02", "2026-12-01", "U", 0.025, harness)
    f = siv.replay(closes, fx, "2026-03-02", "2026-12-01", "F", 0.025, harness)
    assert u["dates"] == f["dates"]
    assert u["net_returns"] != pytest.approx(f["net_returns"])


def test_not_enough_history_raises(harness):
    closes, fx = _market(start="2026-06-01")
    with pytest.raises(ValueError, match="closes up to"):
        siv.replay(closes, fx, "2026-06-10", "2026-09-01", "U", 0.025, harness)


def test_unknown_convention_raises(harness):
    closes, fx = _market()
    with pytest.raises(ValueError, match="convention"):
        siv.replay(closes, fx, "2026-06-03", "2026-09-01", "X", 0.025, harness)


def test_entry_point_meets_the_shadow_contract(monkeypatch, capsys):
    closes, fx = _market()

    def fake_fetch(start, end, folder):
        print("download noise")
        return closes, fx

    monkeypatch.setattr(siv, "fetch_closes", fake_fetch)
    out = siv.inverse_vol(start="2026-06-03", end="2026-09-01", convention="F", target=0.025)
    assert set(out) == {"dates", "net_returns", "turnover", "fees"}
    # the shadow driver parses stdout as JSON: the entry point must not write to it
    captured = capsys.readouterr()
    assert captured.out == ""
    assert "download noise" in captured.err
    row = shadow_replay.metrics(out["dates"], out["net_returns"], out["turnover"], out["fees"])
    assert row["n_days"] == len(out["dates"])
    assert row["sharpe_net"] is not None


def test_simulate_reports_the_traded_weight_of_each_session():
    idx = pd.bdate_range("2026-01-05", periods=6)
    rets = pd.DataFrame({"A": [0.0, 0.01, -0.02, 0.025, 0.0, 0.01],
                         "B": [0.0, -0.01, 0.0, 0.02, 0.01, 0.0]}, index=idx)
    schedule = {idx[0]: {"A": 0.5, "B": 0.3}, idx[3]: {"A": 0.2, "B": 0.6}}
    sim = ivc.simulate(rets, schedule, band=ivc.BAND, fee=0.001)
    turnover = sim["turnover"]
    assert list(turnover.index) == list(idx)
    assert turnover.iloc[0] == pytest.approx(0.8)
    assert turnover.iloc[[1, 2, 4, 5]].tolist() == [0.0, 0.0, 0.0, 0.0]
    assert turnover.sum() == pytest.approx(sim["traded"])
