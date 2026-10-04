"""Tests for voltarget_strategy_verdict.py -- the decision pieces of issue #18921.

Charts are built in the format written by qc-mcp-lite ``read_backtest_chart``:
``{"series": {name: {"values": [[t, v], ...]}}}``, timestamps in UTC seconds.
"""

from __future__ import annotations

import numpy as np
import pandas as pd
import pytest

import voltarget_strategy_verdict as vs


def _ts(day: str) -> int:
    """21:00 UTC: 16:00 or 17:00 in New York, the same calendar day."""
    return int(pd.Timestamp(f"{day} 21:00", tz="UTC").timestamp())


def _chart(series: dict[str, list]) -> dict:
    return {"series": {k: {"values": v} for k, v in series.items()}}


def _interleaved(days: pd.DatetimeIndex, values: np.ndarray) -> dict:
    series = {k: [] for k in vs.EQUITY_SERIES}
    for i, (d, v) in enumerate(zip(days, values)):
        series[f"e{i % 5}"].append([_ts(f"{d:%Y-%m-%d}"), float(v)])
    return _chart(series)


class TestPoints:
    def test_formats(self):
        ts, ys = vs._points([[1, 2.0], [3, 9, 9, 9, 4.0], {"x": 5, "y": 6.0}])
        assert ts == [1, 3, 5] and ys == [2.0, 4.0, 6.0]   # candle -> close

    def test_new_york_dates(self):
        idx = vs._ny_dates([_ts("2008-01-15"), _ts("2008-07-15")])
        assert list(idx.strftime("%Y-%m-%d")) == ["2008-01-15", "2008-07-15"]


class TestDailyEquity:
    days = pd.bdate_range("2020-01-06", periods=23)

    def test_merges_interleaved_series(self):
        eq = vs.daily_close_equity(_interleaved(self.days, np.arange(23) + 100.0))
        assert eq.index.equals(self.days)
        assert eq.iloc[0] == 100.0 and eq.iloc[-1] == 122.0

    def test_missing_series_raises(self):
        chart = _interleaved(self.days, np.ones(23))
        del chart["series"]["e3"]
        with pytest.raises(ValueError, match="e3"):
            vs.daily_close_equity(chart)

    def test_duplicate_session_raises(self):
        chart = _interleaved(self.days, np.ones(23))
        chart["series"]["e1"]["values"].append([_ts("2020-01-06"), 1.0])
        with pytest.raises(ValueError, match="same session"):
            vs.daily_close_equity(chart)

    def test_returns_keep_sessions_only(self):
        eq = pd.Series([100.0, 110.0, 110.0, 121.0],
                       index=pd.to_datetime(["2020-01-03", "2020-01-04", "2020-01-05",
                                             "2020-01-06"]))
        sessions = pd.to_datetime(["2020-01-03", "2020-01-06"])
        r = vs.daily_returns(eq, sessions)
        assert list(r.index) == [pd.Timestamp("2020-01-06")]
        assert r.iloc[0] == pytest.approx(0.21)            # weekend points ignored

    def test_missing_session_raises(self):
        eq = pd.Series([100.0, 101.0], index=pd.to_datetime(["2020-01-03", "2020-01-07"]))
        with pytest.raises(ValueError, match="2020-01-06"):
            vs.daily_returns(eq, pd.to_datetime(["2020-01-03", "2020-01-06", "2020-01-07"]))


class TestBootstrap:
    idx = pd.bdate_range("2010-01-01", periods=600)

    def _series(self, seed: int, drift: float = 0.0) -> pd.Series:
        return pd.Series(np.random.default_rng(seed).normal(drift, 0.01, len(self.idx)),
                         index=self.idx)

    def test_identical_series(self):
        a = self._series(0)
        out = vs.circular_block_diff(a, a.copy(), draws=200)
        assert out["observed"] == 0.0
        assert out["p_one_sided"] == 1.0                    # every draw is exactly 0

    def test_clearly_better_series(self):
        b = self._series(1)
        a = b + 0.002                                       # same noise, higher mean
        out = vs.circular_block_diff(a, b, draws=500)
        assert out["observed"] > 0 and out["p_one_sided"] < 0.01

    def test_paired_and_deterministic(self):
        a, b = self._series(2), self._series(3)
        one = vs.circular_block_diff(a, b, draws=300)
        two = vs.circular_block_diff(a, b, draws=300, chunk=7)
        assert one == two                                   # chunking does not change draws

    def test_index_mismatch_raises(self):
        a = self._series(4)
        with pytest.raises(ValueError, match="same sessions"):
            vs.circular_block_diff(a, a.iloc[1:])


class TestDecision:
    def test_holm(self):
        adj = vs.holm({"har": 0.01, "tsfm": 0.04})
        assert adj == {"har": pytest.approx(0.02), "tsfm": pytest.approx(0.04)}

    def test_holm_is_monotone(self):
        adj = vs.holm({"har": 0.03, "tsfm": 0.02})
        assert adj["tsfm"] == pytest.approx(0.04) and adj["har"] == pytest.approx(0.04)

    @pytest.mark.parametrize("diff,p,placebo,expected", [
        (0.10, 0.01, 0.05, "BEATS"),
        (0.10, 0.01, 0.12, "INCONCLUSIVE"),                 # a placebo does as well
        (0.10, 0.20, 0.05, "INCONCLUSIVE"),
        (0.00, 0.01, -1.0, "NO BEATS"),
        (-0.02, 0.90, -1.0, "NO BEATS"),
    ])
    def test_gate(self, diff, p, placebo, expected):
        assert vs.gate({"observed": diff}, p, placebo) == expected


class TestRv21Check:
    rebal = pd.to_datetime(["2008-04-01", "2008-05-01", "2008-06-02", "2008-07-01"])

    def _chart(self, monthly: dict[str, list[float]], on_rebalance_day: float | None = None):
        # one point every week; month value k applies from rebalance k
        days = pd.bdate_range("2008-04-02", "2008-07-25", freq="W-WED")
        series = {}
        for t in vs.TICKERS:
            vals = monthly[t]
            pts = []
            for d in days:
                k = self.rebal.searchsorted(d, side="right") - 1
                pts.append([_ts(f"{d:%Y-%m-%d}"), vals[k]])
            if on_rebalance_day is not None:
                pts.append([_ts("2008-05-01"), on_rebalance_day])
            series[t] = pts
        return _chart(series)

    def _forecasts(self, monthly: dict[str, list[float]]) -> pd.DataFrame:
        rows = [{"date": d, "ticker": t, "rv21_vol_offqc": monthly[t][k]}
                for k, d in enumerate(self.rebal) for t in vs.TICKERS]
        return pd.DataFrame(rows)

    def test_detects_a_month_without_rebalance(self):
        qc = {t: [0.20, 0.15, 0.15, 0.25] for t in vs.TICKERS}       # June not refreshed
        off = {t: [0.20, 0.15, 0.13, 0.25] for t in vs.TICKERS}
        out = vs.rv21_source_check(self._chart(qc), self._forecasts(off))
        assert out["months_not_rebalanced_by_qc"] == 1
        assert out["of_which_1st_on_weekend"] == 1                   # 2008-06-01 is a Sunday
        assert out["months_compared"] == 3
        assert out["rel_gap_max"] == 0.0

    def test_point_on_rebalance_day_is_ignored(self):
        qc = {t: [0.20, 0.15, 0.13, 0.25] for t in vs.TICKERS}
        out = vs.rv21_source_check(self._chart(qc, on_rebalance_day=0.20),
                                   self._forecasts(qc))
        assert out["months_not_rebalanced_by_qc"] == 0

    def test_two_values_in_a_month_raise(self):
        qc = {t: [0.20, 0.15, 0.13, 0.25] for t in vs.TICKERS}
        chart = self._chart(qc)
        chart["series"]["GLD"]["values"].append([_ts("2008-05-20"), 0.99])
        with pytest.raises(ValueError, match="GLD"):
            vs.qc_monthly_rv21(chart, self.rebal)


class TestCalendarEffect:
    idx = pd.bdate_range("2010-01-01", periods=400)

    def _run(self, shift: float) -> tuple[dict, dict]:
        noise = np.random.default_rng(5).normal(0.0, 0.01, len(self.idx))
        returns = {vs.BASELINE: pd.Series(noise + shift, index=self.idx),
                   "har": pd.Series(noise, index=self.idx)}
        stats = {m: {k: float(r.mean()) for k in vs.REPORTED} | {"n_days": len(r)}
                 for m, r in returns.items()}
        return returns, stats

    def test_same_run_gives_zero(self):
        ret, st = self._run(0.0)
        out = vs.calendar_effect(ret, st, ret, st)
        assert out["rv21_minus_reference_rv21"]["diff"] == 0.0
        assert all(v == 0.0 for v in out["stats_by_calendar"]["har"]["delta"].values())

    def test_side_by_side_and_baseline_gap(self):
        now, now_st = self._run(0.001)                       # fixed calendar does better
        ref, ref_st = self._run(0.0)
        out = vs.calendar_effect(now, now_st, ref, ref_st)
        row = out["stats_by_calendar"][vs.BASELINE]
        assert set(row) == {"this_run", "reference", "delta"}
        assert set(row["this_run"]) == set(vs.REPORTED)       # n_days stays out of the table
        assert row["delta"]["sharpe"] == pytest.approx(0.001, abs=1e-6)
        gap = out["rv21_minus_reference_rv21"]
        assert gap["diff"] > 0 and gap["ci95"][0] > 0          # same noise: the gap is the shift

    def test_sessions_must_match(self):
        now, now_st = self._run(0.0)
        ref = {m: r.iloc[1:] for m, r in now.items()}
        with pytest.raises(ValueError, match="same sessions"):
            vs.calendar_effect(now, now_st, ref, now_st)
