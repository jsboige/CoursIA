"""Tests for voltarget_forecasts.py -- the protocol pieces of issue #18921.

TimesFM is replaced by a deterministic fake: the production loader is never
called here (no network, no GPU).
"""

from __future__ import annotations

import importlib
import sys

import numpy as np
import pandas as pd
import pytest

import voltarget_forecasts as vf
from m18_tsfm_benchmark import TimesFMWrapper


def _gbm_panel(n_days: int = 900, seed: int = 0) -> dict[str, pd.DataFrame]:
    rng = np.random.default_rng(seed)
    idx = pd.bdate_range("2004-11-18", periods=n_days)
    panel = {}
    for k, t in enumerate(vf.TICKERS):
        sigma = 0.008 + 0.002 * k
        r = rng.normal(0, sigma, n_days)
        close = 100 * np.exp(np.cumsum(r))
        open_ = np.concatenate([[100.0], close[:-1]]) * np.exp(rng.normal(0, sigma / 3, n_days))
        high = np.maximum(open_, close) * np.exp(np.abs(rng.normal(0, sigma / 2, n_days)))
        low = np.minimum(open_, close) * np.exp(-np.abs(rng.normal(0, sigma / 2, n_days)))
        panel[t] = pd.DataFrame({"Open": open_, "High": high, "Low": low, "Close": close}, index=idx)
    return panel


class _FakeModel:
    """Forecasts the last context value, flat, for every step."""

    def forecast(self, horizon, inputs):
        point = np.array([[float(c[-1])] * horizon for c in inputs])
        quant = np.repeat(point[:, :, None], 10, axis=2)
        return point, quant


def _fake_tsfm() -> TimesFMWrapper:
    return TimesFMWrapper("fake/repo", vf.CONTEXT_LEN, loader=lambda _repo: _FakeModel())


class TestRebalanceDates:
    def test_first_session_of_each_month(self):
        sessions = pd.DatetimeIndex(["2007-01-02", "2007-01-03", "2007-02-01",
                                     "2007-02-02", "2007-03-01"])
        got = vf.rebalance_dates(sessions, "2007-01-01", "2007-02-28")
        assert got == [pd.Timestamp("2007-01-02"), pd.Timestamp("2007-02-01")]


class TestRv21:
    def test_replicates_main_py(self):
        closes = np.linspace(100, 110, 30)
        last = closes[-21:]
        expected = np.std(np.log(last[1:] / last[:-1])) * np.sqrt(252)
        assert vf.rv21_vol(closes) == pytest.approx(expected, rel=1e-12)

    def test_needs_21_closes(self):
        with pytest.raises(ValueError):
            vf.rv21_vol(np.ones(20))

    def test_logvar_round_trip(self):
        assert vf.logvar_to_vol(vf.vol_to_logvar(0.17)) == pytest.approx(0.17, rel=1e-12)


class TestTarget:
    def test_mean_over_next_21_sessions_starting_at_date(self):
        idx = pd.bdate_range("2020-01-01", periods=40)
        v = pd.Series(np.arange(1.0, 41.0), index=idx)
        d = idx[5]
        assert vf.target_logvar(v, d) == pytest.approx(np.log(np.mean(np.arange(6.0, 27.0))))

    def test_incomplete_window_is_nan(self):
        idx = pd.bdate_range("2020-01-01", periods=10)
        assert np.isnan(vf.target_logvar(pd.Series(1.0, index=idx), idx[0]))


class TestPlacebo:
    def test_keeps_per_asset_distribution_and_is_deterministic(self):
        har = pd.DataFrame({t: np.arange(12.0) + 100 * k for k, t in enumerate(vf.TICKERS)})
        a, b = vf.placebo_logvar(har, 42), vf.placebo_logvar(har, 42)
        pd.testing.assert_frame_equal(a, b)
        for t in vf.TICKERS:
            assert sorted(a[t]) == sorted(har[t])
        assert not a.equals(har)

    def test_seeds_differ(self):
        har = pd.DataFrame({t: np.arange(50.0) for t in vf.TICKERS})
        assert not vf.placebo_logvar(har, 0).equals(vf.placebo_logvar(har, 1))


class TestBuildTable:
    @pytest.fixture(scope="class")
    def built(self):
        with pytest.MonkeyPatch.context() as mp:
            mp.setattr(vf, "VERDICT_START", "2006-12-01")
            mp.setattr(vf, "VERDICT_END", "2008-03-31")
            return vf.build_table(_gbm_panel(), _fake_tsfm())

    def test_no_lookahead_origin_before_date(self, built):
        table, _ = built
        assert (table["origin"] < table["date"]).all()

    def test_columns_and_shape(self, built):
        table, meta = built
        assert meta["n_rebalances"] * len(vf.TICKERS) == len(table)
        for s in vf.PLACEBO_SEEDS:
            assert f"placebo_{s}_logvar" in table
        assert table["har_logvar"].notna().all()

    def test_fake_tsfm_reads_last_context_value(self, built):
        table, meta = built
        assert meta["tsfm_reproducible"] is True
        panel = _gbm_panel()
        row = table.iloc[0]
        v = vf.daily_ohlc_variance(panel[row["ticker"]])
        last = np.log(v[v.index < row["date"]].iloc[-1])
        assert row["tsfm_logvar"] == pytest.approx(last, rel=1e-5)

    def test_forecast_verdict_structure(self, built):
        table, _ = built
        res = vf.forecast_verdict(table)
        assert set(res) == {"har_vs_rv21", "tsfm_vs_rv21", "tsfm_vs_har"}
        for pair in res.values():
            assert pair["verdict"] in {"BEATS", "BEATEN", "INCONCLUSIVE"}
            assert set(pair["per_asset"]) == set(vf.TICKERS)


class TestPairVerdict:
    @staticmethod
    def _r(p, d):
        return {"dm_p": p, "mean_loss_diff": d}

    def test_beats_needs_all_four_significant_same_sign(self):
        assert vf.pair_verdict({t: self._r(0.01, -1.0) for t in vf.TICKERS}) == "BEATS"
        mixed = {t: self._r(0.01, -1.0) for t in vf.TICKERS}
        mixed["GLD"] = self._r(0.20, -1.0)
        assert vf.pair_verdict(mixed) == "INCONCLUSIVE"
        assert vf.pair_verdict({t: self._r(0.01, 1.0) for t in vf.TICKERS}) == "BEATEN"


class TestQcModule:
    @staticmethod
    def _table(n_dates: int = 2) -> pd.DataFrame:
        dates = pd.date_range("2007-01-01", periods=n_dates, freq="MS")
        rows = []
        for t in vf.TICKERS:
            for d in dates:
                row = {"date": d, "ticker": t, "rv21_logvar": -9.0, "har_logvar": -9.5,
                       "tsfm_logvar": -10.0}
                row.update({f"placebo_{s}_logvar": -8.0 for s in vf.PLACEBO_SEEDS})
                rows.append(row)
        return pd.DataFrame(rows)

    @staticmethod
    def _import(tmp_path, monkeypatch):
        monkeypatch.syspath_prepend(str(tmp_path))
        for name in [m for m in sys.modules if m.startswith("vol_forecasts")]:
            monkeypatch.delitem(sys.modules, name)
        return importlib.import_module("vol_forecasts")

    def test_module_is_importable_and_aligned(self, tmp_path, monkeypatch):
        path = tmp_path / "vol_forecasts.py"
        vf.write_qc_module(self._table(), path, {"panel_sha256": "x", "tsfm_revision": "y"})
        mod = self._import(tmp_path, monkeypatch)
        assert mod.DATES == ["2007-01-01", "2007-02-01"]
        assert mod.FORECASTS["har"]["SPY"][0] == pytest.approx(
            float(vf.logvar_to_vol(-9.5)), rel=1e-5)
        assert len(mod.FORECASTS) == 3 + len(vf.PLACEBO_SEEDS)

    def test_split_under_qc_file_limit(self, tmp_path, monkeypatch):
        """236 monthly dates: one file would exceed QC's 64,000-character cap."""
        path = tmp_path / "vol_forecasts.py"
        (tmp_path / "vol_forecasts_part9.py").write_text("STALE = 1\n", encoding="utf-8")
        written = vf.write_qc_module(self._table(236), path,
                                     {"panel_sha256": "x", "tsfm_revision": "y"})
        assert len(written) > 2
        assert not (tmp_path / "vol_forecasts_part9.py").exists()
        for p in written:
            assert len(p.read_text(encoding="utf-8")) <= vf.QC_FILE_MAX_CHARS
        mod = self._import(tmp_path, monkeypatch)
        assert len(mod.DATES) == 236
        assert set(mod.FORECASTS) == {"rv21_offqc", "har", "tsfm",
                                      *(f"placebo_{s}" for s in vf.PLACEBO_SEEDS)}
        for model in mod.FORECASTS.values():
            assert all(len(model[t]) == 236 for t in vf.TICKERS)
