"""Tests for the M11 Kelly debias replay (Epic #1454, 2026-09-24).

Guards, in order of importance:
1. Feature/target alignment of the HAR fit (no same-day RV leakage).
2. The paired three-arm walk reproduces the two reference paths of
   ``walk_forward_har`` bit-for-bit and satisfies fit_raw - adjusted = bias.
3. No temporal leakage: forecasts are invariant to future data.
4. Strategy timing: information-flow causality — a forecast perturbation at
   date t cannot change net returns before t; mu_hat uses only past returns.
   These guards prove the DATA-FLOW ordering (weights depend only on prior
   information). They do NOT prove execution fill quality at the daily
   boundary (close vs open, slippage): that remains a stated assumption of
   the simulation, priced only through the fee term.
5. Oracle arm targets the SAME window as the forecast truth ([i, i+h-1]).
6. Fail-closed sweep contract: missing arms are problems; unavailable sources
   are explicit missing combos, never silent.
7. Forecast-layer stats math (signed bias / MAE / MSE).
"""

from __future__ import annotations

import numpy as np
import pandas as pd
import pytest

from har_model import walk_forward_har
from intraday_loader import hourly_log_returns, synthesize_intraday
from realized_variance import daily_realized_variance, har_lag_features
from simulate_har_kelly import (
    ARMS,
    _annotate_kelly_deltas,
    _buy_hold_strategy,
    _equity_curve,
    _forecast_layer_stats,
    _kelly_strategy,
    paired_walk_forward_har,
    validate_debias_sweep,
)


@pytest.fixture(scope="module")
def synth_rv() -> pd.Series:
    ds = synthesize_intraday(n_days=420, obs_per_day=24, seed=11, annualized_vol=0.7)
    return daily_realized_variance(hourly_log_returns(ds))


@pytest.fixture(scope="module")
def synth_hourly() -> pd.Series:
    ds = synthesize_intraday(n_days=420, obs_per_day=24, seed=11, annualized_vol=0.7)
    return hourly_log_returns(ds)


class TestHarAlignment:
    def test_har_lag_features_use_only_past_rv(self, synth_rv):
        """features at t must equal statistics of rv[t-1] and earlier (no same-day leak)."""
        feats = har_lag_features(synth_rv)
        t = 100
        assert feats["rv_d"].iloc[t] == pytest.approx(synth_rv.iloc[t - 1])
        assert feats["rv_w"].iloc[t] == pytest.approx(synth_rv.iloc[t - 5:t].mean())
        assert feats["rv_m"].iloc[t] == pytest.approx(synth_rv.iloc[t - 22:t].mean())
        # first 22 rows are NaN by construction
        assert feats["rv_m"].iloc[:22].isna().all()


class TestPairedWalk:
    def test_hist_raw_bit_identical_to_reference_raw_path(self, synth_rv):
        paired = paired_walk_forward_har(synth_rv, horizon=5, calibration_size=60)
        ref = walk_forward_har(synth_rv, horizon=5, calibrate_bias=False)
        assert list(paired["hist_raw"].index) == list(ref["forecasts"].index)
        assert np.allclose(paired["hist_raw"].values, ref["forecasts"].values, atol=0, rtol=0)

    def test_adjusted_bit_identical_to_reference_calibrated_path(self, synth_rv):
        paired = paired_walk_forward_har(synth_rv, horizon=5, calibration_size=60)
        ref = walk_forward_har(synth_rv, horizon=5, calibrate_bias=True, calibration_size=60)
        assert np.allclose(paired["adjusted"].values, ref["forecasts"].values, atol=0, rtol=0)

    def test_fit_raw_minus_adjusted_equals_bias_by_pred(self, synth_rv):
        paired = paired_walk_forward_har(synth_rv, horizon=5, calibration_size=60)
        diff = np.asarray(paired["fit_raw"].values) - np.asarray(paired["adjusted"].values)
        assert np.allclose(diff, paired["bias_by_pred"], atol=1e-12)

    def test_arms_share_identical_index_and_targets(self, synth_rv):
        paired = paired_walk_forward_har(synth_rv, horizon=5, calibration_size=60)
        for arm in ARMS:
            assert list(paired[arm].index) == list(paired["targets"].index)
        assert len(paired["targets"]) == len(paired["oos_dates"]) > 0

    def test_no_future_leakage_forecasts_invariant_to_future_rv(self, synth_rv):
        """Perturbing RV strictly after date d must leave forecasts dated < d unchanged."""
        h = 5
        paired_a = paired_walk_forward_har(synth_rv, horizon=h, calibration_size=60)
        d_pos = 300  # inside OOS folds
        rv2 = synth_rv.copy()
        rv2.iloc[d_pos:] = rv2.iloc[d_pos:] * 5.0  # violent future regime change
        paired_b = paired_walk_forward_har(rv2, horizon=h, calibration_size=60)
        cut = synth_rv.index[d_pos]
        for arm in ARMS:
            a = paired_a[arm][paired_a[arm].index < cut]
            b = paired_b[arm][paired_b[arm].index < cut]
            assert list(a.index) == list(b.index)
            assert np.allclose(a.values, b.values, atol=0, rtol=0), (
                f"arm {arm}: forecasts before {cut} changed when only future RV changed"
            )


class TestStrategyTiming:
    def _mk(self, seed: int = 3):
        rng = np.random.default_rng(seed)
        idx = pd.date_range("2020-01-01", periods=400, freq="D")
        r = pd.Series(rng.normal(0.0005, 0.02, 400), index=idx)
        f = pd.Series(np.log(np.full(400, 4e-4)) + rng.normal(0, 0.05, 400), index=idx)
        return r, f

    def test_forecast_perturbation_at_t_leaves_past_net_returns_unchanged(self):
        r, f = self._mk()
        t = 250
        base = _kelly_strategy(r, f, mu_window=60, kelly_cap=1.0, fee_bps=10.0, include_net=True)
        f2 = f.copy()
        f2.iloc[t] = f2.iloc[t] + 2.0  # massive vol forecast spike at t
        pert = _kelly_strategy(r, f2, mu_window=60, kelly_cap=1.0, fee_bps=10.0, include_net=True)
        net_base = np.asarray(base["_net_returns"])
        net_pert = np.asarray(pert["_net_returns"])
        assert np.allclose(net_base[:t - 1], net_pert[:t - 1], atol=1e-12), (
            "net returns before t must not depend on the forecast at t"
        )

    def test_mu_hat_uses_only_past_returns(self):
        r, f = self._mk()
        t = 250
        base = _kelly_strategy(r, f, mu_window=60, kelly_cap=1.0, fee_bps=10.0, include_net=True)
        r2 = r.copy()
        r2.iloc[t:] = r2.iloc[t:] + 0.5  # violent future return shift
        pert = _kelly_strategy(r2, f, mu_window=60, kelly_cap=1.0, fee_bps=10.0, include_net=True)
        w_base = np.asarray(base["_weights"])
        w_pert = np.asarray(pert["_weights"])
        assert np.allclose(w_base[:t], w_pert[:t], atol=1e-12), (
            "weights up to t must not depend on returns from t onward (mu shift guard)"
        )

    def test_matched_delta_is_postwarmup_kelly_vs_postwarmup_bh_on_identical_dates(self):
        """Regression (coordinator review 2026-09-24): delta_sharpe_vs_bh_matched
        must compare the Kelly Sharpe recomputed WITHOUT the warmup rows against
        buy_hold on the IDENTICAL dates — not a full-window Kelly Sharpe against
        a post-warmup buy_hold."""
        rng = np.random.default_rng(5)
        n = 300
        idx = pd.date_range("2020-01-01", periods=n, freq="D")
        # violent bull during the warmup, quiet afterwards: the warmup rows
        # materially distort any full-window vs post-warmup comparison.
        r = pd.Series(np.concatenate([
            rng.normal(0.004, 0.010, 60), rng.normal(0.0002, 0.010, n - 60)
        ]), index=idx)
        f = pd.Series(np.log(np.full(n, 4e-4)), index=idx)
        mu_window = 60
        probe = _kelly_strategy(r, f, mu_window, 1.0, 10.0, include_net=True)
        net = np.asarray(probe["_net_returns"], dtype=float)
        idxs = pd.DatetimeIndex(probe["_index"])
        k = _kelly_strategy(r, f, mu_window, 1.0, 10.0, include_net=True)
        _annotate_kelly_deltas(k, r, mu_window, bh_sharpe_full=0.0)
        # manual ground truth on the post-warmup support
        manual_kelly_post = _equity_curve(net[mu_window:])[0]
        manual_bh_post = _buy_hold_strategy(r.reindex(idxs[mu_window:]).dropna())["sharpe"]
        # annotator rounds to 4 decimals — tolerance matches that rounding
        assert k["kelly_sharpe_postwarmup"] == pytest.approx(manual_kelly_post, abs=1e-4)
        assert k["bh_sharpe_matched"] == pytest.approx(manual_bh_post, abs=1e-4)
        assert k["delta_sharpe_vs_bh_matched"] == pytest.approx(
            manual_kelly_post - manual_bh_post, abs=3e-4)
        # the previously-flawed formula (full-window Kelly vs post-warmup BH)
        # must yield a DIFFERENT number on this construction
        assert k["delta_sharpe_vs_bh_matched"] != pytest.approx(
            k["sharpe"] - manual_bh_post, abs=1e-3)
        # no private/net arrays leak into the strategy row
        assert not any(key.startswith("_") for key in k)
        assert k["warmup_days"] == mu_window

    def test_oracle_formula_targets_same_window_as_forecast_truth(self):
        """rolling(h).mean().shift(-(h-1)) at i == mean over [i, i+h-1]."""
        rng = np.random.default_rng(7)
        rv = pd.Series(np.exp(rng.normal(-8.0, 0.4, 200)),
                       index=pd.date_range("2020-01-01", periods=200, freq="D"))
        for h in (1, 5, 20):
            oracle = np.log(rv).rolling(h).mean().shift(-(h - 1))
            i = 50
            direct = float(np.log(rv.iloc[i:i + h]).mean())
            assert oracle.iloc[i] == pytest.approx(direct, abs=1e-12)


class TestForecastLayerStats:
    def test_signed_bias_mae_mse_math(self):
        idx = pd.date_range("2020-01-01", periods=4, freq="D")
        preds = pd.Series([1.0, 2.0, 3.0, 4.0], index=idx)
        targets = pd.Series([0.5, 2.5, 3.0, 3.0], index=idx)
        s = _forecast_layer_stats("arm", preds, targets)
        # errors: +0.5, -0.5, 0.0, +1.0
        assert s["mean_error"] == pytest.approx(0.25)
        assert s["mae"] == pytest.approx(0.5)
        assert s["mse"] == pytest.approx((0.25 + 0.25 + 0.0 + 1.0) / 4)
        assert s["n_oos"] == 4
        assert s["layer"] == "forecast"


class TestSweepValidator:
    def _row(self, coin, h, strategy, variant):
        return {"coin": coin, "horizon": h, "strategy": strategy,
                "variant": variant, "sharpe": 0.5, "n_periods": 100}

    def test_complete_rows_pass(self):
        rows = []
        for h in (1, 5):
            rows.append(self._row("BTC-USD", h, "buy_hold", "hist_raw"))
            for arm in ARMS:
                rows.append(self._row("BTC-USD", h, "vol_target_har", arm))
                for w in (60, 120, 250):
                    rows.append(self._row("BTC-USD", h, f"kelly_har_mu{w}", arm))
        missing, problems = validate_debias_sweep(
            ["BTC-USD"], [1, 5], rows, {}, mu_windows=[60, 120, 250])
        assert missing == []
        assert problems == []

    def test_missing_arm_is_a_problem(self):
        rows = [self._row("BTC-USD", 1, "buy_hold", "hist_raw")]
        for arm in ARMS:
            rows.append(self._row("BTC-USD", 1, "vol_target_har", arm))
            rows.append(self._row("BTC-USD", 1, "kelly_har_mu60", arm))
        # drop the causal kelly arm -> the sweep contract must flag it
        rows = [r for r in rows
                if not (r["strategy"] == "kelly_har_mu60" and r["variant"] == "adjusted")]
        missing, problems = validate_debias_sweep(
            ["BTC-USD"], [1], rows, {}, mu_windows=[60])
        assert missing == []
        assert problems and any("BTC-USD h=1" in p for p in problems)

    def test_unavailable_source_is_explicit_missing_not_silent(self):
        rows: list[dict] = []
        missing, problems = validate_debias_sweep(
            ["SOL-USD"], [1, 5], rows,
            unavailable={"SOL-USD": "yfinance fetch failed"},
            mu_windows=[60])
        assert problems == []
        assert {m["horizon"] for m in missing} == {1, 5}
        assert all("yfinance fetch failed" in m["reason"] for m in missing)

    def test_degenerate_rows_do_not_count_as_produced(self):
        rows = [self._row("BTC-USD", 1, "buy_hold", "hist_raw")]
        for arm in ARMS:
            rows.append(self._row("BTC-USD", 1, "vol_target_har", arm))
            r = self._row("BTC-USD", 1, "kelly_har_mu60", arm)
            if arm == "adjusted":
                r["sharpe"] = float("nan")  # degenerate: nonfinite Sharpe
            rows.append(r)
        missing, problems = validate_debias_sweep(
            ["BTC-USD"], [1], rows, {}, mu_windows=[60])
        assert missing == []
        assert problems and any("missing/degenerate" in p for p in problems)

    def test_zero_period_rows_do_not_count_as_produced(self):
        rows = [self._row("BTC-USD", 1, "buy_hold", "hist_raw")]
        for arm in ARMS:
            rows.append(self._row("BTC-USD", 1, "vol_target_har", arm))
            r = self._row("BTC-USD", 1, "kelly_har_mu60", arm)
            if arm == "adjusted":
                r["n_periods"] = 0  # degenerate: no evaluation window
            rows.append(r)
        missing, problems = validate_debias_sweep(
            ["BTC-USD"], [1], rows, {}, mu_windows=[60])
        assert missing == []
        assert problems and any("missing/degenerate" in p for p in problems)

    def test_duplicate_rows_are_rejected(self):
        rows = [self._row("BTC-USD", 1, "buy_hold", "hist_raw")]
        for arm in ARMS:
            rows.append(self._row("BTC-USD", 1, "vol_target_har", arm))
            rows.append(self._row("BTC-USD", 1, "kelly_har_mu60", arm))
        rows.append(self._row("BTC-USD", 1, "kelly_har_mu60", "adjusted"))  # duplicate
        missing, problems = validate_debias_sweep(
            ["BTC-USD"], [1], rows, {}, mu_windows=[60])
        assert missing == []
        assert any("duplicate" in p for p in problems)


class TestLegacyContract:
    """Pin the legacy (debias=False) row set and return contract of
    ``_evaluate_one`` — sole caller is ``main()`` (grep-verified 2026-09-24;
    m11c/m11d/m11e replicate the logic by copy, they do not import it)."""

    def test_legacy_rows_and_return_contract(self, synth_hourly):
        from simulate_har_kelly import _evaluate_one
        rows, stats, series = _evaluate_one(
            coin="SYNTH", hourly_rets=synth_hourly, horizon=5,
            target_vol=0.15, kelly_cap=1.0, fee_bps=10.0,
            mu_windows=[60], n_splits=5, refit_every=22, train_size=250,
        )
        # return contract: (rows, forecast_stats, series_frame); legacy has
        # empty stats and no series
        assert isinstance(rows, list) and rows
        assert stats == []
        assert series is None
        strategies = {r["strategy"] for r in rows}
        assert {"buy_hold", "vol_target_har", "vol_target_oracle",
                "kelly_har_mu60"} <= strategies
        # every legacy row carries the uniform variant key
        assert all(r.get("variant") == "hist_raw" for r in rows if "error" not in r)
        # kelly rows disclose warmup + matched-support delta (additive fields)
        k60 = next(r for r in rows if r["strategy"] == "kelly_har_mu60")
        assert k60["warmup_days"] == 60
        assert "delta_sharpe_vs_bh_matched" in k60 and "bh_sharpe_matched" in k60

    def test_debias_rows_and_return_contract(self, synth_hourly):
        from simulate_har_kelly import _evaluate_one
        rows, stats, series = _evaluate_one(
            coin="SYNTH", hourly_rets=synth_hourly, horizon=5,
            target_vol=0.15, kelly_cap=1.0, fee_bps=10.0,
            mu_windows=[60], n_splits=5, refit_every=22, train_size=250,
            debias=True, calibration_size=60,
        )
        assert isinstance(rows, list) and rows
        assert series is not None
        assert {"date", "target_logrv", *ARMS} <= set(series.columns)
        by_arm = {(r["strategy"], r["variant"]) for r in rows if "error" not in r}
        for arm in ARMS:
            assert ("vol_target_har", arm) in by_arm
            assert ("kelly_har_mu60", arm) in by_arm
        tests = {s.get("test") for s in stats}
        assert {"dm_mse_adjusted_vs_fit_raw", "dm_mse_adjusted_vs_hist_raw"} <= tests
        assert all(s["layer"] == "forecast" for s in stats if "test" in s)
        # Regression (coordinator review 2026-09-24): EVERY forecast-layer row,
        # including the per-arm bias/MAE/MSE rows, carries coin/horizon so a
        # multi-coin aggregate stays attributable.
        for s in stats:
            assert s.get("coin") == "SYNTH", f"row missing coin attribution: {s}"
            assert s.get("horizon") == 5, f"row missing horizon attribution: {s}"
