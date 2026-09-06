"""Tests for m18_tsfm_benchmark.py — TimesFM 2.5 zero-shot benchmark (#14768).

No torch / timesfm dependency: the TimesFM model is faked (deterministic
constant-path forecaster) so the harness, metrics, calibration symmetry and
verdict logic are all exercised on synthetic data.
"""

from __future__ import annotations

import numpy as np
import pandas as pd
import pytest

import m18_tsfm_benchmark as m18


# ---------------------------------------------------------------------------
# Metrics — closed forms
# ---------------------------------------------------------------------------

class TestMetrics:
    def test_qlike_zero_at_perfect_forecast(self):
        rv = np.array([1.0, 2.0, 3.0])
        assert m18.qlike_loss(rv, rv) == pytest.approx(0.0, abs=1e-12)

    def test_qlike_known_value(self):
        # ratio = 2 -> 2 - log(2) - 1 = 1 - log(2)
        assert m18.qlike_loss(np.array([2.0]), np.array([1.0])) == pytest.approx(
            1.0 - np.log(2.0), abs=1e-12
        )

    def test_qlike_rejects_nonpositive(self):
        with pytest.raises(ValueError):
            m18.qlike_loss(np.array([1.0]), np.array([0.0]))
        with pytest.raises(ValueError):
            m18.qlike_loss(np.array([0.0]), np.array([1.0]))

    def test_pinball_median_is_half_mae(self):
        y = np.array([1.0, 2.0, 5.0])
        yhat = np.array([2.0, 2.0, 2.0])
        half_mae = 0.5 * np.mean(np.abs(y - yhat))
        assert m18.pinball_loss(y, yhat, 0.5) == pytest.approx(half_mae)

    def test_pinball_asymmetry(self):
        # over-prediction at high q costs (1-q), under-prediction costs q
        assert m18.pinball_loss(np.array([1.0]), np.array([0.0]), 0.9) == pytest.approx(0.9)
        assert m18.pinball_loss(np.array([0.0]), np.array([1.0]), 0.9) == pytest.approx(0.1)

    def test_coverage_and_width_closed_form(self):
        y = np.array([0.0, 1.0, 2.0])
        lower = np.array([0.0, 0.0, 3.0])
        upper = np.array([1.0, 2.0, 3.0])
        cov, width = m18.interval_coverage(y, lower, upper)
        assert cov == pytest.approx(2.0 / 3.0)
        assert width == pytest.approx(np.mean(upper - lower))

    def test_coverage_rejects_crossed_bands(self):
        with pytest.raises(ValueError):
            m18.interval_coverage(np.array([1.0]), np.array([2.0]), np.array([1.0]))


# ---------------------------------------------------------------------------
# Fold arithmetic — must match har_model._make_split_indices
# ---------------------------------------------------------------------------

class TestFoldBounds:
    @pytest.mark.parametrize("n,n_splits", [(1000, 5), (2272, 5), (600, 4)])
    def test_matches_make_split_indices(self, n, n_splits):
        from har_model import _make_split_indices
        expected = _make_split_indices(n, n_splits)
        got = m18._fold_bounds(n, n_splits)
        assert len(got) == len(expected)
        for g, (train_end, test_start, test_end) in zip(got, expected):
            assert g["train_end_idx"] == train_end
            assert g["oos_start_idx"] == test_start
            assert g["oos_end_idx"] == test_end


# ---------------------------------------------------------------------------
# Deterministic baselines — causality and alignment
# ---------------------------------------------------------------------------

class TestBaselines:
    def _series(self, n=400, seed=3):
        rng = np.random.default_rng(seed)
        log_rv = np.cumsum(rng.normal(0, 0.05, n)) - 10.0
        idx = pd.date_range("2020-01-01", periods=n, freq="D")
        rv = pd.Series(np.exp(log_rv), index=idx)
        return log_rv, rv

    def test_persistence_uses_last_observation_only(self):
        log_rv, rv = self._series()
        idx = [50, 100, 150]
        preds = m18._rolling_predictions("persistence", log_rv, rv, idx, horizon=5)
        assert preds[0] == log_rv[49]
        assert preds[1] == log_rv[99]
        assert preds[2] == log_rv[149]

    def test_ewma_matches_pandas_reference(self):
        log_rv, rv = self._series()
        i = 200
        ref = pd.Series(log_rv[:i]).ewm(span=20).mean().iloc[-1]
        preds = m18._rolling_predictions("ewma", log_rv, rv, [i], horizon=1, ewma_span=20)
        assert preds[0] == pytest.approx(float(ref))

    def test_ewma_requires_span(self):
        log_rv, rv = self._series()
        with pytest.raises(ValueError):
            m18._rolling_predictions("ewma", log_rv, rv, [100], horizon=1)

    def test_har_rv_constant_series_forecasts_its_level(self):
        # NOT a discriminating test for the #14791 defect: on a CONSTANT RV the
        # contemporaneous identity fit and a properly-lagged HAR both forecast
        # the constant level (2.0), so this passes on either alignment. It
        # guards a real invariant (level recovery on a flat series), but the
        # tests that actually REJECT #14791 are in TestHarRvAlignment — their
        # fixtures (a persistent series, not a constant) are the ones that go
        # red under the contemporaneous alignment (see its docstring).
        idx = pd.date_range("2020-01-01", periods=200, freq="D")
        rv = pd.Series(np.exp(2.0), index=idx)
        model = m18.HarRvModel().fit(rv)
        assert model.predict_h_step_mean_log(rv, horizon=5) == pytest.approx(2.0, abs=1e-6)

    def test_select_ewma_span_is_train_only(self):
        rng = np.random.default_rng(0)
        log_rv = np.cumsum(rng.normal(0, 0.1, 600))
        train_end = 500
        span_a = m18._select_ewma_span(log_rv, train_end, horizon=1)
        log_rv_mutated = log_rv.copy()
        log_rv_mutated[train_end:] = 999.0  # future garbled
        span_b = m18._select_ewma_span(log_rv_mutated, train_end, horizon=1)
        assert span_a == span_b
        assert span_a in m18.EWMA_SPAN_GRID


# ---------------------------------------------------------------------------
# har_rv alignment (#14791) — lagged features + non-degeneracy guard
# ---------------------------------------------------------------------------

class TestHarRvAlignment:
    """Regression tests for the #14791 defect: HarRvModel.fit originally
    regressed RV_t on CONTEMPORANEOUS features (RV_t itself) — a perfect
    identity fit whose iterated forecast degenerates to persistence (agreement
    5e-14 on the committed manifest). The features must be lagged one step,
    and the non-degeneracy guard must be able to go red on that failure."""

    def _persistent_rv(self, n=500, seed=3):
        rng = np.random.default_rng(seed)
        log_rv = np.cumsum(rng.normal(0, 0.05, n)) - 10.0
        idx = pd.date_range("2020-01-01", periods=n, freq="D")
        return log_rv, pd.Series(np.exp(log_rv), index=idx)

    def test_features_are_lagged_one_step(self):
        # feature row at position t must carry RV_{t-1} — never RV_t
        _, rv = self._persistent_rv()
        feats = m18._har_rv_features(rv)
        assert np.isnan(feats["rv_d"].iloc[0])
        assert feats["rv_d"].iloc[10] == pytest.approx(float(rv.iloc[9]))
        assert feats["rv_w"].iloc[30] == pytest.approx(
            float(rv.iloc[25:30].mean()))

    def test_fit_is_not_the_identity(self):
        # with the contemporaneous bug the coefficients collapse to
        # [0, 1, 0, 0] (in-sample residual ~1e-19); a genuine one-step-ahead
        # fit must spread weight beyond rv_d alone
        _, rv = self._persistent_rv()
        model = m18.HarRvModel().fit(rv)
        b0, bd, bw, bm = model.coef
        assert abs(bw) + abs(bm) + abs(b0) > 1e-3

    def test_har_rv_rolling_predictions_pass_the_distinctness_guard(self):
        # the exact in-situ control: rolling OOS predictions of har_rv vs
        # persistence on a persistent series must clear the 1e-6 separation —
        # with the identity bug this raises (agreement ~1e-14) and the test
        # goes red
        log_rv, rv = self._persistent_rv()
        idx = list(range(150, 500, 10))
        pers = m18._rolling_predictions("persistence", log_rv, rv, idx, horizon=5)
        har = m18._rolling_predictions("har_rv", log_rv, rv, idx, horizon=5)
        sep = m18.assert_baselines_distinct(
            {"persistence": pers, "har_rv": har})
        assert sep["max"] >= 1e-6


class TestBaselineDistinctnessGuard:
    def test_identical_arrays_raise(self):
        a = np.array([-9.1, -9.0, -8.8])
        b = a + 1e-14
        with pytest.raises(RuntimeError, match="degenerate baselines"):
            m18.assert_baselines_distinct({"persistence": a, "har_rv": b})

    def test_distinct_arrays_pass_and_report_weakest_pair(self):
        a = np.array([-9.1, -9.0])
        b = np.array([-8.0, -7.0])
        c = np.array([-5.0, -4.0])
        sep = m18.assert_baselines_distinct(
            {"persistence": a, "ewma": b, "log_har": c})
        # weakest pair is a-vs-b: max rel diff = 0.1/0.9... ~ 1e-1 scale
        assert sep["max"] > 1e-2
        assert sep["median"] > 1e-2

    def test_tsfm_excluded_from_the_guard(self):
        a = np.array([-9.1, -9.0])
        same_as_a = a.copy()
        sep = m18.assert_baselines_distinct(
            {"persistence": a, "tsfm": same_as_a})
        # no baseline pair -> nothing to compare -> both aggregations are inf
        assert sep["max"] == np.inf
        assert sep["median"] == np.inf

    def test_median_surfaces_partial_degeneracy_the_max_hides(self):
        # Two of three OOS points agree to ~1e-8 (below the 1e-6 floor) while a
        # single divergent point keeps the max (the abort signal) at 0.625 — the
        # guard correctly does NOT abort (it only detects agreement-everywhere),
        # but the recorded median (~1.4e-8) exposes the near-total agreement
        # that the max alone would obscure (#14823).
        a = np.array([-8.0, -7.0, -8.0])
        b = np.array([-8.0 + 1e-7, -7.0 + 1e-7, -3.0])
        sep = m18.assert_baselines_distinct(
            {"persistence": a, "har_rv": b})
        assert sep["max"] > 1e-6
        assert sep["median"] < sep["max"]


# ---------------------------------------------------------------------------
# TimesFM wrapper — faked model, layout and fail-explicit contract
# ---------------------------------------------------------------------------

class FakeTimesFM:
    """Deterministic fake: point = last context value (flat path), quantile
    tensor laid out as [mean, q0.1..q0.9] with the median at channel 5."""

    def forecast(self, horizon, inputs):
        point = np.stack([np.full(horizon, float(x[-1]), dtype=np.float32)
                          for x in inputs])
        n_q = 1 + len(m18.TSFM_QUANTILES)
        base = point[:, :1]  # (B, 1)
        quant = np.zeros((len(inputs), horizon, n_q), dtype=np.float32)
        for j, q in enumerate(m18.TSFM_QUANTILES):
            # monotone bands around the flat forecast, width grows with |q-0.5|
            quant[:, :, 1 + j] = (base + (q - 0.5) * 2.0)[:, :, None].repeat(horizon, 1)[:, :, 0]
        quant[:, :, 0] = base[:, :1][:, 0][:, None].repeat(horizon, 1)
        return point, quant


class FakeTimesFMBadAxis:
    def forecast(self, horizon, inputs):
        point = np.zeros((len(inputs), horizon), dtype=np.float32)
        return point, np.zeros((len(inputs), horizon, 9), dtype=np.float32)


def _fake_wrapper(context_len=64, model=None):
    return m18.TimesFMWrapper(
        repo_id="fake/timesfm", context_len=context_len,
        loader=(lambda repo: model if model is not None else FakeTimesFM()),
    )


class TestTimesFMWrapper:
    def test_fail_explicit_when_never_loaded(self):
        w = m18.TimesFMWrapper(repo_id="fake", context_len=64)
        with pytest.raises(RuntimeError, match="aborting"):
            w.forecast_paths([np.zeros(8, dtype=np.float32)], horizon=2)

    def test_fail_explicit_when_loader_raises(self):
        def boom(repo):
            raise OSError("checkpoint unavailable")
        with pytest.raises(OSError):
            m18.TimesFMWrapper(repo_id="fake", context_len=64, loader=boom)

    def test_counts_every_series_served(self):
        w = _fake_wrapper()
        ctxs = [np.arange(10, dtype=np.float32)] * 7
        w.forecast_paths(ctxs, horizon=3)
        assert w.n_calls == 7

    def test_rejects_wrong_quantile_axis(self):
        w = _fake_wrapper(model=FakeTimesFMBadAxis())
        with pytest.raises(RuntimeError, match="channels"):
            w.forecast_paths([np.arange(10, dtype=np.float32)], horizon=3)

    def test_median_channel_is_the_point_output(self):
        # layout contract: quant[..., 5] == point == median
        w = _fake_wrapper()
        ctx = np.linspace(-5, -4, 30).astype(np.float32)
        point, quant = w.forecast_paths([ctx], horizon=4)
        assert np.allclose(quant[0, :, 5], point[0])

    def test_batch_predictions_mean_path_and_last_step_quantiles(self):
        w = _fake_wrapper(context_len=16)
        log_rv = np.linspace(-10, -8, 40)
        idx = [20, 30]
        preds, q_last = m18._tsfm_batch_predictions(log_rv, idx, horizon=5, tsfm=w)
        # flat path at last context value -> mean of path == last value
        assert preds[0] == pytest.approx(log_rv[19])
        assert preds[1] == pytest.approx(log_rv[29])
        assert q_last.shape == (2, 1 + len(m18.TSFM_QUANTILES))
        # q0.1 column is 1 (channel 0 is the mean head)
        assert q_last[0, 1] == pytest.approx(log_rv[19] - 0.8)
        assert q_last[0, 9] == pytest.approx(log_rv[19] + 0.8)


# ---------------------------------------------------------------------------
# run_config end-to-end on synthetic data with the fake model
# ---------------------------------------------------------------------------

def _synthetic_hourly(n_hours=13000, seed=11):
    rng = np.random.default_rng(seed)
    idx = pd.date_range("2015-01-01", periods=n_hours, freq="h")
    # two volatility regimes so RV carries real signal for the HAR models
    regime = np.sin(np.arange(n_hours) / 700.0) > 0
    sigma = np.where(regime, 0.01, 0.03)
    rets = pd.Series(rng.normal(0, 1, n_hours) * sigma, index=idx)
    return rets


class TestRunConfig:
    def test_structure_and_symmetry(self):
        hourly = _synthetic_hourly()
        tsfm = _fake_wrapper()
        cfg = m18.run_config(
            "SYN-USD", hourly, horizon=1, seed=0, n_splits=3,
            calibration_size=30, refit_every=22, tsfm=tsfm,
        )
        assert "skipped" not in cfg
        for model in m18.MODELS:
            row = cfg["models"][model]
            assert row["n_oos"] == cfg["n_oos"] > 0
            assert np.isfinite(row["mse_debiased"])
            assert row["qlike_debiased"] >= 0.0
        # one bias entry per executed fold, for EVERY model (symmetry)
        n_folds = cfg["bounds_train_test"]["n_folds"]
        for model in m18.MODELS:
            assert len(cfg["per_fold_bias"][model]) == n_folds
            assert len(cfg["fc_hash_per_fold"][model]) == n_folds
        # both DM legs present for every baseline
        for leg in ("dm_vs_baselines_mse", "dm_vs_baselines_linear"):
            assert set(cfg[leg].keys()) == set(m18.BASELINES)
            for v in cfg[leg].values():
                assert v["verdict"] in ("BEATS baseline", "BEATEN BY baseline",
                                        "INCONCLUSIVE")
        # quantile evaluation recorded with the layout note
        q = cfg["tsfm_quantiles"]
        assert q["n_obs"] == cfg["n_oos"]
        assert set(q["pinball_loss"].keys()) == {str(x) for x in m18.TSFM_QUANTILES}
        assert 0.0 <= q["coverage_80"] <= 1.0

    def test_calibration_moves_constant_forecast_to_target_level(self):
        # fake model predicts a flat path at the LAST log-RV value: on a
        # trending series its raw bias is negative; the debiased leg must
        # sit closer to the target level than the raw leg.
        hourly = _synthetic_hourly(n_hours=13000, seed=5)
        tsfm = _fake_wrapper()
        cfg = m18.run_config(
            "SYN-USD", hourly, horizon=1, seed=0, n_splits=3,
            calibration_size=30, refit_every=22, tsfm=tsfm,
        )
        row = cfg["models"]["tsfm"]
        assert row["mse_debiased"] < row["mse_raw"]

    def test_debias_false_leaves_raw_predictions(self):
        hourly = _synthetic_hourly(n_hours=13000, seed=5)
        tsfm = _fake_wrapper()
        cfg = m18.run_config(
            "SYN-USD", hourly, horizon=1, seed=0, n_splits=3,
            calibration_size=30, refit_every=22, tsfm=tsfm, debias=False,
        )
        assert all(b == 0.0 for b in cfg["per_fold_bias"]["tsfm"])
        row = cfg["models"]["tsfm"]
        assert row["mse_debiased"] == pytest.approx(row["mse_raw"])

    def test_shallow_series_is_skipped(self):
        idx = pd.date_range("2020-01-01", periods=500, freq="h")
        hourly = pd.Series(0.01, index=idx)  # ~21 RV days
        cfg = m18.run_config(
            "SYN-USD", hourly, horizon=1, seed=0, n_splits=3,
            calibration_size=30, refit_every=22, tsfm=_fake_wrapper(),
        )
        assert "skipped" in cfg


# ---------------------------------------------------------------------------
# Aggregate verdict — §C conjunction logic on synthetic config dicts
# ---------------------------------------------------------------------------

def _cfg(coin, horizon, seed, p_mse, mld_mse, tsfm_hash="aaa", tsfm_mse=1.0,
         base_mse=2.0):
    def dm(p, mld):
        verdict = ("BEATS baseline" if (p < 0.05 and mld < 0)
                   else "BEATEN BY baseline" if (p < 0.05 and mld > 0)
                   else "INCONCLUSIVE")
        return {"p_value": p, "mean_loss_diff": mld, "verdict": verdict}
    return {
        "coin": coin, "horizon": horizon, "seed": seed,
        "models": {"tsfm": {"mse_debiased": tsfm_mse},
                   "log_har": {"mse_debiased": base_mse}},
        "dm_vs_baselines_mse": {"log_har": dm(p_mse, mld_mse)},
        "dm_vs_baselines_linear": {"log_har": dm(0.3, 0.0)},
        "fc_hash_per_fold": {"tsfm": [tsfm_hash], "log_har": ["x"]},
    }


class TestAggregateVerdicts:
    def test_all_beats_and_identical_seeds_gives_beats(self):
        cfgs = [_cfg("X", 1, s, p_mse=1e-4, mld_mse=-0.5) for s in (0, 7, 42, 99)]
        out = m18.aggregate_verdicts(cfgs)
        assert len(out) == 1
        assert out[0]["baseline"] == "log_har"
        assert out[0]["verdict"] == "BEATS"
        assert out[0]["seeds_bit_identical"] is True

    def test_all_beaten_gives_no_beats(self):
        cfgs = [_cfg("X", 5, s, p_mse=1e-4, mld_mse=+0.5) for s in (0, 7)]
        out = m18.aggregate_verdicts(cfgs)
        assert out[0]["verdict"] == "NO BEATS"

    def test_mixed_seeds_inconclusive(self):
        cfgs = [
            _cfg("X", 22, 0, p_mse=1e-4, mld_mse=-0.5),
            _cfg("X", 22, 7, p_mse=0.4, mld_mse=-0.1),
        ]
        out = m18.aggregate_verdicts(cfgs)
        assert out[0]["verdict"] == "INCONCLUSIVE"

    def test_insignificant_p_is_inconclusive(self):
        cfgs = [_cfg("X", 1, s, p_mse=0.4, mld_mse=-0.5) for s in (0, 7)]
        out = m18.aggregate_verdicts(cfgs)
        assert out[0]["verdict"] == "INCONCLUSIVE"

    def test_non_identical_seeds_need_two_sigma_edge(self):
        # all seeds beat with p<0.05, but hashes differ and edge spread is
        # wide relative to the mean -> sigma jambe blocks the BEATS
        cfgs = [
            _cfg("X", 1, 0, p_mse=1e-4, mld_mse=-0.5, tsfm_mse=1.0, base_mse=1.1,
                 tsfm_hash="a"),
            _cfg("X", 1, 7, p_mse=1e-4, mld_mse=-0.5, tsfm_mse=1.0, base_mse=5.0,
                 tsfm_hash="b"),
        ]
        out = m18.aggregate_verdicts(cfgs)
        # edges: +9% and +80% -> mean 44.7, sigma 35.6 -> 2*sigma > edge
        assert out[0]["verdict"] == "INCONCLUSIVE"
        assert out[0]["seeds_bit_identical"] is False

    def test_skipped_configs_are_ignored(self):
        cfgs = [_cfg("X", 1, 0, 1e-4, -0.5),
                {"coin": "X", "horizon": 1, "seed": 7, "skipped": "rv<300"}]
        out = m18.aggregate_verdicts(cfgs)
        assert len(out) == 1
        assert out[0]["n_seeds"] == 1
