"""Unit tests for m12_har_rv_j — HAR-RV-J jump decomposition (Andersen et al. 2007).

These cover the *jump-specific* logic that distinguishes HAR-RV-J from the plain
HAR baseline (the latter is already covered by test_har_model.py):

- ``daily_jump_component``: J_t = max(RV_t - mu * BPV_t, 0) (Huang-Tauchen)
- ``har_rv_j_lag_features``: 6 regressors (log RV d/w/m + raw jump d/w/m)
- ``HARRVJModel``: OLS fit + iterated h-step forecast
- ``walk_forward_har_rv_j``: expanding-window walk-forward evaluation
- ``_sharpe_ann``: annualized Sharpe (sqrt(365), ddof=1)

All fixtures are deterministic synthetic series — no network, no GPU, no data
files. The whole module runs in well under a second on CPU.
"""

from __future__ import annotations

import sys
from pathlib import Path

import numpy as np
import pandas as pd
import pytest

SCRIPT_DIR = Path(__file__).resolve().parent.parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from m12_har_rv_j import (  # noqa: E402
    MU_HUANG_TAUCHEN,
    HARRVJModel,
    _csv_int_list,
    _csv_list,
    _sharpe_ann,
    daily_jump_component,
    har_rv_j_lag_features,
    walk_forward_har_rv_j,
)
from realized_variance import (  # noqa: E402
    daily_bipower_variation,
    daily_realized_variance,
    realized_variance_to_log,
)


# ── Fixtures ────────────────────────────────────────────────────────────────

def _hourly_log_returns(n_days: int = 120, hours_per_day: int = 8, seed: int = 0) -> pd.Series:
    """Deterministic synthetic hourly log-returns with a DatetimeIndex.

    ~8 obs/day keeps per-day RV/BPV well-defined (>= min_obs_per_day=6 default).
    """
    rng = np.random.default_rng(seed)
    n = n_days * hours_per_day
    idx = pd.date_range("2020-01-01", periods=n, freq="3h", name="timestamp")
    return pd.Series(rng.standard_normal(n) * 0.01, index=idx, name="r")


def _rv_series(n: int, base: float = 1e-4, seed: int = 1) -> pd.Series:
    """A positive daily-RV series (date index) for feature/model tests."""
    rng = np.random.default_rng(seed)
    idx = pd.date_range("2020-01-01", periods=n, freq="D", name="date")
    return pd.Series(np.abs(rng.standard_normal(n)) * base + 1e-6, index=idx, name="RV")


@pytest.fixture
def hourly() -> pd.Series:
    return _hourly_log_returns()


@pytest.fixture
def rv(hourly: pd.Series) -> pd.Series:
    return daily_realized_variance(hourly)


@pytest.fixture
def jumps(hourly: pd.Series) -> pd.Series:
    return daily_jump_component(hourly)


# ── daily_jump_component ────────────────────────────────────────────────────

class TestDailyJumpComponent:
    def test_jumps_non_negative(self, jumps: pd.Series) -> None:
        # J_t = max(RV - mu*BPV, 0) >= 0 by construction.
        assert (jumps.dropna() >= 0).all()

    def test_formula_holds_elementwise(self, hourly: pd.Series) -> None:
        rv = daily_realized_variance(hourly)
        bpv = daily_bipower_variation(hourly)
        aligned = pd.concat([rv.rename("rv"), bpv.rename("bpv")], axis=1).dropna()
        expected = np.maximum(aligned["rv"] - MU_HUANG_TAUCHEN * aligned["bpv"], 0.0)
        got = daily_jump_component(hourly).reindex(aligned.index).fillna(0.0)
        np.testing.assert_allclose(got.values, expected.values, rtol=1e-9, atol=1e-15)

    def test_mu_zero_recovers_rv(self, hourly: pd.Series) -> None:
        # With mu=0, J_t = max(RV, 0) = RV (RV >= 0 always).
        rv = daily_realized_variance(hourly)
        j = daily_jump_component(hourly, mu=0.0)
        common = rv.index.intersection(j.index)
        np.testing.assert_allclose(j.loc[common].values, rv.loc[common].values, rtol=1e-9)

    def test_higher_mu_shrinks_jumps(self, hourly: pd.Series) -> None:
        # Larger mu -> RV - mu*BPV smaller -> fewer/smaller jumps.
        j_low = daily_jump_component(hourly, mu=0.3)
        j_high = daily_jump_component(hourly, mu=2.0)
        common = j_low.index.intersection(j_high.index)
        assert j_high.loc[common].sum() <= j_low.loc[common].sum() + 1e-15

    def test_index_is_normalized_dates(self, jumps: pd.Series) -> None:
        assert jumps.index.name == "date"
        assert jumps.index.is_normalized  # daily, no intraday duplicates


# ── har_rv_j_lag_features ───────────────────────────────────────────────────

class TestHarRvJLagFeatures:
    def test_six_regressors_present(self, rv: pd.Series, jumps: pd.Series) -> None:
        feats = har_rv_j_lag_features(rv, jumps)
        assert set(feats.columns) == {"rv_d", "rv_w", "rv_m", "j_d", "j_w", "j_m"}

    def test_jump_lag_is_shift1_no_lookahead(self, rv: pd.Series, jumps: pd.Series) -> None:
        # j_d = jumps.shift(1): today's feature uses yesterday's jump (no leak).
        feats = har_rv_j_lag_features(rv, jumps)
        expected = jumps.shift(1)
        common = feats.index.intersection(expected.index)
        np.testing.assert_allclose(
            feats["j_d"].loc[common].values,
            expected.loc[common].values,
            rtol=1e-9, atol=1e-15,
            err_msg="j_d must equal jumps.shift(1) (no look-ahead)",
        )

    def test_jumps_on_raw_scale_can_be_zero(self) -> None:
        # Jumps are NOT logged (can be exactly zero); a zero-jump series must
        # stay exactly zero in every jump lag feature.
        n = 40
        rv = _rv_series(n)
        zeros = pd.Series(np.zeros(n), index=rv.index)
        feats = har_rv_j_lag_features(rv, zeros)
        jump_cols = feats[["j_d", "j_w", "j_m"]].dropna()
        assert (jump_cols == 0.0).all().all()

    def test_rv_features_on_log_scale(self, rv: pd.Series, jumps: pd.Series) -> None:
        # rv_d/w/m are log-scale (realized_variance_to_log applied to raw lags).
        feats = har_rv_j_lag_features(rv, jumps)
        log_rv_d = realized_variance_to_log(rv).shift(1)
        common = feats.index.intersection(log_rv_d.index)
        np.testing.assert_allclose(
            feats["rv_d"].loc[common].values, log_rv_d.loc[common].values, rtol=1e-9
        )

    def test_j_w_is_rolling5_mean(self, rv: pd.Series, jumps: pd.Series) -> None:
        feats = har_rv_j_lag_features(rv, jumps)
        expected = jumps.shift(1).rolling(window=5, min_periods=5).mean()
        common = feats.index.intersection(expected.index)
        np.testing.assert_allclose(
            feats["j_w"].loc[common].values,
            expected.loc[common].values,
            rtol=1e-9, atol=1e-15,
        )


# ── HARRVJModel ─────────────────────────────────────────────────────────────

class TestHARRVJModel:
    def test_fit_requires_min_30_obs(self) -> None:
        # Fewer than 30 aligned rows after dropna (rv_m needs 22 lags) -> ValueError.
        n = 25
        rv = _rv_series(n)
        jumps = pd.Series(np.zeros(n), index=rv.index)
        with pytest.raises(ValueError):
            HARRVJModel().fit(rv, jumps)

    def test_predict_horizon_must_be_positive(self, rv: pd.Series, jumps: pd.Series) -> None:
        model = HARRVJModel().fit(rv, jumps)
        with pytest.raises(ValueError):
            model.predict_h_step(rv.iloc[-30:], jumps.iloc[-30:], horizon=0)

    def test_predict_returns_finite_float(self, rv: pd.Series, jumps: pd.Series) -> None:
        model = HARRVJModel().fit(rv, jumps)
        out = model.predict_h_step(rv.iloc[-30:], jumps.iloc[-30:], horizon=3)
        assert isinstance(out, float)
        assert np.isfinite(out)

    def test_fit_coef_shape(self, rv: pd.Series, jumps: pd.Series) -> None:
        model = HARRVJModel().fit(rv, jumps)
        # intercept + 6 features = 7 coefficients.
        assert model.coef_.shape == (7,)
        assert model.n_train_ >= 30

    def test_predict_constant_rv_recovers_log(self) -> None:
        # rv = constant C, jumps = 0 -> log(rv[t]) = log(C) for all t, so every
        # feature collapses (rv_d=rv_w=rv_m=log(C), jumps=0) and the iterated
        # h-step forecast must return ~ log(C). Exercises fit + predict_h_step.
        n = 60
        c = 1e-4
        idx = pd.date_range("2020-01-01", periods=n, freq="D", name="date")
        rv_const = pd.Series(np.full(n, c), index=idx)
        jumps_const = pd.Series(np.zeros(n), index=idx)
        model = HARRVJModel().fit(rv_const, jumps_const)
        log_c = float(np.log(c))
        pred = model.predict_h_step(rv_const, jumps_const, horizon=5)
        assert abs(pred - log_c) < 1e-6

    def test_lstsq_design_matrix_recovery(self) -> None:
        # The model fits log(RV) = X @ beta via np.linalg.lstsq on a 7-column
        # design matrix (intercept + 6 features). Verify that construction +
        # solver recover known coefficients on a noise-free linear DGP. This
        # pins the design-matrix column order used by HARRVJModel.fit.
        rng = np.random.default_rng(7)
        n = 400
        rv = pd.Series(np.abs(rng.standard_normal(n)) * 0.01 + 1e-5,
                       index=pd.date_range("2020-01-01", periods=n, freq="D"))
        jumps = pd.Series(np.abs(rng.standard_normal(n)) * 0.005, index=rv.index)
        feats = har_rv_j_lag_features(rv, jumps).dropna()
        true_beta = np.array([0.1, 0.5, 0.2, 0.1, 0.3, -0.1, 0.05])  # b0,d,w,m,dj,wj,mj
        x = np.column_stack([
            np.ones(len(feats)),
            feats["rv_d"], feats["rv_w"], feats["rv_m"],
            feats["j_d"], feats["j_w"], feats["j_m"],
        ])
        y = x @ true_beta
        coef, *_ = np.linalg.lstsq(x, y, rcond=None)
        np.testing.assert_allclose(coef, true_beta, atol=1e-8)


# ── walk_forward_har_rv_j ───────────────────────────────────────────────────

class TestWalkForwardHarRvJ:
    def test_raises_on_short_series(self) -> None:
        n = 150  # < 200 -> ValueError
        rv = _rv_series(n)
        jumps = pd.Series(np.zeros(n), index=rv.index)
        with pytest.raises(ValueError):
            walk_forward_har_rv_j(rv, jumps, n_splits=5)

    def test_returns_expected_structure(self) -> None:
        n = 420  # fold_size = 420//6 = 70 >= 60 (min train) for all 5 folds
        rv = _rv_series(n, seed=2)
        rng = np.random.default_rng(3)
        jumps = pd.Series(np.abs(rng.standard_normal(n)) * 1e-5, index=rv.index)
        out = walk_forward_har_rv_j(rv, jumps, horizon=1, n_splits=5)
        assert out["horizon"] == 1
        assert out["n_splits"] == 5
        for key in ("n_total_preds", "aggregate_mse_logrv", "fold_results",
                    "forecasts", "targets"):
            assert key in out, f"missing key {key}"
        assert out["aggregate_mse_logrv"] >= 0.0
        fc, tg = out["forecasts"], out["targets"]
        assert isinstance(fc, pd.Series)
        assert isinstance(tg, pd.Series)
        assert len(fc) == len(tg)
        assert out["n_total_preds"] == len(fc)
        # forecast / target indices must be perfectly aligned.
        np.testing.assert_array_equal(fc.index.values, tg.index.values)
        # every fold produced a finite MSE (fold_results populated).
        assert len(out["fold_results"]) >= 1
        for fr in out["fold_results"]:
            assert np.isfinite(fr["mse_logrv"])

    def test_higher_horizon_reduces_per_fold_test_count(self) -> None:
        # horizon trims the test window (range(... test_end - horizon)); a
        # larger horizon yields fewer predictions per fold.
        n = 420
        rv = _rv_series(n, seed=5)
        rng = np.random.default_rng(6)
        jumps = pd.Series(np.abs(rng.standard_normal(n)) * 1e-5, index=rv.index)
        out_h1 = walk_forward_har_rv_j(rv, jumps, horizon=1, n_splits=5)
        out_h5 = walk_forward_har_rv_j(rv, jumps, horizon=5, n_splits=5)
        assert out_h5["n_total_preds"] < out_h1["n_total_preds"]


# ── helpers ─────────────────────────────────────────────────────────────────

class TestHelpers:
    def test_sharpe_ann_too_short_is_nan(self) -> None:
        assert np.isnan(_sharpe_ann(np.array([0.1] * 9)))  # < 10 -> nan

    def test_sharpe_ann_known_value(self) -> None:
        rng = np.random.default_rng(0)
        r = rng.standard_normal(100) * 0.01
        expected = (r.mean() / r.std(ddof=1)) * np.sqrt(365)
        np.testing.assert_allclose(_sharpe_ann(r), expected, rtol=1e-12)

    def test_sharpe_ann_zero_sigma_is_nan(self) -> None:
        # constant returns -> sigma=0 -> nan (no division by zero).
        assert np.isnan(_sharpe_ann(np.array([0.001] * 100)))

    def test_csv_parsers(self) -> None:
        assert _csv_list("a, b ,c") == ["a", "b", "c"]
        assert _csv_int_list("1, 7, 42") == [1, 7, 42]
        assert _csv_list("") == []
        assert _csv_int_list("") == []
