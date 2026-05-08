"""Tests for har_model.py — Corsi (2009) HAR model + walk-forward evaluation."""

from __future__ import annotations

import numpy as np
import pandas as pd
import pytest

from har_model import HARModel, _make_split_indices, walk_forward_har
from intraday_loader import hourly_log_returns, synthesize_intraday
from realized_variance import daily_realized_variance


@pytest.fixture
def synth_rv() -> pd.Series:
    ds = synthesize_intraday(n_days=400, obs_per_day=24, seed=11, annualized_vol=0.7)
    return daily_realized_variance(hourly_log_returns(ds))


class TestHARFit:
    def test_fit_recovers_intercept_only_for_constant_rv(self):
        rv = pd.Series(
            np.full(100, 0.0004),
            index=pd.date_range("2020-01-01", periods=100, freq="D"),
        )
        model = HARModel().fit(rv)
        assert model.fit_ is not None
        assert model.fit_.coef.shape == (4,)
        assert model.fit_.in_sample_mse == pytest.approx(0.0, abs=1e-12)

    def test_fit_raises_when_too_few_obs(self):
        rv = pd.Series(
            np.linspace(1e-4, 5e-4, 25),
            index=pd.date_range("2020-01-01", periods=25, freq="D"),
        )
        with pytest.raises(ValueError):
            HARModel().fit(rv)

    def test_in_sample_mse_is_nonneg(self, synth_rv):
        model = HARModel().fit(synth_rv)
        assert model.fit_.in_sample_mse >= 0.0


class TestPredictOneStep:
    def test_predict_one_step_uses_last_22(self, synth_rv):
        model = HARModel().fit(synth_rv)
        full = float(model.predict_one_step(synth_rv))
        partial = float(model.predict_one_step(synth_rv.iloc[-22:]))
        assert full == pytest.approx(partial)

    def test_predict_requires_min_22_history(self, synth_rv):
        model = HARModel().fit(synth_rv)
        with pytest.raises(ValueError):
            model.predict_one_step(synth_rv.iloc[-10:])

    def test_predict_before_fit_raises(self, synth_rv):
        model = HARModel()
        with pytest.raises(RuntimeError):
            model.predict_one_step(synth_rv)


class TestPredictHStep:
    def test_h1_matches_one_step(self, synth_rv):
        model = HARModel().fit(synth_rv)
        h1 = model.predict_h_step(synth_rv, horizon=1)
        one = model.predict_one_step(synth_rv)
        assert h1 == pytest.approx(one)

    def test_h_must_be_positive(self, synth_rv):
        model = HARModel().fit(synth_rv)
        with pytest.raises(ValueError):
            model.predict_h_step(synth_rv, horizon=0)

    def test_h5_returns_finite(self, synth_rv):
        model = HARModel().fit(synth_rv)
        out = model.predict_h_step(synth_rv, horizon=5)
        assert np.isfinite(out)


class TestSplitIndices:
    def test_n_splits_yields_n_folds(self):
        splits = _make_split_indices(n=600, n_splits=5)
        assert len(splits) == 5

    def test_train_grows_monotonically(self):
        splits = _make_split_indices(n=600, n_splits=5)
        train_ends = [s[0] for s in splits]
        assert all(train_ends[i + 1] > train_ends[i] for i in range(4))

    def test_test_window_no_overlap_with_future_train(self):
        splits = _make_split_indices(n=600, n_splits=5)
        for k in range(len(splits) - 1):
            te_end_k = splits[k][2]
            tr_end_k1 = splits[k + 1][0]
            assert te_end_k <= tr_end_k1

    def test_raises_on_too_few_splits(self):
        with pytest.raises(ValueError):
            _make_split_indices(n=600, n_splits=1)

    def test_raises_on_tiny_n(self):
        with pytest.raises(ValueError):
            _make_split_indices(n=100, n_splits=5)


class TestWalkForwardHAR:
    def test_returns_expected_keys(self, synth_rv):
        out = walk_forward_har(synth_rv, horizon=1, n_splits=4, refit_every=22)
        for key in (
            "horizon", "n_splits", "n_total_preds",
            "aggregate_mse_logrv", "fold_results",
            "forecasts", "targets",
        ):
            assert key in out

    def test_predictions_align_with_targets(self, synth_rv):
        out = walk_forward_har(synth_rv, horizon=1, n_splits=4, refit_every=22)
        assert len(out["forecasts"]) == len(out["targets"])
        assert (out["forecasts"].index == out["targets"].index).all()

    def test_aggregate_mse_is_finite(self, synth_rv):
        out = walk_forward_har(synth_rv, horizon=1, n_splits=4, refit_every=22)
        assert np.isfinite(out["aggregate_mse_logrv"])
        assert out["aggregate_mse_logrv"] >= 0.0

    def test_horizon_5_runs(self, synth_rv):
        out = walk_forward_har(synth_rv, horizon=5, n_splits=4, refit_every=22)
        assert out["horizon"] == 5
        assert out["n_total_preds"] > 0

    def test_raises_on_short_series(self):
        rv = pd.Series(
            np.full(100, 0.0004),
            index=pd.date_range("2020-01-01", periods=100, freq="D"),
        )
        with pytest.raises(ValueError):
            walk_forward_har(rv)
