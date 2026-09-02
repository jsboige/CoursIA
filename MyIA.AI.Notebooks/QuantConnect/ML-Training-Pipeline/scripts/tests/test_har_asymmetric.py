"""Tests for asymmetric HAR walk-forward evaluation and M16 verdicts."""

from __future__ import annotations

import numpy as np
import pandas as pd
import pytest

import har_asymmetric
from har_asymmetric import (
    AsymmetricHARModel,
    _eval_one_coin,
    _fit_asymmetric_with_train_calibration,
    aggregate_verdicts,
    walk_forward_asymmetric_har,
)


@pytest.fixture
def asymmetric_rv() -> tuple[pd.Series, pd.Series, pd.Series]:
    rng = np.random.default_rng(17)
    index = pd.date_range("2020-01-01", periods=360, freq="D")
    log_rv = np.empty(len(index))
    log_rv[0] = -7.5
    for i in range(1, len(index)):
        log_rv[i] = -1.2 + 0.84 * log_rv[i - 1] + rng.normal(0.0, 0.12)
    rv = pd.Series(np.exp(log_rv), index=index, name="RV")
    downside_share = np.clip(0.55 + rng.normal(0.0, 0.05, len(index)), 0.2, 0.8)
    rv_neg = pd.Series(rv.to_numpy() * downside_share, index=index, name="RV_neg")
    rv_pos = pd.Series(rv.to_numpy() * (1.0 - downside_share), index=index, name="RV_pos")
    return rv_neg, rv_pos, rv


def test_walk_forward_predictions_align_and_are_finite(asymmetric_rv):
    rv_neg, rv_pos, rv = asymmetric_rv
    out = walk_forward_asymmetric_har(
        rv_neg,
        rv_pos,
        rv,
        horizon=1,
        n_splits=4,
        refit_every=22,
        calibrate_bias=True,
        calibration_size=40,
    )

    forecasts = out["forecasts"]
    targets = out["targets"]
    assert len(forecasts) == len(targets) > 0
    assert forecasts.index.equals(targets.index)
    assert np.isfinite(forecasts).all()
    assert np.isfinite(targets).all()
    assert np.isfinite(out["aggregate_mse_logrv"])


def test_ols_predictions_are_exactly_seed_stable(asymmetric_rv):
    rv_neg, rv_pos, rv = asymmetric_rv
    first = walk_forward_asymmetric_har(
        rv_neg, rv_pos, rv, n_splits=4, seed=0,
    )
    second = walk_forward_asymmetric_har(
        rv_neg, rv_pos, rv, n_splits=4, seed=99,
    )

    np.testing.assert_array_equal(first["forecasts"], second["forecasts"])
    np.testing.assert_array_equal(first["targets"], second["targets"])


def test_train_tail_calibration_returns_signed_forecast_bias(
    asymmetric_rv,
    monkeypatch,
):
    rv_neg, rv_pos, rv = asymmetric_rv
    constant_prediction = float(np.log(rv.iloc[-80:]).mean() + 0.4)

    monkeypatch.setattr(
        AsymmetricHARModel,
        "predict_h_step",
        lambda self, rv_neg_history, rv_pos_history, rv_history, horizon: (
            constant_prediction
        ),
    )
    _, bias = _fit_asymmetric_with_train_calibration(
        rv_neg,
        rv_pos,
        rv,
        horizon=1,
        calibration_size=60,
    )

    expected_targets = np.log(rv.iloc[-60:-1]).to_numpy()
    expected_bias = float(np.mean(constant_prediction - expected_targets))
    assert bias == pytest.approx(expected_bias)
    assert bias > 0.0


def test_eval_persists_strictly_aligned_predictions(asymmetric_rv, monkeypatch):
    rv_neg, rv_pos, rv = asymmetric_rv
    hours = pd.date_range(
        rv.index[0], periods=len(rv) * 24, freq="h",
    )
    hourly_returns = pd.Series(np.zeros(len(hours)), index=hours)
    monkeypatch.setattr(har_asymmetric, "daily_realized_variance", lambda _: rv)
    monkeypatch.setattr(
        har_asymmetric, "daily_semivariance_negative", lambda _: rv_neg,
    )
    monkeypatch.setattr(
        har_asymmetric, "daily_semivariance_positive", lambda _: rv_pos,
    )

    row = _eval_one_coin(
        "BTC-USD",
        hourly_returns,
        horizons=[1],
        seeds=[0],
        n_splits=4,
        refit_every=22,
        debias=True,
        calibration_size=40,
    )[0]

    n_predictions = row["n_predictions"]
    assert n_predictions > 0
    assert len(row["pred_dates"]) == n_predictions
    assert len(row["pred_asym"]) == n_predictions
    assert len(row["pred_classic_har"]) == n_predictions
    assert len(row["pred_target"]) == n_predictions
    assert np.isfinite(row["pred_asym"]).all()
    assert np.isfinite(row["pred_classic_har"]).all()
    assert np.isfinite(row["pred_target"]).all()
    assert row["debias"] is True


def _verdict_row(seed: int, asym_mse: float, classic_mse: float, pvalue: float) -> dict:
    return {
        "coin": "BTC-USD",
        "horizon": 1,
        "seed": seed,
        "asym_mse_logrv": asym_mse,
        "classic_mse_logrv": classic_mse,
        "dm_verdict": "MODEL BEATS BASELINE",
        "dm_pvalue": pvalue,
    }


def test_aggregate_marks_deterministic_seed_stability():
    rows = [
        _verdict_row(seed, 0.80, 1.0, 0.01)
        for seed in (0, 7, 42, 99)
    ]
    aggregate = aggregate_verdicts(rows)[0]

    assert aggregate["median_dm_pvalue"] < 0.05
    assert aggregate["seed_stable"] is True
    assert aggregate["edge_sigma"] is None
    assert aggregate["verdict"] == "BEATS"


def test_aggregate_rejects_significant_but_unstable_edge():
    rows = [
        _verdict_row(seed, asym_mse, 1.0, 0.01)
        for seed, asym_mse in zip((0, 7, 42, 99), (0.60, 1.20, 0.70, 1.10))
    ]
    aggregate = aggregate_verdicts(rows)[0]

    assert aggregate["edge_sigma"] < 2.0
    assert aggregate["verdict"] == "INCONCLUSIVE"
