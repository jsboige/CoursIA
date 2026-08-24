"""Regression tests for calibrated HAR evidence in dlinear_vol (#12684)."""

from __future__ import annotations

import numpy as np
import pandas as pd
import pytest

from dlinear_vol import _edge_pct, _mse_without_bias, aggregate_verdicts
from har_model import walk_forward_har


def test_debiased_edge_exposes_mean_recalibration_inversion() -> None:
    target = np.zeros(200)
    har_error = np.tile([-1.0, 1.0], 100) - 0.5
    model_error = np.tile([-1.05, 1.05], 100)

    har_mse = float(np.mean(har_error**2))
    model_mse = float(np.mean(model_error**2))
    raw_edge = _edge_pct(har_mse, model_mse)
    debiased_edge = _edge_pct(
        _mse_without_bias(har_error),
        _mse_without_bias(model_error),
    )

    assert target.shape == har_error.shape
    assert raw_edge > 0.0
    assert debiased_edge < 0.0


def _inverted_rows(calibrated_verdict: str) -> list[dict]:
    return [{
        "coin": "SPY",
        "horizon": 1,
        "seed": seed,
        "dlinear_mse_logrv": 0.80,
        "har_mse_logrv": 1.00,
        "har_calibrated_mse_logrv": 0.75,
        "mse_reduction_pct": 20.0,
        "edge_debiased_pct": -6.0,
        "calibrated_edge_pct": -6.67,
        "calibrated_dm_pvalue": 0.01,
        "calibrated_dm_verdict": calibrated_verdict,
    } for seed in (0, 1, 7, 42)]


def test_aggregate_verdict_uses_calibrated_baseline() -> None:
    result = aggregate_verdicts(_inverted_rows("BEATEN BY baseline"))[0]

    assert result["mean_reduction_pct"] == pytest.approx(20.0)
    assert result["calibrated_edge_pct"] < 0.0
    assert result["mean_debiased_edge_pct"] < 0.0
    assert result["verdict_sc"] == "NO BEATS"


def test_conjunction_rejects_positive_raw_but_negative_calibrated_edge() -> None:
    result = aggregate_verdicts(_inverted_rows("INCONCLUSIVE"))[0]

    assert result["mean_reduction_pct"] > 0.0
    assert result["calibrated_edge_pct"] < 0.0
    assert result["dm_p_median"] < 0.05
    assert result["verdict_sc"] == "INCONCLUSIVE"


def test_har_calibration_is_estimated_from_train_only() -> None:
    rng = np.random.default_rng(12684)
    n = 420
    log_rv = np.cumsum(rng.normal(0.0, 0.03, n)) - 7.0
    rv = pd.Series(
        np.exp(log_rv),
        index=pd.date_range("2020-01-01", periods=n, freq="D"),
    )

    base = walk_forward_har(
        rv, horizon=1, n_splits=4, refit_every=22,
        calibrate_bias=True, calibration_size=45,
    )
    mutated = rv.copy()
    first_test_start = n // 5
    mutated.iloc[first_test_start:] *= np.exp(2.0)
    changed = walk_forward_har(
        mutated, horizon=1, n_splits=4, refit_every=22,
        calibrate_bias=True, calibration_size=45,
    )

    assert base["calibrate_bias"] is True
    assert base["calibration_size"] == 45
    base_biases = base["initial_calibration_bias_by_fold"]
    changed_biases = changed["initial_calibration_bias_by_fold"]
    assert len(base_biases) == 4
    assert abs(base_biases[0]) > 0.0
    assert base_biases[0] == pytest.approx(changed_biases[0])
    assert base["aggregate_mse_logrv"] != pytest.approx(
        changed["aggregate_mse_logrv"],
    )
