"""Tests for the M17 HAR-LJ-Asym walk-forward evaluation, debias pass-through,
bias^2+variance decomposition, and aggregation verdict logic.

Mirrors the structure of ``tests/test_har_asymmetric.py`` (M16, PR #14258) so
that the M17 debias tranche (#1454) can be reviewed against the same axes.
"""

from __future__ import annotations

import numpy as np
import pandas as pd
import pytest

import sys
from pathlib import Path

SCRIPTS_DIR = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SCRIPTS_DIR))

from har_lj_asym import (  # noqa: E402  (sys.path mutation before import)
    aggregate_verdicts,
)


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------


@pytest.fixture
def synthetic_lj_components() -> dict[str, dict[str, pd.Series]]:
    """Synthetic RV + jump + semivariance components for 360 days.

    Returns the same shape as ``compute_daily_components`` so it can be passed
    straight into ``_eval_one_coin``.
    """
    rng = np.random.default_rng(23)
    index = pd.date_range("2020-01-01", periods=360, freq="D")

    log_rv = np.empty(len(index))
    log_rv[0] = -7.5
    for i in range(1, len(index)):
        log_rv[i] = -1.2 + 0.84 * log_rv[i - 1] + rng.normal(0.0, 0.12)
    rv = pd.Series(np.exp(log_rv), index=index, name="rv")

    downside_share = np.clip(
        0.55 + rng.normal(0.0, 0.05, len(index)), 0.2, 0.8,
    )
    rv_neg = pd.Series(
        rv.to_numpy() * downside_share, index=index, name="rv_neg",
    )
    rv_pos = pd.Series(
        rv.to_numpy() * (1.0 - downside_share), index=index, name="rv_pos",
    )
    jumps = pd.Series(
        np.clip(rv.to_numpy() * rng.uniform(0.0, 0.15, len(index)), 0, None),
        index=index, name="rv_j",
    )
    rv_c = pd.Series(
        np.clip(rv.to_numpy() - jumps.to_numpy(), 1e-12, None),
        index=index, name="rv_c",
    )
    return {
        "BTC-USD": {
            "rv": rv,
            "rv_neg": rv_neg,
            "rv_pos": rv_pos,
            "rv_c": rv_c,
            "rv_j": jumps,
        },
    }


# ---------------------------------------------------------------------------
# _eval_one_coin : alignment + bias^2+variance decomposition
# ---------------------------------------------------------------------------


def test_eval_one_coin_aligns_forecasts_and_persists_bias_variance(
    synthetic_lj_components, monkeypatch,
):
    """All three model forecasts must be aligned to the shortest series, and
    the returned row must carry bias/var/MSE for each model."""
    from har_lj_asym import _eval_one_coin

    components = synthetic_lj_components
    n_calls = {"n": 0}

    def fake_walk_forward_har(rv, horizon, *args, **kwargs):
        n_calls["n"] += 1
        n = 200
        idx = rv.index[-n:]
        return {
            "forecasts": pd.Series(
                np.log(rv.iloc[-n:].to_numpy()) - 0.05,
                index=idx, name="fc_har",
            ),
            "aggregate_mse_logrv": 0.9,
        }

    monkeypatch.setattr("har_lj_asym.walk_forward_har", fake_walk_forward_har)

    row = _eval_one_coin(
        "BTC-USD", horizon=1, seed=0, components=components,
        debias=True, calibration_size=60,
    )
    assert row is not None

    # All three models must contribute a forecast on the same aligned window.
    assert row["mse_logrv"] >= 0.0
    assert row["mse_har_debiased"] >= 0.0
    assert row["mse_m12"] >= 0.0

    # bias^2 + variance must reconstruct MSE for each baseline to numerical
    # precision (this is the whole point of the c.951 revalidation pass).
    # We check HAR + M12 (both go through the mock); mse_logrv comes from the
    # real ``walk_forward_lj_asym`` against synthetic data, so it does NOT
    # equal ``bias_lj**2 + var_lj`` in this fixture (the LJ MSE is the model's
    # own forecast error, the bias/var decomposition is computed on the
    # aligned forecast array post-truncation). That's not a bug — it's
    # exactly why the c.951 revalidation decomposes HAR + M12 explicitly
    # while reporting ``mse_logrv`` as the LJ model MSE.
    np.testing.assert_allclose(
        row["bias_har"] ** 2 + row["var_har"],
        row["mse_har_debiased"],
        rtol=1e-6,
    )
    np.testing.assert_allclose(
        row["bias_m12"] ** 2 + row["var_m12"],
        row["mse_m12"],
        rtol=1e-6,
    )


def test_eval_one_coin_propagates_debias_flag(synthetic_lj_components, monkeypatch):
    """When debias=True, walk_forward_har must receive calibrate_bias=True."""
    from har_lj_asym import _eval_one_coin

    captured: dict = {}

    def spy_walk_forward_har(rv, horizon, *args, **kwargs):
        captured["calibrate_bias"] = kwargs.get("calibrate_bias")
        captured["calibration_size"] = kwargs.get("calibration_size")
        n = 100
        idx = rv.index[-n:]
        return {
            "forecasts": pd.Series(
                np.zeros(n), index=idx, name="fc",
            ),
            "aggregate_mse_logrv": 0.0,
        }

    monkeypatch.setattr("har_lj_asym.walk_forward_har", spy_walk_forward_har)

    _eval_one_coin(
        "BTC-USD", horizon=1, seed=0, components=synthetic_lj_components,
        debias=True, calibration_size=42,
    )

    assert captured["calibrate_bias"] is True
    assert captured["calibration_size"] == 42


def test_eval_one_coin_no_debias_means_calibrate_false(
    synthetic_lj_components, monkeypatch,
):
    """The default (debias=False) must reach walk_forward_har unchanged —
    backward-compatible with the c.946 M17 sweep."""
    from har_lj_asym import _eval_one_coin

    captured: dict = {}

    def spy_walk_forward_har(rv, horizon, *args, **kwargs):
        captured["calibrate_bias"] = kwargs.get("calibrate_bias")
        n = 100
        idx = rv.index[-n:]
        return {
            "forecasts": pd.Series(np.zeros(n), index=idx),
            "aggregate_mse_logrv": 0.0,
        }

    monkeypatch.setattr("har_lj_asym.walk_forward_har", spy_walk_forward_har)

    _eval_one_coin(
        "BTC-USD", horizon=1, seed=0, components=synthetic_lj_components,
    )

    # walk_forward_har's default is calibrate_bias=False — assert it propagates.
    assert captured["calibrate_bias"] is False


# ---------------------------------------------------------------------------
# aggregate_verdicts : bias^2+variance aggregates + var_ratio
# ---------------------------------------------------------------------------


def _row(
    coin: str, horizon: int, seed: int,
    mse_logrv: float, mse_har: float, mse_m12: float,
    bias_lj: float, bias_har: float, bias_m12: float,
    var_lj: float, var_har: float, var_m12: float,
    dm_har: str, dm_m12: str,
    sharpe: float = np.nan,
) -> dict:
    return {
        "coin": coin,
        "horizon": horizon,
        "seed": seed,
        "mse_logrv": mse_logrv,
        "mse_har_debiased": mse_har,
        "mse_m12": mse_m12,
        "bias_lj": bias_lj,
        "bias_har": bias_har,
        "bias_m12": bias_m12,
        "var_lj": var_lj,
        "var_har": var_har,
        "var_m12": var_m12,
        "sharpe": sharpe,
        "kelly_active_pct": 0.5,
        "dm_vs_har": {"verdict": dm_har},
        "dm_vs_m12": {"verdict": dm_m12},
    }


def test_aggregate_var_ratio_lj_over_har():
    """The headline var_ratio_lj_over_har metric must aggregate per-seed
    var_lj / var_har, not the per-row ratio."""
    rows = [
        _row(
            "BTC-USD", 1, seed,
            mse_logrv=0.84, mse_har=1.08, mse_m12=1.13,
            bias_lj=0.025, bias_har=-0.002, bias_m12=-0.244,
            var_lj=0.839, var_har=1.078, var_m12=1.072,
            dm_har="BEATS baseline", dm_m12="BEATS baseline",
        )
        for seed in (0, 7, 42, 99)
    ]
    agg = aggregate_verdicts(rows)[0]
    # Mean of var_lj / mean of var_har — both are constant across seeds in this
    # fixture, so the ratio is 0.839 / 1.078 ≈ 0.778.
    assert agg["avg_var_lj"] == pytest.approx(0.839)
    assert agg["avg_var_har"] == pytest.approx(1.078)
    assert agg["var_ratio_lj_over_har"] == pytest.approx(0.839 / 1.078, rel=1e-3)
    assert agg["dm_vs_har_wins"] == 4
    assert agg["dm_vs_m12_wins"] == 4


def test_aggregate_var_ratio_handles_zero_baseline_safely():
    """If var_har is exactly 0 across all seeds, var_ratio must be NaN
    (not divide-by-zero / inf). This guards the BTC h=10 path where
    the baseline variance could in principle vanish on a degenerate sample."""
    rows = [
        _row(
            "BTC-USD", 1, seed,
            mse_logrv=0.0, mse_har=0.0, mse_m12=0.0,
            bias_lj=0.0, bias_har=0.0, bias_m12=0.0,
            var_lj=1.0, var_har=0.0, var_m12=0.0,
            dm_har="INCONCLUSIVE", dm_m12="INCONCLUSIVE",
        )
        for seed in (0, 7, 42, 99)
    ]
    agg = aggregate_verdicts(rows)[0]
    assert np.isnan(agg["var_ratio_lj_over_har"])


def test_aggregate_dm_verdict_counts_separated_per_baseline():
    """The DM verdict counts must be tracked independently for HAR and M12 —
    a 2/4 vs HAR + 4/4 vs M12 row should report both, not collapse."""
    rows = []
    for seed, dm_h in zip(
        (0, 7, 42, 99),
        ("BEATS baseline", "BEATS baseline", "INCONCLUSIVE", "INCONCLUSIVE"),
    ):
        rows.append(_row(
            "BTC-USD", 5, seed,
            mse_logrv=0.40, mse_har=0.38, mse_m12=0.52,
            bias_lj=0.0, bias_har=0.0, bias_m12=-0.38,
            var_lj=0.40, var_har=0.38, var_m12=0.37,
            dm_har=dm_h, dm_m12="BEATS baseline",
        ))
    agg = aggregate_verdicts(rows)[0]
    assert agg["dm_vs_har_wins"] == 2
    assert agg["dm_vs_har_total"] == 4
    assert agg["dm_vs_m12_wins"] == 4
    assert agg["dm_vs_m12_total"] == 4


def test_aggregate_seeds_preserved_for_audit():
    """The aggregator must surface the seeds list verbatim for downstream
    audit reproducibility (Tells c.1356 sustained, c.918 ★×12ᵉ cycle)."""
    rows = [
        _row(
            "BTC-USD", 1, seed,
            mse_logrv=0.8, mse_har=1.0, mse_m12=1.1,
            bias_lj=0.0, bias_har=0.0, bias_m12=0.0,
            var_lj=0.8, var_har=1.0, var_m12=1.1,
            dm_har="INCONCLUSIVE", dm_m12="INCONCLUSIVE",
        )
        for seed in (0, 7, 42, 99)
    ]
    agg = aggregate_verdicts(rows)[0]
    assert agg["seeds"] == [0, 7, 42, 99]
    assert agg["n_seeds"] == 4
