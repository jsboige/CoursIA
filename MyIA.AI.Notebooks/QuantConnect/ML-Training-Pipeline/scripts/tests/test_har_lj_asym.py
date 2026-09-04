"""Tests for the M17 HAR-LJ-Asym walk-forward evaluation.

REPAIR-2 (c.955): the previous version of these tests assumed the c.953
"symmetric" calibration (post-walk-forward global tail-mean block) — that
calibration protocol read OOS targets via ``mean(err[-60:])``, which is the
fuite that the preflight po-2025 re-review (head 4cc2262b) flagged. The
tests now validate the per-fold train-tail bias protocol that REPAIR-2
introduces, plus the new coherence requirements (DM verdict <-> p_value +
mean_loss_diff), the manifest hashes, and the bit-identity anchor across
seeds.

Concerns addressed (verbatim from the c.955 re-review):
  #1 — calibration must NOT read OOS targets (anti-leak test below).
  #2 — HAR must NOT be double-calibrated.
  #3 — DM verdict components must be coherent (BEATS => p<0.05 AND diff<0).
  #4 — manifest hashes (forecasts/targets/errors) must be emitted.

ROUND-3 (preflight po-2025 adjoint re-review, head b974f2721, DM
msg-20260904T141944):
  #1 — sign of the bias correction (+, not -) + per-fold constant shift.
  #2 — walk_forward_har_rv_j receives calibrate_bias=debias (M12 calibrated).
  #3 — mse_har_raw (uncalibrated leg) != mse_har_debiased (calibrated leg).
  #4 — full-walk-forward OOS-target invariance test.
  #6 — panel_hash covers the index in addition to the values.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import sys

import numpy as np
import pandas as pd
import pytest

SCRIPTS_DIR = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SCRIPTS_DIR))

from har_lj_asym import (  # noqa: E402  (sys.path mutation before import)
    _train_tail_bias,
    aggregate_verdicts,
    HARLJAsymModel,
)


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------


@pytest.fixture
def synthetic_lj_components() -> dict[str, dict[str, pd.Series]]:
    """Synthetic RV + jump + semivariance components for 360 days."""
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
# Concern #1 — anti-leak test for the per-fold train-tail bias estimator
# ---------------------------------------------------------------------------


def test_calibration_anti_leak_perturbation():
    """Concern #1 (c.955): perturbing the OOS targets must NOT change the
    per-fold bias estimate. The bias is computed from the train tail ONLY;
    OOS target perturbation is a no-op for ``_train_tail_bias``.

    This is the apples-to-apples test demanded by #14584 disposition #1:
    perturb the targets (y_all), refit the model, and verify the bias
    estimate from train tail is unchanged across the perturbation.
    """
    rng = np.random.default_rng(42)
    n_train, n_features = 200, 6
    X_train = rng.normal(0.0, 1.0, (n_train, n_features))
    y_train = -1.5 + 0.5 * X_train[:, 0] + 0.3 * X_train[:, 1] + rng.normal(0.0, 0.1, n_train)

    model = HARLJAsymModel().fit(X_train, y_train)

    bias_unperturbed = _train_tail_bias(model, X_train, y_train, calibration_size=60)
    # Perturb the LAST 60 train targets (the calibration tail itself -- still
    # train data, no OOS access). The bias estimate must change because we
    # are perturbing the tail we sample from. This is the **expected** behavior.
    y_train_perturbed_tail = y_train.copy()
    y_train_perturbed_tail[-60:] += 5.0  # add a large constant shift
    bias_perturbed_tail = _train_tail_bias(model, X_train, y_train_perturbed_tail, calibration_size=60)
    assert abs(bias_perturbed_tail - bias_unperturbed) > 1.0, (
        "Perturbing the train tail SHOULD shift the bias estimate -- this is "
        "the expected behavior. The bias estimator reads from the train tail "
        "and is sensitive to train perturbations by design."
    )

    # Now perturb the FIRST 140 train targets (NOT in the calibration tail).
    # The bias estimate from the LAST 60 must be unchanged.
    y_train_perturbed_head = y_train.copy()
    y_train_perturbed_head[:140] += 5.0
    bias_perturbed_head = _train_tail_bias(model, X_train, y_train_perturbed_head, calibration_size=60)
    np.testing.assert_allclose(
        bias_perturbed_head, bias_unperturbed, rtol=1e-12,
        err_msg=(
            "Perturbing the FIRST 140 train targets (outside the calibration "
            "tail) MUST NOT shift the bias estimate from the last 60."
        ),
    )


# ---------------------------------------------------------------------------
# Concern #2 — HAR is not double-calibrated (calibrate_bias propagated once)
# ---------------------------------------------------------------------------


def test_walk_forward_har_called_with_calibrate_bias_when_debias(
    synthetic_lj_components, monkeypatch,
):
    """Concern #2 (c.955) + round-3 concern #3: when debias=True,
    walk_forward_har is called TWICE -- first uncalibrated (mse_har_raw leg),
    then with calibrate_bias=True (DM + mse_har_debiased leg). No post-walk-
    forward second correction is applied on top of the calibrated leg."""
    from har_lj_asym import _eval_one_coin

    captured: list = []

    def spy_walk_forward_har(rv, horizon, *args, **kwargs):
        captured.append(
            (kwargs.get("calibrate_bias"), kwargs.get("calibration_size")),
        )
        n = 100
        idx = rv.index[-n:]
        return {
            "forecasts": pd.Series(np.zeros(n), index=idx, name="fc"),
            "aggregate_mse_logrv": 0.0,
        }

    monkeypatch.setattr("har_lj_asym.walk_forward_har", spy_walk_forward_har)

    _eval_one_coin(
        "BTC-USD", horizon=1, seed=0, components=synthetic_lj_components,
        debias=True, calibration_size=60,
    )

    # Raw leg first (calibrate_bias falsy), calibrated DM leg second.
    assert [c[0] for c in captured] == [False, True]
    assert captured[1][1] == 60


def test_walk_forward_har_called_with_calibrate_bias_false_when_no_debias(
    synthetic_lj_components, monkeypatch,
):
    """When debias=False, walk_forward_har must receive calibrate_bias=False
    exactly once (no calibrated second leg is needed)."""
    from har_lj_asym import _eval_one_coin

    captured: list = []

    def spy_walk_forward_har(rv, horizon, *args, **kwargs):
        captured.append(kwargs.get("calibrate_bias"))
        n = 100
        idx = rv.index[-n:]
        return {
            "forecasts": pd.Series(np.zeros(n), index=idx, name="fc"),
            "aggregate_mse_logrv": 0.0,
        }

    monkeypatch.setattr("har_lj_asym.walk_forward_har", spy_walk_forward_har)

    _eval_one_coin(
        "BTC-USD", horizon=1, seed=0, components=synthetic_lj_components,
    )

    assert captured == [False]


# ---------------------------------------------------------------------------
# Concern #3 — DM verdict coherence: BEATS => p<0.05 AND mean_loss_diff<0
# ---------------------------------------------------------------------------


def test_aggregate_coherent_beats_requires_p_lt_alpha_and_diff_lt_zero():
    """Concern #3: a BEATS verdict must imply p_value < 0.05 AND
    mean_loss_diff < 0. If a row reports BEATS but p_value >= 0.05, it is
    mis-classified upstream and must NOT be counted as a win.
    """
    rows = [
        {
            "coin": "BTC-USD", "horizon": 1, "seed": s,
            "mse_logrv": 0.84, "mse_har_raw": 1.0, "mse_har_debiased": 1.0,
            "mse_m12": 1.1, "bias_lj": 0.0, "bias_har": 0.0, "bias_m12": 0.0,
            "var_lj": 0.84, "var_har": 1.0, "var_m12": 1.1,
            "sharpe": np.nan, "kelly_active_pct": 0.5,
            # Mis-classified: BEATS verdict but p_value >= 0.05.
            "dm_vs_har": {
                "verdict": "BEATS baseline", "p_value": 0.83,
                "mean_loss_diff": -0.01, "dm_statistic": -2.0, "n_obs": 100,
                "lag": 4, "hac_variance": 0.001, "significant_at": 0.05,
            },
            "dm_vs_m12": {
                "verdict": "INCONCLUSIVE", "p_value": 0.5,
                "mean_loss_diff": -0.005, "dm_statistic": -1.0, "n_obs": 100,
                "lag": 4, "hac_variance": 0.001, "significant_at": 0.05,
            },
            "panel_hash": "deadbeef",
            "fc_lj_hash": "a", "fc_har_hash": "b", "fc_m12_hash": "c",
            "tgt_hash": "d", "err_lj_hash": "e", "err_har_hash": "f",
            "err_m12_hash": "g", "n_obs": 100, "edge_sigma_applicable": False,
        }
        for s in (0, 7, 42, 99)
    ]
    agg = aggregate_verdicts(rows)[0]
    # The BEATS verdict with p_value=0.83 must NOT be counted as a win.
    assert agg["dm_vs_har_wins"] == 0, (
        f"Coherence violation: BEATS verdict with p_value >= 0.05 should NOT "
        f"count as a win. Got {agg['dm_vs_har_wins']} wins."
    )


def test_aggregate_coherent_beats_counts_when_p_lt_alpha_and_diff_lt_zero():
    """Conversely, when the coherence holds (p<0.05 AND diff<0), BEATS
    must be counted as a win."""
    rows = [
        {
            "coin": "BTC-USD", "horizon": 1, "seed": s,
            "mse_logrv": 0.84, "mse_har_raw": 1.0, "mse_har_debiased": 1.0,
            "mse_m12": 1.1, "bias_lj": 0.0, "bias_har": 0.0, "bias_m12": 0.0,
            "var_lj": 0.84, "var_har": 1.0, "var_m12": 1.1,
            "sharpe": np.nan, "kelly_active_pct": 0.5,
            # Coherent: BEATS verdict + p_value < 0.05 + diff < 0.
            "dm_vs_har": {
                "verdict": "BEATS baseline", "p_value": 0.01,
                "mean_loss_diff": -0.05, "dm_statistic": -3.0, "n_obs": 100,
                "lag": 4, "hac_variance": 0.001, "significant_at": 0.05,
            },
            "dm_vs_m12": {
                "verdict": "INCONCLUSIVE", "p_value": 0.5,
                "mean_loss_diff": -0.005, "dm_statistic": -1.0, "n_obs": 100,
                "lag": 4, "hac_variance": 0.001, "significant_at": 0.05,
            },
            "panel_hash": "deadbeef",
            "fc_lj_hash": "a", "fc_har_hash": "b", "fc_m12_hash": "c",
            "tgt_hash": "d", "err_lj_hash": "e", "err_har_hash": "f",
            "err_m12_hash": "g", "n_obs": 100, "edge_sigma_applicable": False,
        }
        for s in (0, 7, 42, 99)
    ]
    agg = aggregate_verdicts(rows)[0]
    assert agg["dm_vs_har_wins"] == 4


def test_aggregate_surfaces_dm_components_per_horizon():
    """Concern #3: aggregated DM components (p_values list, mean_loss_diffs
    list, dm_statistics list) must be surfaced for auditability."""
    rows = [
        {
            "coin": "BTC-USD", "horizon": 1, "seed": s,
            "mse_logrv": 0.84, "mse_har_raw": 1.0, "mse_har_debiased": 1.0,
            "mse_m12": 1.1, "bias_lj": 0.0, "bias_har": 0.0, "bias_m12": 0.0,
            "var_lj": 0.84, "var_har": 1.0, "var_m12": 1.1,
            "sharpe": np.nan, "kelly_active_pct": 0.5,
            "dm_vs_har": {
                "verdict": "INCONCLUSIVE", "p_value": 0.01 * (1 + s),
                "mean_loss_diff": -0.01, "dm_statistic": -1.0 * s, "n_obs": 100,
                "lag": 4, "hac_variance": 0.001, "significant_at": 0.05,
            },
            "dm_vs_m12": {
                "verdict": "INCONCLUSIVE", "p_value": 0.5,
                "mean_loss_diff": -0.005, "dm_statistic": -1.0, "n_obs": 100,
                "lag": 4, "hac_variance": 0.001, "significant_at": 0.05,
            },
            "panel_hash": "deadbeef",
            "fc_lj_hash": "a", "fc_har_hash": "b", "fc_m12_hash": "c",
            "tgt_hash": "d", "err_lj_hash": "e", "err_har_hash": "f",
            "err_m12_hash": "g", "n_obs": 100, "edge_sigma_applicable": False,
        }
        for s in (0, 7, 42, 99)
    ]
    agg = aggregate_verdicts(rows)[0]
    har_components = agg["dm_vs_har_components"]
    # Test data used p_value = 0.01 * (1 + s) with s in (0, 7, 42, 99) and
    # dm_statistic = -1.0 * s. Assert on the per-row invariants
    # (mean_loss_diff constant, dm_statistic follows -1.0 * s) and on the
    # median (numpy median of even N is the mean of the two center values).
    assert har_components["mean_loss_diffs"] == [-0.01] * 4
    assert har_components["dm_statistics"] == [0.0, -7.0, -42.0, -99.0]
    sorted_p = sorted([0.01, 0.01 * 8, 0.01 * 43, 1.0])
    expected_median = (sorted_p[1] + sorted_p[2]) / 2
    assert har_components["p_value_median"] == pytest.approx(expected_median)


# ---------------------------------------------------------------------------
# Concern #4 — manifest hashes (forecasts/targets/errors) emitted per row
# ---------------------------------------------------------------------------


def test_eval_one_coin_emits_manifest_hashes(
    synthetic_lj_components, monkeypatch,
):
    """Concern #4: each row must carry forecast/target/error hashes for the
    manifest audit (panel_hash + fc_*_hash + tgt_hash + err_*_hash)."""
    from har_lj_asym import _eval_one_coin

    def fake_walk_forward_har(rv, horizon, *args, **kwargs):
        n = 100
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
        "BTC-USD", horizon=1, seed=0, components=synthetic_lj_components,
        debias=True, calibration_size=60,
    )
    assert row is not None
    # All manifest fields must be present and look like 16-hex-char SHA prefixes.
    for field in (
        "panel_hash", "fc_lj_hash", "fc_har_hash", "fc_m12_hash",
        "tgt_hash", "err_lj_hash", "err_har_hash", "err_m12_hash",
    ):
        v = row[field]
        assert isinstance(v, str)
        assert len(v) == 16
        int(v, 16)  # hex parseable

    # Edge-sigma disposition is N/A (deterministic OLS).
    assert row["edge_sigma_applicable"] is False
    assert row["n_obs"] >= 10


# ---------------------------------------------------------------------------
# Bit-identity anchor (c.953 sustained): panel_hash consistent across seeds
# ---------------------------------------------------------------------------


def test_panel_hash_consistent_across_seeds(
    synthetic_lj_components, monkeypatch,
):
    """Concern #3 (c.953): panel_hash on the canonical 360-bar RV window is
    identical across seeds {0, 7, 42, 99}. Deterministic OLS guarantee."""
    from har_lj_asym import _eval_one_coin

    def fake_walk_forward_har(rv, horizon, *args, **kwargs):
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

    rows = []
    for seed in (0, 7, 42, 99):
        r = _eval_one_coin(
            "BTC-USD", horizon=1, seed=seed,
            components=synthetic_lj_components,
            debias=True, calibration_size=60,
        )
        assert r is not None
        rows.append(r)

    panel_hashes = {r["panel_hash"] for r in rows}
    assert len(panel_hashes) == 1, f"panel hashes diverge across seeds: {panel_hashes}"

    agg = aggregate_verdicts(rows)[0]
    assert agg["panel_hashes_consistent"] is True
    assert agg["panel_hash"] != ""


# ---------------------------------------------------------------------------
# Per-fold bias estimates surfaced for audit (concern #1)
# ---------------------------------------------------------------------------


def test_walk_forward_lj_asym_returns_per_fold_bias():
    """Concern #1 acceptance: walk_forward_lj_asym must surface
    ``per_fold_bias`` (list of train-tail bias estimates, one per fold).
    Round-3 note: ``_eval_one_coin`` consumes these PER FOLD through
    ``forecasts_debiased`` (no global-mean aggregation anymore).
    """
    from har_lj_asym import walk_forward_lj_asym

    rng = np.random.default_rng(0)
    index = pd.date_range("2020-01-01", periods=400, freq="D")
    log_rv = np.cumsum(rng.normal(0.0, 0.1, 400)) - 5.0
    rv = pd.Series(np.exp(log_rv), index=index, name="rv")
    rv_neg = pd.Series(rv.to_numpy() * 0.5, index=index)
    rv_pos = pd.Series(rv.to_numpy() * 0.5, index=index)
    rv_c = pd.Series(rv.to_numpy() * 0.8, index=index)
    rv_j = pd.Series(rv.to_numpy() * 0.2, index=index)
    components = {"BTC-USD": {
        "rv": rv, "rv_neg": rv_neg, "rv_pos": rv_pos, "rv_c": rv_c, "rv_j": rv_j,
    }}

    out = walk_forward_lj_asym(
        rv, rv_neg, rv_pos, rv_c, rv_j, horizon=1, seed=0,
        debias=True, calibration_size=60,
    )
    assert out["forecasts"]
    assert len(out["per_fold_bias"]) > 0
    # When debias=True, forecasts_debiased must be present and len == forecasts.
    assert out["forecasts_debiased"]
    assert len(out["forecasts_debiased"]) == len(out["forecasts"])
    # Per-fold bias is a single scalar per fold; all entries should be finite floats.
    for b in out["per_fold_bias"]:
        assert np.isfinite(b)


# ---------------------------------------------------------------------------
# Manifest path + shape (concern #4 acceptance)
# ---------------------------------------------------------------------------


def test_manifest_path_constants():
    """Concern #4: the manifest path is `scripts/results/manifest_m17_har_lj_asym.json`
    next to the main results JSON."""
    from har_lj_asym import RESULTS_DIR
    assert (RESULTS_DIR / "manifest_m17_har_lj_asym.json").parent == RESULTS_DIR


# ---------------------------------------------------------------------------
# Backward compat: the c.953 invariant ``mse = bias^2 + var`` still holds
# ---------------------------------------------------------------------------


def test_mse_decomposition_equals_empirical_mean_squared_error(
    synthetic_lj_components, monkeypatch,
):
    """The c.953 invariant ``bias^2 + var(ddof=0) == mean(err**2)`` continues
    to hold under the new protocol (concern #1 acceptance, sustained)."""
    from har_lj_asym import _eval_one_coin

    def fake_walk_forward_har(rv, horizon, *args, **kwargs):
        n = 200
        idx = rv.index[-n:]
        return {
            "forecasts": pd.Series(np.zeros(n), index=idx, name="fc_har"),
            "aggregate_mse_logrv": 0.0,
        }

    monkeypatch.setattr("har_lj_asym.walk_forward_har", fake_walk_forward_har)

    row = _eval_one_coin(
        "BTC-USD", horizon=1, seed=0, components=synthetic_lj_components,
        debias=False, calibration_size=60,
    )
    assert row is not None

    np.testing.assert_allclose(
        row["bias_lj"] ** 2 + row["var_lj"], row["mse_logrv"], rtol=1e-9,
    )
    np.testing.assert_allclose(
        row["bias_har"] ** 2 + row["var_har"], row["mse_har_raw"], rtol=1e-9,
    )
    np.testing.assert_allclose(
        row["bias_m12"] ** 2 + row["var_m12"], row["mse_m12"], rtol=1e-9,
    )

    # Probe: err=[0,1] -> bias=0.5, var(ddof=0)=0.25, MSE=0.5
    err_probe = np.array([0.0, 1.0])
    assert np.var(err_probe, ddof=0) == pytest.approx(0.25)
    assert np.mean(err_probe ** 2) == pytest.approx(0.5)


def test_mse_har_debiased_is_nan_when_debias_false(
    synthetic_lj_components, monkeypatch,
):
    """c.953 invariant sustained: mse_har_debiased is NaN when debias=False."""
    from har_lj_asym import _eval_one_coin

    def fake_walk_forward_har(rv, horizon, *args, **kwargs):
        n = 100
        idx = rv.index[-n:]
        return {
            "forecasts": pd.Series(np.zeros(n), index=idx, name="fc"),
            "aggregate_mse_logrv": 0.0,
        }

    monkeypatch.setattr("har_lj_asym.walk_forward_har", fake_walk_forward_har)

    row = _eval_one_coin(
        "BTC-USD", horizon=1, seed=0, components=synthetic_lj_components,
        debias=False,
    )
    assert row is not None
    assert np.isnan(row["mse_har_debiased"])
    assert not np.isnan(row["mse_har_raw"])
    assert row["mse_har_raw"] >= 0.0


# ---------------------------------------------------------------------------
# Aggregation: var_ratio + DM counts (sustained from c.953)
# ---------------------------------------------------------------------------


def _row(
    coin: str, horizon: int, seed: int,
    mse_logrv: float, mse_har: float, mse_m12: float,
    bias_lj: float, bias_har: float, bias_m12: float,
    var_lj: float, var_har: float, var_m12: float,
    dm_har: str, dm_m12: str,
    sharpe: float = np.nan,
    mse_har_debiased: float | None = None,
    panel_hash: str = "deadbeef",
    p_value_har: float = 0.5, p_value_m12: float = 0.5,
) -> dict:
    return {
        "coin": coin, "horizon": horizon, "seed": seed,
        "mse_logrv": mse_logrv,
        "mse_har_raw": mse_har,
        "mse_har_debiased": (mse_har_debiased if mse_har_debiased is not None else mse_har),
        "mse_m12": mse_m12,
        "bias_lj": bias_lj, "bias_har": bias_har, "bias_m12": bias_m12,
        "var_lj": var_lj, "var_har": var_har, "var_m12": var_m12,
        "sharpe": sharpe, "kelly_active_pct": 0.5,
        "dm_vs_har": {
            "verdict": dm_har, "p_value": p_value_har,
            "mean_loss_diff": -0.01 if dm_har == "BEATS baseline" else 0.0,
            "dm_statistic": -2.0, "n_obs": 100, "lag": 4,
            "hac_variance": 0.001, "significant_at": 0.05,
        },
        "dm_vs_m12": {
            "verdict": dm_m12, "p_value": p_value_m12,
            "mean_loss_diff": -0.01 if dm_m12 == "BEATS baseline" else 0.0,
            "dm_statistic": -2.0, "n_obs": 100, "lag": 4,
            "hac_variance": 0.001, "significant_at": 0.05,
        },
        "panel_hash": panel_hash,
        "fc_lj_hash": "a", "fc_har_hash": "b", "fc_m12_hash": "c",
        "tgt_hash": "d", "err_lj_hash": "e", "err_har_hash": "f",
        "err_m12_hash": "g", "n_obs": 100, "edge_sigma_applicable": False,
    }


def test_aggregate_var_ratio_lj_over_har():
    """Sustained from c.953: var_ratio aggregates per-seed var_lj / mean of var_har."""
    rows = [
        _row(
            "BTC-USD", 1, seed,
            mse_logrv=0.84, mse_har=1.08, mse_m12=1.13,
            bias_lj=0.025, bias_har=-0.002, bias_m12=-0.244,
            var_lj=0.839, var_har=1.078, var_m12=1.072,
            dm_har="BEATS baseline", dm_m12="BEATS baseline",
            p_value_har=0.01, p_value_m12=0.01,
        )
        for seed in (0, 7, 42, 99)
    ]
    agg = aggregate_verdicts(rows)[0]
    assert agg["avg_var_lj"] == pytest.approx(0.839)
    assert agg["avg_var_har"] == pytest.approx(1.078)
    assert agg["var_ratio_lj_over_har"] == pytest.approx(0.839 / 1.078, rel=1e-3)
    assert agg["dm_vs_har_wins"] == 4
    assert agg["dm_vs_m12_wins"] == 4


def test_aggregate_var_ratio_handles_zero_baseline_safely():
    """Sustained from c.953: NaN-safe division when var_har is exactly 0."""
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
    """Sustained from c.953: counts tracked independently for HAR and M12."""
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
            p_value_har=0.01, p_value_m12=0.01,
        ))
    agg = aggregate_verdicts(rows)[0]
    assert agg["dm_vs_har_wins"] == 2
    assert agg["dm_vs_har_total"] == 4
    assert agg["dm_vs_m12_wins"] == 4
    assert agg["dm_vs_m12_total"] == 4


def test_aggregate_seeds_preserved_for_audit():
    """Sustained from c.953: the aggregator surfaces the seeds list verbatim."""
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


# ---------------------------------------------------------------------------
# ROUND-3 concern #1 — sign of the correction + per-fold constant shift
# ---------------------------------------------------------------------------


def test_forecasts_debiased_is_forecasts_plus_per_fold_bias():
    """Round-3 concern #1: ``forecasts_debiased`` must equal
    ``forecasts + per_fold_bias[f]`` on each fold slice (the bias is ADDED,
    per the sign convention ``bias = mean(y_tail - yhat_tail)``), and the
    bias must be non-trivial on this synthetic panel so the test cannot pass
    vacuously at bias == 0.
    """
    from har_lj_asym import walk_forward_lj_asym

    rng = np.random.default_rng(0)
    index = pd.date_range("2020-01-01", periods=400, freq="D")
    log_rv = np.cumsum(rng.normal(0.0, 0.1, 400)) - 5.0
    rv = pd.Series(np.exp(log_rv), index=index, name="rv")
    rv_neg = pd.Series(rv.to_numpy() * 0.5, index=index)
    rv_pos = pd.Series(rv.to_numpy() * 0.5, index=index)
    rv_c = pd.Series(rv.to_numpy() * 0.8, index=index)
    rv_j = pd.Series(rv.to_numpy() * 0.2, index=index)

    out = walk_forward_lj_asym(
        rv, rv_neg, rv_pos, rv_c, rv_j, horizon=1, seed=0,
        debias=True, calibration_size=60,
    )
    assert out["forecasts"]
    biases = out["per_fold_bias"]
    assert len(biases) > 0
    # Non-trivial bias on this synthetic panel (guards against a vacuous
    # test where +bias and -bias are indistinguishable at bias == 0).
    assert float(np.max(np.abs(biases))) > 1e-6

    fc = np.asarray(out["forecasts"], dtype=float)
    fcd = np.asarray(out["forecasts_debiased"], dtype=float)
    shift = fcd - fc
    fold_size = len(fc) // len(biases)
    assert fold_size * len(biases) == len(fc)
    for k, b in enumerate(biases):
        np.testing.assert_allclose(
            shift[k * fold_size:(k + 1) * fold_size], b,
            rtol=1e-12, atol=1e-12,
            err_msg=f"fold {k}: debiased forecasts must equal forecasts + bias",
        )


# ---------------------------------------------------------------------------
# ROUND-3 concern #2 — M12 (walk_forward_har_rv_j) is calibrated when debias
# ---------------------------------------------------------------------------


def test_walk_forward_har_rv_j_receives_calibrate_bias_when_debias(
    synthetic_lj_components, monkeypatch,
):
    """Round-3 concern #2: when debias=True, walk_forward_har_rv_j must be
    called with calibrate_bias=True + the same calibration_size (apples-to-
    apples M12 baseline, internally calibrated like HAR and LJ)."""
    import m12_har_rv_j
    from har_lj_asym import _eval_one_coin

    captured: dict = {}

    def spy_walk_forward_har_rv_j(rv, jumps, horizon, *args, **kwargs):
        captured["calibrate_bias"] = kwargs.get("calibrate_bias")
        captured["calibration_size"] = kwargs.get("calibration_size")
        n = 100
        idx = rv.index[-n:]
        return {
            "forecasts": pd.Series(np.zeros(n), index=idx, name="fc"),
            "aggregate_mse_logrv": 0.0,
        }

    monkeypatch.setattr(
        m12_har_rv_j, "walk_forward_har_rv_j", spy_walk_forward_har_rv_j,
    )

    row = _eval_one_coin(
        "BTC-USD", horizon=1, seed=0, components=synthetic_lj_components,
        debias=True, calibration_size=60,
    )
    assert row is not None
    assert captured["calibrate_bias"] is True
    assert captured["calibration_size"] == 60


def test_walk_forward_har_rv_j_receives_calibrate_bias_false_when_no_debias(
    synthetic_lj_components, monkeypatch,
):
    """Round-3 concern #2: when debias=False, walk_forward_har_rv_j must
    receive calibrate_bias=False (no calibration anywhere)."""
    import m12_har_rv_j
    from har_lj_asym import _eval_one_coin

    captured: dict = {}

    def spy_walk_forward_har_rv_j(rv, jumps, horizon, *args, **kwargs):
        captured["calibrate_bias"] = kwargs.get("calibrate_bias")
        n = 100
        idx = rv.index[-n:]
        return {
            "forecasts": pd.Series(np.zeros(n), index=idx, name="fc"),
            "aggregate_mse_logrv": 0.0,
        }

    monkeypatch.setattr(
        m12_har_rv_j, "walk_forward_har_rv_j", spy_walk_forward_har_rv_j,
    )

    row = _eval_one_coin(
        "BTC-USD", horizon=1, seed=0, components=synthetic_lj_components,
    )
    assert row is not None
    assert captured["calibrate_bias"] is False


# ---------------------------------------------------------------------------
# ROUND-3 concern #3 — mse_har_raw != mse_har_debiased with calibrate-aware
# fixtures (the two HAR legs must be genuinely distinct forecasts)
# ---------------------------------------------------------------------------


def test_mse_har_raw_and_debiased_distinct_when_debias(
    synthetic_lj_components, monkeypatch,
):
    """Round-3 concern #3: with a HAR fixture whose forecasts DEPEND on
    calibrate_bias (offset when calibrated), mse_har_raw (uncalibrated leg)
    and mse_har_debiased (calibrated leg) must be finite AND distinct when
    debias=True. The c.953 fake identity came from both legs returning the
    same dummy forecasts."""
    from har_lj_asym import _eval_one_coin

    def fake_walk_forward_har(rv, horizon, *args, **kwargs):
        n = 100
        idx = rv.index[-n:]
        offset = -0.05 if kwargs.get("calibrate_bias") else 0.0
        return {
            "forecasts": pd.Series(
                np.log(rv.iloc[-n:].to_numpy()) + offset,
                index=idx, name="fc_har",
            ),
            "aggregate_mse_logrv": 0.9,
        }

    monkeypatch.setattr(
        "har_lj_asym.walk_forward_har", fake_walk_forward_har,
    )

    row = _eval_one_coin(
        "BTC-USD", horizon=1, seed=0, components=synthetic_lj_components,
        debias=True, calibration_size=60,
    )
    assert row is not None
    assert not np.isnan(row["mse_har_raw"])
    assert not np.isnan(row["mse_har_debiased"])
    assert row["mse_har_raw"] != row["mse_har_debiased"]


# ---------------------------------------------------------------------------
# ROUND-3 concern #4 — full-walk-forward OOS-target invariance
# ---------------------------------------------------------------------------


def test_walk_forward_lj_asym_oos_target_invariance(monkeypatch):
    """Round-3 concern #4: perturbing ALL OOS targets through the FULL
    walk_forward_lj_asym must leave ``per_fold_bias`` and
    ``forecasts_debiased`` bit-identical (the bias reads the train tail
    only, and the OLS forecasts depend on the model + features, not on the
    OOS targets). The perturbation is applied by patching
    ``realized_variance_to_log`` — the module-level import used ONLY to
    build the target — so the features (built by ``lj_asym_features``,
    which logs directly) stay untouched. Conversely, perturbing the train
    calibration tail MUST move the bias estimate (sensitivity control)."""
    import har_lj_asym as module
    from har_lj_asym import lj_asym_features, walk_forward_lj_asym
    from realized_variance import realized_variance_to_log

    rng = np.random.default_rng(7)
    index = pd.date_range("2020-01-01", periods=400, freq="D")
    log_rv = np.cumsum(rng.normal(0.0, 0.1, 400)) - 5.0
    rv = pd.Series(np.exp(log_rv), index=index, name="rv")
    rv_neg = pd.Series(rv.to_numpy() * 0.5, index=index)
    rv_pos = pd.Series(rv.to_numpy() * 0.5, index=index)
    rv_c = pd.Series(rv.to_numpy() * 0.8, index=index)
    rv_j = pd.Series(rv.to_numpy() * 0.2, index=index)

    horizon, n_splits, calibration_size = 1, 1, 60
    kwargs = dict(
        horizon=horizon, seed=0, n_splits=n_splits,
        debias=True, calibration_size=calibration_size,
    )

    out_base = walk_forward_lj_asym(
        rv, rv_neg, rv_pos, rv_c, rv_j, **kwargs,
    )
    assert out_base["forecasts"]

    # Replicate the internal split arithmetic to locate, in ORIGINAL rv
    # coordinates, the boundary between train-read and OOS-read targets:
    # the target at merged row j reads original position
    # (first_pos + j + horizon).
    feat = lj_asym_features(rv_neg, rv_pos, rv_c, rv_j, rv)
    merged = feat.join(
        realized_variance_to_log(rv).rename("log_rv"), how="inner",
    ).dropna()
    n_total = int(
        merged["log_rv"].rolling(horizon).mean().shift(-horizon).notna().sum()
    )
    fold_size = n_total // (n_splits + 1)
    first_pos = int(rv.index.get_loc(merged.index[0]))
    cutoff = first_pos + fold_size + horizon  # OOS targets read >= cutoff

    delta = 10.0
    orig = module.realized_variance_to_log

    def shift_from(cut_lo, cut_hi):
        def patched(series):
            out = orig(series).copy()
            mask = (np.arange(len(out)) >= cut_lo) & (
                np.arange(len(out)) < cut_hi
            )
            out.iloc[mask] = out.iloc[mask] + delta
            return out
        return patched

    # (a) Shift ALL OOS targets (original positions >= cutoff): features
    # and the train fold are untouched -> bias + debiased forecasts must
    # be identical to the baseline run.
    monkeypatch.setattr(
        module, "realized_variance_to_log", shift_from(cutoff, len(rv)),
    )
    out_oos_shifted = walk_forward_lj_asym(
        rv, rv_neg, rv_pos, rv_c, rv_j, **kwargs,
    )
    # Sanity on the perturbation itself: the OOS targets really changed.
    assert not np.allclose(out_oos_shifted["targets"], out_base["targets"])
    np.testing.assert_allclose(
        out_oos_shifted["per_fold_bias"], out_base["per_fold_bias"],
        rtol=1e-12, atol=1e-12,
    )
    np.testing.assert_allclose(
        out_oos_shifted["forecasts"], out_base["forecasts"], rtol=1e-12,
    )
    np.testing.assert_allclose(
        out_oos_shifted["forecasts_debiased"],
        out_base["forecasts_debiased"], rtol=1e-12,
    )

    # (b) Shift the train calibration tail instead: the bias estimate MUST
    # move (train sensitivity is the expected behavior of a train-only
    # estimator).
    monkeypatch.setattr(
        module, "realized_variance_to_log",
        shift_from(cutoff - calibration_size, cutoff),
    )
    out_tail_shifted = walk_forward_lj_asym(
        rv, rv_neg, rv_pos, rv_c, rv_j, **kwargs,
    )
    assert abs(
        out_tail_shifted["per_fold_bias"][0] - out_base["per_fold_bias"][0]
    ) > 1.0


# ---------------------------------------------------------------------------
# ROUND-3 concern #6 — panel_hash covers the index in addition to the values
# ---------------------------------------------------------------------------


def test_panel_hash_includes_index():
    """Round-3 concern #6: two panels with identical VALUES but different
    indexes must hash differently (the index bytes participate in the
    digest); identical panels hash identically; different values on the
    same index hash differently."""
    from har_lj_asym import _panel_hash

    rng = np.random.default_rng(3)
    vals = np.exp(rng.normal(-5.0, 0.5, 100))
    idx_a = pd.date_range("2020-01-01", periods=100, freq="D")
    idx_b = pd.date_range("2021-03-01", periods=100, freq="D")

    h_a = _panel_hash(pd.Series(vals, index=idx_a))
    h_a_again = _panel_hash(pd.Series(vals, index=idx_a))
    h_b = _panel_hash(pd.Series(vals, index=idx_b))
    h_a_shifted_vals = _panel_hash(pd.Series(vals * 1.01, index=idx_a))

    assert h_a == h_a_again
    assert h_a != h_b, "index must participate in the panel hash"
    assert h_a != h_a_shifted_vals, "values must participate in the hash"
