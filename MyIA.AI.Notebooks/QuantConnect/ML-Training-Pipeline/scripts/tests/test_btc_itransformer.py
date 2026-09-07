"""Tests for btc_itransformer.py (issue #14860) -- pure CPU, fast.

Covers:
- MSE = bias^2 + variance decomposition identity through ``evaluate_combo``.
- Timestamp alignment (intersection + target-consistency guard).
- Walk-forward boundaries / expansion and train-only normalisation
  (no test leakage), including a mutate-the-test-region probe.
- Genuinely-OOS HAR debias (train-tail calibration untouched by the test
  region) on the ``run_debiased_har`` wrapper.
- Aggregation verdicts: BEATS / NO BEATS (dominance) / INCONCLUSIVE.
- Dry-run end-to-end: full pipeline on synthetic log-RV writes valid JSON.

The real BTC sweep (Bitstamp CSV, 5 folds x 4 seeds x 3 horizons) is NOT
exercised here -- it is run out-of-band by the coordinator (issue #14860).
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np
import pandas as pd
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from btc_itransformer import (  # noqa: E402
    aggregate_by_horizon,
    align_by_timestamps,
    evaluate_combo,
    make_expanding_splits,
    run_debiased_har,
    run_pipeline,
    synthetic_rv,
    train_normalization_stats,
    walk_forward_itransformer,
)
from dlinear_vol import create_sequences  # noqa: E402
from realized_variance import realized_variance_to_log  # noqa: E402

# Tiny CPU architecture used by every test that trains a model.
# iTransformerModel has no patch_len/stride; it uses ff_dropout instead of
# fc_dropout (mirroring train_itransformer.py).
TINY = dict(
    seq_len=16, d_model=8, n_heads=2, n_layers=1,
    epochs=2, batch_size=16, lr=5e-4, ff_dropout=0.2,
)


def _aligned_from_errors(model_errors: np.ndarray, har_errors: np.ndarray) -> dict:
    """Build an `aligned` payload from crafted error series."""
    target = np.zeros(len(model_errors))
    dates = pd.date_range("2020-01-01", periods=len(target), freq="D")
    return align_by_timestamps(
        pd.Series(target + model_errors, index=dates),
        pd.Series(target, index=dates),
        pd.Series(target + har_errors, index=dates),
        pd.Series(target, index=dates),
    )


class TestEvaluateComboDecomposition:
    def test_mse_equals_bias_sq_plus_variance(self):
        # iTransformer errors: constant +0.5 (pure bias, zero variance).
        # HAR errors: alternating +/-1 (zero bias, unit variance).
        model_err = np.full(50, 0.5)
        har_err = np.tile([-1.0, 1.0], 25)

        out = evaluate_combo(_aligned_from_errors(model_err, har_err), horizon=1)

        assert out["n_aligned"] == 50
        # Decomposition identity: MSE == bias^2 + variance (exact in float64).
        assert out["itransformer_mse_logrv"] == pytest.approx(0.25)
        assert out["itransformer_bias_sq"] + out["itransformer_variance"] == pytest.approx(
            out["itransformer_mse_logrv"]
        )
        assert out["har_debiased_mse_logrv"] == pytest.approx(1.0)
        assert out["har_debiased_bias_sq"] + out["har_debiased_variance"] == pytest.approx(
            out["har_debiased_mse_logrv"]
        )
        # Signed biases are reported with their sign.
        assert out["itransformer_bias"] == pytest.approx(0.5)
        assert out["har_debiased_bias"] == pytest.approx(0.0)
        assert out["itransformer_variance"] == pytest.approx(0.0)
        assert out["har_debiased_variance"] == pytest.approx(1.0)
        # Edge vs debiased HAR: (1.0 - 0.25) / 1.0 = 75%.
        assert out["edge_vs_debiased_har_pct"] == pytest.approx(75.0)
        assert out["var_ratio_itransformer_over_har_debiased"] == pytest.approx(0.0)

    def test_insufficient_data_short_circuit(self):
        out = evaluate_combo(_aligned_from_errors(np.zeros(5), np.zeros(5)), horizon=1)
        assert out["dm_centered_verdict"] == "INSUFFICIENT_DATA"
        assert np.isnan(out["edge_vs_debiased_har_pct"])


class TestAlignByTimestamps:
    def test_intersection_on_shared_dates(self):
        dates = pd.date_range("2020-01-01", periods=12, freq="D")
        target = pd.Series(np.arange(12.0), index=dates)
        model_fc = pd.Series(np.arange(10.0) + 0.1, index=dates[:10])
        har_fc = pd.Series(np.arange(10.0) - 0.2, index=dates[2:])

        out = align_by_timestamps(model_fc, target[:10], har_fc, target[2:])

        assert len(out["timestamps"]) == 8
        assert out["timestamps"][0] == dates[2]
        assert out["timestamps"][-1] == dates[9]
        assert len(out["model_pred"]) == len(out["har_pred"]) == 8
        np.testing.assert_allclose(out["model_target"], np.arange(2.0, 10.0))

    def test_target_convention_mismatch_raises(self):
        dates = pd.date_range("2020-01-01", periods=12, freq="D")
        model_fc = pd.Series(np.zeros(10), index=dates[:10])
        model_tg = pd.Series(np.zeros(10), index=dates[:10])
        har_fc = pd.Series(np.zeros(10), index=dates[2:])
        har_tg = pd.Series(np.ones(10), index=dates[2:])  # diverged convention

        with pytest.raises(ValueError, match="target mismatch"):
            align_by_timestamps(model_fc, model_tg, har_fc, har_tg)


class TestExpandingSplits:
    def test_boundaries_expanding_and_contiguous(self):
        splits = make_expanding_splits(300, 5)
        assert len(splits) == 5
        train_ends = [s[0] for s in splits]
        assert train_ends == sorted(train_ends)          # expanding...
        assert len(set(train_ends)) == 5                 # ...strictly
        assert train_ends[0] == 300 // 6                 # fold_size = n//(k+1)
        for train_end, test_start, test_end in splits:
            assert test_start == train_end               # test starts where train ends
            assert test_end > test_start                 # non-empty test
            assert test_end <= 300                       # within the sample
        assert splits[-1][2] == 300

    def test_dry_run_geometry(self):
        # Dry-run uses n=360, 2 splits -> folds [120,240) and [240,360).
        assert make_expanding_splits(360, 2) == [(120, 120, 240), (240, 240, 360)]


class TestTrainOnlyNormalization:
    def test_stats_use_train_slice_only(self):
        log_rv = np.concatenate([np.ones(100), np.full(100, 10.0)])
        mean, std = train_normalization_stats(log_rv, 100)
        assert mean == pytest.approx(1.0)
        assert std == pytest.approx(1e-6)  # zero std clamped, no NaN

        # Mutating the post-train region cannot move the train stats.
        log_rv[100:] = -999.0
        mean2, std2 = train_normalization_stats(log_rv, 100)
        assert (mean2, std2) == (mean, std)

        # Full-array stats DO see the tail (sanity of the probe above).
        mean_full, _ = train_normalization_stats(log_rv, 200)
        assert mean_full == pytest.approx((100 * 1.0 + 100 * -999.0) / 200)


class TestSequenceWindowsNoLeakage:
    def test_training_targets_end_within_train_region(self):
        arr = np.arange(50.0)
        seq_len, horizon, train_end = 5, 3, 20
        x_all, y_all = create_sequences(arr, seq_len, horizon)
        n_train = train_end - seq_len - horizon + 1
        x_train, y_train = x_all[:n_train], y_all[:n_train]

        # Window definition: x[j] = arr[j:j+seq_len], y[j] = arr[j+seq_len:j+seq_len+h).
        np.testing.assert_array_equal(x_train[0], arr[0:5])
        np.testing.assert_array_equal(y_train[0], arr[5:8])
        # Last training target ends at index train_end - 1 (strictly inside train).
        np.testing.assert_array_equal(y_train[-1], arr[17:20])
        assert (n_train - 1) + seq_len + horizon == train_end
        # No training sample ever touches arr[train_end:].
        assert x_train.shape == (n_train, seq_len)
        assert y_train.shape == (n_train, horizon)


class TestWalkForwardItransformer:
    def _run(self, log_rv: np.ndarray, seed: int = 0):
        return walk_forward_itransformer(
            log_rv,
            pd.date_range("2021-01-01", periods=len(log_rv), freq="D"),
            horizon=1, n_splits=2, seed=seed, device="cpu", **TINY,
        )

    def test_fold_boundaries_and_prediction_count(self):
        rv = synthetic_rv(n=360, seed=0)
        log_rv = realized_variance_to_log(rv).values.astype(float)
        out = self._run(log_rv)

        active = [f for f in out["fold_info"] if "skipped" not in f]
        assert len(active) == 2
        assert [(f["train_end"], f["test_start"], f["test_end"]) for f in active] == [
            (120, 120, 240), (240, 240, 360),
        ]
        # One prediction per test day minus the horizon tail, per fold.
        assert out["n_total_preds"] == (240 - 120 - 1) + (360 - 240 - 1)

    def test_normalization_recorded_from_train_slice_only(self):
        rv = synthetic_rv(n=360, seed=0)
        log_rv = realized_variance_to_log(rv).values.astype(float)
        out = self._run(log_rv)

        for f in out["fold_info"]:
            if "skipped" in f:
                continue
            expected = train_normalization_stats(log_rv, f["train_end"])
            assert f["train_mean"] == pytest.approx(expected[0])
            assert f["train_std"] == pytest.approx(expected[1])

    def test_mutating_test_region_leaves_fold0_training_untouched(self):
        """Direct leakage probe: fold 0 trains on [0,120) only."""
        rv = synthetic_rv(n=360, seed=0)
        log_rv = realized_variance_to_log(rv).values.astype(float)
        base = self._run(log_rv)

        mutated = log_rv.copy()
        mutated[120:] += 5.0  # distort everything after fold-0's train window
        changed = self._run(mutated)

        base_f0 = next(f for f in base["fold_info"] if f.get("fold") == 0)
        changed_f0 = next(f for f in changed["fold_info"] if f.get("fold") == 0)
        # Fold-0 train stats (and val-selected training) see only [0,120).
        assert changed_f0["train_mean"] == pytest.approx(base_f0["train_mean"])
        assert changed_f0["train_std"] == pytest.approx(base_f0["train_std"])
        assert changed_f0["best_val_loss"] == pytest.approx(base_f0["best_val_loss"])
        # Fold-1 train window includes the mutated region -> stats must move.
        base_f1 = next(f for f in base["fold_info"] if f.get("fold") == 1)
        changed_f1 = next(f for f in changed["fold_info"] if f.get("fold") == 1)
        assert changed_f1["train_mean"] != pytest.approx(base_f1["train_mean"])

    def test_targets_follow_forecast_dates(self):
        rv = synthetic_rv(n=360, seed=0)
        log_rv = realized_variance_to_log(rv).values.astype(float)
        idx = pd.date_range("2021-01-01", periods=360, freq="D")
        out = walk_forward_itransformer(
            log_rv, idx, horizon=1, n_splits=2, seed=0, device="cpu", **TINY,
        )
        positions = idx.get_indexer(out["targets"].index)
        # horizon=1: target of a forecast dated t is exactly log_rv[t].
        np.testing.assert_allclose(out["targets"].values, log_rv[positions])


class TestDebiasedHarIsOos:
    def test_calibration_ignores_test_region(self):
        rv = synthetic_rv(n=420, seed=7)
        base = run_debiased_har(rv, horizon=1, n_splits=4, refit_every=22,
                                calibration_size=45)

        mutated = rv.copy()
        first_test_start = 420 // 5
        mutated.iloc[first_test_start:] *= np.exp(2.0)
        changed = run_debiased_har(mutated, horizon=1, n_splits=4, refit_every=22,
                                   calibration_size=45)

        assert base["calibrate_bias"] is True
        base_biases = base["initial_calibration_bias_by_fold"]
        changed_biases = changed["initial_calibration_bias_by_fold"]
        assert len(base_biases) == 4
        # The debias constant of fold 0 is estimated on train history only:
        # rescaling the test region cannot move it.
        assert base_biases[0] == pytest.approx(changed_biases[0])
        # ...while the test-support MSE obviously changes (probe sanity).
        assert base["aggregate_mse_logrv"] != pytest.approx(
            changed["aggregate_mse_logrv"]
        )


def _combo_rows(verdicts: list[str], edges: list[float], p: float = 0.01,
                horizon: int = 1) -> list[dict]:
    return [
        {
            "horizon": horizon,
            "seed": seed,
            "edge_vs_debiased_har_pct": edge,
            "dm_centered_pvalue": p,
            "dm_centered_verdict": verdict,
            "var_ratio_itransformer_over_har_debiased": 0.9,
            "itransformer_mse_logrv": 1.0,
            "har_debiased_mse_logrv": 1.1,
            "itransformer_bias": 0.0,
            "har_debiased_bias": 0.0,
        }
        for seed, verdict, edge in zip((0, 1, 7, 42), verdicts, edges)
    ]


class TestAggregateVerdicts:
    def test_beats_requires_edge_and_significance(self):
        rows = _combo_rows(["BEATS baseline"] * 4, [10.0] * 4)
        agg = aggregate_by_horizon(rows)[0]
        assert agg["mean_edge_vs_debiased_har_pct"] == pytest.approx(10.0)
        assert agg["edge_std_pct"] == pytest.approx(0.0)
        assert agg["dm_centered_p_median"] < 0.05
        assert agg["n_beats"] == 4
        assert agg["verdict"] == "BEATS"

    def test_any_beaten_seed_dominates_to_no_beats(self):
        rows = _combo_rows(
            ["BEATS baseline", "BEATS baseline", "BEATS baseline",
             "BEATEN BY baseline"],
            [10.0, 10.0, 10.0, 10.0],
        )
        agg = aggregate_by_horizon(rows)[0]
        assert agg["n_beaten"] == 1
        assert agg["n_beats"] == 3
        # Dominance: one BEATEN seed vetoes BEATS even with a strong mean edge.
        assert agg["verdict"] == "NO BEATS"

    def test_all_beaten_is_no_beats(self):
        rows = _combo_rows(["BEATEN BY baseline"] * 4, [-10.0] * 4)
        agg = aggregate_by_horizon(rows)[0]
        assert agg["verdict"] == "NO BEATS"

    def test_edge_below_two_sigma_is_inconclusive(self):
        # mean=10, std=20 -> 10 < 2*20 despite p=0.01.
        rows = _combo_rows(["BEATS baseline"] * 4, [30.0, -10.0, 30.0, -10.0])
        agg = aggregate_by_horizon(rows)[0]
        assert agg["edge_std_pct"] == pytest.approx(20.0)
        assert agg["verdict"] == "INCONCLUSIVE"

    def test_high_dm_p_is_inconclusive(self):
        rows = _combo_rows(["BEATS baseline"] * 4, [10.0] * 4, p=0.5)
        agg = aggregate_by_horizon(rows)[0]
        assert agg["dm_centered_p_median"] == pytest.approx(0.5)
        assert agg["verdict"] == "INCONCLUSIVE"

    def test_grouped_by_horizon(self):
        rows = (
            _combo_rows(["BEATS baseline"] * 4, [10.0] * 4, horizon=1)
            + _combo_rows(["BEATEN BY baseline"] * 4, [10.0] * 4, horizon=5)
        )
        aggs = aggregate_by_horizon(rows)
        assert [a["horizon"] for a in aggs] == [1, 5]
        assert aggs[0]["verdict"] == "BEATS"
        assert aggs[1]["verdict"] == "NO BEATS"


class TestDryRunEndToEnd:
    def test_full_pipeline_writes_json(self, tmp_path):
        out_json = tmp_path / "dry_run.json"
        payload = run_pipeline(
            synthetic_rv(n=360, seed=0),
            horizons=[1],
            seeds=[0],
            n_splits=2,
            refit_every=22,
            calibration_size=60,
            device="cpu",
            out_json=out_json,
            dry_run=True,
            **TINY,
        )

        assert out_json.exists()
        on_disk = json.loads(out_json.read_text())
        assert on_disk["dry_run"] is True
        assert payload["dry_run"] is True

        rows = on_disk["rows"]
        assert len(rows) == 1  # 1 horizon x 1 seed
        row = rows[0]
        # Requirement #14860: per-combo arrays persisted and consistent.
        for key in ("model_errors", "har_errors", "predictions", "targets",
                    "timestamps"):
            assert key in row
            assert len(row[key]) == row["n_aligned"] >= 10
        for pred, target, err in zip(
            row["predictions"], row["targets"], row["model_errors"]
        ):
            assert err == pytest.approx(pred - target)
        assert row["har_calibrate_bias"] is True
        # Decomposition identity holds on the persisted errors.
        errors = np.asarray(row["model_errors"])
        bias_sq = float(np.mean(errors)) ** 2
        variance = float(np.var(errors))
        assert bias_sq + variance == pytest.approx(row["itransformer_mse_logrv"])

        aggregated = on_disk["aggregated"]
        assert len(aggregated) == 1
        assert aggregated[0]["horizon"] == 1
        assert aggregated[0]["verdict"] in ("BEATS", "NO BEATS", "INCONCLUSIVE")
        assert on_disk["config"]["har_debias"].startswith("train_tail_calibration")
