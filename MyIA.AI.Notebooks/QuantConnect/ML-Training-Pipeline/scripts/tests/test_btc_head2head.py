"""Tests for btc_patchtst_itransformer_head2head.py (issue #14942) -- pure CPU, fast.

Covers:
- Model builders produce correctly-shaped architectures for n_vars=1.
- MSE = bias^2 + variance decomposition identity through ``evaluate_combo``.
- Head-to-head DM semantics: PatchTST="model", iTransformer="baseline".
- Two-model timestamp alignment (intersection + target-consistency guard).
- Walk-forward boundaries / expansion and train-only normalisation
  (no test leakage), exercised through the generic ``walk_forward_logrv``.
- Aggregation verdicts: BEATS / NO BEATS (dominance) / INCONCLUSIVE.
- Dry-run end-to-end: full pipeline on synthetic log-RV writes valid JSON.

The real BTC sweep (Bitstamp CSV, 5 folds x 4 seeds x 3 horizons x 2
architectures) is NOT exercised here -- it is run out-of-band (issue #14942).
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np
import pandas as pd
import pytest
import torch

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from btc_patchtst_itransformer_head2head import (  # noqa: E402
    aggregate_by_horizon,
    align_two_models,
    evaluate_combo,
    make_expanding_splits,
    make_itransformer_builder,
    make_patchtst_builder,
    run_debiased_har,
    run_pipeline,
    synthetic_rv,
    train_normalization_stats,
    walk_forward_logrv,
)
from realized_variance import realized_variance_to_log  # noqa: E402

# Tiny CPU architecture used by every test that trains a model.
TINY = dict(
    seq_len=16, patch_len=4, stride=2, d_model=8, n_heads=2, n_layers=1,
    epochs=2, batch_size=16, lr=5e-4,
)


def _aligned_from_errors(
    patchtst_errors: np.ndarray, itransformer_errors: np.ndarray
) -> dict:
    """Build an `aligned` payload from crafted error series."""
    target = np.zeros(len(patchtst_errors))
    dates = pd.date_range("2020-01-01", periods=len(target), freq="D")
    return align_two_models(
        pd.Series(target + patchtst_errors, index=dates),
        pd.Series(target, index=dates),
        pd.Series(target + itransformer_errors, index=dates),
        pd.Series(target, index=dates),
    )


class TestModelBuilders:
    def test_patchtst_output_shape(self):
        build = make_patchtst_builder(
            seq_len=16, patch_len=4, stride=2,
            d_model=8, n_heads=2, n_layers=1,
            dropout=0.2, fc_dropout=0.2,
        )
        model = build(horizon=5)
        out = model(torch.zeros(4, 16, 1))
        assert out.shape == (4, 5)

    def test_itransformer_output_shape(self):
        build = make_itransformer_builder(
            seq_len=16, d_model=8, n_heads=2, n_layers=1,
            dropout=0.2, ff_dropout=0.2,
        )
        model = build(horizon=5)
        out = model(torch.zeros(4, 16, 1))
        assert out.shape == (4, 5)


class TestEvaluateComboDecomposition:
    def test_mse_equals_bias_sq_plus_variance(self):
        # PatchTST errors: constant +0.5 (pure bias, zero variance).
        # iTransformer errors: alternating +/-1 (zero bias, unit variance).
        patchtst_err = np.full(50, 0.5)
        itr_err = np.tile([-1.0, 1.0], 25)

        out = evaluate_combo(_aligned_from_errors(patchtst_err, itr_err), horizon=1)

        assert out["n_aligned"] == 50
        # Decomposition identity: MSE == bias^2 + variance (exact in float64).
        assert out["patchtst_mse_logrv"] == pytest.approx(0.25)
        assert out["patchtst_bias_sq"] + out["patchtst_variance"] == pytest.approx(
            out["patchtst_mse_logrv"]
        )
        assert out["itransformer_mse_logrv"] == pytest.approx(1.0)
        assert out["itransformer_bias_sq"] + out["itransformer_variance"] == pytest.approx(
            out["itransformer_mse_logrv"]
        )
        # Signed biases are reported with their sign.
        assert out["patchtst_bias"] == pytest.approx(0.5)
        assert out["itransformer_bias"] == pytest.approx(0.0)
        assert out["patchtst_variance"] == pytest.approx(0.0)
        assert out["itransformer_variance"] == pytest.approx(1.0)
        # Edge vs iTransformer: (1.0 - 0.25) / 1.0 = 75% (PatchTST lower MSE).
        assert out["edge_vs_itransformer_pct"] == pytest.approx(75.0)
        assert out["var_ratio_patchtst_over_itransformer"] == pytest.approx(0.0)

    def test_insufficient_data_short_circuit(self):
        out = evaluate_combo(_aligned_from_errors(np.zeros(5), np.zeros(5)), horizon=1)
        assert out["dm_centered_verdict"] == "INSUFFICIENT_DATA"
        assert np.isnan(out["edge_vs_itransformer_pct"])


class TestAlignTwoModels:
    def test_intersection_on_shared_dates(self):
        dates = pd.date_range("2020-01-01", periods=12, freq="D")
        target = pd.Series(np.arange(12.0), index=dates)
        pb_fc = pd.Series(np.arange(10.0) + 0.1, index=dates[:10])
        itr_fc = pd.Series(np.arange(10.0) - 0.2, index=dates[2:])

        out = align_two_models(pb_fc, target[:10], itr_fc, target[2:])

        assert len(out["timestamps"]) == 8
        assert out["timestamps"][0] == dates[2]
        assert out["timestamps"][-1] == dates[9]
        assert len(out["pb_pred"]) == len(out["itr_pred"]) == 8
        np.testing.assert_allclose(out["pb_target"], np.arange(2.0, 10.0))

    def test_target_convention_mismatch_raises(self):
        dates = pd.date_range("2020-01-01", periods=12, freq="D")
        pb_fc = pd.Series(np.zeros(10), index=dates[:10])
        pb_tg = pd.Series(np.zeros(10), index=dates[:10])
        itr_fc = pd.Series(np.zeros(10), index=dates[2:])
        itr_tg = pd.Series(np.ones(10), index=dates[2:])  # diverged convention

        with pytest.raises(ValueError, match="target mismatch"):
            align_two_models(pb_fc, pb_tg, itr_fc, itr_tg)


class TestExpandingSplits:
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


class TestWalkForwardLogrv:
    def _run(self, log_rv: np.ndarray, seed: int = 0):
        build = make_patchtst_builder(
            seq_len=TINY["seq_len"], patch_len=TINY["patch_len"],
            stride=TINY["stride"], d_model=TINY["d_model"],
            n_heads=TINY["n_heads"], n_layers=TINY["n_layers"],
            dropout=0.2, fc_dropout=0.2,
        )
        # walk_forward_logrv takes the seq/model config only via the builder;
        # its own signature accepts the train loop hyperparams, not arch kwargs.
        return walk_forward_logrv(
            log_rv,
            pd.date_range("2021-01-01", periods=len(log_rv), freq="D"),
            build,
            horizon=1, n_splits=2, seed=seed, device="cpu",
            seq_len=TINY["seq_len"], epochs=TINY["epochs"],
            batch_size=TINY["batch_size"], lr=TINY["lr"],
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
        # Fold-0 train stats see only [0,120).
        assert changed_f0["train_mean"] == pytest.approx(base_f0["train_mean"])
        assert changed_f0["train_std"] == pytest.approx(base_f0["train_std"])
        assert changed_f0["best_val_loss"] == pytest.approx(base_f0["best_val_loss"])
        # Fold-1 train window includes the mutated region -> stats must move.
        base_f1 = next(f for f in base["fold_info"] if f.get("fold") == 1)
        changed_f1 = next(f for f in changed["fold_info"] if f.get("fold") == 1)
        assert changed_f1["train_mean"] != pytest.approx(base_f1["train_mean"])


def _combo_rows(verdicts: list[str], edges: list[float], p: float = 0.01,
                horizon: int = 1) -> list[dict]:
    return [
        {
            "horizon": horizon,
            "seed": seed,
            "edge_vs_itransformer_pct": edge,
            "dm_centered_pvalue": p,
            "dm_centered_verdict": verdict,
            "var_ratio_patchtst_over_itransformer": 0.9,
            "patchtst_mse_logrv": 1.0,
            "itransformer_mse_logrv": 1.1,
            "patchtst_bias": 0.0,
            "itransformer_bias": 0.0,
        }
        for seed, verdict, edge in zip((0, 1, 7, 42), verdicts, edges)
    ]


class TestAggregateVerdicts:
    def test_beats_requires_edge_and_significance(self):
        rows = _combo_rows(["BEATS baseline"] * 4, [10.0] * 4)
        agg = aggregate_by_horizon(rows)[0]
        assert agg["mean_edge_vs_itransformer_pct"] == pytest.approx(10.0)
        assert agg["edge_std_pct"] == pytest.approx(0.0)
        assert agg["dm_centered_p_median"] < 0.05
        assert agg["n_patchtst_wins"] == 4
        assert agg["verdict"] == "BEATS"

    def test_any_itransformer_win_dominates_to_no_beats(self):
        rows = _combo_rows(
            ["BEATS baseline", "BEATS baseline", "BEATS baseline",
             "BEATEN BY baseline"],
            [10.0, 10.0, 10.0, 10.0],
        )
        agg = aggregate_by_horizon(rows)[0]
        assert agg["n_itransformer_wins"] == 1
        assert agg["n_patchtst_wins"] == 3
        # Dominance: one iTransformer-win seed vetoes BEATS even with a strong mean edge.
        assert agg["verdict"] == "NO BEATS"

    def test_all_itransformer_wins_is_no_beats(self):
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
        # Requirement #14942: both architectures' per-combo arrays persisted.
        for key in ("patchtst_errors", "itransformer_errors", "patchtst_predictions",
                    "itransformer_predictions", "targets", "timestamps"):
            assert key in row
            assert len(row[key]) == row["n_aligned"] >= 10
        for pred, target, err in zip(
            row["patchtst_predictions"], row["targets"], row["patchtst_errors"]
        ):
            assert err == pytest.approx(pred - target)
        for pred, target, err in zip(
            row["itransformer_predictions"], row["targets"], row["itransformer_errors"]
        ):
            assert err == pytest.approx(pred - target)
        # Decomposition identity holds on the persisted PatchTST errors.
        errors = np.asarray(row["patchtst_errors"])
        bias_sq = float(np.mean(errors)) ** 2
        variance = float(np.var(errors))
        assert bias_sq + variance == pytest.approx(row["patchtst_mse_logrv"])
        # HAR context is present on every row.
        assert "har_debiased_mse_logrv" in row

        aggregated = on_disk["aggregated"]
        assert len(aggregated) == 1
        assert aggregated[0]["horizon"] == 1
        assert aggregated[0]["verdict"] in ("BEATS", "NO BEATS", "INCONCLUSIVE")
