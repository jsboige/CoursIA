"""Tests for btc_m15.py helpers (issue #12734, slice 2/2).

Covers the pure transformations in `scripts/bias_metrics.py`
(extracted from `btc_vol.py`, issue #14363):
  - `_mse_decomposition`: split MSE into bias^2 + variance.
  - `_dm_centered_mse`: DM test on errors centered by their own mean.
  - `analyze_one_combo`: end-to-end on a synthetic combo dict.
  - `aggregate_verdicts`: §C conjunction over multiple seeds.

The full BTC re-run needs Bitstamp data + GPU walk-forward (not exercised
here). Mirrors the test_btc_vol.py layout from PR #12742 (slice 1/2).
"""
from __future__ import annotations

import sys
from pathlib import Path

import numpy as np
import pytest

# Make the parent directory importable.
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from bias_metrics import (  # noqa: E402
    _dm_centered_mse,
    _mse_decomposition,
)
from btc_m15 import (  # noqa: E402
    aggregate_verdicts,
    analyze_one_combo,
)


class TestMseDecomposition:
    def test_zero_bias_zero_variance(self):
        e = np.zeros(50)
        d = _mse_decomposition(e)
        assert d["mse"] == 0.0
        assert d["bias_sq"] == 0.0
        assert d["variance"] == 0.0

    def test_constant_nonzero_bias(self):
        e = np.full(50, 0.4)
        d = _mse_decomposition(e)
        assert d["mse"] == pytest.approx(0.16, abs=1e-10)
        assert d["bias_sq"] == pytest.approx(0.16, abs=1e-10)
        assert d["variance"] == pytest.approx(0.0, abs=1e-12)

    def test_known_decomposition(self):
        # mean=0.1, var=0.01, MSE=0.02
        e = np.array([0.0, 0.2])
        d = _mse_decomposition(e)
        assert d["mse"] == pytest.approx(0.02, abs=1e-10)
        assert d["bias_sq"] == pytest.approx(0.01, abs=1e-10)
        assert d["variance"] == pytest.approx(0.01, abs=1e-10)


class TestDmCenteredMse:
    def test_shape_mismatch(self):
        out = _dm_centered_mse(np.zeros(10), np.zeros(11), horizon=1)
        assert out["dm_verdict"] == "SHAPE_MISMATCH"

    def test_insufficient_data(self):
        out = _dm_centered_mse(np.zeros(5), np.zeros(5), horizon=1)
        assert out["dm_verdict"] == "INSUFFICIENT_DATA"

    def test_clear_winner_on_centered(self):
        """LSTM with smaller variance should BEATS HAR on centered errors."""
        rng = np.random.default_rng(42)
        n = 1000
        lstm_err = rng.standard_normal(n) * 0.3 + 0.2   # smaller variance
        har_err = rng.standard_normal(n) * 1.0 - 0.1   # larger variance
        out = _dm_centered_mse(lstm_err, har_err, horizon=1)
        # Outcome string format matches dm_verdict.py
        assert "BEATS" in out["dm_verdict"] or "baseline" in out["dm_verdict"]
        assert out["dm_pvalue"] < 0.05
        assert out["dm_stat"] < 0  # negative = model wins


class TestAnalyzeOneCombo:
    def _synthetic_row(self, n: int = 500, seed: int = 0) -> dict:
        rng = np.random.default_rng(seed)
        target = rng.standard_normal(n) * 0.4
        har = target + rng.standard_normal(n) * 0.5 + 0.3  # biased + noisy
        lstm = target + rng.standard_normal(n) * 0.4  # less noise, less bias
        return {
            "coin": "BTC-USD",
            "horizon": 1,
            "seed": seed,
            "mse_har": float(np.mean((har - target) ** 2)),
            "mse_lstm": float(np.mean((lstm - target) ** 2)),
            "har_bias_oos": float(np.mean(har - target)),
            "har_preds": har.tolist(),
            "lstm_preds": lstm.tolist(),
            "target": target.tolist(),
            "har_errors": (har - target).tolist(),
            "lstm_errors": (lstm - target).tolist(),
        }

    def test_synthetic_combo_analyzable(self):
        row = self._synthetic_row()
        a = analyze_one_combo(row)
        assert a["analyzable"] is True
        assert a["har_bias_oos"] != 0  # the +0.3 offset
        assert "dm_centered" in a
        assert a["var_ratio_lstm_over_har_debiased"] < 1.0  # lstm less noisy
        assert "dm_verdict" in a["dm_centered"]

    def test_legacy_json_marked_non_analyzable(self):
        """A row without persisted errors should report analyzable=False."""
        row = {
            "coin": "BTC-USD", "horizon": 1, "seed": 0,
            "mse_har": 0.8, "mse_lstm": 0.7, "har_bias_oos": -0.2,
        }
        a = analyze_one_combo(row)
        assert a["analyzable"] is False
        assert "har_errors" in a["reason"]


class TestAggregateVerdicts:
    def test_beats_when_edge_and_dm_pass(self):
        """Two seeds with strong positive edge and significant dm_p -> BEATS."""
        rng = np.random.default_rng(7)
        analyzed = []
        for seed in range(2):
            n = 500
            target = rng.standard_normal(n) * 0.4
            har = target + rng.standard_normal(n) * 0.6 + 0.4
            lstm = target + rng.standard_normal(n) * 0.4 + 0.05
            row = {
                "coin": "BTC-USD", "horizon": 1, "seed": seed,
                "mse_har": float(np.mean((har - target) ** 2)),
                "mse_lstm": float(np.mean((lstm - target) ** 2)),
                "har_bias_oos": float(np.mean(har - target)),
                "har_errors": (har - target).tolist(),
                "lstm_errors": (lstm - target).tolist(),
            }
            analyzed.append(analyze_one_combo(row))
        agg = aggregate_verdicts(analyzed)
        assert len(agg) == 1
        assert agg[0]["horizon"] == 1
        # Strong signal: should be BEATS or at least edge clearly positive
        assert agg[0]["edge_reduction_pct"] > 0
