"""Tests for train_moe_regimes.py -- regime decode plumbing (#21054 case 4).

Covers the opt-in causal decode added for the walk-forward re-measure:
- ``regime_decode`` reaches the ``detect_regimes`` call only for
  ``regime_method="hmm"`` (price labels are causal by construction);
- the decode + causality provenance land in the per-seed result JSON and in
  the multiseed summary;
- torch seeding makes same-seed runs reproducible (no silent init noise
  mixing with the decode effect);
- the walk-forward records the per-observation OOS squared errors that the
  paired DM comparison (``moe_regimes_decode_dm.py``) consumes.
"""

from __future__ import annotations

import numpy as np
import pandas as pd
import pytest

import train_moe_regimes as tmr


# ---------------------------------------------------------------------------
# Fixtures / helpers
# ---------------------------------------------------------------------------

@pytest.fixture
def synthetic_raw():
    np.random.seed(0)
    return tmr.generate_synthetic_data(560)


def _fake_walk_forward(n_folds=2):
    """Minimal fold list matching the recorder contract (no torch)."""
    return [
        {
            "fold": i,
            "train_end": 100 * (i + 1),
            "test_size": 40,
            "direction_accuracy": 0.5,
            "mse": 1.0,
            "n_experts": 1,
            "expert_regimes": ["bull"],
            "expert_stats": {},
            "regime_pred_counts": {"bull": 40},
            "oos_sq_errors": [0.5, 0.25] * 20,
        }
        for i in range(n_folds)
    ]


def _run_pipeline(monkeypatch, raw, *, regime_method, regime_decode="viterbi",
                  captured=None):
    def fake_detect(prices, method="price", **kwargs):
        if captured is not None:
            captured["method"] = method
            captured["kwargs"] = dict(kwargs)
        # Deterministic 2-regime labels aligned with the price index.
        labels = pd.Series(
            np.where(np.arange(len(prices)) % 7 < 4, "bull", "bear"),
            index=prices.index,
        )
        return labels

    monkeypatch.setattr(tmr, "detect_regimes", fake_detect)
    monkeypatch.setattr(
        tmr, "train_moe_regimes_walk_forward", lambda *a, **k: _fake_walk_forward()
    )
    return tmr.train_moe_regimes_pipeline(
        raw_data=raw,
        regime_method=regime_method,
        regime_decode=regime_decode,
        epochs=1,
        n_folds=2,
        min_samples=5,
    )


# ---------------------------------------------------------------------------
# Decode plumbing
# ---------------------------------------------------------------------------

class TestRegimeDecodePlumbing:
    def test_filter_decode_reaches_hmm_call(self, monkeypatch, synthetic_raw):
        captured: dict = {}
        result = _run_pipeline(
            monkeypatch, synthetic_raw,
            regime_method="hmm", regime_decode="filter", captured=captured,
        )
        assert captured["method"] == "hmm"
        assert captured["kwargs"].get("decode_mode") == "filter"
        assert result["regime_decode"] == "filter"
        assert result["regime_decode_causal"] is True
        assert "viterbi" in result["lookahead_note"].lower()

    def test_default_viterbi_reaches_hmm_call(self, monkeypatch, synthetic_raw):
        captured: dict = {}
        result = _run_pipeline(
            monkeypatch, synthetic_raw,
            regime_method="hmm", regime_decode="viterbi", captured=captured,
        )
        assert captured["kwargs"].get("decode_mode") == "viterbi"
        assert result["regime_decode"] == "viterbi"
        assert result["regime_decode_causal"] is False

    def test_price_method_gets_no_decode_kwarg(self, monkeypatch, synthetic_raw):
        captured: dict = {}
        result = _run_pipeline(
            monkeypatch, synthetic_raw,
            regime_method="price", regime_decode="filter", captured=captured,
        )
        assert "decode_mode" not in captured["kwargs"]
        assert result["regime_decode"] == "n/a"
        assert result["regime_decode_causal"] is True

    def test_multiseed_summary_carries_decode(self, monkeypatch, synthetic_raw):
        def fake_pipeline(**kwargs):
            return {
                "moe_mean_diracc": 0.5,
                "majority_baseline_acc": 0.5,
                "regime_decode": kwargs.get("regime_decode", "viterbi"),
            }

        monkeypatch.setattr(tmr, "train_moe_regimes_pipeline", fake_pipeline)
        summary = tmr.run_multiseed(
            seeds=[0, 1],
            raw_data=synthetic_raw,
            regime_method="hmm",
            regime_decode="filter",
            epochs=1,
            n_folds=2,
            min_samples=5,
        )
        assert summary["regime_decode"] == "filter"


# ---------------------------------------------------------------------------
# Seeding reproducibility
# ---------------------------------------------------------------------------

class TestSeeding:
    def test_torch_manual_seed_called_with_seed(self, monkeypatch, synthetic_raw):
        import torch

        calls: list[int] = []
        real_manual_seed = torch.manual_seed

        def spy(seed):
            calls.append(int(seed))
            return real_manual_seed(seed)

        monkeypatch.setattr(torch, "manual_seed", spy)
        _run_pipeline(monkeypatch, synthetic_raw, regime_method="price", regime_decode="viterbi")
        assert 42 in calls  # pipeline default seed (numpy seed was already seeded; torch now too)

    def test_same_seed_same_fold_losses(self, synthetic_raw):
        """Real (unmocked) tiny walk-forward: same seed twice -> identical losses."""
        r1 = tmr.train_moe_regimes_pipeline(
            raw_data=synthetic_raw, regime_method="price", seed=7,
            epochs=2, n_folds=2, min_samples=5,
        )
        r2 = tmr.train_moe_regimes_pipeline(
            raw_data=synthetic_raw, regime_method="price", seed=7,
            epochs=2, n_folds=2, min_samples=5,
        )
        e1 = [f["oos_sq_errors"] for f in r1["fold_details"]]
        e2 = [f["oos_sq_errors"] for f in r2["fold_details"]]
        assert len(e1) > 0 and len(e1) == len(e2)
        for a, b in zip(e1, e2):
            assert a == pytest.approx(b, rel=1e-9, abs=1e-12)


# ---------------------------------------------------------------------------
# Recorder contract for the DM comparison
# ---------------------------------------------------------------------------

class TestOosRecorder:
    def test_walk_forward_records_paired_losses(self, synthetic_raw):
        """The recorder output feeds moe_regimes_decode_dm.py: lengths must match y_test."""
        X, y, _cols = tmr.build_sequences(
            tmr.FeatureEngineer(lookback=20).transform(synthetic_raw), seq_len=20
        )
        labels = np.full(len(y), "bull")
        folds = tmr.train_moe_regimes_walk_forward(
            X, y, labels, expert_type="lstm", epochs=2, n_folds=2,
            min_samples=5, device="cpu",
        )
        assert folds, "expected at least one fold on 560 synthetic rows"
        for f in folds:
            assert len(f["oos_sq_errors"]) == f["test_size"]
            assert all(e >= 0 for e in f["oos_sq_errors"])
