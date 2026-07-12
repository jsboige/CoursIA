"""Tests for eval_rl_dt.py — Decision Transformer evaluation harness."""

from __future__ import annotations

import json
import tempfile
from pathlib import Path

import numpy as np
import pytest

from eval_rl_dt import (
    compute_max_drawdown,
    compute_sharpe,
    load_checkpoint,
    run_dry_run,
)


class TestComputeSharpe:
    """Sharpe ratio computation tests."""

    def test_empty_returns(self):
        assert compute_sharpe(np.array([])) == 0.0

    def test_single_return(self):
        assert compute_sharpe(np.array([0.01])) == 0.0

    def test_constant_returns(self):
        assert compute_sharpe(np.array([0.01] * 100)) == 0.0

    def test_positive_sharpe(self):
        rng = np.random.default_rng(42)
        returns = rng.normal(0.001, 0.01, 252)
        assert compute_sharpe(returns) > 0

    def test_negative_sharpe(self):
        rng = np.random.default_rng(99)
        returns = rng.normal(-0.005, 0.01, 252)
        assert compute_sharpe(returns) < 0

    def test_annualize_multiplier(self):
        rng = np.random.default_rng(42)
        returns = rng.normal(0.001, 0.01, 252)
        s_ann = compute_sharpe(returns, annualize=True)
        s_raw = compute_sharpe(returns, annualize=False)
        assert abs(s_ann) > abs(s_raw)


class TestComputeMaxDrawdown:
    """Max drawdown computation tests."""

    def test_empty(self):
        assert compute_max_drawdown(np.array([])) == 0.0

    def test_single_value(self):
        assert compute_max_drawdown(np.array([1.0])) == 0.0

    def test_monotonic_increase(self):
        cum = np.cumsum(np.array([0.01] * 50))
        assert compute_max_drawdown(cum) == 0.0

    def test_drawdown_detected(self):
        cum = np.array([0.0, 0.1, 0.2, 0.1, 0.0, -0.1])
        dd = compute_max_drawdown(cum)
        assert dd < 0

    def test_small_drawdown_on_dip(self):
        cum = np.array([0.0, 0.1, 0.2, 0.15, 0.2, 0.3])
        dd = compute_max_drawdown(cum)
        assert dd < 0  # dip from 0.2 to 0.15
        assert dd > -0.5  # but not catastrophic


class TestLoadCheckpoint:
    """Checkpoint loading tests."""

    def test_missing_metadata_raises(self, tmp_path):
        ckpt_dir = tmp_path / "no_meta"
        ckpt_dir.mkdir()
        with pytest.raises(FileNotFoundError, match="metadata.json"):
            load_checkpoint(ckpt_dir)

    def test_loads_model_and_metadata(self, tmp_path):
        import torch
        from train_rl_dt import DecisionTransformerModel

        ckpt_dir = tmp_path / "valid_ckpt"
        ckpt_dir.mkdir()

        model = DecisionTransformerModel(
            state_dim=10, d_model=32, nhead=2, num_layers=1,
            context_length=5, n_actions=3,
        )
        torch.save(model.state_dict(), ckpt_dir / "model.pt")

        metadata = {
            "model_type": "decision_transformer",
            "architecture": {
                "state_dim": 10, "d_model": 32, "nhead": 2,
                "num_layers": 1, "context_length": 5, "n_actions": 3,
            },
        }
        (ckpt_dir / "metadata.json").write_text(json.dumps(metadata))

        loaded_model, loaded_meta = load_checkpoint(ckpt_dir)
        assert loaded_meta["model_type"] == "decision_transformer"
        assert isinstance(loaded_model, DecisionTransformerModel)


class TestRunDryRun:
    """Dry-run integration tests."""

    def test_returns_dict(self):
        result = run_dry_run()
        assert isinstance(result, dict)
        assert result["dry_run"] is True

    def test_has_expected_keys(self):
        result = run_dry_run()
        for key in [
            "dry_run", "train_samples", "test_accuracy", "test_loss",
            "majority_class_baseline", "edge_over_majority",
            "sharpe", "max_drawdown",
        ]:
            assert key in result, f"Missing key: {key}"

    def test_sharpe_finite(self):
        result = run_dry_run()
        assert np.isfinite(result["sharpe"])

    def test_max_drawdown_non_positive(self):
        result = run_dry_run()
        assert result["max_drawdown"] <= 0.0

    def test_train_samples_positive(self):
        result = run_dry_run()
        assert result["train_samples"] > 0
