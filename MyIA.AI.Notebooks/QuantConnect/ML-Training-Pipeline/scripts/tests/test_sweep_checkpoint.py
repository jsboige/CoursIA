"""Tests for sweep_checkpoint.py — generic sweep checkpoint-resume utility."""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from sweep_checkpoint import SweepCheckpoint


@pytest.fixture
def sweep_dir(tmp_path):
    return tmp_path / "sweep_test"


class TestSweepCheckpointInit:
    def test_creates_output_dir(self, sweep_dir):
        SweepCheckpoint(sweep_dir, resume=False)
        assert sweep_dir.exists()

    def test_generates_seed_symbol_combos(self, sweep_dir):
        sc = SweepCheckpoint(sweep_dir, seeds=[0, 1], symbols=["SPY", "ETH"], resume=False)
        done, total = sc.progress
        assert total == 4  # 2 seeds x 2 symbols
        assert done == 0

    def test_generates_extra_param_grid(self, sweep_dir):
        sc = SweepCheckpoint(
            sweep_dir, seeds=[42], symbols=["SPY"],
            extra_param_grid={"hidden_size": [64, 128], "layers": [1, 2]},
            resume=False,
        )
        done, total = sc.progress
        assert total == 4  # 1 seed x 1 symbol x 2 hidden x 2 layers

    def test_generates_only_seeds_when_no_symbols(self, sweep_dir):
        sc = SweepCheckpoint(sweep_dir, seeds=[0, 7, 42], resume=False)
        done, total = sc.progress
        assert total == 3


class TestSweepCheckpointIteration:
    def test_yields_all_combos(self, sweep_dir):
        sc = SweepCheckpoint(sweep_dir, seeds=[0, 1], symbols=["SPY"], resume=False)
        combos = list(sc.remaining())
        assert len(combos) == 2
        assert all("seed" in c and "symbol" in c for c in combos)

    def test_mark_done_reduces_pending(self, sweep_dir):
        sc = SweepCheckpoint(sweep_dir, seeds=[0, 1], symbols=["SPY"], resume=False)
        for combo in sc.remaining():
            sc.mark_done(combo, {"mse": 0.01})
        done, total = sc.progress
        assert done == 2
        assert total == 2

    def test_state_file_updated_after_mark_done(self, sweep_dir):
        sc = SweepCheckpoint(sweep_dir, seeds=[0], symbols=["SPY"], resume=False)
        for combo in sc.remaining():
            sc.mark_done(combo, {"sharpe": 1.5})
            break
        state = json.loads((sweep_dir / "sweep_state.json").read_text(encoding="utf-8"))
        assert len(state["completed"]) == 1
        assert state["completed"][0]["metrics"]["sharpe"] == 1.5


class TestSweepCheckpointResume:
    def test_resume_skips_completed(self, sweep_dir):
        sc1 = SweepCheckpoint(sweep_dir, seeds=[0, 1, 42], symbols=["SPY"], resume=False)
        count = 0
        for combo in sc1.remaining():
            sc1.mark_done(combo, {"dir_acc": 0.55})
            count += 1
            if count >= 2:
                break

        done1, _ = sc1.progress
        assert done1 == 2

        sc2 = SweepCheckpoint(sweep_dir, seeds=[0, 1, 42], symbols=["SPY"], resume=True)
        done2, total = sc2.progress
        assert done2 == 2
        assert total == 3

        remaining = list(sc2.remaining())
        assert len(remaining) == 1

    def test_fresh_start_ignores_existing(self, sweep_dir):
        sc1 = SweepCheckpoint(sweep_dir, seeds=[0, 1], symbols=["SPY"], resume=False)
        for combo in sc1.remaining():
            sc1.mark_done(combo, {"mse": 0.01})

        sc2 = SweepCheckpoint(sweep_dir, seeds=[0, 1], symbols=["SPY"], resume=False)
        done, total = sc2.progress
        assert done == 0
        assert total == 2


class TestSweepCheckpointFinalize:
    def test_finalize_creates_summary(self, sweep_dir):
        sc = SweepCheckpoint(sweep_dir, seeds=[0, 1], symbols=["SPY"], resume=False)
        for combo in sc.remaining():
            sc.mark_done(combo, {"mse": 0.01})
        summary = sc.finalize()

        assert summary["completed"] == 2
        assert summary["total_combos"] == 2
        assert summary["remaining"] == 0
        assert "elapsed_s" in summary
        assert (sweep_dir / "sweep_summary.json").exists()

    def test_partial_finalize(self, sweep_dir):
        sc = SweepCheckpoint(sweep_dir, seeds=[0, 1, 42], symbols=["SPY"], resume=False)
        for combo in sc.remaining():
            sc.mark_done(combo, {"mse": 0.01})
            break
        summary = sc.finalize()
        assert summary["completed"] == 1
        assert summary["remaining"] == 2


class TestSweepCheckpointResults:
    def test_results_returns_completed(self, sweep_dir):
        sc = SweepCheckpoint(sweep_dir, seeds=[0, 1], symbols=["SPY"], resume=False)
        for combo in sc.remaining():
            sc.mark_done(combo, {"dir_acc": 0.6})
        assert len(sc.results) == 2
        assert sc.results[0]["metrics"]["dir_acc"] == 0.6
