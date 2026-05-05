"""Tests for demo_tsflow.py — CPU-only smoke tests for Stage 6 TSFlow demo."""

import sys
from pathlib import Path

import numpy as np
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))

from demo_tsflow import ScenarioGenerator, SimpleFlowMatcher, run_demo


class TestSimpleFlowMatcher:
    def test_generate_shape(self):
        fm = SimpleFlowMatcher(seq_len=48, hidden_dim=32)
        samples = fm.generate(n_samples=5, n_steps=10, seed=42)
        assert samples.shape == (5, 48)

    def test_generate_deterministic(self):
        fm = SimpleFlowMatcher(seq_len=24, hidden_dim=16)
        s1 = fm.generate(n_samples=3, n_steps=5, seed=123)
        s2 = fm.generate(n_samples=3, n_steps=5, seed=123)
        np.testing.assert_array_equal(s1, s2)

    def test_generate_different_seeds(self):
        fm = SimpleFlowMatcher(seq_len=24, hidden_dim=16)
        s1 = fm.generate(n_samples=3, n_steps=5, seed=1)
        s2 = fm.generate(n_samples=3, n_steps=5, seed=2)
        assert not np.allclose(s1, s2)


class TestScenarioGenerator:
    def test_scenario_types(self):
        gen = ScenarioGenerator()
        assert len(gen.SCENARIO_PARAMS) == 8
        expected = {
            "baseline", "bull", "bear", "flash_crash",
            "volatility_spike", "mean_reversion", "trending_up", "range_bound",
        }
        assert set(gen.SCENARIO_PARAMS.keys()) == expected

    def test_generate_path_shape(self):
        gen = ScenarioGenerator()
        path = gen.generate_path("baseline", seq_len=96, seed=42)
        assert path.shape == (96,)

    def test_generate_path_positive_prices(self):
        gen = ScenarioGenerator()
        path = gen.generate_path("baseline", seq_len=96, seed=42)
        assert np.all(path > 0)

    def test_bull_positive_drift(self):
        gen = ScenarioGenerator()
        paths = np.array(
            [gen.generate_path("bull", seq_len=96, seed=i) for i in range(200)]
        )
        final_returns = paths[:, -1] / paths[:, 0] - 1
        assert np.mean(final_returns) > 0

    def test_bear_negative_drift(self):
        gen = ScenarioGenerator()
        paths = np.array(
            [gen.generate_path("bear", seq_len=96, seed=i) for i in range(200)]
        )
        final_returns = paths[:, -1] / paths[:, 0] - 1
        assert np.mean(final_returns) < 0

    def test_generate_scenarios_all_types(self):
        gen = ScenarioGenerator()
        scenarios = gen.generate_scenarios(n_per_type=5, seq_len=48)
        assert len(scenarios) == 8
        for name, paths in scenarios.items():
            assert paths.shape == (5, 48)

    def test_deterministic_with_seed(self):
        gen = ScenarioGenerator()
        p1 = gen.generate_path("baseline", seq_len=48, seed=99)
        p2 = gen.generate_path("baseline", seq_len=48, seed=99)
        np.testing.assert_array_equal(p1, p2)


class TestScenarioStats:
    def test_stats_keys(self):
        gen = ScenarioGenerator()
        paths = np.array(
            [gen.generate_path("baseline", seq_len=96, seed=i) for i in range(10)]
        )
        stats = gen.compute_scenario_stats(paths)
        expected_keys = {
            "n_paths", "seq_len", "mean_final_return",
            "std_final_return", "mean_volatility", "max_drawdown", "pct_positive",
        }
        assert set(stats.keys()) == expected_keys

    def test_stats_values_range(self):
        gen = ScenarioGenerator()
        paths = np.array(
            [gen.generate_path("baseline", seq_len=96, seed=i) for i in range(20)]
        )
        stats = gen.compute_scenario_stats(paths)
        assert stats["n_paths"] == 20
        assert stats["seq_len"] == 96
        assert 0.0 <= stats["pct_positive"] <= 1.0
        assert stats["max_drawdown"] >= 0
        assert stats["mean_volatility"] > 0

    def test_flash_crash_high_drawdown(self):
        gen = ScenarioGenerator()
        paths = np.array(
            [gen.generate_path("flash_crash", seq_len=96, seed=i) for i in range(50)]
        )
        stats = gen.compute_scenario_stats(paths)
        assert stats["mean_volatility"] > 0.03
        assert stats["mean_final_return"] < -0.1


class TestRunDemo:
    def test_dry_run_returns_results(self):
        import argparse

        args = argparse.Namespace(
            dry_run=True, seq_len=48, n_scenarios=5, output_dir=None
        )
        results = run_demo(args)
        assert "timestamp" in results
        assert results["seq_len"] == 48
        assert results["n_scenarios_per_type"] == 5
        assert len(results["scenario_types"]) == 8
        assert len(results["statistics"]) == 8
