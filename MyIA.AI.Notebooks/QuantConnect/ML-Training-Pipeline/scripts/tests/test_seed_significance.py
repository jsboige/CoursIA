"""Tests for seed_significance.py -- one-sample edge significance battery.

These are CPU-only unit tests on the statistical helpers + format auto-detection.
Real significance verdicts on the anti-bias basket are proven by the committed
seed_significance.json (Kronos), not by these tests.
"""

import sys
from pathlib import Path

import numpy as np
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))

from seed_significance import (  # noqa: E402
    analyze_config,
    auto_extract,
    render_md,
    run,
    sign_test,
)


class TestSignTest:
    def test_balanced(self):
        # 3 pos, 3 neg -> p=1.0 (perfectly balanced)
        edges = np.array([0.1, 0.2, 0.05, -0.1, -0.2, -0.05])
        out = sign_test(edges)
        assert out["n_pos"] == 3 and out["n_neg"] == 3
        assert abs(out["p_value"] - 1.0) < 1e-9

    def test_all_positive(self):
        # 6 pos, 0 neg -> very unlikely under p=0.5 -> significant.
        # (n=5 all-positive gives p=2*(0.5)^5=0.0625, just above 0.05 -- a real
        # small-n power limit, not a bug; use n=6 to land clearly under 0.05.)
        edges = np.array([0.1, 0.2, 0.05, 0.3, 0.15, 0.08])
        out = sign_test(edges)
        assert out["n_pos"] == 6 and out["n_neg"] == 0
        assert out["p_value"] < 0.05

    def test_all_positive_n5_documents_small_n_limit(self):
        # n=5 all-positive -> p=0.0625 exactly (just above 0.05). Documents the
        # honest small-n ceiling of the sign test, not a code defect.
        edges = np.array([0.1, 0.2, 0.05, 0.3, 0.15])
        out = sign_test(edges)
        assert out["n_pos"] == 5 and out["n_neg"] == 0
        assert out["p_value"] == pytest.approx(0.0625)

    def test_all_zero(self):
        edges = np.zeros(5)
        out = sign_test(edges)
        assert out["p_value"] == 1.0  # no nonzero -> cannot reject balance

    def test_empty(self):
        out = sign_test(np.array([]))
        assert out["n"] == 0
        assert np.isnan(out["p_value"])


class TestAnalyzeConfig:
    def test_zero_edge_not_significant(self):
        # Symmetric edges around 0 -> mean 0 -> not significant
        edges_diracc = np.array([0.54, 0.52, 0.50, 0.48, 0.46])  # mean 0.50
        out = analyze_config("SYM", 24, majority=0.50,
                             diraccs=edges_diracc, deterministic=False)
        assert out["n_seeds"] == 5
        assert abs(out["mean_edge"]) < 1e-9
        assert abs(out["t_stat"]) < 1e-6
        assert out["t_p_value"] > 0.90
        assert out["significant_at_alpha"] is False
        assert "NOT SIGNIFICANT" in out["verdict"]

    def test_all_negative_significant(self):
        # All seeds clearly under majority -> significant-negative
        out = analyze_config("SYM", 66, majority=0.55,
                             diraccs=[0.45, 0.46, 0.44, 0.45, 0.47],
                             deterministic=False)
        assert out["mean_edge"] < 0
        assert out["significant_at_alpha"] is True
        assert "SIGNIFICANT-NEGATIVE" in out["verdict"]

    def test_identical_nonzero_edge_significant(self):
        # Zero variance, nonzero mean -> certain -> significant
        out = analyze_config("SYM", 132, majority=0.55,
                             diraccs=[0.50, 0.50, 0.50, 0.50, 0.50],
                             deterministic=False)
        assert out["mean_edge"] == pytest.approx(-0.05)
        assert out["std_edge"] == 0.0
        assert out["significant_at_alpha"] is True

    def test_degenerate_deterministic(self):
        out = analyze_config("SYM", 24, majority=0.55,
                             diraccs=[0.49], deterministic=True)
        assert "DEGENERATE" in out["verdict"]
        assert np.isnan(out["t_stat"])
        assert out["significant_at_alpha"] is False

    def test_ci_brackets_mean(self):
        out = analyze_config("SYM", 24, majority=0.50,
                             diraccs=[0.40, 0.42, 0.41, 0.43, 0.39],
                             deterministic=False)
        # 95% CI should contain the mean and both bounds should be negative here
        assert out["ci95_low"] < out["mean_edge"] < out["ci95_high"]
        assert out["ci95_high"] < 0


class TestAutoExtract:
    def test_kronos_format(self):
        doc = {
            "model": "Kronos",
            "sweep": [{
                "symbol": "SPY", "pred_len": 24,
                "majority_baseline": {"majority_class_accuracy": 0.55},
                "seed_results": [
                    {"seed": 0, "avg_direction_accuracy": 0.50},
                    {"seed": 1, "avg_direction_accuracy": 0.48},
                ],
            }],
        }
        rows, model = auto_extract(doc)
        assert model == "Kronos"
        assert rows[0]["symbol"] == "SPY"
        assert rows[0]["majority"] == 0.55
        assert rows[0]["diraccs"] == [0.50, 0.48]

    def test_chronos_format(self):
        doc = {
            "model": "Chronos-Bolt",
            "sweep": [{
                "symbol": "SPY", "pred_len": 24, "majority": 0.55,
                "diracc": 0.49, "std_edge": 0.0,
            }],
        }
        rows, model = auto_extract(doc)
        assert model == "Chronos-Bolt"
        assert rows[0]["diraccs"] == [0.49]
        assert rows[0].get("deterministic") is True

    def test_m15_format(self):
        doc = {
            "model": "M15",
            "summary": [],
            "combos": [
                {"symbol": "TLT", "horizon": 24, "direction_accuracy": 0.49,
                 "majority_baseline": {"majority_class_accuracy": 0.51}},
                {"symbol": "TLT", "horizon": 24, "direction_accuracy": 0.50,
                 "majority_baseline": {"majority_class_accuracy": 0.51}},
            ],
        }
        rows, model = auto_extract(doc)
        assert model == "M15"
        assert rows[0]["symbol"] == "TLT"
        assert rows[0]["diraccs"] == [0.49, 0.50]
        assert rows[0]["majority"] == 0.51

    def test_unrecognized_raises(self):
        with pytest.raises(ValueError):
            auto_extract({"model": "???"})


class TestRunAndRender:
    def test_run_kronos_doc(self, tmp_path):
        doc = {
            "model": "Kronos",
            "sweep": [{
                "symbol": "SPY", "pred_len": 24,
                "majority_baseline": {"majority_class_accuracy": 0.55},
                "seed_results": [
                    {"seed": i, "avg_direction_accuracy": v}
                    for i, v in enumerate([0.45, 0.44, 0.46, 0.45, 0.43])
                ],
            }],
        }
        p = tmp_path / "results.json"
        p.write_text(__import__("json").dumps(doc))
        out = run(p)
        assert out["model"] == "Kronos"
        assert out["n_configs"] == 1
        assert out["n_significant"] == 1  # all clearly under majority
        md = render_md(out)
        assert "Kronos" in md
        assert "SPY" in md
