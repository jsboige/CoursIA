"""Tests for paired_rung_comparison.py -- paired cross-rung edge comparison.

CPU-only unit tests on the per-seed extractors, the paired statistical battery
(analytically known t-stats), and the deterministic-vs-perseed alignment. The
real Kronos<->M15 verdict is proven by the committed paired_comparison.json,
not by these tests.
"""

import math
import sys
from pathlib import Path

import numpy as np
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))

from paired_rung_comparison import (  # noqa: E402
    _chronos_per_config,
    _kronos_per_seed,
    _m15_per_seed,
    compare,
    extract_per_seed,
    paired_battery,
    render_md,
)


# ---------------------------------------------------------------------------
# Synthetic minimal docs (same shapes as the real results.json)
# ---------------------------------------------------------------------------

def _kronos_doc(edges_by_seed):
    """edges_by_seed: {(sym, h, seed): edge}. majority fixed at 0.55."""
    sweep = []
    for (sym, h), seed_edges in edges_by_seed.items():
        sr = [{"seed": sd, "edge_vs_majority": e, "avg_direction_accuracy": 0.55 + e,
               "majority_baseline": 0.55} for sd, e in seed_edges.items()]
        sweep.append({"symbol": sym, "pred_len": h, "majority_baseline":
                      {"majority_class_accuracy": 0.55}, "seed_results": sr})
    return {"model": "NeoQuasar/Kronos-base", "sweep": sweep}


def _m15_doc(edges_by_combo):
    """edges_by_combo: {(sym, h, seed): edge}."""
    combos = []
    for (sym, h, seed), e in edges_by_combo.items():
        combos.append({"symbol": sym, "horizon": h, "seed": seed,
                       "direction_accuracy": 0.55 + e,
                       "majority_baseline": {"majority_class_accuracy": 0.55},
                       "edge_vs_majority": e})
    return {"model": "Log-LSTM ETF-direction (M15)", "combos": combos,
            "summary": []}


def _chronos_doc(edges_by_cfg):
    """edges_by_cfg: {(sym, h): edge}."""
    sweep = [{"symbol": sym, "pred_len": h, "diracc": 0.55 + e,
              "majority": 0.55, "edge": e, "mean_edge": e, "std_edge": 0.0}
             for (sym, h), e in edges_by_cfg.items()]
    return {"model": "amazon/chronos-bolt-base", "sweep": sweep}


class TestExtractPerSeed:
    def test_kronos_extracts_all_seeds(self):
        doc = _kronos_doc({("SPY", 24): {0: -0.01, 1: -0.02, 99: -0.03}})
        edges, name, det = extract_per_seed(doc)
        assert name == "Kronos" and det is False
        assert edges[("SPY", 24, 0)] == pytest.approx(-0.01)
        assert edges[("SPY", 24, 99)] == pytest.approx(-0.03)
        assert len(edges) == 3

    def test_m15_extracts_per_combo(self):
        doc = _m15_doc({("GLD", 66, 7): -0.03, ("TLT", 132, 0): -0.01})
        edges, name, det = extract_per_seed(doc)
        assert name == "M15" and det is False
        assert edges[("GLD", 66, 7)] == pytest.approx(-0.03)
        assert len(edges) == 2

    def test_chronos_deterministic_flag(self):
        doc = _chronos_doc({("SPY", 24): -0.05})
        edges, name, det = extract_per_seed(doc)
        assert name == "Chronos-Bolt" and det is True
        # Chronos key has seed=None (deterministic, single value per config)
        assert edges[("SPY", 24, None)] == pytest.approx(-0.05)

    def test_m15_fallback_diracc_minus_majority(self):
        # If edge_vs_majority is missing, fall back to direction_accuracy - majority.
        combos = [{"symbol": "SPY", "horizon": 24, "seed": 0,
                   "direction_accuracy": 0.50,
                   "majority_baseline": {"majority_class_accuracy": 0.55}}]
        edges = _m15_per_seed(combos)
        assert edges[("SPY", 24, 0)] == pytest.approx(0.50 - 0.55)

    def test_kronos_fallback_diracc_minus_majority(self):
        sweep = [{"symbol": "SPY", "pred_len": 24,
                  "majority_baseline": {"majority_class_accuracy": 0.55},
                  "seed_results": [{"seed": 0, "avg_direction_accuracy": 0.50}]}]
        edges = _kronos_per_seed(sweep)
        assert edges[("SPY", 24, 0)] == pytest.approx(0.50 - 0.55)


class TestPairedBattery:
    def test_known_t_stat(self):
        # diffs with known mean/std -> analytic t-stat.
        # mean=0.02, and chosen so std gives a round t. Use a simple series.
        diffs = np.array([0.02, 0.02, 0.02, 0.02, 0.02])  # std=0 -> t=inf
        out = paired_battery(diffs)
        assert out["n_pairs"] == 5
        assert math.isinf(out["t_stat"]) or abs(out["t_stat"]) > 1e6
        assert out["t_p_value"] == pytest.approx(0.0)

    def test_zero_diff_not_significant(self):
        diffs = np.array([0.0, 0.0, 0.0, 0.0, 0.0, 0.0])
        out = paired_battery(diffs)
        assert out["significant_at_alpha"] is False
        assert out["mean_diff"] == 0.0

    def test_symmetric_diff_zero_mean(self):
        # +x and -x balanced -> mean 0 -> not significant.
        diffs = np.array([0.05, -0.05, 0.03, -0.03, 0.04, -0.04, 0.02, -0.02])
        out = paired_battery(diffs)
        assert abs(out["mean_diff"]) < 1e-9
        assert out["significant_at_alpha"] is False
        assert out["sign_n_pos"] == 4 and out["sign_n_neg"] == 4

    def test_clearly_different_is_significant(self):
        # All diffs positive, large vs std -> significant, B better than A.
        diffs = np.array([0.1, 0.12, 0.09, 0.11, 0.13, 0.10, 0.08, 0.12])
        out = paired_battery(diffs)
        assert out["significant_at_alpha"] is True
        assert "B better" in out["direction"]
        assert out["ci95_low"] > 0  # CI excludes 0

    def test_ci_straddles_zero(self):
        diffs = np.array([0.05, -0.05, 0.04, -0.04, 0.06, -0.06])
        out = paired_battery(diffs)
        assert out["ci95_low"] < 0 < out["ci95_high"]

    def test_n_below_2(self):
        out = paired_battery(np.array([0.1]))
        assert "n<2" in out["verdict"]
        assert out["significant_at_alpha"] is False


class TestCompare:
    def test_kronos_vs_m15_full_alignment(self):
        seeds = {0: -0.03, 1: -0.035, 7: -0.04}
        kronos = _kronos_doc({("SPY", 24): seeds, ("GLD", 66): seeds})
        m15 = _m15_doc({("SPY", 24, s): e for s, e in seeds.items()})
        # Add GLD to M15 too for full alignment (2 configs x 3 seeds = 6 pairs)
        m15["combos"].extend([{"symbol": "GLD", "horizon": 66, "seed": s,
                               "direction_accuracy": 0.55 + e + 0.001,
                               "majority_baseline": {"majority_class_accuracy": 0.55},
                               "edge_vs_majority": e + 0.001} for s, e in seeds.items()])
        out = compare(kronos, m15)
        assert out["rung_a"] == "Kronos" and out["rung_b"] == "M15"
        assert out["n_common_keys"] == 6  # 2 configs x 3 seeds
        # Only GLD has the +0.001 offset (3 pairs); SPY diffs are 0 (3 pairs).
        # mean diff = (0*3 + 0.001*3) / 6 = 0.0005
        assert out["battery"]["mean_diff"] == pytest.approx(0.0005, abs=1e-9)

    def test_deterministic_vs_perseed_pairs_each_seed(self):
        chronos = _chronos_doc({("SPY", 24): -0.05})
        kronos = _kronos_doc({("SPY", 24): {0: -0.02, 1: -0.03, 7: -0.01}})
        out = compare(chronos, kronos)  # A=deterministic, B=per-seed
        assert out["rung_a_deterministic"] is True
        # 3 pairs: each Kronos seed paired against the Chronos constant -0.05.
        assert out["n_common_keys"] == 3
        assert out["battery"]["mean_diff"] == pytest.approx(np.mean([-0.02, -0.03, -0.01]) - (-0.05))

    def test_no_common_keys(self):
        kronos = _kronos_doc({("SPY", 24): {0: -0.01}})
        m15 = _m15_doc({("TLT", 66, 0): -0.02})  # disjoint
        out = compare(kronos, m15)
        assert out["n_common_keys"] == 0
        assert out["battery"]["n_pairs"] == 0

    def test_render_md_contains_verdict(self):
        kronos = _kronos_doc({("SPY", 24): {0: -0.01, 1: -0.02}})
        m15 = _m15_doc({("SPY", 24, 0): -0.01, ("SPY", 24, 1): -0.02})
        out = compare(kronos, m15)
        md = render_md(out)
        assert "Paired cross-rung comparison" in md
        assert "verdict" in md
        assert "Kronos" in md and "M15" in md
