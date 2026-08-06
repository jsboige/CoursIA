"""Tests for analyze_moe_754.py -- MoE+regimes verdict harness for issue #754.

The harness codifies the anti-complaisance QC validation criteria (CLAUDE.md
section C/H, regles-vigilance G.2): a model "BEATS" the majority baseline ONLY
when it is simultaneously (a) above baseline in mean direction accuracy, (b)
statistically significant at p<0.05 across seeds, AND (c) the edge exceeds
2*std cross-seed. Below baseline + significant = NO BEATS; anything else with
<4 seeds or a non-significant edge = INCONCLUSIVE. Profitability is judged
independently against a 10 bps crypto round-trip transaction cost.

These tests lock those thresholds in place so a future edit cannot quietly
relax one gate (e.g. drop the 2*std edge, or widen alpha) to manufacture a
BEATS. CPU-only: they drive the real scipy.stats.ttest_1samp path used in
production, with hand-built seed groups chosen so scipy produces p-values
clearly above/below 0.05.
"""

import json
import sys
from pathlib import Path

import pytest

# ``analyze_moe_754`` is a standalone script (sibling of ``tests/``), not a
# package member; put its directory on the path. NOTE: this points straight at
# ``scripts/`` (``parent.parent``) rather than ``parent.parent / "scripts"``
# (which would resolve to a non-existent ``scripts/scripts``) -- the redundant
# ``/ "scripts"`` seen in some sibling test files is a latent bug that only
# works because pytest's own sys.path insertion saves it.
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from analyze_moe_754 import load_results, verdict  # noqa: E402


def _result_json(mean_diracc, baseline, *, std=0.01, folds=None, n_folds=5,
                 n_samples=1000, beats=None, regimes=None):
    """Build the dict shape ``load_results`` reads from each seed JSON file."""
    return {
        "moe_mean_diracc": mean_diracc,
        "moe_std_diracc": std,
        "moe_fold_diraccs": folds if folds is not None else [mean_diracc] * n_folds,
        "majority_baseline_acc": baseline,
        "beats_majority": beats if beats is not None else (mean_diracc > baseline),
        "regime_counts": regimes if regimes is not None else {"bull": 60, "bear": 40},
        "n_folds": n_folds,
        "n_samples": n_samples,
    }


def _seed_file(results_dir, symbol, expert, method, seed, **payload):
    """Write one ``moe_regimes_<symbol>_<expert>_<method>_seed<N>.json`` fixture."""
    path = results_dir / f"moe_regimes_{symbol}_{expert}_{method}_seed{seed}.json"
    path.write_text(json.dumps(_result_json(**payload)), encoding="utf-8")
    return path


class TestLoadResults:
    """Filename parsing + JSON loading into the ``{symbol_method: [entries]}`` map."""

    def test_two_symbols_two_seeds_each_builds_two_groups(self, tmp_path):
        _seed_file(tmp_path, "BTC-USD", "lstm", "hmm", 0, mean_diracc=0.55, baseline=0.50)
        _seed_file(tmp_path, "BTC-USD", "lstm", "hmm", 1, mean_diracc=0.56, baseline=0.50)
        _seed_file(tmp_path, "ETH-USD", "lstm", "hmm", 0, mean_diracc=0.52, baseline=0.50)
        _seed_file(tmp_path, "ETH-USD", "lstm", "hmm", 1, mean_diracc=0.53, baseline=0.50)

        groups = load_results(str(tmp_path))

        assert set(groups.keys()) == {"BTC-USD_hmm", "ETH-USD_hmm"}
        assert len(groups["BTC-USD_hmm"]) == 2
        assert len(groups["ETH-USD_hmm"]) == 2

    def test_entry_exposes_all_documented_fields(self, tmp_path):
        _seed_file(tmp_path, "SPY", "transformer", "gmm", 7,
                   mean_diracc=0.54, baseline=0.52, std=0.02, n_folds=5, n_samples=2500)
        groups = load_results(str(tmp_path))
        entry = groups["SPY_gmm"][0]
        # Every key the verdict harness consults or forwards must survive loading.
        for key in ("seed", "diracc", "std", "fold_diraccs", "baseline",
                    "beats", "regimes", "n_folds", "n_samples"):
            assert key in entry, f"missing field {key!r} after load_results"
        assert entry["diracc"] == 0.54
        assert entry["baseline"] == 0.52
        assert entry["n_samples"] == 2500

    def test_seed_string_parsed_as_int(self, tmp_path):
        _seed_file(tmp_path, "BTC-USD", "lstm", "hmm", 0, mean_diracc=0.55, baseline=0.50)
        _seed_file(tmp_path, "BTC-USD", "lstm", "hmm", 42, mean_diracc=0.56, baseline=0.50)
        groups = load_results(str(tmp_path))
        seeds = sorted(e["seed"] for e in groups["BTC-USD_hmm"])
        assert seeds == [0, 42]
        assert all(isinstance(s, int) for s in seeds)

    def test_hyphenated_symbol_preserved_in_group_key(self, tmp_path):
        # ``split('_')`` must keep the '-' inside ``BTC-USD`` intact (real symbols
        # use hyphens); only underscores are field separators.
        _seed_file(tmp_path, "BTC-USD", "lstm", "hmm", 0, mean_diracc=0.55, baseline=0.50)
        groups = load_results(str(tmp_path))
        assert "BTC-USD_hmm" in groups

    def test_empty_directory_returns_empty_map(self, tmp_path):
        assert load_results(str(tmp_path)) == {}

    def test_non_matching_filename_ignored(self, tmp_path):
        # The glob is ``moe_regimes_*_seed*.json``; unrelated files are skipped.
        _seed_file(tmp_path, "BTC-USD", "lstm", "hmm", 0, mean_diracc=0.55, baseline=0.50)
        (tmp_path / "summary.json").write_text("{}", encoding="utf-8")
        (tmp_path / "moe_regimes_other.txt").write_text("noise", encoding="utf-8")
        groups = load_results(str(tmp_path))
        assert list(groups.keys()) == ["BTC-USD_hmm"]


class TestVerdict:
    """The BEATS / NO BEATS / INCONCLUSIVE decision rule + tx-cost gate.

    Fixtures were chosen so scipy.stats.ttest_1samp yields p-values clearly on
    one side of 0.05 (verified empirically before writing these assertions).
    """

    @staticmethod
    def _group(symbol, method, baseline, diraccs):
        return {
            f"{symbol}_{method}": [
                {"seed": i, "diracc": d, "baseline": baseline}
                for i, d in enumerate(diraccs)
            ]
        }

    def test_beats_significant_above_baseline(self):
        # 4 seeds clearly above baseline -> mean 0.595, p~7e-4, delta >> 2*std.
        groups = self._group("BTC-USD", "hmm", 0.50, [0.58, 0.59, 0.60, 0.61])
        table = verdict(groups)
        assert len(table) == 1
        row = table[0]
        assert row["verdict"] == "BEATS"
        assert row["coin"] == "BTC-USD"
        assert row["method"] == "hmm"
        assert row["seeds"] == 4
        assert row["p_value"] < 0.05
        assert row["delta_pp"] > 0
        # 950 bps edge comfortably clears the 10 bps crypto round-trip cost.
        assert bool(row["profitable_after_tx"])

    def test_no_beats_significant_below_baseline(self):
        # 4 seeds clearly below baseline -> mean 0.415, p~1e-3.
        groups = self._group("ETH-USD", "hmm", 0.50, [0.40, 0.41, 0.42, 0.43])
        table = verdict(groups)
        assert table[0]["verdict"] == "NO BEATS"
        assert table[0]["p_value"] < 0.05
        assert table[0]["delta_pp"] < 0
        assert not table[0]["profitable_after_tx"]

    def test_inconclusive_when_fewer_than_four_seeds(self):
        # 3 seeds, edge barely above baseline and NOT significant (p~0.48):
        # both BEATS and NO BEATS gates fail on alpha, then n<4 fires.
        groups = self._group("SPY", "hmm", 0.50, [0.49, 0.51, 0.53])
        table = verdict(groups)
        assert table[0]["verdict"] == "INCONCLUSIVE (<4 seeds)"
        assert table[0]["p_value"] > 0.05

    def test_inconclusive_when_not_significant_at_four_seeds(self):
        # 4 seeds hovering at baseline -> mean 0.505, p~0.50 (not significant).
        groups = self._group("SPY", "gmm", 0.50, [0.49, 0.50, 0.51, 0.52])
        table = verdict(groups)
        assert table[0]["verdict"] == "INCONCLUSIVE"
        assert table[0]["p_value"] > 0.05

    def test_beats_but_not_profitable_after_transaction_costs(self):
        # Anti-complaisance distinction: a result can be statistically BEATS
        # yet UNPROFITABLE once the 10 bps crypto round-trip is paid. Tiny but
        # very consistent edge -> p~1e-3, delta>2*std (so BEATS), but only
        # ~5 bps of edge < 10 bps cost. Statistical significance is not profitability.
        groups = self._group("BTC-USD", "hmm", 0.50,
                             [0.5005, 0.5004, 0.5006, 0.5005])
        table = verdict(groups)
        row = table[0]
        assert row["verdict"] == "BEATS"
        assert row["p_value"] < 0.05
        assert not row["profitable_after_tx"]

    def test_baseline_propagated_into_result_row(self):
        groups = self._group("SPY", "hmm", 0.535, [0.58, 0.59, 0.60, 0.61])
        table = verdict(groups)
        assert table[0]["baseline"] == pytest.approx(0.535)

    def test_multiple_groups_each_get_own_verdict(self):
        groups = {}
        groups.update(self._group("BTC-USD", "hmm", 0.50, [0.58, 0.59, 0.60, 0.61]))
        groups.update(self._group("ETH-USD", "hmm", 0.50, [0.40, 0.41, 0.42, 0.43]))
        table = verdict(groups)
        assert len(table) == 2
        verdicts = {row["coin"]: row["verdict"] for row in table}
        assert verdicts["BTC-USD"] == "BEATS"
        assert verdicts["ETH-USD"] == "NO BEATS"

    def test_result_row_has_all_documented_columns(self):
        groups = self._group("SPY", "hmm", 0.50, [0.58, 0.59, 0.60, 0.61])
        row = verdict(groups)[0]
        for key in ("coin", "method", "seeds", "mean_diracc", "std_diracc",
                    "baseline", "delta_pp", "p_value", "verdict",
                    "profitable_after_tx"):
            assert key in row, f"results_table missing column {key!r}"
