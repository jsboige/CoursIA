"""Tests for run_panier_baselines.py orchestration script."""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))

from panier_loader import PANIER_GROUPS, get_panier_symbols
from run_panier_baselines import _get_group, collect_results


class TestGetGroup:
    def test_spy_is_us_equity_broad(self):
        assert _get_group("SPY") == "us_equity_broad"

    def test_xlf_is_sector(self):
        assert _get_group("XLF") == "us_equity_sectors"

    def test_vix_is_volatility(self):
        assert _get_group("VIX") == "volatility"

    def test_tlt_is_bonds(self):
        assert _get_group("TLT") == "us_bonds"

    def test_gld_is_commodities(self):
        assert _get_group("GLD") == "commodities"

    def test_efa_is_international(self):
        assert _get_group("EFA") == "international"

    def test_btc_is_crypto(self):
        assert _get_group("BTC-USD") == "crypto"

    def test_unknown_symbol(self):
        assert _get_group("UNKNOWN") == "unknown"


class TestCollectResults:
    def test_empty_dir(self, tmp_path):
        baselines_dir = tmp_path / "panier_baselines"
        baselines_dir.mkdir()
        results = collect_results()
        assert isinstance(results, list)

    def test_valid_checkpoint(self, tmp_path, monkeypatch):
        baselines_dir = tmp_path / "panier_baselines"
        ckpt_dir = baselines_dir / "SPY" / "rf" / "20260506_120000"
        ckpt_dir.mkdir(parents=True)

        metadata = {
            "timestamp": "20260506_120000",
            "model_type": "rf",
            "hyperparams": {"symbol": "SPY", "model_type": "rf"},
            "metrics": {
                "oos_direction_accuracy": 0.52,
                "majority_class_acc": 0.54,
                "majority_class_freq": 0.54,
                "vs_majority_class": -0.02,
                "n_wf_folds": 5,
            },
            "data_hash": "abc123",
            "files": ["model.joblib", "metadata.json"],
        }
        (ckpt_dir / "metadata.json").write_text(json.dumps(metadata), encoding="utf-8")

        monkeypatch.setattr(
            "run_panier_baselines.CHECKPOINTS_DIR", tmp_path,
        )
        results = collect_results()
        assert len(results) == 1
        assert results[0]["symbol"] == "SPY"
        assert results[0]["model"] == "rf"
        assert results[0]["vs_majority"] == -0.02

    def test_invalid_json_skipped(self, tmp_path, monkeypatch):
        baselines_dir = tmp_path / "panier_baselines"
        ckpt_dir = baselines_dir / "GLD" / "xgb" / "20260506_120000"
        ckpt_dir.mkdir(parents=True)
        (ckpt_dir / "metadata.json").write_text("not json", encoding="utf-8")

        monkeypatch.setattr(
            "run_panier_baselines.CHECKPOINTS_DIR", tmp_path,
        )
        results = collect_results()
        assert len(results) == 0


class TestPanierSymbols:
    def test_total_count(self):
        symbols = get_panier_symbols()
        assert len(symbols) == 26

    def test_no_forbidden_symbols(self):
        from panier_loader import FORBIDDEN_SYMBOLS

        symbols = get_panier_symbols()
        for s in symbols:
            assert s not in FORBIDDEN_SYMBOLS, f"Forbidden symbol in panier: {s}"

    def test_group_balance(self):
        assert len(PANIER_GROUPS) == 7
        expected = {
            "us_equity_broad": 3,
            "us_equity_sectors": 10,
            "volatility": 1,
            "us_bonds": 3,
            "commodities": 3,
            "international": 2,
            "crypto": 4,
        }
        for group, symbols in PANIER_GROUPS.items():
            assert len(symbols) == expected[group], f"{group} has {len(symbols)}, expected {expected[group]}"
