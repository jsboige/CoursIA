"""Tests for build_panier_anti_bias.py — panier symbol management and anti-bias policy."""

import importlib.util
import sys
from pathlib import Path

import pytest

# Load module directly by file path to avoid conflict with HuggingFace 'datasets'
_MOD_PATH = Path(__file__).resolve().parent.parent.parent / "datasets" / "build_panier_anti_bias.py"
_spec = importlib.util.spec_from_file_location("build_panier_anti_bias", _MOD_PATH)
_mod = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_mod)

get_all_symbols = _mod.get_all_symbols
get_group = _mod.get_group
PANIER = _mod.PANIER
FORBIDDEN_SYMBOLS = _mod.FORBIDDEN_SYMBOLS
TICKER_MAP = _mod.TICKER_MAP


# --- PANIER structure ---


class TestPanierConfig:
    def test_panier_has_required_groups(self):
        expected = {
            "us_equity_broad", "us_equity_sectors", "volatility",
            "us_bonds", "commodities", "international", "crypto",
        }
        assert set(PANIER.keys()) == expected

    def test_panier_minimum_symbols(self):
        """At least 22 symbols required for diversification."""
        total = sum(len(v) for v in PANIER.values())
        assert total >= 22

    def test_no_forbidden_in_panier(self):
        """No FAANG+ individual stocks in the panier."""
        all_symbols = set()
        for group in PANIER.values():
            all_symbols.update(group.keys())
        forbidden_present = all_symbols & FORBIDDEN_SYMBOLS
        assert forbidden_present == set(), f"Forbidden symbols found: {forbidden_present}"

    def test_forbidden_symbols_set(self):
        assert FORBIDDEN_SYMBOLS == {"AAPL", "MSFT", "GOOG", "AMZN", "NVDA", "TSLA", "META"}

    def test_ticker_map_has_vix(self):
        assert TICKER_MAP.get("VIX") == "^VIX"


# --- get_all_symbols ---


class TestGetAllSymbols:
    def test_returns_list(self):
        result = get_all_symbols()
        assert isinstance(result, list)

    def test_contains_spy(self):
        assert "SPY" in get_all_symbols()

    def test_contains_btc(self):
        assert "BTC-USD" in get_all_symbols()

    def test_no_duplicates(self):
        symbols = get_all_symbols()
        assert len(symbols) == len(set(symbols))

    def test_minimum_count(self):
        assert len(get_all_symbols()) >= 22


# --- get_group ---


class TestGetGroup:
    def test_spy_is_equity_broad(self):
        assert get_group("SPY") == "us_equity_broad"

    def test_btc_is_crypto(self):
        assert get_group("BTC-USD") == "crypto"

    def test_gld_is_commodities(self):
        assert get_group("GLD") == "commodities"

    def test_tlt_is_bonds(self):
        assert get_group("TLT") == "us_bonds"

    def test_unknown_symbol(self):
        assert get_group("FAKE") == "unknown"

    def test_all_symbols_have_group(self):
        """Every symbol in PANIER should resolve to its group."""
        for group_name, group_dict in PANIER.items():
            for symbol in group_dict:
                assert get_group(symbol) == group_name, f"{symbol} should be in {group_name}"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
