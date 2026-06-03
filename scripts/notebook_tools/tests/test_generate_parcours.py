"""Tests for generate_parcours.py — parcours filtering logic."""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).parent.parent))
from generate_parcours import filter_for_parcours, PARCOURS


def _entry(serie: str, maturity: str = "PRODUCTION", status: str = "OK",
           sous_serie: str = "") -> dict:
    """Build a minimal catalog entry."""
    e = {"serie": serie, "maturity": maturity, "status": status, "path": f"{serie}/test.ipynb"}
    if sous_serie:
        e["sous_serie"] = sous_serie
    return e


# --- PARCOURS config validation ---


class TestParcoursConfig:
    def test_all_parcours_have_required_keys(self):
        for pid, cfg in PARCOURS.items():
            assert "title" in cfg, f"{pid} missing title"
            assert "series" in cfg, f"{pid} missing series"
            assert "maturity_filter" in cfg, f"{pid} missing maturity_filter"
            assert "description" in cfg, f"{pid} missing description"

    def test_five_parcours_defined(self):
        expected = {"ia-classique", "ia-symbolique", "genai", "trading", "recherche"}
        assert set(PARCOURS.keys()) == expected


# --- filter_for_parcours ---


class TestFilterForParcours:
    def test_empty_entries(self):
        result = filter_for_parcours([], "ia-classique")
        assert result == []

    def test_matching_serie_and_maturity(self):
        entries = [_entry("Search", "PRODUCTION")]
        result = filter_for_parcours(entries, "ia-classique")
        assert len(result) == 1

    def test_wrong_serie_excluded(self):
        entries = [_entry("GenAI", "PRODUCTION")]
        result = filter_for_parcours(entries, "ia-classique")
        assert len(result) == 0

    def test_wrong_maturity_excluded(self):
        entries = [_entry("Search", "DRAFT")]
        result = filter_for_parcours(entries, "ia-classique")
        assert len(result) == 0

    def test_broken_excluded(self):
        entries = [_entry("Search", "PRODUCTION", status="BROKEN")]
        result = filter_for_parcours(entries, "ia-classique")
        assert len(result) == 0

    def test_genai_accepts_alpha(self):
        entries = [_entry("GenAI", "ALPHA")]
        result = filter_for_parcours(entries, "genai")
        assert len(result) == 1

    def test_ia_classique_excludes_alpha(self):
        """ia-classique only accepts PRODUCTION and BETA."""
        entries = [_entry("Search", "ALPHA")]
        result = filter_for_parcours(entries, "ia-classique")
        assert len(result) == 0

    def test_multiple_series_trading(self):
        entries = [
            _entry("QuantConnect", "PRODUCTION"),
            _entry("ML", "BETA"),
            _entry("Probas", "ALPHA"),
            _entry("GenAI", "PRODUCTION"),  # not in trading
        ]
        result = filter_for_parcours(entries, "trading")
        assert len(result) == 3

    def test_mixed_entries(self):
        entries = [
            _entry("Search", "PRODUCTION"),
            _entry("Search", "BETA"),
            _entry("Search", "BROKEN", status="BROKEN"),
            _entry("Search", "DRAFT"),
            _entry("GenAI", "PRODUCTION"),
        ]
        result = filter_for_parcours(entries, "ia-classique")
        assert len(result) == 2  # PRODUCTION + BETA, not BROKEN or DRAFT
