"""Tests for scripts/notebook_tools/generate_parcours.py — student parcours generator.

Tests focus on pure functions: filter_for_parcours, generate_parcours_page,
check_coverage. Uses synthetic catalog entries.
"""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from generate_parcours import (
    PARCOURS,
    check_coverage,
    filter_for_parcours,
    generate_parcours_page,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

SAMPLE_ENTRIES = [
    {"path": "Search/Part1/Search-1.ipynb", "title": "BFS", "serie": "Search",
     "maturity": "PRODUCTION", "status": "READY", "executable_locally": True},
    {"path": "Search/Part2/CSP-1.ipynb", "title": "CSP Intro", "serie": "Search",
     "maturity": "BETA", "status": "READY", "executable_locally": True,
     "sous_serie": "Part2-CSP"},
    {"path": "Sudoku/Sudoku-1.ipynb", "title": "Sudoku Base", "serie": "Sudoku",
     "maturity": "PRODUCTION", "status": "READY", "executable_locally": True},
    {"path": "GenAI/Image/GenAI-1.ipynb", "title": "Image Gen", "serie": "GenAI",
     "maturity": "PRODUCTION", "status": "READY", "executable_locally": True},
    {"path": "GenAI/Audio/GenAI-10.ipynb", "title": "Audio", "serie": "GenAI",
     "maturity": "ALPHA", "status": "READY", "executable_locally": False},
    {"path": "SymbolicAI/Lean/Lean-1.ipynb", "title": "Lean Intro", "serie": "SymbolicAI",
     "maturity": "BETA", "status": "READY", "executable_locally": True},
    {"path": "QuantConnect/QC-1.ipynb", "title": "QC Intro", "serie": "QuantConnect",
     "maturity": "BETA", "status": "READY", "executable_locally": False},
    {"path": "ML/ML-1.ipynb", "title": "ML Intro", "serie": "ML",
     "maturity": "PRODUCTION", "status": "READY", "executable_locally": True},
    {"path": "Probas/Probas-1.ipynb", "title": "Probas", "serie": "Probas",
     "maturity": "PRODUCTION", "status": "READY", "executable_locally": True},
    {"path": "IIT/IIT-1.ipynb", "title": "IIT", "serie": "IIT",
     "maturity": "ALPHA", "status": "READY", "executable_locally": True},
    {"path": "RL/RL-1.ipynb", "title": "RL", "serie": "RL",
     "maturity": "BETA", "status": "READY", "executable_locally": True},
    {"path": "GameTheory/GT-1.ipynb", "title": "Game Theory", "serie": "GameTheory",
     "maturity": "BETA", "status": "READY", "executable_locally": True},
    # BROKEN — should be excluded
    {"path": "Search/Part3/Broken.ipynb", "title": "Broken", "serie": "Search",
     "maturity": "PRODUCTION", "status": "BROKEN", "executable_locally": False},
    # DRAFT — should be excluded from parcours with maturity_filter PRODUCTION/BETA
    {"path": "Search/Part1/Draft.ipynb", "title": "Draft", "serie": "Search",
     "maturity": "DRAFT", "status": "READY", "executable_locally": True},
]


# ---------------------------------------------------------------------------
# filter_for_parcours
# ---------------------------------------------------------------------------

class TestFilterForParcours:
    def test_ia_classique_search_and_sudoku(self):
        result = filter_for_parcours(SAMPLE_ENTRIES, "ia-classique")
        series = {e["serie"] for e in result}
        assert series == {"Search", "Sudoku"}

    def test_ia_classique_excludes_broken(self):
        result = filter_for_parcours(SAMPLE_ENTRIES, "ia-classique")
        assert not any(e["status"] == "BROKEN" for e in result)

    def test_ia_classique_excludes_draft(self):
        result = filter_for_parcours(SAMPLE_ENTRIES, "ia-classique")
        assert not any(e["maturity"] == "DRAFT" for e in result)

    def test_genai_includes_alpha(self):
        result = filter_for_parcours(SAMPLE_ENTRIES, "genai")
        assert any(e["maturity"] == "ALPHA" for e in result)

    def test_trading_includes_quantconnect_and_ml(self):
        result = filter_for_parcours(SAMPLE_ENTRIES, "trading")
        series = {e["serie"] for e in result}
        assert "QuantConnect" in series
        assert "ML" in series

    def test_recherche_includes_probas_iit_rl(self):
        result = filter_for_parcours(SAMPLE_ENTRIES, "recherche")
        series = {e["serie"] for e in result}
        assert "Probas" in series
        assert "IIT" in series
        assert "RL" in series
        assert "GameTheory" in series

    def test_ia_symbolique_only_symbolic(self):
        result = filter_for_parcours(SAMPLE_ENTRIES, "ia-symbolique")
        series = {e["serie"] for e in result}
        assert series == {"SymbolicAI"}

    def test_empty_entries(self):
        result = filter_for_parcours([], "ia-classique")
        assert result == []


# ---------------------------------------------------------------------------
# generate_parcours_page
# ---------------------------------------------------------------------------

class TestGenerateParcoursPage:
    def test_has_title(self):
        entries = filter_for_parcours(SAMPLE_ENTRIES, "ia-classique")
        page = generate_parcours_page("ia-classique", entries)
        assert "# IA Classique" in page

    def test_has_subtitle(self):
        entries = filter_for_parcours(SAMPLE_ENTRIES, "ia-classique")
        page = generate_parcours_page("ia-classique", entries)
        assert "Recherche, CSP et resolution" in page

    def test_has_statistics(self):
        entries = filter_for_parcours(SAMPLE_ENTRIES, "ia-classique")
        page = generate_parcours_page("ia-classique", entries)
        assert "## Statistiques" in page
        assert "| Notebooks |" in page
        assert "| PRODUCTION |" in page

    def test_notebook_count_matches(self):
        entries = filter_for_parcours(SAMPLE_ENTRIES, "ia-classique")
        page = generate_parcours_page("ia-classique", entries)
        assert f"| Notebooks | {len(entries)} |" in page

    def test_has_table_rows(self):
        entries = filter_for_parcours(SAMPLE_ENTRIES, "genai")
        page = generate_parcours_page("genai", entries)
        assert "| Notebook |" in page
        assert "Maturite" in page

    def test_executable_column(self):
        entries = filter_for_parcours(SAMPLE_ENTRIES, "genai")
        page = generate_parcours_page("genai", entries)
        assert "Oui" in page
        assert "Non" in page

    def test_empty_entries(self):
        page = generate_parcours_page("ia-classique", [])
        assert "| Notebooks | 0 |" in page


# ---------------------------------------------------------------------------
# check_coverage
# ---------------------------------------------------------------------------

class TestCheckCoverage:
    def test_coverage_reports(self, capsys):
        check_coverage(SAMPLE_ENTRIES)
        output = capsys.readouterr().out
        assert "Coverage:" in output

    def test_full_coverage_no_uncovered(self, capsys):
        """All PRODUCTION/BETA in SAMPLE_ENTRIES should be covered by some parcours."""
        check_coverage(SAMPLE_ENTRIES)
        output = capsys.readouterr().out
        # Broken is excluded from prod/beta check
        # Search PRODUCTION (BFS) + Sudoku PRODUCTION + GenAI PRODUCTION +
        # SymbolicAI BETA + QC BETA + ML PRODUCTION + Probas PRODUCTION +
        # Search BETA (CSP) + RL BETA + GameTheory BETA = 10
        assert "Coverage:" in output

    def test_empty_entries(self, capsys):
        check_coverage([])
        output = capsys.readouterr().out
        assert "Coverage: 0/0" in output


# ---------------------------------------------------------------------------
# PARCOURS constants
# ---------------------------------------------------------------------------

class TestParcoursConstants:
    def test_five_parcours(self):
        assert len(PARCOURS) == 5

    def test_all_have_required_keys(self):
        for pid, config in PARCOURS.items():
            assert "title" in config, f"{pid} missing title"
            assert "series" in config, f"{pid} missing series"
            assert "maturity_filter" in config, f"{pid} missing maturity_filter"
            assert "description" in config, f"{pid} missing description"

    def test_all_parcours_ids(self):
        expected = {"ia-classique", "ia-symbolique", "genai", "trading", "recherche"}
        assert set(PARCOURS.keys()) == expected

    def test_series_are_valid(self):
        all_series = set()
        for config in PARCOURS.values():
            all_series.update(config["series"])
        # Should cover known series
        assert "Search" in all_series
        assert "GenAI" in all_series
        assert "QuantConnect" in all_series
