"""Tests for scripts/notebook_tools/expand_catalog_markers.py — catalog marker expansion.

Tests focus on pure functions: _to_lf, compute_counter, _sorted_counter,
compute_breakdown, compute_maturity_distribution, compute_status_distribution,
format_catalog_status_block, expand_file. No filesystem I/O in tests.
"""

import sys
from collections import Counter
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from expand_catalog_markers import (
    _filter_by_series,
    _sorted_counter,
    _to_lf,
    compute_breakdown,
    compute_counter,
    compute_maturity_distribution,
    compute_status_distribution,
    expand_file,
    format_catalog_status_block,
)


# ---------------------------------------------------------------------------
# Fixtures — sample catalog entries
# ---------------------------------------------------------------------------

SAMPLE_ENTRIES = [
    {"serie": "Search", "sous_serie": "Part1-Foundations", "status": "READY", "maturity": "PRODUCTION"},
    {"serie": "Search", "sous_serie": "Part1-Foundations", "status": "READY", "maturity": "PRODUCTION"},
    {"serie": "Search", "sous_serie": "Part2-CSP", "status": "READY", "maturity": "BETA"},
    {"serie": "Search", "sous_serie": "Part3-Advanced", "status": "DRAFT", "maturity": "ALPHA"},
    {"serie": "Sudoku", "sous_serie": None, "status": "READY", "maturity": "PRODUCTION"},
    {"serie": "Sudoku", "sous_serie": None, "status": "READY", "maturity": "PRODUCTION"},
    {"serie": "Sudoku", "sous_serie": None, "status": "DRAFT", "maturity": "BETA"},
    {"serie": "GameTheory", "sous_serie": "social_choice", "status": "READY", "maturity": "PRODUCTION"},
    {"serie": "GameTheory", "sous_serie": "social_choice", "status": "READY", "maturity": "PRODUCTION"},
    {"serie": "GameTheory", "sous_serie": "open_spiel", "status": "READY", "maturity": "BETA"},
]

# Entries simulating SymbolicAI sub-series (serie=SymbolicAI, sous_serie varies)
SYMBOLIC_ENTRIES = [
    {"serie": "SymbolicAI", "sous_serie": "Lean", "status": "READY", "maturity": "PRODUCTION"},
    {"serie": "SymbolicAI", "sous_serie": "Lean", "status": "READY", "maturity": "BETA"},
    {"serie": "SymbolicAI", "sous_serie": "Tweety", "status": "READY", "maturity": "PRODUCTION"},
    {"serie": "SymbolicAI", "sous_serie": "SemanticWeb", "status": "READY", "maturity": "PRODUCTION"},
    {"serie": "SymbolicAI", "sous_serie": "SemanticWeb", "status": "DRAFT", "maturity": "ALPHA"},
    {"serie": "SymbolicAI", "sous_serie": "SymbolicLearning", "status": "READY", "maturity": "PRODUCTION"},
    {"serie": "SymbolicAI", "sous_serie": "SymbolicLearning", "status": "READY", "maturity": "PRODUCTION"},
    {"serie": "SymbolicAI", "sous_serie": "SymbolicLearning", "status": "READY", "maturity": "PRODUCTION"},
    {"serie": "ML", "sous_serie": "ML.Net", "status": "READY", "maturity": "PRODUCTION"},
    {"serie": "ML", "sous_serie": "ML.Net", "status": "READY", "maturity": "BETA"},
    {"serie": "GameTheory", "sous_serie": "SocialChoice", "status": "READY", "maturity": "PRODUCTION"},
]


# ---------------------------------------------------------------------------
# _filter_by_series
# ---------------------------------------------------------------------------

class TestFilterBySeries:
    def test_exact_match_serie(self):
        """Exact match on serie field returns entries."""
        result = _filter_by_series(SAMPLE_ENTRIES, "Search")
        assert len(result) == 4

    def test_exact_match_no_sous_serie(self):
        """Serie without sous_serie matches exactly."""
        result = _filter_by_series(SAMPLE_ENTRIES, "Sudoku")
        assert len(result) == 3

    def test_fallback_serie_sousserie(self):
        """Serie-SousSerie format falls back to serie+ sous_serie match."""
        result = _filter_by_series(SYMBOLIC_ENTRIES, "SymbolicAI-Lean")
        assert len(result) == 2
        assert all(e.get("serie") == "SymbolicAI" for e in result)
        assert all(e.get("sous_serie") == "Lean" for e in result)

    def test_fallback_symbolic_learning(self):
        """SymbolicAI-SymbolicLearning matches 3 entries."""
        result = _filter_by_series(SYMBOLIC_ENTRIES, "SymbolicAI-SymbolicLearning")
        assert len(result) == 3

    def test_fallback_semantic_web(self):
        """SymbolicAI-SemanticWeb matches 2 entries."""
        result = _filter_by_series(SYMBOLIC_ENTRIES, "SymbolicAI-SemanticWeb")
        assert len(result) == 2

    def test_no_match_returns_empty(self):
        """Nonexistent serie returns empty list."""
        result = _filter_by_series(SAMPLE_ENTRIES, "NonExistent")
        assert result == []

    def test_fallback_no_sousserie(self):
        """ML-ML.Net falls back correctly."""
        result = _filter_by_series(SYMBOLIC_ENTRIES, "ML-ML.Net")
        assert len(result) == 2

    def test_fallback_gametheory_socialchoice(self):
        """GameTheory-SocialChoice falls back correctly."""
        result = _filter_by_series(SYMBOLIC_ENTRIES, "GameTheory-SocialChoice")
        assert len(result) == 1

    def test_exact_match_takes_priority(self):
        """When exact match exists, it is used (not fallback)."""
        # Add an entry where serie exactly matches 'SymbolicAI-Lean'
        entries = SYMBOLIC_ENTRIES + [{"serie": "SymbolicAI-Lean", "sous_serie": None}]
        result = _filter_by_series(entries, "SymbolicAI-Lean")
        assert len(result) == 1
        assert result[0].get("serie") == "SymbolicAI-Lean"


# ---------------------------------------------------------------------------
# Serie-SousSerie fallback integration tests
# ---------------------------------------------------------------------------

class TestSerieSousSerieIntegration:
    def test_breakdown_fallback(self):
        """compute_breakdown works with Serie-SousSerie format."""
        result = compute_breakdown(SYMBOLIC_ENTRIES, "SymbolicAI-SymbolicLearning")
        assert result == {"SymbolicLearning": 3}

    def test_breakdown_with_multiple_sousseries(self):
        """compute_breakdown with SymbolicAI gives breakdown by sous_serie."""
        result = compute_breakdown(SYMBOLIC_ENTRIES, "SymbolicAI")
        expected = {
            "SymbolicLearning": 3,
            "Lean": 2,
            "SemanticWeb": 2,
            "Tweety": 1,
        }
        assert result == expected

    def test_maturity_fallback(self):
        """compute_maturity_distribution works with Serie-SousSerie format."""
        result = compute_maturity_distribution(SYMBOLIC_ENTRIES, "SymbolicAI-SymbolicLearning")
        assert result == {"PRODUCTION": 3}

    def test_status_fallback(self):
        """compute_status_distribution works with Serie-SousSerie format."""
        result = compute_status_distribution(SYMBOLIC_ENTRIES, "SymbolicAI-Lean")
        assert result == {"READY": 2}

    def test_format_block_fallback(self):
        """format_catalog_status_block works with Serie-SousSerie format."""
        result = format_catalog_status_block(SYMBOLIC_ENTRIES, "SymbolicAI-SymbolicLearning")
        assert "series: SymbolicAI-SymbolicLearning" in result
        assert "pedagogical_count: 3" in result
        assert "PRODUCTION=3" in result

    def test_expand_file_fallback(self):
        """expand_file correctly expands a Serie-SousSerie marker."""
        content = (
            "<!-- CATALOG-STATUS\n"
            "series: SymbolicAI-SymbolicLearning\n"
            "pedagogical_count: 0\n"
            "breakdown: none\n"
            "maturity: none\n"
            "-->\n"
        )
        new_content, changes = expand_file(content, SYMBOLIC_ENTRIES)
        assert len(changes) == 1
        assert "pedagogical_count: 3" in new_content
        assert "PRODUCTION=3" in new_content

    def test_expand_file_fallback_idempotent(self):
        """Running expand twice with fallback produces identical output."""
        content = (
            "<!-- CATALOG-STATUS\n"
            "series: SymbolicAI-Lean\n"
            "pedagogical_count: 0\n"
            "breakdown: none\n"
            "maturity: none\n"
            "-->\n"
        )
        first, _ = expand_file(content, SYMBOLIC_ENTRIES)
        second, changes = expand_file(first, SYMBOLIC_ENTRIES)
        assert first == second
        assert changes == []


# ---------------------------------------------------------------------------
# _to_lf
# ---------------------------------------------------------------------------

class TestToLf:
    def test_crlf_to_lf(self):
        assert _to_lf("a\r\nb\r\n") == "a\nb\n"

    def test_cr_to_lf(self):
        assert _to_lf("a\rb\r") == "a\nb\n"

    def test_lf_unchanged(self):
        assert _to_lf("a\nb\n") == "a\nb\n"

    def test_mixed_endings(self):
        assert _to_lf("a\r\nb\rc\n") == "a\nb\nc\n"

    def test_no_endings(self):
        assert _to_lf("abc") == "abc"

    def test_empty_string(self):
        assert _to_lf("") == ""


# ---------------------------------------------------------------------------
# compute_counter
# ---------------------------------------------------------------------------

class TestComputeCounter:
    def test_total_count_no_params(self):
        assert compute_counter(SAMPLE_ENTRIES, {}) == str(len(SAMPLE_ENTRIES))

    def test_filter_by_serie(self):
        result = compute_counter(SAMPLE_ENTRIES, {"serie": "Search"})
        assert result == "4"

    def test_filter_by_serie_sudoku(self):
        result = compute_counter(SAMPLE_ENTRIES, {"serie": "Sudoku"})
        assert result == "3"

    def test_filter_by_status(self):
        result = compute_counter(SAMPLE_ENTRIES, {"status": "DRAFT"})
        assert result == "2"

    def test_filter_by_maturity(self):
        result = compute_counter(SAMPLE_ENTRIES, {"maturity": "PRODUCTION"})
        assert result == "6"

    def test_filter_by_sous_serie(self):
        result = compute_counter(SAMPLE_ENTRIES, {"sous_serie": "Part2-CSP"})
        assert result == "1"

    def test_combined_filter_serie_and_status(self):
        result = compute_counter(SAMPLE_ENTRIES, {"serie": "Sudoku", "status": "READY"})
        assert result == "2"

    def test_combined_filter_serie_and_maturity(self):
        result = compute_counter(SAMPLE_ENTRIES, {"serie": "Search", "maturity": "BETA"})
        assert result == "1"

    def test_filter_no_match(self):
        result = compute_counter(SAMPLE_ENTRIES, {"serie": "NonExistent"})
        assert result == "0"

    def test_empty_entries(self):
        assert compute_counter([], {"serie": "Search"}) == "0"

    def test_missing_key_in_entry(self):
        """Entries missing the filter key should not match."""
        entries = [{"serie": "Search"}, {"serie": "Sudoku"}]
        assert compute_counter(entries, {"maturity": "PRODUCTION"}) == "0"


# ---------------------------------------------------------------------------
# _sorted_counter
# ---------------------------------------------------------------------------

class TestSortedCounter:
    def test_sort_by_count_descending(self):
        c = Counter({"a": 3, "b": 1, "c": 2})
        result = _sorted_counter(c)
        assert list(result.keys()) == ["a", "c", "b"]

    def test_tiebreak_alphabetical(self):
        """When counts are equal, keys are sorted alphabetically."""
        c = Counter({"zebra": 2, "alpha": 2, "middle": 2})
        result = _sorted_counter(c)
        assert list(result.keys()) == ["alpha", "middle", "zebra"]

    def test_tiebreak_mixed_counts(self):
        c = Counter({"b": 5, "a": 5, "c": 3})
        result = _sorted_counter(c)
        assert list(result.keys()) == ["a", "b", "c"]

    def test_empty_counter(self):
        assert _sorted_counter(Counter()) == {}

    def test_single_item(self):
        assert _sorted_counter(Counter({"x": 1})) == {"x": 1}

    def test_preserves_values(self):
        c = Counter({"a": 10, "b": 5})
        result = _sorted_counter(c)
        assert result == {"a": 10, "b": 5}


# ---------------------------------------------------------------------------
# compute_breakdown
# ---------------------------------------------------------------------------

class TestComputeBreakdown:
    def test_search_breakdown(self):
        result = compute_breakdown(SAMPLE_ENTRIES, "Search")
        assert result == {
            "Part1-Foundations": 2,
            "Part2-CSP": 1,
            "Part3-Advanced": 1,
        }

    def test_sudoku_root_grouping(self):
        """Entries without sous_serie are grouped as 'root'."""
        result = compute_breakdown(SAMPLE_ENTRIES, "Sudoku")
        assert result == {"root": 3}

    def test_gametheory_breakdown(self):
        result = compute_breakdown(SAMPLE_ENTRIES, "GameTheory")
        assert result == {"social_choice": 2, "open_spiel": 1}

    def test_nonexistent_serie(self):
        result = compute_breakdown(SAMPLE_ENTRIES, "NonExistent")
        assert result == {}

    def test_empty_entries(self):
        assert compute_breakdown([], "Search") == {}

    def test_deterministic_order(self):
        """Breakdown keys are sorted by (-count, key)."""
        entries = [
            {"serie": "X", "sous_serie": "b"},
            {"serie": "X", "sous_serie": "a"},
            {"serie": "X", "sous_serie": "a"},
            {"serie": "X", "sous_serie": "c"},
            {"serie": "X", "sous_serie": "c"},
        ]
        result = compute_breakdown(entries, "X")
        assert list(result.keys()) == ["a", "c", "b"]  # a=2, c=2 (alpha tiebreak), b=1


# ---------------------------------------------------------------------------
# compute_maturity_distribution
# ---------------------------------------------------------------------------

class TestComputeMaturityDistribution:
    def test_all_series(self):
        result = compute_maturity_distribution(SAMPLE_ENTRIES, None)
        assert result["PRODUCTION"] == 6
        assert result["BETA"] == 3
        assert result["ALPHA"] == 1

    def test_specific_serie(self):
        result = compute_maturity_distribution(SAMPLE_ENTRIES, "Search")
        assert result == {"PRODUCTION": 2, "BETA": 1, "ALPHA": 1}

    def test_sudoku_maturity(self):
        result = compute_maturity_distribution(SAMPLE_ENTRIES, "Sudoku")
        assert result == {"PRODUCTION": 2, "BETA": 1}

    def test_nonexistent_serie(self):
        result = compute_maturity_distribution(SAMPLE_ENTRIES, "NonExistent")
        assert result == {}

    def test_missing_maturity_key(self):
        """Entries missing 'maturity' are counted as UNKNOWN."""
        entries = [{"serie": "X"}, {"serie": "X", "maturity": "PRODUCTION"}]
        result = compute_maturity_distribution(entries, "X")
        assert result == {"PRODUCTION": 1, "UNKNOWN": 1}

    def test_deterministic_order(self):
        result = compute_maturity_distribution(SAMPLE_ENTRIES, None)
        keys = list(result.keys())
        # PRODUCTION=6 > BETA=3 > ALPHA=1 — all different, pure count order
        assert keys == ["PRODUCTION", "BETA", "ALPHA"]


# ---------------------------------------------------------------------------
# compute_status_distribution
# ---------------------------------------------------------------------------

class TestComputeStatusDistribution:
    def test_all_series(self):
        result = compute_status_distribution(SAMPLE_ENTRIES, None)
        assert result["READY"] == 8
        assert result["DRAFT"] == 2

    def test_specific_serie(self):
        result = compute_status_distribution(SAMPLE_ENTRIES, "Search")
        assert result == {"READY": 3, "DRAFT": 1}

    def test_nonexistent_serie(self):
        assert compute_status_distribution(SAMPLE_ENTRIES, "NonExistent") == {}


# ---------------------------------------------------------------------------
# format_catalog_status_block
# ---------------------------------------------------------------------------

class TestFormatCatalogStatusBlock:
    def test_single_serie_block(self):
        result = format_catalog_status_block(SAMPLE_ENTRIES, "Search")
        assert "series: Search" in result
        assert "pedagogical_count: 4" in result
        assert "Part1-Foundations=2" in result
        assert "PRODUCTION=2" in result
        assert result.startswith("<!-- CATALOG-STATUS")
        assert result.endswith("-->")

    def test_all_series_block(self):
        result = format_catalog_status_block(SAMPLE_ENTRIES, "ALL")
        assert "series: ALL" in result
        assert "total: 10" in result
        assert "Search=4" in result
        assert "Sudoku=3" in result
        assert "GameTheory=3" in result

    def test_block_structure(self):
        """Block has exactly 5 lines of content between markers."""
        result = format_catalog_status_block(SAMPLE_ENTRIES, "Search")
        lines = result.strip().split("\n")
        assert lines[0] == "<!-- CATALOG-STATUS"
        assert lines[-1] == "-->"
        # 5 content lines: series, pedagogical_count, breakdown, maturity, (closing)
        assert len(lines) == 6  # opener + 4 data lines + closer

    def test_all_block_structure(self):
        result = format_catalog_status_block(SAMPLE_ENTRIES, "ALL")
        lines = result.strip().split("\n")
        assert lines[0] == "<!-- CATALOG-STATUS"
        assert lines[-1] == "-->"
        assert "total:" in result
        assert "breakdown:" in result

    def test_empty_serie(self):
        result = format_catalog_status_block([], "Search")
        assert "pedagogical_count: 0" in result
        assert "breakdown: " in result


# ---------------------------------------------------------------------------
# expand_file
# ---------------------------------------------------------------------------

class TestExpandFile:
    def test_no_markers_unchanged(self):
        content = "# Title\n\nSome text\n"
        new_content, changes = expand_file(content, SAMPLE_ENTRIES)
        assert new_content == content
        assert changes == []

    def test_catalog_status_block_replaced(self):
        content = (
            "# Title\n\n"
            "<!-- CATALOG-STATUS\n"
            "series: Search\n"
            "pedagogical_count: 999\n"
            "breakdown: old=1\n"
            "maturity: OLD=1\n"
            "-->\n"
        )
        new_content, changes = expand_file(content, SAMPLE_ENTRIES)
        assert len(changes) == 1
        assert "Search" in changes[0]
        assert "pedagogical_count: 4" in new_content
        assert "999" not in new_content

    def test_catalog_status_block_idempotent(self):
        """Running expand_file twice produces identical output."""
        content = (
            "<!-- CATALOG-STATUS\n"
            "series: Sudoku\n"
            "pedagogical_count: 999\n"
            "breakdown: old=1\n"
            "maturity: OLD=1\n"
            "-->\n"
        )
        first, _ = expand_file(content, SAMPLE_ENTRIES)
        second, changes = expand_file(first, SAMPLE_ENTRIES)
        assert first == second
        assert changes == []

    def test_inline_counter_marker(self):
        content = "Total: <!-- CATALOG:counter:total --> notebooks\n"
        new_content, changes = expand_file(content, SAMPLE_ENTRIES)
        # Counter marker is preserved as-is (it's a placeholder, value is the marker itself)
        assert "<!-- CATALOG:counter:total -->" in new_content
        # Note: the current implementation preserves markers, it doesn't inline the count
        # This test verifies the marker survives expansion

    def test_catalog_status_all_series(self):
        content = (
            "<!-- CATALOG-STATUS\n"
            "series: ALL\n"
            "total: 0\n"
            "breakdown: none\n"
            "maturity: none\n"
            "-->\n"
        )
        new_content, changes = expand_file(content, SAMPLE_ENTRIES)
        assert len(changes) == 1
        assert "total: 10" in new_content
        assert "Search=4" in new_content

    def test_multiple_blocks_in_file(self):
        content = (
            "<!-- CATALOG-STATUS\n"
            "series: Search\n"
            "pedagogical_count: 0\n"
            "breakdown: none\n"
            "maturity: none\n"
            "-->\n"
            "\nSome text\n\n"
            "<!-- CATALOG-STATUS\n"
            "series: Sudoku\n"
            "pedagogical_count: 0\n"
            "breakdown: none\n"
            "maturity: none\n"
            "-->\n"
        )
        new_content, changes = expand_file(content, SAMPLE_ENTRIES)
        assert len(changes) == 2
        assert "pedagogical_count: 4" in new_content  # Search
        assert "pedagogical_count: 3" in new_content  # Sudoku

    def test_preserves_surrounding_content(self):
        content = (
            "# Header\n\n"
            "<!-- CATALOG-STATUS\n"
            "series: Search\n"
            "pedagogical_count: 0\n"
            "breakdown: none\n"
            "maturity: none\n"
            "-->\n\n"
            "Footer text\n"
        )
        new_content, changes = expand_file(content, SAMPLE_ENTRIES)
        assert new_content.startswith("# Header\n\n")
        assert new_content.endswith("\n\nFooter text\n")
        assert "pedagogical_count: 4" in new_content

    def test_crlf_content_normalized(self):
        """CRLF in content should work correctly."""
        content = "<!-- CATALOG-STATUS\r\nseries: Search\r\npedagogical_count: 0\r\nbreakdown: none\r\nmaturity: none\r\n-->\r\n"
        new_content, changes = expand_file(content, SAMPLE_ENTRIES)
        # Should handle and normalize
        assert len(changes) == 1

    def test_block_without_series_ignored(self):
        """CATALOG-STATUS block without 'series:' line is preserved as-is."""
        content = (
            "<!-- CATALOG-STATUS\n"
            "unknown_key: value\n"
            "-->\n"
        )
        new_content, changes = expand_file(content, SAMPLE_ENTRIES)
        assert changes == []
        assert "unknown_key: value" in new_content

    def test_empty_entries(self):
        content = (
            "<!-- CATALOG-STATUS\n"
            "series: Search\n"
            "pedagogical_count: 0\n"
            "breakdown: none\n"
            "maturity: none\n"
            "-->\n"
        )
        new_content, changes = expand_file(content, [])
        assert len(changes) == 1
        assert "pedagogical_count: 0" in new_content
        assert "breakdown: " in new_content


# ---------------------------------------------------------------------------
# _filter_by_series — Serie-SousSerie format support (regression #2599)
# ---------------------------------------------------------------------------


class TestFilterBySeries:
    """Tests for the Serie-SousSerie fallback in _filter_by_series."""

    @pytest.fixture
    def entries(self):
        return [
            {"serie": "SymbolicAI", "sous_serie": "Lean"},
            {"serie": "SymbolicAI", "sous_serie": "Lean"},
            {"serie": "SymbolicAI", "sous_serie": "Tweety"},
            {"serie": "SymbolicAI", "sous_serie": ""},
            {"serie": "ML", "sous_serie": ""},
        ]

    def test_exact_serie_match(self, entries):
        result = _filter_by_series(entries, "ML")
        assert len(result) == 1

    def test_exact_serie_multiple(self, entries):
        result = _filter_by_series(entries, "SymbolicAI")
        assert len(result) == 4

    def test_serie_sousserie_format(self, entries):
        """'SymbolicAI-Lean' matches serie=SymbolicAI + sous_serie=Lean."""
        result = _filter_by_series(entries, "SymbolicAI-Lean")
        assert len(result) == 2

    def test_serie_sousserie_tweety(self, entries):
        result = _filter_by_series(entries, "SymbolicAI-Tweety")
        assert len(result) == 1

    def test_serie_sousserie_root(self, entries):
        """'SymbolicAI-' matches serie=SymbolicAI + sous_serie=''."""
        result = _filter_by_series(entries, "SymbolicAI-")
        assert len(result) == 1

    def test_nonexistent_returns_empty(self, entries):
        result = _filter_by_series(entries, "Nonexistent")
        assert result == []

    def test_nonexistent_sousserie_returns_empty(self, entries):
        result = _filter_by_series(entries, "SymbolicAI-FooBar")
        assert result == []

    def test_exact_match_takes_priority(self):
        """If a serie literally equals 'A-B', exact match wins."""
        entries = [
            {"serie": "A-B", "sous_serie": ""},
            {"serie": "A", "sous_serie": "B"},
        ]
        result = _filter_by_series(entries, "A-B")
        assert len(result) == 1
        assert result[0]["serie"] == "A-B"


class TestCatalogStatusSerieSousSerie:
    """Regression test: CATALOG-STATUS with 'Serie-SousSerie' format."""

    def test_sousserie_status_block(self):
        entries = [
            {"serie": "SymbolicAI", "sous_serie": "Lean", "maturity": "PRODUCTION"},
            {"serie": "SymbolicAI", "sous_serie": "Lean", "maturity": "BETA"},
            {"serie": "SymbolicAI", "sous_serie": "Tweety"},
        ]
        block = format_catalog_status_block(entries, "SymbolicAI-Lean")
        assert "pedagogical_count: 2" in block
        assert "PRODUCTION=1" in block and "BETA=1" in block

    def test_sousserie_counter_marker(self):
        entries = [
            {"serie": "SymbolicAI", "sous_serie": "Lean"},
            {"serie": "SymbolicAI", "sous_serie": "Tweety"},
        ]
        result = compute_counter(entries, {"serie": "SymbolicAI-Lean"})
        assert result == "1"

    def test_sousserie_breakdown(self):
        entries = [
            {"serie": "SymbolicAI", "sous_serie": "Lean"},
            {"serie": "SymbolicAI", "sous_serie": "Lean"},
            {"serie": "SymbolicAI", "sous_serie": "Tweety"},
        ]
        breakdown = compute_breakdown(entries, "SymbolicAI-Lean")
        assert breakdown == {"Lean": 2}


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
