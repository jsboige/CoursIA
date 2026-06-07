"""Tests for expand_catalog_markers.py — catalog marker expansion.

Covers: compute_counter, _sorted_counter, compute_breakdown,
compute_maturity_distribution, compute_status_distribution,
format_catalog_status_block, expand_file, _to_lf.
"""

import os
import sys
from collections import Counter

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

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


def _entry(serie="ML", status="READY", maturity="PRODUCTION", sous_serie=None, **kw):
    e = {"serie": serie, "status": status, "maturity": maturity}
    if sous_serie:
        e["sous_serie"] = sous_serie
    e.update(kw)
    return e


SAMPLE_ENTRIES = [
    _entry(serie="ML", status="READY", maturity="PRODUCTION"),
    _entry(serie="ML", status="READY", maturity="PRODUCTION"),
    _entry(serie="ML", status="BROKEN", maturity="EXPERIMENTAL"),
    _entry(serie="GenAI", status="READY", maturity="PRODUCTION", sous_serie="Image"),
    _entry(serie="GenAI", status="READY", maturity="PRODUCTION", sous_serie="Audio"),
    _entry(serie="GenAI", status="NEEDS_IMPROVEMENT", maturity="EXPERIMENTAL", sous_serie="Image"),
]


# --- _to_lf (mutation tests) ---

class TestToLf:
    """Mutation tests for _to_lf (L42-45) — CRLF/CR normalization."""

    def test_crlf_to_lf(self):
        assert _to_lf("a\r\nb\r\n") == "a\nb\n"

    def test_cr_to_lf(self):
        assert _to_lf("a\rb\n") == "a\nb\n"

    def test_lf_unchanged(self):
        assert _to_lf("a\nb\n") == "a\nb\n"

    def test_mixed_line_endings(self):
        assert _to_lf("a\r\nb\rc\n") == "a\nb\nc\n"

    def test_empty_string(self):
        assert _to_lf("") == ""


# --- _sorted_counter (mutation tests) ---

class TestSortedCounter:
    """Mutation tests for _sorted_counter (L70-72) — deterministic sorting."""

    def test_sort_by_count_descending(self):
        c = Counter(["a", "a", "b"])
        result = _sorted_counter(c)
        assert list(result.keys()) == ["a", "b"]
        assert result["a"] == 2
        assert result["b"] == 1

    def test_tiebreak_alphabetical(self):
        c = Counter(["b", "a", "c"])
        result = _sorted_counter(c)
        # All count=1, alphabetical order
        assert list(result.keys()) == ["a", "b", "c"]

    def test_empty_counter(self):
        assert _sorted_counter(Counter()) == {}

    def test_single_item(self):
        c = Counter(["x"])
        assert _sorted_counter(c) == {"x": 1}

    def test_multiple_ties(self):
        c = Counter(["z", "m", "a"])
        result = _sorted_counter(c)
        assert list(result.keys()) == ["a", "m", "z"]


# --- compute_counter ---

class TestComputeCounter:

    def test_total(self):
        assert compute_counter(SAMPLE_ENTRIES, {}) == "6"

    def test_filter_serie(self):
        assert compute_counter(SAMPLE_ENTRIES, {"serie": "ML"}) == "3"

    def test_filter_status(self):
        assert compute_counter(SAMPLE_ENTRIES, {"status": "BROKEN"}) == "1"

    def test_filter_serie_and_status(self):
        assert compute_counter(SAMPLE_ENTRIES, {"serie": "ML", "status": "READY"}) == "2"

    def test_filter_maturity(self):
        assert compute_counter(SAMPLE_ENTRIES, {"maturity": "PRODUCTION"}) == "4"

    def test_filter_sous_serie(self):
        assert compute_counter(SAMPLE_ENTRIES, {"sous_serie": "Image"}) == "2"

    def test_no_match(self):
        assert compute_counter(SAMPLE_ENTRIES, {"serie": "NonExistent"}) == "0"

    def test_empty_entries(self):
        assert compute_counter([], {}) == "0"

    def test_returns_string(self):
        result = compute_counter(SAMPLE_ENTRIES, {})
        assert isinstance(result, str)


# --- compute_breakdown ---

class TestComputeBreakdown:

    def test_breakdown_genai(self):
        bd = compute_breakdown(SAMPLE_ENTRIES, "GenAI")
        assert bd["Image"] == 2
        assert bd["Audio"] == 1

    def test_breakdown_no_sous_serie(self):
        bd = compute_breakdown(SAMPLE_ENTRIES, "ML")
        assert bd["root"] == 3

    def test_breakdown_empty(self):
        bd = compute_breakdown(SAMPLE_ENTRIES, "NonExistent")
        assert bd == {}

    def test_breakdown_sorted_by_count(self):
        entries = [
            _entry(serie="X", sous_serie="B"),
            _entry(serie="X", sous_serie="A"),
            _entry(serie="X", sous_serie="A"),
        ]
        bd = compute_breakdown(entries, "X")
        assert list(bd.keys()) == ["A", "B"]  # A=2 before B=1

    def test_breakdown_none_sous_serie(self):
        entries = [{"serie": "ML", "sous_serie": None, "status": "READY", "maturity": "PRODUCTION"}]
        bd = compute_breakdown(entries, "ML")
        assert bd == {"root": 1}


# --- compute_maturity_distribution ---

class TestComputeMaturityDistribution:

    def test_all(self):
        dist = compute_maturity_distribution(SAMPLE_ENTRIES)
        assert dist["PRODUCTION"] == 4
        assert dist["EXPERIMENTAL"] == 2

    def test_by_serie(self):
        dist = compute_maturity_distribution(SAMPLE_ENTRIES, "ML")
        assert dist["PRODUCTION"] == 2
        assert dist["EXPERIMENTAL"] == 1

    def test_unknown_maturity(self):
        entries = [{"serie": "ML", "status": "READY"}]  # no maturity key
        dist = compute_maturity_distribution(entries, "ML")
        assert dist == {"UNKNOWN": 1}

    def test_no_serie_filter(self):
        entries = [_entry(maturity="BETA"), _entry(maturity="BETA"), _entry(maturity="ALPHA")]
        dist = compute_maturity_distribution(entries)
        assert dist["BETA"] == 2
        assert dist["ALPHA"] == 1

    def test_sorted_output(self):
        entries = [_entry(maturity="Z"), _entry(maturity="A")]
        dist = compute_maturity_distribution(entries)
        # Z=1, A=1 → alphabetical tiebreak
        assert list(dist.keys()) == ["A", "Z"]


# --- compute_status_distribution ---

class TestComputeStatusDistribution:

    def test_all(self):
        dist = compute_status_distribution(SAMPLE_ENTRIES)
        assert dist["READY"] == 4
        assert dist["BROKEN"] == 1
        assert dist["NEEDS_IMPROVEMENT"] == 1

    def test_by_serie(self):
        dist = compute_status_distribution(SAMPLE_ENTRIES, "GenAI")
        assert dist["READY"] == 2
        assert dist["NEEDS_IMPROVEMENT"] == 1

    def test_sorted_output(self):
        entries = [_entry(status="DEMO"), _entry(status="ALPHA")]
        dist = compute_status_distribution(entries)
        assert list(dist.keys()) == ["ALPHA", "DEMO"]


# --- format_catalog_status_block ---

class TestFormatCatalogStatusBlock:

    def test_serie_block(self):
        block = format_catalog_status_block(SAMPLE_ENTRIES, "ML")
        assert "series: ML" in block
        assert "pedagogical_count: 3" in block
        assert "CATALOG-STATUS" in block
        assert "-->" in block

    def test_all_block(self):
        block = format_catalog_status_block(SAMPLE_ENTRIES, "ALL")
        assert "series: ALL" in block
        assert "total: 6" in block
        assert "breakdown:" in block

    def test_all_block_series_breakdown(self):
        block = format_catalog_status_block(SAMPLE_ENTRIES, "ALL")
        assert "ML=3" in block
        assert "GenAI=3" in block

    def test_serie_block_with_sous_serie_breakdown(self):
        block = format_catalog_status_block(SAMPLE_ENTRIES, "GenAI")
        assert "Image=2" in block
        assert "Audio=1" in block

    def test_nonexistent_serie_empty(self):
        block = format_catalog_status_block(SAMPLE_ENTRIES, "NonExistent")
        assert "pedagogical_count: 0" in block

    def test_block_starts_and_ends_correctly(self):
        block = format_catalog_status_block(SAMPLE_ENTRIES, "ML")
        assert block.startswith("<!-- CATALOG-STATUS\n")
        assert block.endswith("-->")


# --- expand_file ---

class TestExpandFile:

    def test_no_markers(self):
        content = "# Title\nSome text.\n"
        new_content, changes = expand_file(content, SAMPLE_ENTRIES)
        assert new_content == content
        assert changes == []

    def test_counter_marker_preserved(self):
        content = "<!-- CATALOG:counter:total -->\n"
        new_content, changes = expand_file(content, SAMPLE_ENTRIES)
        assert "CATALOG:counter:total" in new_content

    def test_counter_with_params(self):
        content = "<!-- CATALOG:counter:serie=ML -->\n"
        new_content, changes = expand_file(content, SAMPLE_ENTRIES)
        assert "CATALOG:counter:serie=ML" in new_content

    def test_catalog_status_block_updated(self):
        content = "<!-- CATALOG-STATUS\nseries: ML\n-->\n"
        new_content, changes = expand_file(content, SAMPLE_ENTRIES)
        assert "series: ML" in new_content
        assert "pedagogical_count: 3" in new_content

    def test_catalog_status_block_all(self):
        content = "<!-- CATALOG-STATUS\nseries: ALL\n-->\n"
        new_content, changes = expand_file(content, SAMPLE_ENTRIES)
        assert "total: 6" in new_content

    def test_mixed_markers(self):
        content = (
            "# Title\n"
            "<!-- CATALOG:counter:total -->\n"
            "<!-- CATALOG-STATUS\nseries: ML\n-->\n"
        )
        new_content, changes = expand_file(content, SAMPLE_ENTRIES)
        assert "CATALOG:counter:total" in new_content
        assert "series: ML" in new_content

    def test_catalog_status_block_unchanged_when_current(self):
        """Block that matches current data produces no changes."""
        block = format_catalog_status_block(SAMPLE_ENTRIES, "ML")
        content = f"# README\n{block}\n"
        new_content, changes = expand_file(content, SAMPLE_ENTRIES)
        assert changes == []

    def test_catalog_status_no_series_line_preserved(self):
        """Block with no 'series:' line is preserved as-is."""
        content = "<!-- CATALOG-STATUS\nnonsense: here\n-->\n"
        new_content, changes = expand_file(content, [_entry()])
        assert changes == []
        assert "nonsense: here" in new_content

    def test_unknown_marker_type_preserved(self):
        content = "<!-- CATALOG:unknown:foo -->\n"
        new_content, changes = expand_file(content, [_entry()])
        assert "<!-- CATALOG:unknown:foo -->" in new_content
        assert changes == []

    def test_counter_empty_params(self):
        content = "<!-- CATALOG:counter: -->\n"
        new_content, changes = expand_file(content, [_entry()])
        assert "CATALOG:counter:" in new_content

    def test_multiple_counter_markers(self):
        content = (
            "<!-- CATALOG:counter:total -->\n"
            "<!-- CATALOG:counter:serie=ML -->\n"
        )
        new_content, changes = expand_file(content, SAMPLE_ENTRIES)
        assert "CATALOG:counter:total" in new_content
        assert "CATALOG:counter:serie=ML" in new_content

    def test_catalog_status_multiline_block(self):
        """Multi-line CATALOG-STATUS block is correctly replaced."""
        entries = [_entry(serie="ML")]
        content = (
            "<!-- CATALOG-STATUS\n"
            "series: ML\n"
            "pedagogical_count: 999\n"
            "-->\n"
        )
        new_content, changes = expand_file(content, entries)
        assert "pedagogical_count: 1" in new_content
        assert len(changes) > 0


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
            _entry(serie="SymbolicAI", sous_serie="Lean", maturity="PRODUCTION"),
            _entry(serie="SymbolicAI", sous_serie="Lean", maturity="BETA"),
            _entry(serie="SymbolicAI", sous_serie="Tweety"),
        ]
        block = format_catalog_status_block(entries, "SymbolicAI-Lean")
        assert "pedagogical_count: 2" in block
        assert "PRODUCTION=1" in block and "BETA=1" in block

    def test_sousserie_counter_marker(self):
        entries = [
            _entry(serie="SymbolicAI", sous_serie="Lean"),
            _entry(serie="SymbolicAI", sous_serie="Tweety"),
        ]
        result = compute_counter(entries, {"serie": "SymbolicAI-Lean"})
        assert result == "1"

    def test_sousserie_breakdown(self):
        entries = [
            _entry(serie="SymbolicAI", sous_serie="Lean"),
            _entry(serie="SymbolicAI", sous_serie="Lean"),
            _entry(serie="SymbolicAI", sous_serie="Tweety"),
        ]
        breakdown = compute_breakdown(entries, "SymbolicAI-Lean")
        assert breakdown == {"Lean": 2}


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
