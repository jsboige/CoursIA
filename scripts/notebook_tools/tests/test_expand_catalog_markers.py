"""Tests for expand_catalog_markers.py — catalog marker expansion."""

import os
import sys

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from expand_catalog_markers import (
    compute_counter,
    compute_breakdown,
    compute_maturity_distribution,
    compute_status_distribution,
    format_catalog_status_block,
    expand_file,
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


class TestComputeBreakdown:

    def test_breakdown_genai(self):
        bd = compute_breakdown(SAMPLE_ENTRIES, "GenAI")
        assert bd["Image"] == 2
        assert bd["Audio"] == 1

    def test_breakdown_no_sous_serie(self):
        bd = compute_breakdown(SAMPLE_ENTRIES, "ML")
        assert bd["_root"] == 3

    def test_breakdown_empty(self):
        bd = compute_breakdown(SAMPLE_ENTRIES, "NonExistent")
        assert bd == {}


class TestComputeMaturityDistribution:

    def test_all(self):
        dist = compute_maturity_distribution(SAMPLE_ENTRIES)
        assert dist["PRODUCTION"] == 4
        assert dist["EXPERIMENTAL"] == 2

    def test_by_serie(self):
        dist = compute_maturity_distribution(SAMPLE_ENTRIES, "ML")
        assert dist["PRODUCTION"] == 2
        assert dist["EXPERIMENTAL"] == 1


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


class TestFormatCatalogStatusBlock:

    def test_serie_block(self):
        block = format_catalog_status_block(SAMPLE_ENTRIES, "ML")
        assert "series: ML" in block
        assert "pedagogical_count: 3" in block
        assert "CATALOG-STATUS" in block

    def test_all_block(self):
        block = format_catalog_status_block(SAMPLE_ENTRIES, "ALL")
        assert "series: ALL" in block
        assert "total: 6" in block


class TestExpandFile:

    def test_no_markers(self):
        content = "# Title\nSome text.\n"
        new_content, changes = expand_file(content, SAMPLE_ENTRIES)
        assert new_content == content
        assert changes == []

    def test_counter_marker_preserved(self):
        content = "<!-- CATALOG:counter:total -->\n"
        new_content, changes = expand_file(content, SAMPLE_ENTRIES)
        # The marker itself is preserved (not replaced with a number)
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
