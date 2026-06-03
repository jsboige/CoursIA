"""Tests for verify_catalog_readme.py — catalog block parsing and building."""

import os
import re
import sys

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from verify_catalog_readme import parse_catalog_block, build_catalog_block


class TestParseCatalogBlock:

    def test_full_block(self):
        text = (
            "# Series Title\n"
            "<!-- CATALOG-STATUS\n"
            "series: Search\n"
            "pedagogical_count: 40\n"
            "breakdown: Part1=11, Part2=9, Part3=20\n"
            "updated: 2026-05-01\n"
            "-->\n"
        )
        result = parse_catalog_block(text)
        assert result is not None
        assert result["series"] == "Search"
        assert result["pedagogical_count"] == 40
        assert result["breakdown"]["Part1"] == 11
        assert result["breakdown"]["Part2"] == 9
        assert result["breakdown"]["Part3"] == 20
        assert result["updated"] == "2026-05-01"

    def test_no_block(self):
        text = "# Title\nSome content\n"
        assert parse_catalog_block(text) is None

    def test_minimal_block(self):
        text = (
            "<!-- CATALOG-STATUS\n"
            "series: ML\n"
            "-->\n"
        )
        result = parse_catalog_block(text)
        assert result is not None
        assert result["series"] == "ML"
        assert "pedagogical_count" not in result

    def test_empty_breakdown(self):
        text = (
            "<!-- CATALOG-STATUS\n"
            "series: GenAI\n"
            "pedagogical_count: 5\n"
            "breakdown: \n"
            "-->\n"
        )
        result = parse_catalog_block(text)
        assert result is not None
        assert result["pedagogical_count"] == 5

    def test_single_subfolder_breakdown(self):
        text = (
            "<!-- CATALOG-STATUS\n"
            "series: Sudoku\n"
            "pedagogical_count: 10\n"
            "breakdown: _root=10\n"
            "-->\n"
        )
        result = parse_catalog_block(text)
        assert result["breakdown"] == {"_root": 10}

    def test_extra_fields_ignored(self):
        text = (
            "<!-- CATALOG-STATUS\n"
            "series: ML\n"
            "pedagogical_count: 3\n"
            "custom_field: some value\n"
            "-->\n"
        )
        result = parse_catalog_block(text)
        assert result["series"] == "ML"
        assert result["pedagogical_count"] == 3
        assert result["custom_field"] == "some value"


class TestBuildCatalogBlock:

    def test_basic_block(self):
        counts = {"total": 15, "by_subfolder": {"Part1": 8, "Part2": 7}}
        block = build_catalog_block("Search", counts)
        assert "series: Search" in block
        assert "pedagogical_count: 15" in block
        assert "Part1=8" in block
        assert "Part2=7" in block
        assert "CATALOG-STATUS" in block
        assert "-->" in block

    def test_single_subfolder(self):
        counts = {"total": 5, "by_subfolder": {"_root": 5}}
        block = build_catalog_block("Sudoku", counts)
        assert "pedagogical_count: 5" in block
        assert "_root=5" in block

    def test_sorted_breakdown(self):
        counts = {"total": 6, "by_subfolder": {"Zebra": 1, "Alpha": 3, "Mid": 2}}
        block = build_catalog_block("Test", counts)
        # Keys should be sorted
        idx_alpha = block.index("Alpha=3")
        idx_mid = block.index("Mid=2")
        idx_zebra = block.index("Zebra=1")
        assert idx_alpha < idx_mid < idx_zebra

    def test_includes_today_date(self):
        from datetime import date
        counts = {"total": 1, "by_subfolder": {"_root": 1}}
        block = build_catalog_block("X", counts)
        assert date.today().isoformat() in block

    def test_empty_subfolder(self):
        counts = {"total": 0, "by_subfolder": {}}
        block = build_catalog_block("Empty", counts)
        assert "pedagogical_count: 0" in block
