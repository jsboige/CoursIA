"""Tests for scripts/notebook_tools/verify_catalog_readme.py — catalog marker verifier.

Tests focus on pure functions: parse_catalog_block, build_catalog_block.
Filesystem-dependent verify_series is tested with tmp_path and mocked
NOTEBOOKS_DIR.
"""

import json
import sys
from pathlib import Path
from unittest.mock import patch

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from verify_catalog_readme import (
    CATALOG_BLOCK_RE,
    build_catalog_block,
    parse_catalog_block,
    verify_series,
)


# ---------------------------------------------------------------------------
# parse_catalog_block
# ---------------------------------------------------------------------------

class TestParseCatalogBlock:
    def test_full_block(self):
        text = (
            "# Search\n\n"
            "<!-- CATALOG-STATUS\n"
            "series: Search\n"
            "pedagogical_count: 40\n"
            "breakdown: Part1-Foundations=11, Part2-CSP=9, Applications=20\n"
            "updated: 2026-05-01\n"
            "-->"
        )
        result = parse_catalog_block(text)
        assert result is not None
        assert result["series"] == "Search"
        assert result["pedagogical_count"] == 40
        assert result["breakdown"]["Part1-Foundations"] == 11
        assert result["breakdown"]["Part2-CSP"] == 9
        assert result["breakdown"]["Applications"] == 20
        assert result["updated"] == "2026-05-01"

    def test_no_block(self):
        text = "# Title\nSome content without catalog block."
        assert parse_catalog_block(text) is None

    def test_minimal_block(self):
        text = "<!-- CATALOG-STATUS\nseries: ML\n-->"
        result = parse_catalog_block(text)
        assert result is not None
        assert result["series"] == "ML"
        assert "pedagogical_count" not in result

    def test_no_breakdown(self):
        text = (
            "<!-- CATALOG-STATUS\n"
            "series: Sudoku\n"
            "pedagogical_count: 12\n"
            "updated: 2026-04-15\n"
            "-->"
        )
        result = parse_catalog_block(text)
        assert result["pedagogical_count"] == 12
        assert "breakdown" not in result

    def test_breakdown_single_entry(self):
        text = (
            "<!-- CATALOG-STATUS\n"
            "series: IIT\n"
            "pedagogical_count: 5\n"
            "breakdown: Core=5\n"
            "-->"
        )
        result = parse_catalog_block(text)
        assert result["breakdown"] == {"Core": 5}

    def test_line_without_colon_skipped(self):
        text = (
            "<!-- CATALOG-STATUS\n"
            "series: RL\n"
            "this line has no colon separator\n"
            "pedagogical_count: 8\n"
            "-->"
        )
        result = parse_catalog_block(text)
        assert result["series"] == "RL"
        assert result["pedagogical_count"] == 8

    def test_multiple_blocks_returns_first(self):
        text = (
            "<!-- CATALOG-STATUS\nseries: First\npedagogical_count: 10\n-->\n"
            "<!-- CATALOG-STATUS\nseries: Second\npedagogical_count: 20\n-->"
        )
        result = parse_catalog_block(text)
        assert result["series"] == "First"
        assert result["pedagogical_count"] == 10


# ---------------------------------------------------------------------------
# CATALOG_BLOCK_RE
# ---------------------------------------------------------------------------

class TestCatalogBlockRe:
    def test_matches_standard_block(self):
        text = "<!-- CATALOG-STATUS\nseries: X\n-->"
        assert CATALOG_BLOCK_RE.search(text) is not None

    def test_matches_with_whitespace(self):
        text = "<!--  CATALOG-STATUS \nseries: X\n  -->"
        assert CATALOG_BLOCK_RE.search(text) is not None

    def test_no_match_regular_comment(self):
        text = "<!-- Just a regular HTML comment -->"
        assert CATALOG_BLOCK_RE.search(text) is None

    def test_multiline_capture(self):
        text = "<!-- CATALOG-STATUS\nline1\nline2\nline3\n-->"
        m = CATALOG_BLOCK_RE.search(text)
        assert m is not None
        assert "line1" in m.group(1)
        assert "line3" in m.group(1)


# ---------------------------------------------------------------------------
# build_catalog_block
# ---------------------------------------------------------------------------

class TestBuildCatalogBlock:
    def test_basic_block(self):
        counts = {"total": 15, "by_subfolder": {"Part1": 10, "Part2": 5}}
        block = build_catalog_block("Search", counts)
        assert "CATALOG-STATUS" in block
        assert "series: Search" in block
        assert "pedagogical_count: 15" in block
        assert "Part1=10" in block
        assert "Part2=5" in block
        assert "<!--" in block
        assert "-->" in block

    def test_empty_subfolders(self):
        counts = {"total": 0, "by_subfolder": {}}
        block = build_catalog_block("Empty", counts)
        assert "pedagogical_count: 0" in block
        assert "breakdown: " in block

    def test_single_subfolder(self):
        counts = {"total": 7, "by_subfolder": {"Core": 7}}
        block = build_catalog_block("IIT", counts)
        assert "Core=7" in block

    def test_sorted_subfolders(self):
        counts = {"total": 30, "by_subfolder": {"Zebra": 10, "Alpha": 20}}
        block = build_catalog_block("Test", counts)
        # Alpha comes before Zebra in sorted order
        alpha_pos = block.index("Alpha=20")
        zebra_pos = block.index("Zebra=10")
        assert alpha_pos < zebra_pos

    def test_date_in_block(self):
        counts = {"total": 5, "by_subfolder": {"A": 5}}
        block = build_catalog_block("X", counts)
        assert "updated: " in block
        # Should be a valid ISO date
        import re
        date_match = re.search(r"updated: (\d{4}-\d{2}-\d{2})", block)
        assert date_match is not None


# ---------------------------------------------------------------------------
# verify_series (filesystem tests with tmp_path)
# ---------------------------------------------------------------------------

class TestVerifySeries:
    def _setup_series(self, tmp_path, series_name, readme_content,
                      notebook_count=3):
        """Create a fake series directory with README and notebooks."""
        series_dir = tmp_path / series_name
        series_dir.mkdir()
        if readme_content:
            (series_dir / "README.md").write_text(readme_content, encoding="utf-8")
        # Create fake notebooks
        for i in range(notebook_count):
            nb = {"cells": [], "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
            (series_dir / f"nb{i}.ipynb").write_text(json.dumps(nb), encoding="utf-8")
        return series_dir

    def test_no_readme(self, tmp_path):
        with patch("verify_catalog_readme.NOTEBOOKS_DIR", tmp_path):
            series_dir = tmp_path / "TestSeries"
            series_dir.mkdir()
            for i in range(3):
                (series_dir / f"nb{i}.ipynb").write_text("{}", encoding="utf-8")
            result = verify_series("TestSeries")
        assert result["status"] == "NO_README"
        assert result["actual"] == 3

    def test_catalog_block_match(self, tmp_path):
        readme = (
            "# Search\n\n"
            "<!-- CATALOG-STATUS\n"
            "series: Search\n"
            "pedagogical_count: 2\n"
            "breakdown: Core=2\n"
            "-->"
        )
        with patch("verify_catalog_readme.NOTEBOOKS_DIR", tmp_path):
            self._setup_series(tmp_path, "Search", readme, notebook_count=2)
            result = verify_series("Search")
        assert result["status"] == "OK"
        assert result["declared"] == 2
        assert result["actual"] == 2
        assert result["match"] is True
        assert result["declared_source"] == "catalog"

    def test_catalog_block_drift(self, tmp_path):
        readme = (
            "# Search\n\n"
            "<!-- CATALOG-STATUS\n"
            "series: Search\n"
            "pedagogical_count: 10\n"
            "-->"
        )
        with patch("verify_catalog_readme.NOTEBOOKS_DIR", tmp_path):
            self._setup_series(tmp_path, "Search", readme, notebook_count=3)
            result = verify_series("Search")
        assert result["status"] == "DRIFT"
        assert result["declared"] == 10
        assert result["actual"] == 3
        assert result["match"] is False

    def test_no_marker(self, tmp_path):
        readme = "# Search\n\nSome text without catalog markers."
        with patch("verify_catalog_readme.NOTEBOOKS_DIR", tmp_path):
            self._setup_series(tmp_path, "Search", readme, notebook_count=5)
            result = verify_series("Search")
        assert result["status"] == "NO_MARKER"
        assert result["actual"] == 5
        assert result["declared"] is None

    def test_inject_new_block(self, tmp_path):
        readme = "# Search\n\nSome text."
        with patch("verify_catalog_readme.NOTEBOOKS_DIR", tmp_path):
            self._setup_series(tmp_path, "Search", readme, notebook_count=3)
            result = verify_series("Search", inject=True)
        assert result.get("injected") is True
        # Re-read the README to verify block was injected
        readme_text = (tmp_path / "Search" / "README.md").read_text(encoding="utf-8")
        assert "CATALOG-STATUS" in readme_text
        assert "pedagogical_count: 3" in readme_text

    def test_inject_updates_existing_block(self, tmp_path):
        readme = (
            "# Search\n\n"
            "<!-- CATALOG-STATUS\n"
            "series: Search\n"
            "pedagogical_count: 99\n"
            "-->"
        )
        with patch("verify_catalog_readme.NOTEBOOKS_DIR", tmp_path):
            self._setup_series(tmp_path, "Search", readme, notebook_count=4)
            result = verify_series("Search", inject=True)
        assert result.get("injected") is True
        readme_text = (tmp_path / "Search" / "README.md").read_text(encoding="utf-8")
        assert "pedagogical_count: 4" in readme_text
        assert "pedagogical_count: 99" not in readme_text

    def test_inject_no_title_inserts_at_top(self, tmp_path):
        readme = "Just some text without a title."
        with patch("verify_catalog_readme.NOTEBOOKS_DIR", tmp_path):
            self._setup_series(tmp_path, "Test", readme, notebook_count=2)
            result = verify_series("Test", inject=True)
        assert result.get("injected") is True
        readme_text = (tmp_path / "Test" / "README.md").read_text(encoding="utf-8")
        # Block should be at the top since no title found
        assert readme_text.startswith("<!-- CATALOG-STATUS")

    def test_breakdown_populated(self, tmp_path):
        readme = "# ML\n\n<!-- CATALOG-STATUS\nseries: ML\npedagogical_count: 2\n-->"
        with patch("verify_catalog_readme.NOTEBOOKS_DIR", tmp_path):
            series_dir = tmp_path / "ML"
            series_dir.mkdir()
            (series_dir / "README.md").write_text(readme, encoding="utf-8")
            sub = series_dir / "Core"
            sub.mkdir()
            for i in range(2):
                (sub / f"nb{i}.ipynb").write_text("{}", encoding="utf-8")
            result = verify_series("ML")
        assert "breakdown" in result
        assert result["breakdown"].get("Core") == 2
