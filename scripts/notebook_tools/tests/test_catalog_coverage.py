"""Tests for scripts/notebook_tools/catalog_coverage.py — catalog coverage report.

Tests focus on pure functions: check_catalog_completeness, check_c2_by_maturity,
check_readme_markers, generate_report. Filesystem checks use tmp_path for isolation.
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from catalog_coverage import (
    check_c2_by_maturity,
    check_catalog_completeness,
    check_readme_markers,
    generate_report,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

SAMPLE_ENTRIES = [
    {
        "path": "GenAI/Image/GenAI-1.ipynb",
        "title": "Intro to GenAI",
        "serie": "GenAI",
        "kernel": "python3",
        "maturity": "PRODUCTION",
        "status": "READY",
        "cells_total": 20,
        "cells_without_outputs": 0,
        "executable_locally": True,
        "requires_api": False,
    },
    {
        "path": "GenAI/Image/GenAI-2.ipynb",
        "title": "Advanced GenAI",
        "serie": "GenAI",
        "kernel": "python3",
        "maturity": "BETA",
        "status": "READY",
        "cells_total": 15,
        "cells_without_outputs": 2,
        "executable_locally": True,
        "requires_api": True,
    },
    {
        "path": "Search/Part1/Search-1.ipynb",
        "title": "BFS & DFS",
        "serie": "Search",
        "kernel": "python3",
        "maturity": "PRODUCTION",
        "status": "DEMO",
        "cells_total": 10,
        "cells_without_outputs": 0,
        "executable_locally": True,
        "requires_api": False,
    },
    {
        "path": "ML/ML-1.ipynb",
        "title": "",
        "serie": "",
        "kernel": "unknown",
        "maturity": "ALPHA",
        "status": "READY",
        "cells_total": 0,
        "cells_without_outputs": 5,
        "executable_locally": False,
        "requires_api": False,
    },
    {
        "path": "QuantConnect/QC-1.ipynb",
        "title": "QC Intro",
        "serie": "QuantConnect",
        "kernel": "python3",
        "maturity": "DRAFT",
        "status": "BROKEN",
        "cells_total": 8,
        "cells_without_outputs": 8,
        "executable_locally": False,
        "requires_api": True,
    },
]


# ---------------------------------------------------------------------------
# check_catalog_completeness
# ---------------------------------------------------------------------------

class TestCheckCatalogCompleteness:
    def test_no_issues_for_complete_entries(self):
        complete = [
            {"path": "a.ipynb", "title": "A", "serie": "GenAI",
             "kernel": "python3", "cells_total": 10},
        ]
        issues = check_catalog_completeness(complete)
        assert len(issues) == 0

    def test_missing_title(self):
        entries = [{"path": "a.ipynb", "title": "", "serie": "S", "kernel": "k", "cells_total": 5}]
        issues = check_catalog_completeness(entries)
        assert any(i["issue"] == "missing title" for i in issues)

    def test_missing_serie(self):
        entries = [{"path": "a.ipynb", "title": "T", "serie": "", "kernel": "k", "cells_total": 5}]
        issues = check_catalog_completeness(entries)
        assert any(i["issue"] == "missing serie" for i in issues)

    def test_missing_kernel(self):
        entries = [{"path": "a.ipynb", "title": "T", "serie": "S", "kernel": "unknown", "cells_total": 5}]
        issues = check_catalog_completeness(entries)
        assert any(i["issue"] == "missing kernel" for i in issues)

    def test_zero_cells(self):
        entries = [{"path": "a.ipynb", "title": "T", "serie": "S", "kernel": "k", "cells_total": 0}]
        issues = check_catalog_completeness(entries)
        assert any(i["issue"] == "zero cells" for i in issues)

    def test_multiple_issues_in_one_entry(self):
        entries = [{"path": "bad.ipynb", "title": "", "serie": "", "kernel": "unknown", "cells_total": 0}]
        issues = check_catalog_completeness(entries)
        assert len(issues) == 4

    def test_sample_has_four_issues(self):
        """ML-1 entry in SAMPLE_ENTRIES has 4 issues."""
        issues = check_catalog_completeness(SAMPLE_ENTRIES)
        assert len(issues) == 4
        paths = [i["path"] for i in issues]
        assert all(p == "ML/ML-1.ipynb" for p in paths)

    def test_empty_list(self):
        assert check_catalog_completeness([]) == []


# ---------------------------------------------------------------------------
# check_c2_by_maturity
# ---------------------------------------------------------------------------

class TestCheckC2ByMaturity:
    def test_production_full_compliance(self):
        entries = [
            {"maturity": "PRODUCTION", "status": "READY", "cells_without_outputs": 0},
        ]
        result = check_c2_by_maturity(entries)
        assert result["PRODUCTION"]["total"] == 1
        assert result["PRODUCTION"]["compliant"] == 1
        assert result["PRODUCTION"]["rate"] == 100.0

    def test_broken_excluded_from_production(self):
        entries = [
            {"maturity": "PRODUCTION", "status": "BROKEN", "cells_without_outputs": 0},
        ]
        result = check_c2_by_maturity(entries)
        assert result["PRODUCTION"]["total"] == 0

    def test_partial_compliance(self):
        entries = [
            {"maturity": "BETA", "status": "READY", "cells_without_outputs": 0},
            {"maturity": "BETA", "status": "READY", "cells_without_outputs": 3},
        ]
        result = check_c2_by_maturity(entries)
        assert result["BETA"]["total"] == 2
        assert result["BETA"]["compliant"] == 1
        assert result["BETA"]["rate"] == 50.0

    def test_alpha_with_zero_total(self):
        entries = [
            {"maturity": "PRODUCTION", "status": "READY", "cells_without_outputs": 0},
        ]
        result = check_c2_by_maturity(entries)
        assert result["ALPHA"]["total"] == 0
        assert result["ALPHA"]["rate"] == 0

    def test_all_four_maturities_present(self):
        result = check_c2_by_maturity(SAMPLE_ENTRIES)
        assert set(result.keys()) == {"PRODUCTION", "BETA", "ALPHA", "DRAFT"}

    def test_sample_production(self):
        result = check_c2_by_maturity(SAMPLE_ENTRIES)
        # GenAI-1 (PRODUCTION, READY, 0 missing) + Search-1 (PRODUCTION, DEMO, 0 missing)
        assert result["PRODUCTION"]["total"] == 2
        assert result["PRODUCTION"]["compliant"] == 2


# ---------------------------------------------------------------------------
# check_readme_markers
# ---------------------------------------------------------------------------

class TestCheckReadmeMarkers:
    def test_no_readme(self, tmp_path, monkeypatch):
        monkeypatch.setattr("catalog_coverage.NOTEBOOKS_DIR", tmp_path)
        entries = [{"serie": "GenAI"}]
        result = check_readme_markers(entries)
        assert len(result) == 1
        assert result[0]["has_readme"] is False
        assert result[0]["has_marker"] is False

    def test_readme_with_marker(self, tmp_path, monkeypatch):
        nb_dir = tmp_path / "Search"
        nb_dir.mkdir()
        readme = nb_dir / "README.md"
        readme.write_text("# Search\n\n<!-- CATALOG-STATUS: ok -->\n", encoding="utf-8")
        monkeypatch.setattr("catalog_coverage.NOTEBOOKS_DIR", tmp_path)
        entries = [{"serie": "Search"}]
        result = check_readme_markers(entries)
        assert result[0]["has_readme"] is True
        assert result[0]["has_marker"] is True

    def test_readme_without_marker(self, tmp_path, monkeypatch):
        nb_dir = tmp_path / "ML"
        nb_dir.mkdir()
        readme = nb_dir / "README.md"
        readme.write_text("# ML\nNo markers here.\n", encoding="utf-8")
        monkeypatch.setattr("catalog_coverage.NOTEBOOKS_DIR", tmp_path)
        entries = [{"serie": "ML"}]
        result = check_readme_markers(entries)
        assert result[0]["has_readme"] is True
        assert result[0]["has_marker"] is False

    def test_multiple_series(self, tmp_path, monkeypatch):
        nb_dir = tmp_path / "GenAI"
        nb_dir.mkdir()
        (nb_dir / "README.md").write_text("<!-- CATALOG-STATUS -->", encoding="utf-8")
        monkeypatch.setattr("catalog_coverage.NOTEBOOKS_DIR", tmp_path)
        entries = [{"serie": "GenAI"}, {"serie": "Missing"}]
        result = check_readme_markers(entries)
        assert len(result) == 2
        genai = [r for r in result if r["serie"] == "GenAI"][0]
        missing = [r for r in result if r["serie"] == "Missing"][0]
        assert genai["has_marker"] is True
        assert missing["has_readme"] is False

    def test_empty_entries(self, tmp_path, monkeypatch):
        monkeypatch.setattr("catalog_coverage.NOTEBOOKS_DIR", tmp_path)
        result = check_readme_markers([])
        assert result == []


# ---------------------------------------------------------------------------
# generate_report
# ---------------------------------------------------------------------------

class TestGenerateReport:
    def test_full_report_has_sections(self):
        report = generate_report(SAMPLE_ENTRIES)
        assert "# Catalog Coverage Report" in report
        assert "## Overview" in report
        assert "## Catalog Completeness" in report
        assert "## C.2 Compliance by Maturity" in report
        assert "## README Markers" in report

    def test_short_report_format(self):
        report = generate_report(SAMPLE_ENTRIES, short=True)
        assert "# Catalog Coverage Report" in report
        assert "Per-Serie Summary" in report
        assert "GenAI" in report
        # Short report should NOT have full sections
        assert "## Catalog Completeness" not in report

    def test_serie_filter(self):
        report = generate_report(SAMPLE_ENTRIES, serie_filter="Search")
        assert "Search" in report
        # Only Search entries (1 notebook)
        assert "| Total notebooks | 1 |" in report

    def test_serie_filter_excludes_others(self):
        report = generate_report(SAMPLE_ENTRIES, serie_filter="Search")
        # GenAI should not appear in per-serie breakdown
        assert "### GenAI" not in report

    def test_total_count(self):
        report = generate_report(SAMPLE_ENTRIES)
        assert "| Total notebooks | 5 |" in report

    def test_broken_count(self):
        report = generate_report(SAMPLE_ENTRIES)
        assert "| BROKEN | 1 |" in report

    def test_empty_entries(self):
        report = generate_report([])
        assert "| Total notebooks | 0 |" in report
