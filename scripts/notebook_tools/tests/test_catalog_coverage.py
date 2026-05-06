"""Tests for catalog_coverage.py — catalog coverage reporting."""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from catalog_coverage import (
    check_c2_by_maturity,
    check_catalog_completeness,
    generate_report,
)


def _entry(path="Test/nb.ipynb", title="Test", serie="Test", kernel="Python 3",
           maturity="ALPHA", status="READY", cells_total=5, cells_without_outputs=0,
           executable_locally=True, requires_api=False):
    """Build a catalog entry."""
    return {
        "path": path,
        "title": title,
        "serie": serie,
        "kernel": kernel,
        "maturity": maturity,
        "status": status,
        "cells_total": cells_total,
        "cells_without_outputs": cells_without_outputs,
        "executable_locally": executable_locally,
        "requires_api": requires_api,
    }


# --- check_catalog_completeness ---

class TestCheckCatalogCompleteness:
    def test_complete_entries(self):
        entries = [_entry()]
        assert check_catalog_completeness(entries) == []

    def test_missing_title(self):
        entries = [_entry(title="")]
        issues = check_catalog_completeness(entries)
        assert len(issues) == 1
        assert issues[0]["issue"] == "missing title"

    def test_missing_serie(self):
        entries = [_entry(serie="")]
        issues = check_catalog_completeness(entries)
        assert len(issues) == 1
        assert issues[0]["issue"] == "missing serie"

    def test_missing_kernel(self):
        entries = [_entry(kernel="unknown")]
        issues = check_catalog_completeness(entries)
        assert len(issues) == 1
        assert issues[0]["issue"] == "missing kernel"

    def test_zero_cells(self):
        entries = [_entry(cells_total=0)]
        issues = check_catalog_completeness(entries)
        assert any(i["issue"] == "zero cells" for i in issues)

    def test_multiple_issues(self):
        entries = [_entry(title="", serie="", kernel="unknown", cells_total=0)]
        issues = check_catalog_completeness(entries)
        assert len(issues) == 4


# --- check_c2_by_maturity ---

class TestCheckC2ByMaturity:
    def test_all_compliant(self):
        entries = [
            _entry(maturity="PRODUCTION", status="READY"),
            _entry(maturity="BETA", status="READY"),
        ]
        result = check_c2_by_maturity(entries)
        assert result["PRODUCTION"]["compliant"] == 1
        assert result["BETA"]["compliant"] == 1

    def test_non_compliant(self):
        entries = [_entry(maturity="PRODUCTION", cells_without_outputs=3)]
        result = check_c2_by_maturity(entries)
        assert result["PRODUCTION"]["compliant"] == 0
        assert result["PRODUCTION"]["total"] == 1

    def test_broken_excluded(self):
        entries = [_entry(maturity="PRODUCTION", status="BROKEN")]
        result = check_c2_by_maturity(entries)
        assert result["PRODUCTION"]["total"] == 0

    def test_empty_entries(self):
        result = check_c2_by_maturity([])
        for mat in ["PRODUCTION", "BETA", "ALPHA", "DRAFT"]:
            assert result[mat]["total"] == 0
            assert result[mat]["rate"] == 0

    def test_rate_calculation(self):
        entries = [
            _entry(maturity="ALPHA"),
            _entry(maturity="ALPHA", cells_without_outputs=2),
        ]
        result = check_c2_by_maturity(entries)
        assert result["ALPHA"]["total"] == 2
        assert result["ALPHA"]["compliant"] == 1
        assert result["ALPHA"]["rate"] == 50.0


# --- generate_report ---

class TestGenerateReport:
    def test_basic_report(self):
        entries = [_entry()]
        report = generate_report(entries)
        assert "Catalog Coverage Report" in report
        assert "Overview" in report

    def test_serie_filter(self):
        entries = [
            _entry(serie="GenAI"),
            _entry(serie="ML"),
        ]
        report = generate_report(entries, serie_filter="GenAI")
        assert "GenAI" in report

    def test_short_report(self):
        entries = [
            _entry(serie="GenAI", maturity="PRODUCTION"),
            _entry(serie="GenAI", maturity="BETA"),
        ]
        report = generate_report(entries, short=True)
        assert "Per-Serie Summary" in report
        assert "P:" in report

    def test_completeness_section(self):
        entries = [_entry(title="")]
        report = generate_report(entries)
        assert "Catalog Completeness" in report
        assert "Missing titles" in report

    def test_c2_section(self):
        entries = [_entry(maturity="PRODUCTION")]
        report = generate_report(entries)
        assert "C.2 Compliance" in report


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
