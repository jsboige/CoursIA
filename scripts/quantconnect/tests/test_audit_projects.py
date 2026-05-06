"""Tests for audit_projects.py — QC Cloud project classification."""

import json
import sys
import tempfile
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from audit_projects import (
    classify_project,
    generate_report,
    get_catalog_bt_count,
    get_catalog_sharpe,
    get_org_name,
    load_catalog,
    load_projects,
)


def _project(name="TestProject", pid=1, modified="2026-04-01T00:00:00Z",
             created="2026-01-01T00:00:00Z", org_id="d600793eabcd"):
    """Build a project dict."""
    return {
        "name": name,
        "projectId": pid,
        "modified": modified,
        "created": created,
        "organizationId": org_id,
    }


# --- load_projects ---

class TestLoadProjects:
    def test_loads_projects(self, tmp_path):
        p = tmp_path / "projects.json"
        p.write_text(json.dumps({"projects": [_project()]}), encoding="utf-8")
        result = load_projects(str(p))
        assert len(result) == 1
        assert result[0]["name"] == "TestProject"

    def test_empty_projects(self, tmp_path):
        p = tmp_path / "empty.json"
        p.write_text(json.dumps({}), encoding="utf-8")
        result = load_projects(str(p))
        assert result == []

    def test_missing_file(self):
        with pytest.raises(FileNotFoundError):
            load_projects("/nonexistent/path.json")


# --- load_catalog ---

class TestLoadCatalog:
    def test_loads_catalog(self, tmp_path):
        p = tmp_path / "catalog.json"
        p.write_text(json.dumps({"projects": [
            {"projectId": 42, "best_sharpe": 1.5, "backtest_count": 10}
        ]}), encoding="utf-8")
        result = load_catalog(str(p))
        assert 42 in result
        assert result[42]["best_sharpe"] == 1.5

    def test_empty_catalog(self, tmp_path):
        p = tmp_path / "empty.json"
        p.write_text(json.dumps({}), encoding="utf-8")
        result = load_catalog(str(p))
        assert result == {}


# --- get_catalog_sharpe / get_catalog_bt_count ---

class TestCatalogHelpers:
    def test_sharpe_found(self):
        catalog = {1: {"best_sharpe": 2.3}}
        assert get_catalog_sharpe(catalog, 1) == 2.3

    def test_sharpe_not_found(self):
        assert get_catalog_sharpe({1: {"best_sharpe": 1.0}}, 99) is None

    def test_sharpe_none_catalog(self):
        assert get_catalog_sharpe(None, 1) is None

    def test_bt_count_found(self):
        catalog = {1: {"backtest_count": 5}}
        assert get_catalog_bt_count(catalog, 1) == 5

    def test_bt_count_not_found(self):
        assert get_catalog_bt_count({}, 99) is None


# --- get_org_name ---

class TestGetOrgName:
    def test_personal(self):
        assert get_org_name("d600793efghi") == "Personal"

    def test_esgf(self):
        assert get_org_name("94aa4bcb1234") == "ESGF"

    def test_unknown(self):
        result = get_org_name("abcdef01")
        assert "Unknown" in result


# --- classify_project ---

class TestClassifyProject:
    def _classify(self, name="TestProject", pid=1, all_projects=None, catalog=None, **kwargs):
        proj = _project(name=name, pid=pid, **kwargs)
        all_projs = all_projects or [proj]
        return classify_project(proj, all_projs, catalog)

    def test_test_validation_pattern(self):
        cat, reason = self._classify(name="Alpha-Validation")
        assert cat == "TEST"
        assert "test" in reason.lower()

    def test_test_staging_pattern(self):
        cat, _ = self._classify(name="MyProject-Staging")
        assert cat == "TEST"

    def test_test_sandbox_pattern(self):
        cat, _ = self._classify(name="Experiment-Sandbox")
        assert cat == "TEST"

    def test_esgf_validation(self):
        cat, reason = self._classify(name="ESGF-2026-Validation")
        assert cat == "TEST"
        # Matches generic "-Validation" pattern before ESGF-specific check
        assert "validation" in reason.lower()

    def test_superseded_risk_parity(self):
        p1 = _project(name="RiskParity", pid=1)
        p2 = _project(name="RiskParity-v2", pid=2)
        cat, reason = classify_project(p1, [p1, p2], None)
        assert cat == "SUPERSEDED"
        assert "RiskParity-v2" in reason

    def test_researcher_superseded_by_framework(self):
        p1 = _project(name="Alpha-Researcher", pid=1)
        p2 = _project(name="Framework_Alpha", pid=2)
        cat, reason = classify_project(p1, [p1, p2], None)
        assert cat == "SUPERSEDED"
        assert "Framework" in reason

    def test_researcher_active_with_backtests(self):
        catalog = {1: {"best_sharpe": 1.5, "backtest_count": 3}}
        p1 = _project(name="Alpha-Researcher", pid=1)
        cat, reason = classify_project(p1, [p1], catalog)
        assert cat == "ALIVE"
        assert "Sharpe" in reason

    def test_alive_by_sharpe(self):
        catalog = {1: {"best_sharpe": 2.0, "backtest_count": 5}}
        cat, reason = self._classify(pid=1, catalog=catalog)
        assert cat == "ALIVE"
        assert "Sharpe" in reason

    def test_alive_negative_sharpe(self):
        catalog = {1: {"best_sharpe": -0.3, "backtest_count": 3}}
        cat, reason = self._classify(pid=1, catalog=catalog)
        assert cat == "ALIVE"
        assert "Negative" in reason

    def test_dead_no_backtests(self):
        catalog = {1: {"best_sharpe": None, "backtest_count": 0}}
        cat, reason = self._classify(name="RandomProject", pid=1, catalog=catalog)
        assert cat == "DEAD"
        assert "No backtests" in reason

    def test_dead_very_negative_sharpe(self):
        catalog = {1: {"best_sharpe": -5.0, "backtest_count": 2}}
        cat, reason = self._classify(name="BrokenProject", pid=1, catalog=catalog)
        assert cat == "DEAD"
        assert "broken" in reason.lower()

    def test_alive_many_bts_very_negative(self):
        catalog = {1: {"best_sharpe": -5.0, "backtest_count": 10}}
        cat, reason = self._classify(pid=1, catalog=catalog)
        assert cat == "ALIVE"
        assert "structural" in reason.lower()

    def test_alive_by_naming_convention(self):
        cat, reason = self._classify(name="Alpha-MyStrategy")
        assert cat == "ALIVE"
        assert "naming" in reason.lower()

    def test_alive_framework_no_backtests(self):
        catalog = {1: {"backtest_count": 0}}
        cat, _ = self._classify(name="Framework_ML", pid=1, catalog=catalog)
        assert cat == "ALIVE"

    def test_alive_fresh_project(self):
        catalog = {1: {"backtest_count": 0}}
        cat, _ = self._classify(
            name="NewProject", pid=1, catalog=catalog,
            created="2026-05-03T00:00:00Z"
        )
        assert cat == "ALIVE"

    def test_alive_backtests_no_sharpe(self):
        catalog = {1: {"best_sharpe": None, "backtest_count": 3}}
        cat, reason = self._classify(pid=1, catalog=catalog)
        assert cat == "ALIVE"
        assert "unavailable" in reason

    def test_dead_stale(self):
        cat, reason = self._classify(name="OldProject", modified="2025-01-01T00:00:00Z")
        assert cat == "DEAD"
        assert "Stale" in reason

    def test_dead_no_activity(self):
        cat, reason = self._classify(name="UnknownProject", modified="")
        assert cat == "DEAD"


# --- generate_report ---

class TestGenerateReport:
    def test_empty_report(self):
        report = generate_report([])
        assert "QuantConnect" in report
        assert "ALIVE" in report
        assert "DEAD" in report

    def test_report_with_projects(self):
        projects = [
            _project(name="Alpha-Strategy", pid=1),
            _project(name="Dead-Project", pid=2, modified="2025-01-01T00:00:00Z"),
        ]
        report = generate_report(projects)
        assert "Alpha-Strategy" in report
        assert "Dead-Project" in report
        assert "Summary" in report

    def test_report_categories_in_table(self):
        projects = [_project(name="Alpha-Strategy", pid=1)]
        report = generate_report(projects)
        assert "| ALIVE |" in report
        assert "| DEAD |" in report

    def test_report_deletion_candidates(self):
        projects = [
            _project(name="DeadProject", pid=1, modified="2025-01-01T00:00:00Z"),
        ]
        report = generate_report(projects)
        assert "Deletion Candidates" in report


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
