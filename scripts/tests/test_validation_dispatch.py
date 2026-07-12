"""Tests for scripts/validation/dispatch.py — pure functions.

Tests cover:
- _worst_severity: severity ranking from issue list
- _classify_maturity: maturity classification from struct + issues
- build_aggregate: cross-family summary aggregation

These are pure functions with no I/O, safe to test without fixtures.
"""

import sys
from dataclasses import dataclass
from pathlib import Path

import pytest

# Add scripts parent to path so we can import dispatch
DISPATCH_DIR = Path(__file__).resolve().parent.parent / "validation"
sys.path.insert(0, str(DISPATCH_DIR))

from dispatch import _worst_severity, _classify_maturity, build_aggregate


# --- Helpers ---

@dataclass
class FakeValidationIssue:
    """Minimal ValidationIssue-compatible object for testing."""
    issue_type: str
    category: str = "test"
    cell_index: int = 0
    message: str = ""


@dataclass
class FakeStruct:
    """Minimal struct compatible with _classify_maturity's attribute access."""
    has_cells: bool = True
    code_cells: int = 0
    valid_json: bool = True
    cells_with_output: int = 0
    cells_with_errors: int = 0
    markdown_cells: int = 0


def _make_struct(
    code_cells: int = 3,
    cells_with_output: int = 3,
    cells_with_errors: int = 0,
    markdown_cells: int = 2,
    has_cells: bool = True,
    valid_json: bool = True,
) -> FakeStruct:
    return FakeStruct(
        has_cells=has_cells,
        code_cells=code_cells,
        valid_json=valid_json,
        cells_with_output=cells_with_output,
        cells_with_errors=cells_with_errors,
        markdown_cells=markdown_cells,
    )


# =============================================================================
# _worst_severity
# =============================================================================

class TestWorstSeverity:
    """Tests for _worst_severity(issues) -> 'error' | 'warning' | 'ok'."""

    def test_empty_list_returns_ok(self):
        assert _worst_severity([]) == "ok"

    def test_single_error_returns_error(self):
        issues = [FakeValidationIssue(issue_type="error")]
        assert _worst_severity(issues) == "error"

    def test_single_warning_returns_warning(self):
        issues = [FakeValidationIssue(issue_type="warning")]
        assert _worst_severity(issues) == "warning"

    def test_single_info_returns_ok(self):
        issues = [FakeValidationIssue(issue_type="info")]
        assert _worst_severity(issues) == "ok"

    def test_error_takes_priority_over_warning(self):
        issues = [
            FakeValidationIssue(issue_type="warning"),
            FakeValidationIssue(issue_type="error"),
        ]
        assert _worst_severity(issues) == "error"

    def test_error_takes_priority_over_info(self):
        issues = [
            FakeValidationIssue(issue_type="info"),
            FakeValidationIssue(issue_type="error"),
        ]
        assert _worst_severity(issues) == "error"

    def test_multiple_warnings_returns_warning(self):
        issues = [
            FakeValidationIssue(issue_type="warning"),
            FakeValidationIssue(issue_type="warning"),
        ]
        assert _worst_severity(issues) == "warning"

    def test_multiple_infos_returns_ok(self):
        issues = [
            FakeValidationIssue(issue_type="info"),
            FakeValidationIssue(issue_type="info"),
        ]
        assert _worst_severity(issues) == "ok"

    def test_error_warning_info_mixed_returns_error(self):
        issues = [
            FakeValidationIssue(issue_type="info"),
            FakeValidationIssue(issue_type="warning"),
            FakeValidationIssue(issue_type="error"),
        ]
        assert _worst_severity(issues) == "error"

    def test_warning_before_info_in_order(self):
        """Warning appears first in iteration — should return warning."""
        issues = [
            FakeValidationIssue(issue_type="warning"),
            FakeValidationIssue(issue_type="info"),
        ]
        assert _worst_severity(issues) == "warning"


# =============================================================================
# _classify_maturity
# =============================================================================

class TestClassifyMaturity:
    """Tests for _classify_maturity(struct, issues) -> str."""

    # --- DRAFT cases ---

    def test_no_cells_returns_draft(self):
        struct = _make_struct(code_cells=0, has_cells=False, cells_with_output=0)
        assert _classify_maturity(struct, []) == "DRAFT"

    def test_code_cells_zero_returns_draft(self):
        """has_cells=True but code_cells=0 → DRAFT."""
        struct = _make_struct(code_cells=0, has_cells=True, cells_with_output=0)
        assert _classify_maturity(struct, []) == "DRAFT"

    def test_invalid_json_returns_draft(self):
        struct = _make_struct(valid_json=False)
        assert _classify_maturity(struct, []) == "DRAFT"

    def test_no_outputs_returns_draft(self):
        """Code cells exist but zero outputs → DRAFT."""
        struct = _make_struct(code_cells=3, cells_with_output=0)
        assert _classify_maturity(struct, []) == "DRAFT"

    def test_outputs_but_no_markdown_returns_draft(self):
        """All code has outputs, zero markdown cells → DRAFT."""
        struct = _make_struct(code_cells=3, cells_with_output=3, markdown_cells=0)
        assert _classify_maturity(struct, []) == "DRAFT"

    # --- ALPHA cases ---

    def test_partial_outputs_returns_alpha(self):
        """Some but not all code cells have outputs → ALPHA."""
        struct = _make_struct(code_cells=3, cells_with_output=2, markdown_cells=1)
        assert _classify_maturity(struct, []) == "ALPHA"

    def test_all_outputs_but_errors_returns_alpha(self):
        """All code has outputs + markdown, but errors present → ALPHA."""
        struct = _make_struct(
            code_cells=3, cells_with_output=3, cells_with_errors=1, markdown_cells=2
        )
        assert _classify_maturity(struct, []) == "ALPHA"

    def test_one_output_of_three_returns_alpha(self):
        struct = _make_struct(code_cells=3, cells_with_output=1, markdown_cells=1)
        assert _classify_maturity(struct, []) == "ALPHA"

    # --- BETA cases ---

    def test_all_outputs_markdown_many_issues_returns_beta(self):
        """All outputs + markdown + >2 issues → BETA."""
        struct = _make_struct(code_cells=3, cells_with_output=3, markdown_cells=2)
        issues = [FakeValidationIssue(issue_type="warning") for _ in range(3)]
        assert _classify_maturity(struct, issues) == "BETA"

    def test_all_outputs_markdown_3_issues_returns_beta(self):
        """Exactly 3 issues → BETA (threshold is <=2 for PRODUCTION)."""
        struct = _make_struct(code_cells=3, cells_with_output=3, markdown_cells=2)
        issues = [FakeValidationIssue(issue_type="info") for _ in range(3)]
        assert _classify_maturity(struct, issues) == "BETA"

    def test_all_outputs_markdown_10_issues_returns_beta(self):
        struct = _make_struct(code_cells=3, cells_with_output=3, markdown_cells=2)
        issues = [FakeValidationIssue(issue_type="info") for _ in range(10)]
        assert _classify_maturity(struct, issues) == "BETA"

    # --- PRODUCTION cases ---

    def test_all_outputs_markdown_zero_issues_returns_production(self):
        struct = _make_struct(code_cells=3, cells_with_output=3, markdown_cells=2)
        assert _classify_maturity(struct, []) == "PRODUCTION"

    def test_all_outputs_markdown_one_issue_returns_production(self):
        struct = _make_struct(code_cells=3, cells_with_output=3, markdown_cells=2)
        issues = [FakeValidationIssue(issue_type="warning")]
        assert _classify_maturity(struct, issues) == "PRODUCTION"

    def test_all_outputs_markdown_two_issues_returns_production(self):
        """Exactly 2 issues → still PRODUCTION (boundary)."""
        struct = _make_struct(code_cells=3, cells_with_output=3, markdown_cells=2)
        issues = [FakeValidationIssue(issue_type="info"), FakeValidationIssue(issue_type="info")]
        assert _classify_maturity(struct, issues) == "PRODUCTION"

    # --- Edge cases ---

    def test_single_code_cell_with_output_and_md_is_production(self):
        struct = _make_struct(code_cells=1, cells_with_output=1, markdown_cells=1)
        assert _classify_maturity(struct, []) == "PRODUCTION"

    def test_all_outputs_errors_and_markdown_is_alpha_not_beta(self):
        """Errors take priority over issue count → ALPHA."""
        struct = _make_struct(
            code_cells=3, cells_with_output=3, cells_with_errors=2, markdown_cells=2
        )
        assert _classify_maturity(struct, []) == "ALPHA"

    def test_markdown_one_cell_minimum(self):
        """1 markdown cell is enough (has_md check uses >0)."""
        struct = _make_struct(code_cells=2, cells_with_output=2, markdown_cells=1)
        assert _classify_maturity(struct, []) == "PRODUCTION"


# =============================================================================
# build_aggregate
# =============================================================================

class TestBuildAggregate:
    """Tests for build_aggregate(all_results) -> dict."""

    def _make_result(
        self,
        total: int = 10,
        pass_count: int = 7,
        warn: int = 2,
        fail: int = 1,
        production: int = 5,
        beta: int = 3,
        alpha: int = 1,
        draft: int = 1,
        broken: list | None = None,
        duration: float = 5.0,
    ) -> dict:
        return {
            "name": "TestFamily",
            "total": total,
            "pass": pass_count,
            "warn": warn,
            "fail": fail,
            "skip": 0,
            "broken": broken or [],
            "maturity": {
                "PRODUCTION": production,
                "BETA": beta,
                "ALPHA": alpha,
                "DRAFT": draft,
            },
            "status": {"READY": 0, "DEMO": 0, "RESEARCH": 0, "BROKEN": 0},
            "duration_s": duration,
        }

    def test_empty_list_returns_zeros(self):
        result = build_aggregate([])
        assert result["n_families"] == 0
        assert result["totals"]["total"] == 0
        assert result["totals"]["pass"] == 0
        assert result["totals"]["pass_rate"] == 0.0
        assert result["n_broken"] == 0
        assert result["total_duration_s"] == 0.0

    def test_single_family(self):
        r = self._make_result(total=10, pass_count=8, warn=1, fail=1)
        result = build_aggregate([r])
        assert result["n_families"] == 1
        assert result["totals"]["total"] == 10
        assert result["totals"]["pass"] == 8
        assert result["totals"]["warn"] == 1
        assert result["totals"]["fail"] == 1
        assert result["totals"]["pass_rate"] == 80.0

    def test_multiple_families_sum(self):
        r1 = self._make_result(total=10, pass_count=8, warn=1, fail=1, production=5, beta=3, alpha=1, draft=1)
        r2 = self._make_result(total=5, pass_count=3, warn=1, fail=1, production=2, beta=1, alpha=1, draft=1)
        result = build_aggregate([r1, r2])
        assert result["n_families"] == 2
        assert result["totals"]["total"] == 15
        assert result["totals"]["pass"] == 11
        assert result["totals"]["pass_rate"] == pytest.approx(73.3, abs=0.1)

    def test_maturity_aggregation(self):
        r1 = self._make_result(production=5, beta=3, alpha=1, draft=1)
        r2 = self._make_result(production=2, beta=1, alpha=1, draft=1)
        result = build_aggregate([r1, r2])
        assert result["maturity"]["PRODUCTION"] == 7
        assert result["maturity"]["BETA"] == 4
        assert result["maturity"]["ALPHA"] == 2
        assert result["maturity"]["DRAFT"] == 2

    def test_broken_flattened(self):
        r1 = self._make_result(broken=[{"path": "a.ipynb", "reason": "err"}])
        r2 = self._make_result(broken=[
            {"path": "b.ipynb", "reason": "err1"},
            {"path": "c.ipynb", "reason": "err2"},
        ])
        result = build_aggregate([r1, r2])
        assert result["n_broken"] == 3
        assert len(result["broken"]) == 3
        paths = [b["path"] for b in result["broken"]]
        assert "a.ipynb" in paths
        assert "b.ipynb" in paths
        assert "c.ipynb" in paths

    def test_pass_rate_calculation(self):
        r = self._make_result(total=20, pass_count=15, warn=3, fail=2)
        result = build_aggregate([r])
        assert result["totals"]["pass_rate"] == 75.0

    def test_pass_rate_rounded_to_one_decimal(self):
        r = self._make_result(total=7, pass_count=3, warn=2, fail=2)
        result = build_aggregate([r])
        assert result["totals"]["pass_rate"] == pytest.approx(42.9, abs=0.1)

    def test_total_duration_summed(self):
        r1 = self._make_result(duration=3.2)
        r2 = self._make_result(duration=4.8)
        result = build_aggregate([r1, r2])
        assert result["total_duration_s"] == 8.0

    def test_missing_maturity_keys_tolerated(self):
        """Family result missing some maturity keys should default to 0."""
        r = self._make_result()
        r["maturity"] = {"PRODUCTION": 5}  # Missing BETA, ALPHA, DRAFT
        result = build_aggregate([r])
        assert result["maturity"]["PRODUCTION"] == 5
        assert result["maturity"]["BETA"] == 0
        assert result["maturity"]["ALPHA"] == 0
        assert result["maturity"]["DRAFT"] == 0

    def test_no_broken_entries(self):
        r = self._make_result(broken=[])
        result = build_aggregate([r])
        assert result["n_broken"] == 0
        assert result["broken"] == []

    def test_zero_total_gives_zero_pass_rate(self):
        """Edge case: family with total=0."""
        r = self._make_result(total=0, pass_count=0, warn=0, fail=0)
        result = build_aggregate([r])
        assert result["totals"]["pass_rate"] == 0.0

    def test_all_pass_gives_100_rate(self):
        r = self._make_result(total=10, pass_count=10, warn=0, fail=0)
        result = build_aggregate([r])
        assert result["totals"]["pass_rate"] == 100.0

    def test_duration_rounded_to_one_decimal(self):
        r1 = self._make_result(duration=3.14159)
        r2 = self._make_result(duration=2.71828)
        result = build_aggregate([r1, r2])
        assert result["total_duration_s"] == 5.9
