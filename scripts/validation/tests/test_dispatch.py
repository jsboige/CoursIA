"""Tests for scripts/validation/dispatch.py — per-family validation dispatcher.

Covers the pure / composable helpers that the family-validation pipeline builds
on:
- ``_worst_severity``: worst-of(error, warning, ok) from issue list
- ``_classify_maturity``: DRAFT/ALPHA/BETA/PRODUCTION maturity verdict from a
  notebook structure snapshot + issue list
- ``build_aggregate``: cross-family totals + maturity rollup + pass rate
- ``_extract_error_names``: error ename extraction from a notebook's outputs

``_classify_maturity`` / ``_worst_severity`` consume duck-typed objects
(``struct`` with ``has_cells``/``code_cells``/``valid_json``/``markdown_cells``
/``cells_with_output``/``cells_with_errors``; ``issue`` with ``issue_type``).
We use ``types.SimpleNamespace`` stand-ins rather than importing the concrete
notebook_tools types, so the tests stay hermetic to that module's evolution.

Synthetic notebooks under ``tmp_path`` for ``_extract_error_names``; no real
families executed, no Papermill, no kernel.
"""

import json
import sys
from pathlib import Path
from types import SimpleNamespace

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import dispatch  # noqa: E402


# ---------------------------------------------------------------------------
# helpers
# ---------------------------------------------------------------------------

def _issue(itype: str):
    return SimpleNamespace(issue_type=itype)


def _struct(*, has_cells=True, code_cells=2, valid_json=True,
            markdown_cells=1, cells_with_output=2, cells_with_errors=0):
    return SimpleNamespace(
        has_cells=has_cells, code_cells=code_cells, valid_json=valid_json,
        markdown_cells=markdown_cells, cells_with_output=cells_with_output,
        cells_with_errors=cells_with_errors,
    )


def _nb(path: Path, cells):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps({"cells": cells, "metadata": {},
                                "nbformat": 4, "nbformat_minor": 5}),
                    encoding="utf-8")


def _err(ename="RuntimeError"):
    return {"output_type": "error", "ename": ename, "evalue": "x",
            "traceback": []}


# ---------------------------------------------------------------------------
# _worst_severity
# ---------------------------------------------------------------------------

class TestWorstSeverity:
    def test_empty_is_ok(self):
        assert dispatch._worst_severity([]) == "ok"

    def test_only_warnings(self):
        assert dispatch._worst_severity([_issue("warning"), _issue("warning")]) == "warning"

    def test_error_beats_warning(self):
        assert dispatch._worst_severity([_issue("warning"), _issue("error")]) == "error"

    def test_error_alone(self):
        assert dispatch._worst_severity([_issue("error")]) == "error"

    def test_only_ok(self):
        assert dispatch._worst_severity([_issue("ok")]) == "ok"

    def test_mixed_error_dominates(self):
        assert dispatch._worst_severity([_issue("ok"), _issue("warning"),
                                         _issue("error")]) == "error"


# ---------------------------------------------------------------------------
# _classify_maturity
# ---------------------------------------------------------------------------

class TestClassifyMaturity:
    def test_no_cells_is_draft(self):
        assert dispatch._classify_maturity(
            _struct(has_cells=False, code_cells=0), []) == "DRAFT"

    def test_zero_code_cells_is_draft(self):
        assert dispatch._classify_maturity(
            _struct(has_cells=True, code_cells=0), []) == "DRAFT"

    def test_invalid_json_is_draft(self):
        assert dispatch._classify_maturity(
            _struct(valid_json=False), []) == "DRAFT"

    def test_no_outputs_is_draft(self):
        assert dispatch._classify_maturity(
            _struct(cells_with_output=0), []) == "DRAFT"

    def test_partial_outputs_is_alpha(self):
        # 2 code cells but only 1 has output.
        assert dispatch._classify_maturity(
            _struct(code_cells=2, cells_with_output=1), []) == "ALPHA"

    def test_outputs_but_no_markdown_is_draft(self):
        assert dispatch._classify_maturity(
            _struct(markdown_cells=0), []) == "DRAFT"

    def test_outputs_with_errors_is_alpha(self):
        assert dispatch._classify_maturity(
            _struct(cells_with_errors=1), []) == "ALPHA"

    def test_production_when_clean_full_outputs_and_few_issues(self):
        assert dispatch._classify_maturity(
            _struct(), [_issue("ok"), _issue("ok")]) == "PRODUCTION"

    def test_production_threshold_exactly_two_issues(self):
        # <= 2 issues stays PRODUCTION (with full outputs + markdown + clean).
        assert dispatch._classify_maturity(
            _struct(), [_issue("warning"), _issue("warning")]) == "PRODUCTION"

    def test_beta_when_more_than_two_issues(self):
        assert dispatch._classify_maturity(
            _struct(), [_issue("warning")] * 3) == "BETA"

    def test_outputs_all_but_zero_code_cells_is_draft(self):
        # all_outputs requires code_cells > 0; the guard short-circuits to DRAFT.
        assert dispatch._classify_maturity(
            _struct(code_cells=0, cells_with_output=0,
                    markdown_cells=0), []) == "DRAFT"


# ---------------------------------------------------------------------------
# build_aggregate
# ---------------------------------------------------------------------------

class TestBuildAggregate:
    def _r(self, total=0, passed=0, warn=0, fail=0, **kw):
        # `pass` is a Python keyword -> accept `passed` and map to the "pass" key.
        base = {"total": total, "pass": passed, "warn": warn, "fail": fail,
                "maturity": {"PRODUCTION": 0, "BETA": 0, "ALPHA": 0, "DRAFT": 0},
                "broken": [], "duration_s": 0.0}
        base.update(kw)
        return base

    def test_empty_results(self):
        agg = dispatch.build_aggregate([])
        assert agg["n_families"] == 0
        assert agg["totals"] == {"total": 0, "pass": 0, "warn": 0, "fail": 0,
                                 "pass_rate": 0.0}
        assert agg["n_broken"] == 0

    def test_totals_summed(self):
        agg = dispatch.build_aggregate([
            self._r(total=10, passed=8, warn=1, fail=1),
            self._r(total=5, passed=3, warn=2, fail=0),
        ])
        assert agg["totals"]["total"] == 15
        assert agg["totals"]["pass"] == 11
        assert agg["totals"]["warn"] == 3
        assert agg["totals"]["fail"] == 1

    def test_pass_rate_rounded(self):
        agg = dispatch.build_aggregate([
            self._r(total=3, passed=2),
        ])
        assert agg["totals"]["pass_rate"] == 66.7

    def test_pass_rate_zero_total(self):
        agg = dispatch.build_aggregate([self._r(total=0)])
        assert agg["totals"]["pass_rate"] == 0.0

    def test_maturity_rollup(self):
        agg = dispatch.build_aggregate([
            self._r(maturity={"PRODUCTION": 3, "BETA": 1, "ALPHA": 0, "DRAFT": 0}),
            self._r(maturity={"PRODUCTION": 1, "BETA": 0, "ALPHA": 2, "DRAFT": 1}),
        ])
        assert agg["maturity"] == {"PRODUCTION": 4, "BETA": 1, "ALPHA": 2, "DRAFT": 1}

    def test_broken_collected(self):
        agg = dispatch.build_aggregate([
            self._r(broken=["a.ipynb"]),
            self._r(broken=["b.ipynb", "c.ipynb"]),
        ])
        assert agg["n_broken"] == 3
        assert sorted(agg["broken"]) == ["a.ipynb", "b.ipynb", "c.ipynb"]

    def test_duration_summed_rounded(self):
        agg = dispatch.build_aggregate([
            self._r(duration_s=12.34), self._r(duration_s=7.66),
        ])
        assert agg["total_duration_s"] == 20.0

    def test_n_families(self):
        agg = dispatch.build_aggregate([self._r(), self._r(), self._r()])
        assert agg["n_families"] == 3


# ---------------------------------------------------------------------------
# _extract_error_names
# ---------------------------------------------------------------------------

class TestExtractErrorNames:
    def test_unparsable_file_returns_parseerror(self, tmp_path):
        p = tmp_path / "x.ipynb"
        p.write_text("{not valid json", encoding="utf-8")
        assert dispatch._extract_error_names(p) == ["ParseError"]

    def test_missing_file_returns_parseerror(self, tmp_path):
        # open() raises -> caught -> ["ParseError"]
        assert dispatch._extract_error_names(tmp_path / "nope.ipynb") == ["ParseError"]

    def test_no_errors_returns_unknown(self):
        # No error outputs at all -> ["Unknown"] sentinel (not empty).
        import tempfile
        with tempfile.NamedTemporaryFile("w", suffix=".ipynb", delete=False,
                                         encoding="utf-8") as f:
            json.dump({"cells": [{"cell_type": "code", "outputs": []}]}, f)
            p = Path(f.name)
        try:
            assert dispatch._extract_error_names(p) == ["Unknown"]
        finally:
            p.unlink()

    def test_collects_error_enames(self, tmp_path):
        p = tmp_path / "nb.ipynb"
        _nb(p, [
            {"cell_type": "code", "outputs": [_err("ZeroDivisionError")]},
            {"cell_type": "code", "outputs": [_err("KeyError")]},
        ])
        assert dispatch._extract_error_names(p) == ["ZeroDivisionError", "KeyError"]

    def test_error_without_ename_uses_unknown(self, tmp_path):
        p = tmp_path / "nb.ipynb"
        _nb(p, [{"cell_type": "code",
                 "outputs": [{"output_type": "error"}]}])
        assert dispatch._extract_error_names(p) == ["Unknown"]

    def test_non_error_outputs_ignored(self, tmp_path):
        p = tmp_path / "nb.ipynb"
        _nb(p, [{"cell_type": "code", "outputs": [
            {"output_type": "stream", "name": "stdout", "text": "ok"},
            _err("ValueError"),
        ]}])
        assert dispatch._extract_error_names(p) == ["ValueError"]
