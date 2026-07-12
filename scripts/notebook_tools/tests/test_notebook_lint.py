"""Tests for scripts/notebook_tools/notebook_lint.py — unified notebook validator.

Tests focus on pure functions: scan_c1_source, _is_in_docstring,
check_c1, check_c2, check_structure, check_metadata, lint_notebook.
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from notebook_lint import (
    C1_PATTERNS,
    check_c1,
    check_c2,
    check_metadata,
    check_structure,
    lint_notebook,
    scan_c1_source,
    _is_in_docstring,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _nb(cells: list[dict], metadata: dict | None = None) -> dict:
    """Build a minimal notebook dict."""
    nb = {"cells": cells, "metadata": metadata or {}}
    return nb


def _code(source: str, exec_count: int | None = None, outputs: list | None = None) -> dict:
    return {
        "cell_type": "code",
        "source": [source],
        "execution_count": exec_count,
        "outputs": outputs or [],
    }


def _md(source: str) -> dict:
    return {"cell_type": "markdown", "source": [source]}


def _write_nb(path: Path, cells: list[dict], metadata: dict | None = None) -> Path:
    """Write a minimal .ipynb file."""
    path.parent.mkdir(parents=True, exist_ok=True)
    nb = {"cells": cells, "metadata": metadata or {}, "nbformat": 4, "nbformat_minor": 5}
    path.write_text(json.dumps(nb), encoding="utf-8")
    return path


# ---------------------------------------------------------------------------
# _is_in_docstring
# ---------------------------------------------------------------------------

class TestIsInDocstring:
    def test_not_in_docstring(self):
        in_doc, is_inside = _is_in_docstring("x = 1", False)
        assert in_doc is False
        assert is_inside is False

    def test_entering_docstring(self):
        in_doc, is_inside = _is_in_docstring('"""doc text', False)
        assert in_doc is True
        assert is_inside is True

    def test_exiting_docstring(self):
        in_doc, is_inside = _is_in_docstring('end of doc"""', True)
        assert in_doc is False
        assert is_inside is True

    def test_still_inside_docstring(self):
        in_doc, is_inside = _is_in_docstring("some doc text", True)
        assert in_doc is True
        assert is_inside is True

    def test_single_quotes_docstring(self):
        in_doc, is_inside = _is_in_docstring("'''doc text", False)
        assert in_doc is True
        assert is_inside is True

    def test_complete_docstring_line(self):
        """Complete docstring on one line: 2 triple-quotes = even, no toggle, but toggled check."""
        in_doc, is_inside = _is_in_docstring('"""complete doc"""', False)
        assert in_doc is False
        # 2 triple-quotes = even count, no net toggle → was_in_doc == in_doc → toggled=False
        # is_inside = was_in_doc or toggled = False or False = False
        assert is_inside is False

    def test_triple_quotes_in_string(self):
        """Triple quotes inside a string: even count = no toggle, not inside."""
        in_doc, is_inside = _is_in_docstring('x = """not a doc"""', False)
        # 2 triple-quotes = even, no net toggle → is_inside = False
        assert in_doc is False
        assert is_inside is False


# ---------------------------------------------------------------------------
# scan_c1_source
# ---------------------------------------------------------------------------

class TestScanC1Source:
    def test_raise_not_implemented_error(self):
        hits = scan_c1_source("raise NotImplementedError('TODO')")
        assert len(hits) == 1
        assert hits[0][1] == "raise NotImplementedError"

    def test_assert_false(self):
        hits = scan_c1_source("assert False, 'should not reach'")
        assert len(hits) == 1
        assert hits[0][1] == "assert False"

    def test_division_by_zero(self):
        hits = scan_c1_source("x = 1/0")
        assert len(hits) == 1
        assert hits[0][1] == "1/0"

    def test_clean_code_no_hits(self):
        hits = scan_c1_source("x = 1\ny = 2\nprint(x + y)")
        assert hits == []

    def test_commented_out_not_flagged(self):
        hits = scan_c1_source("# raise NotImplementedError('TODO')")
        assert hits == []

    def test_inline_comment_stripped(self):
        hits = scan_c1_source("pass  # raise NotImplementedError")
        assert hits == []

    def test_csharp_line_comment_not_flagged(self):
        """C-family '//' comment mentioning a banned pattern is not code (#5261).

        A .net-csharp stub whose comment reads
        '// stub : pas de raise NotImplementedError' must not false-flag C.1.
        """
        hits = scan_c1_source("// Cellule stub : pas de raise NotImplementedError")
        assert hits == []

    def test_csharp_inline_comment_stripped(self):
        hits = scan_c1_source('Console.WriteLine("ok");  // raise NotImplementedError')
        assert hits == []

    def test_csharp_executable_division_still_flagged(self):
        """Executable C# 'int x = 1/0;' sits before any '//' and is still caught."""
        hits = scan_c1_source("int x = 1/0;  // divide by zero")
        assert len(hits) == 1
        assert hits[0][1] == "1/0"

    def test_date_not_flagged(self):
        """Date 21/02/2022 should not be flagged as 1/0."""
        hits = scan_c1_source("date = '21/02/2022'")
        assert hits == []

    def test_fraction_not_flagged(self):
        """10/0 should not be flagged (digit before 1/0)."""
        hits = scan_c1_source("ratio = 10/0.5")
        assert hits == []

    def test_fraction_21_not_flagged(self):
        """21/0 should not be flagged (digit before 1/0)."""
        hits = scan_c1_source("val = 21/0")
        assert hits == []

    def test_in_docstring_not_flagged(self):
        source = '"""\nraise NotImplementedError("example")\n"""'
        hits = scan_c1_source(source)
        assert hits == []

    def test_multiple_violations(self):
        source = "raise NotImplementedError('a')\nassert False\nx = 1/0"
        hits = scan_c1_source(source)
        assert len(hits) == 3

    def test_pass_not_flagged(self):
        hits = scan_c1_source("pass")
        assert hits == []

    def test_return_none_not_flagged(self):
        hits = scan_c1_source("return None  # TODO etudiant")
        assert hits == []

    def test_raise_value_error_not_flagged(self):
        """Only NotImplementedError is flagged, not other exceptions."""
        hits = scan_c1_source("raise ValueError('bad input')")
        assert hits == []

    def test_csharp_throw_not_implemented_flagged(self):
        """C# `throw new NotImplementedException()` is the idiomatic stub and
        the C# equivalent of Python's raise NotImplementedError (#C1, .NET).
        Found via a Tweety-10 investigation (c.334): the shared detector was
        Python-pattern-only, so .NET stubs could violate C.1 undetected.
        """
        hits = scan_c1_source("throw new NotImplementedException();")
        assert len(hits) == 1
        assert "NotImplementedException" in hits[0][1]

    def test_csharp_throw_system_qualified_flagged(self):
        """Fully-qualified `throw new System.NotImplementedException()` flagged."""
        hits = scan_c1_source("throw new System.NotImplementedException();")
        assert len(hits) == 1

    def test_csharp_not_supported_not_flagged(self):
        """NotSupportedException is a DIFFERENT, legitimate exception (read-only
        collections, unsupported operations) — must NOT be flagged."""
        hits = scan_c1_source("throw new NotSupportedException();")
        assert hits == []

    def test_csharp_catch_not_implemented_not_flagged(self):
        """Handling a NotImplementedException (catch) is NOT a stub — the throw
        form is required to flag."""
        hits = scan_c1_source("catch (NotImplementedException ex) { }")
        assert hits == []

    def test_csharp_throw_not_implemented_in_comment_not_flagged(self):
        """Commented-out C# throw is not executable (#5261 comment-awareness)."""
        hits = scan_c1_source("// throw new NotImplementedException();")
        assert hits == []


# ---------------------------------------------------------------------------
# check_c1
# ---------------------------------------------------------------------------

class TestCheckC1:
    def test_clean_notebook(self):
        nb = _nb([_code("x = 1"), _code("pass")])
        assert check_c1(nb) == []

    def test_violation_in_code_cell(self):
        nb = _nb([_code("raise NotImplementedError('TODO')")])
        violations = check_c1(nb)
        assert len(violations) == 1
        assert violations[0]["check"] == "C1"
        assert violations[0]["cell_index"] == 0

    def test_markdown_cells_ignored(self):
        nb = _nb([_md("raise NotImplementedError is forbidden")])
        assert check_c1(nb) == []

    def test_multiple_cells_multiple_violations(self):
        nb = _nb([
            _code("raise NotImplementedError('a')"),
            _code("x = 1"),
            _code("assert False"),
        ])
        violations = check_c1(nb)
        assert len(violations) == 2
        assert violations[0]["cell_index"] == 0
        assert violations[1]["cell_index"] == 2

    def test_empty_cells_list(self):
        nb = _nb([])
        assert check_c1(nb) == []

    def test_cell_index_correct(self):
        nb = _nb([
            _md("# Title"),
            _code("x = 1"),
            _code("raise NotImplementedError"),
        ])
        violations = check_c1(nb)
        assert violations[0]["cell_index"] == 2


# ---------------------------------------------------------------------------
# check_c2
# ---------------------------------------------------------------------------

class TestCheckC2:
    def test_all_executed(self):
        nb = _nb([_code("x = 1", exec_count=1)])
        assert check_c2(nb) == []

    def test_missing_execution_count(self):
        nb = _nb([_code("x = 1")])
        violations = check_c2(nb)
        assert len(violations) == 1
        assert violations[0]["check"] == "C2"
        assert violations[0]["reason"] == "missing execution_count"

    def test_empty_source_skipped(self):
        nb = _nb([_code("")])
        assert check_c2(nb) == []

    def test_comment_only_skipped(self):
        nb = _nb([_code("# just a comment")])
        assert check_c2(nb) == []

    def test_qc_reference_skipped(self):
        nb = _nb([_code("[REFERENCE QC] some code")])
        assert check_c2(nb) == []

    def test_markdown_cells_ignored(self):
        nb = _nb([_md("# Title")])
        assert check_c2(nb) == []

    def test_exec_count_zero_counts_as_executed(self):
        nb = _nb([_code("x = 1", exec_count=0)])
        assert check_c2(nb) == []

    def test_source_preview_in_violation(self):
        nb = _nb([_code("x = 1 + 2 + 3")])
        violations = check_c2(nb)
        assert "source_preview" in violations[0]

    def test_multiline_comment_only_skipped(self):
        nb = _nb([_code("# line 1\n# line 2\n# line 3")])
        assert check_c2(nb) == []


# ---------------------------------------------------------------------------
# check_structure
# ---------------------------------------------------------------------------

class TestCheckStructure:
    def test_clean_structure(self):
        nb = _nb([_md("# Title"), _code("x = 1"), _md("## Section")])
        assert check_structure(nb) == []

    def test_empty_code_cell(self):
        nb = _nb([_md("# Title"), _code("")])
        violations = check_structure(nb)
        assert any(v["reason"] == "empty code cell" for v in violations)

    def test_consecutive_code_cells_ok(self):
        """5 or fewer consecutive code cells is OK."""
        nb = _nb([_code(f"x{i} = {i}") for i in range(5)])
        assert check_structure(nb) == []

    def test_consecutive_code_cells_violation(self):
        """More than 5 consecutive code cells triggers violation."""
        nb = _nb([_code(f"x{i} = {i}") for i in range(7)])
        violations = check_structure(nb)
        streak_violations = [v for v in violations if "consecutive code cells" in v["reason"]]
        assert len(streak_violations) > 0

    def test_markdown_resets_streak(self):
        nb = _nb([
            _code("a"), _code("b"), _code("c"), _code("d"), _code("e"),
            _md("break"),
            _code("f"), _code("g"), _code("h"), _code("i"), _code("j"),
        ])
        assert check_structure(nb) == []

    def test_empty_markdown_not_flagged(self):
        """Empty markdown cells are allowed."""
        nb = _nb([_md("")])
        assert check_structure(nb) == []

    def test_empty_cells_list(self):
        nb = _nb([])
        assert check_structure(nb) == []


# ---------------------------------------------------------------------------
# check_metadata
# ---------------------------------------------------------------------------

class TestCheckMetadata:
    def test_kernel_and_title_present(self):
        nb = _nb(
            [_md("# My Notebook"), _code("x = 1")],
            metadata={"kernelspec": {"display_name": "Python 3"}},
        )
        assert check_metadata(nb) == []

    def test_no_kernel(self):
        nb = _nb([_md("# Title")], metadata={})
        violations = check_metadata(nb)
        assert any(v["reason"] == "no kernel defined" for v in violations)

    def test_no_title(self):
        nb = _nb([_code("x = 1")], metadata={"kernelspec": {"name": "python3"}})
        violations = check_metadata(nb)
        assert any(v["reason"] == "no title heading found" for v in violations)

    def test_kernel_name_only(self):
        """Kernel with only 'name' (no display_name) is OK."""
        nb = _nb(
            [_md("# Title")],
            metadata={"kernelspec": {"name": "python3"}},
        )
        kernel_violations = [v for v in check_metadata(nb) if "kernel" in v["reason"]]
        assert len(kernel_violations) == 0

    def test_empty_cells_no_title_violation(self):
        """Empty notebook has no cells but len(cells)==0 skips title check."""
        nb = _nb([], metadata={"kernelspec": {"display_name": "Python 3"}})
        violations = check_metadata(nb)
        assert all("title" not in v["reason"] for v in violations)

    def test_h2_counts_as_heading(self):
        """## heading starts with '#' so it counts as having a title."""
        nb = _nb([_md("## Subtitle")], metadata={"kernelspec": {"display_name": "Python 3"}})
        violations = check_metadata(nb)
        # startswith("#") matches both # and ## — this is the actual behavior
        title_violations = [v for v in violations if "title" in v["reason"]]
        assert len(title_violations) == 0


# ---------------------------------------------------------------------------
# lint_notebook
# ---------------------------------------------------------------------------

class TestLintNotebook:
    def test_clean_notebook(self, tmp_path):
        nb_path = _write_nb(tmp_path / "clean.ipynb", [
            _md("# Title"),
            _code("x = 1", exec_count=1),
        ], metadata={"kernelspec": {"display_name": "Python 3"}})
        result = lint_notebook(nb_path, {"c1", "c2", "structure", "meta"})
        assert result["violations"] == []

    def test_c1_violation(self, tmp_path):
        nb_path = _write_nb(tmp_path / "bad.ipynb", [
            _code("raise NotImplementedError('TODO')"),
        ])
        result = lint_notebook(nb_path, {"c1"})
        assert len(result["violations"]) == 1

    def test_c2_violation(self, tmp_path):
        nb_path = _write_nb(tmp_path / "noexec.ipynb", [
            _code("x = 1"),
        ])
        result = lint_notebook(nb_path, {"c2"})
        assert len(result["violations"]) == 1

    def test_structure_violation(self, tmp_path):
        nb_path = _write_nb(tmp_path / "struct.ipynb", [
            _code("") for _ in range(1)
        ])
        result = lint_notebook(nb_path, {"structure"})
        assert len(result["violations"]) >= 1

    def test_meta_violation(self, tmp_path):
        nb_path = _write_nb(tmp_path / "nometa.ipynb", [
            _code("x = 1"),
        ])
        result = lint_notebook(nb_path, {"meta"})
        assert len(result["violations"]) >= 1

    def test_missing_file(self, tmp_path):
        result = lint_notebook(tmp_path / "missing.ipynb", {"c1"})
        assert "error" in result

    def test_invalid_json(self, tmp_path):
        bad = tmp_path / "bad.ipynb"
        bad.write_text("{invalid json!!!", encoding="utf-8")
        result = lint_notebook(bad, {"c1"})
        assert "error" in result

    def test_selective_checks(self, tmp_path):
        """Only requested checks run."""
        nb_path = _write_nb(tmp_path / "sel.ipynb", [
            _code("raise NotImplementedError"),
        ])
        # Only C2 — C1 violation should not appear
        result = lint_notebook(nb_path, {"c2"})
        assert all(v["check"] != "C1" for v in result["violations"])

    def test_all_checks_combined(self, tmp_path):
        nb_path = _write_nb(tmp_path / "all.ipynb", [
            _code("raise NotImplementedError"),
            _code("x = 1"),  # C2: no exec_count
            _code(""),  # Structure: empty
        ])
        result = lint_notebook(nb_path, {"c1", "c2", "structure", "meta"})
        checks = {v["check"] for v in result["violations"]}
        assert "C1" in checks
        assert "C2" in checks
        assert "STRUCTURE" in checks
        assert "META" in checks


# ---------------------------------------------------------------------------
# C1_PATTERNS constants
# ---------------------------------------------------------------------------

class TestC1Patterns:
    def test_four_patterns(self):
        # Python (raise NotImplementedError, assert False, 1/0) + C# throw.
        assert len(C1_PATTERNS) == 4

    def test_pattern_tuples(self):
        for pattern, desc in C1_PATTERNS:
            assert isinstance(pattern, str)
            assert isinstance(desc, str)
            assert len(desc) > 0

    def test_known_patterns_present(self):
        descs = {desc for _, desc in C1_PATTERNS}
        assert "raise NotImplementedError" in descs
        assert "assert False" in descs
        assert "1/0" in descs
        assert any("NotImplementedException" in d for d in descs)
