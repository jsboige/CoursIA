"""Tests for scripts/notebook_tools/validate_pr_notebooks.py — PR notebook validator.

Tests focus on pure functions: get_kernel_name, validate_notebook — covering
kernel detection, H.1/H.3/C.1 checks, edge cases, skip-kernel logic.
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from validate_pr_notebooks import get_kernel_name, validate_notebook


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _write_nb(path: Path, cells: list[dict], kernelspec: dict | None = None,
              extra_metadata: dict | None = None) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    metadata = {}
    if kernelspec:
        metadata["kernelspec"] = kernelspec
    if extra_metadata:
        metadata.update(extra_metadata)
    nb = {"cells": cells, "metadata": metadata, "nbformat": 4, "nbformat_minor": 5}
    path.write_text(json.dumps(nb), encoding="utf-8")
    return path


def _code(source: str, exec_count: int | None = 1,
          outputs: list | None = None) -> dict:
    return {
        "cell_type": "code",
        "source": [source],
        "execution_count": exec_count,
        "outputs": outputs or [],
    }


def _md(source: str) -> dict:
    return {"cell_type": "markdown", "source": [source]}


# ---------------------------------------------------------------------------
# get_kernel_name
# ---------------------------------------------------------------------------

class TestGetKernelName:
    """Tests for kernel name extraction from notebook metadata."""

    def test_python3_kernel(self, tmp_path):
        nb = _write_nb(tmp_path / "test.ipynb", [],
                       kernelspec={"name": "python3", "language": "python"})
        assert get_kernel_name(nb) == "python3"

    def test_dotnet_csharp_kernel(self, tmp_path):
        nb = _write_nb(tmp_path / "test.ipynb", [],
                       kernelspec={"name": ".net-csharp", "language": "C#"})
        assert get_kernel_name(nb) == ".net-csharp"

    def test_lean4_kernel(self, tmp_path):
        nb = _write_nb(tmp_path / "test.ipynb", [],
                       kernelspec={"name": "lean4", "language": "lean4"})
        assert get_kernel_name(nb) == "lean4"

    def test_no_metadata(self, tmp_path):
        nb = _write_nb(tmp_path / "test.ipynb", [])
        assert get_kernel_name(nb) == "python3"  # default

    def test_empty_kernelspec(self, tmp_path):
        nb = _write_nb(tmp_path / "test.ipynb", [], kernelspec={})
        assert get_kernel_name(nb) == "python3"  # default

    def test_invalid_json(self, tmp_path):
        bad = tmp_path / "bad.ipynb"
        bad.write_text("not json{{{", encoding="utf-8")
        assert get_kernel_name(bad) == "unknown"

    def test_unicode_decode_error(self, tmp_path):
        bad = tmp_path / "binary.ipynb"
        bad.write_bytes(b"\xff\xfe\x00\x00invalid")
        assert get_kernel_name(bad) == "unknown"


# ---------------------------------------------------------------------------
# validate_notebook — H.3 checks (execution_count)
# ---------------------------------------------------------------------------

class TestValidateNotebookH3:
    """Tests for execution_count validation (H.3)."""

    def test_all_cells_have_exec_count(self, tmp_path):
        nb = _write_nb(tmp_path / "test.ipynb", [
            _code("x = 1", exec_count=1),
            _code("y = 2", exec_count=2),
        ])
        result = validate_notebook(nb)
        assert result["passed"] is True
        assert result["total_code"] == 2
        assert result["errors"] == []

    def test_null_exec_count_fails(self, tmp_path):
        nb = _write_nb(tmp_path / "test.ipynb", [
            _code("x = 1", exec_count=None),
        ])
        result = validate_notebook(nb)
        assert result["passed"] is False
        assert any("execution_count is null" in e for e in result["errors"])

    def test_skip_exec_for_dotnet_kernel(self, tmp_path):
        """dotnet kernel notebooks skip execution_count check."""
        nb = _write_nb(tmp_path / "test.ipynb", [
            _code("Console.WriteLine(\"hi\")", exec_count=None),
        ], kernelspec={"name": ".net-csharp", "language": "C#"})
        result = validate_notebook(nb)
        assert result["passed"] is True

    def test_skip_exec_for_lean_kernel(self, tmp_path):
        nb = _write_nb(tmp_path / "test.ipynb", [
            _code("#check Nat", exec_count=None),
        ], kernelspec={"name": "lean4", "language": "lean4"})
        result = validate_notebook(nb)
        assert result["passed"] is True

    def test_skip_exec_for_qc_cloud_path(self, tmp_path):
        """Notebooks in QuantConnect/ paths skip execution check."""
        qc_path = tmp_path / "QuantConnect" / "Python" / "test.ipynb"
        nb = _write_nb(qc_path, [
            _code("qb = QuantBook()", exec_count=None),
        ])
        result = validate_notebook(nb)
        assert result["passed"] is True

    def test_skip_exec_for_qc_projects_path(self, tmp_path):
        qc_path = tmp_path / "QuantConnect" / "projects" / "test.ipynb"
        nb = _write_nb(qc_path, [
            _code("self.Debug('test')", exec_count=None),
        ])
        result = validate_notebook(nb)
        assert result["passed"] is True

    def test_skip_exec_for_qc_reference_metadata(self, tmp_path):
        """A notebook flagged metadata.qc_reference=True skips H.3 even outside
        QC_CLOUD_PATHS (content-aware unification with regression_scan.py:261,
        #3776). E.g. partner-course reference templates."""
        # Path deliberately OUTSIDE QuantConnect/Python|projects
        ref_path = tmp_path / "partner-course" / "examples" / "research.ipynb"
        nb = _write_nb(ref_path, [
            _code("qb = QuantBook()", exec_count=None),
        ], extra_metadata={"qc_reference": True})
        result = validate_notebook(nb)
        assert result["passed"] is True

    def test_no_skip_exec_without_qc_reference_metadata(self, tmp_path):
        """Without the qc_reference flag, a non-QC-path notebook with null
        execution_count must still FAIL H.3 (content-aware check is opt-in)."""
        ref_path = tmp_path / "partner-course" / "examples" / "research.ipynb"
        nb = _write_nb(ref_path, [
            _code("print('hi')", exec_count=None),
        ])  # no qc_reference flag
        result = validate_notebook(nb)
        assert result["passed"] is False
        assert any("execution_count is null" in e for e in result["errors"])


# ---------------------------------------------------------------------------
# validate_notebook — C.1 checks (forbidden patterns)
# ---------------------------------------------------------------------------

class TestValidateNotebookC1:
    """Tests for C.1 forbidden pattern detection."""

    def test_raise_not_implemented_detected(self, tmp_path):
        nb = _write_nb(tmp_path / "test.ipynb", [
            _code("raise NotImplementedError('TODO')", exec_count=1),
        ])
        result = validate_notebook(nb)
        assert result["passed"] is False
        assert any("C.1 violation" in e for e in result["errors"])

    def test_assert_false_detected(self, tmp_path):
        nb = _write_nb(tmp_path / "test.ipynb", [
            _code("assert False", exec_count=1),
        ])
        result = validate_notebook(nb)
        assert result["passed"] is False
        assert any("C.1 violation" in e for e in result["errors"])

    def test_clean_code_passes(self, tmp_path):
        nb = _write_nb(tmp_path / "test.ipynb", [
            _code("x = 1\ny = 2\nprint(x + y)", exec_count=1),
        ])
        result = validate_notebook(nb)
        assert result["passed"] is True

    def test_pass_stub_passes(self, tmp_path):
        """pass is a valid stub pattern (C.1 compliant)."""
        nb = _write_nb(tmp_path / "test.ipynb", [
            _code("pass", exec_count=1),
        ])
        result = validate_notebook(nb)
        assert result["passed"] is True

    def test_print_stub_passes(self, tmp_path):
        """print('Exercice a completer') is a valid stub."""
        nb = _write_nb(tmp_path / "test.ipynb", [
            _code("print('Exercice a completer')", exec_count=1),
        ])
        result = validate_notebook(nb)
        assert result["passed"] is True

    def test_return_none_stub_passes(self, tmp_path):
        nb = _write_nb(tmp_path / "test.ipynb", [
            _code("return None  # TODO", exec_count=1),
        ])
        result = validate_notebook(nb)
        assert result["passed"] is True

    def test_date_not_flagged(self, tmp_path):
        """Dates like 21/02/2022 should NOT be flagged as 1/0 (#1505)."""
        nb = _write_nb(tmp_path / "test.ipynb", [
            _code("date = '21/02/2022'", exec_count=1),
        ])
        result = validate_notebook(nb)
        assert result["passed"] is True


# ---------------------------------------------------------------------------
# validate_notebook — H.1 checks (error outputs)
# ---------------------------------------------------------------------------

class TestValidateNotebookH1:
    """Tests for error output detection (H.1)."""

    def test_error_output_fails(self, tmp_path):
        nb = _write_nb(tmp_path / "test.ipynb", [
            _code("x = 1", exec_count=1,
                  outputs=[{"output_type": "error", "ename": "NameError",
                            "evalue": "foo", "traceback": []}]),
        ])
        result = validate_notebook(nb)
        assert result["passed"] is False
        assert any("error output" in e and "NameError" in e for e in result["errors"])

    def test_stream_output_passes(self, tmp_path):
        nb = _write_nb(tmp_path / "test.ipynb", [
            _code("print('hello')", exec_count=1,
                  outputs=[{"output_type": "stream", "name": "stdout", "text": ["hello"]}]),
        ])
        result = validate_notebook(nb)
        assert result["passed"] is True

    def test_execute_result_passes(self, tmp_path):
        nb = _write_nb(tmp_path / "test.ipynb", [
            _code("1 + 1", exec_count=1,
                  outputs=[{"output_type": "execute_result", "data": {"text/plain": ["2"]}}]),
        ])
        result = validate_notebook(nb)
        assert result["passed"] is True

    def test_error_in_skip_kernel_is_advisory(self, tmp_path):
        """Error output in dotnet kernel = advisory, not failure."""
        nb = _write_nb(tmp_path / "test.ipynb", [
            _code("invalid code", exec_count=1,
                  outputs=[{"output_type": "error", "ename": "Error",
                            "evalue": "bad", "traceback": []}]),
        ], kernelspec={"name": ".net-csharp", "language": "C#"})
        result = validate_notebook(nb)
        # Advisory = error listed but passed=True
        assert result["passed"] is True
        assert any("advisory" in e.lower() or "QC Cloud" in e for e in result["errors"])


# ---------------------------------------------------------------------------
# validate_notebook — structural checks
# ---------------------------------------------------------------------------

class TestValidateNotebookStructural:
    """Tests for structural notebook checks."""

    def test_empty_notebook_passes(self, tmp_path):
        nb = _write_nb(tmp_path / "test.ipynb", [])
        result = validate_notebook(nb)
        assert result["passed"] is True
        assert result["total_code"] == 0

    def test_markdown_only_passes(self, tmp_path):
        nb = _write_nb(tmp_path / "test.ipynb", [
            _md("# Title"),
            _md("Some text"),
        ])
        result = validate_notebook(nb)
        assert result["passed"] is True
        assert result["total_code"] == 0

    def test_empty_code_cell_skipped(self, tmp_path):
        nb = _write_nb(tmp_path / "test.ipynb", [
            _code("", exec_count=None),
        ])
        result = validate_notebook(nb)
        assert result["passed"] is True
        assert result["total_code"] == 0

    def test_comment_only_code_cell_skipped(self, tmp_path):
        nb = _write_nb(tmp_path / "test.ipynb", [
            _code("# just a comment", exec_count=None),
        ])
        result = validate_notebook(nb)
        assert result["passed"] is True
        assert result["total_code"] == 0

    def test_mixed_content_notebook(self, tmp_path):
        nb = _write_nb(tmp_path / "test.ipynb", [
            _md("# Title"),
            _code("x = 1", exec_count=1,
                  outputs=[{"output_type": "stream", "name": "stdout", "text": ["1"]}]),
            _md("## Section"),
            _code("y = 2", exec_count=2),
        ])
        result = validate_notebook(nb)
        assert result["passed"] is True
        assert result["total_code"] == 2

    def test_invalid_json_fails(self, tmp_path):
        bad = tmp_path / "bad.ipynb"
        bad.write_text("not json{{{", encoding="utf-8")
        result = validate_notebook(bad)
        assert result["passed"] is False
        assert any("Cannot parse JSON" in e for e in result["errors"])

    def test_result_has_required_keys(self, tmp_path):
        nb = _write_nb(tmp_path / "test.ipynb", [
            _code("x = 1", exec_count=1),
        ])
        result = validate_notebook(nb)
        assert "path" in result
        assert "kernel" in result
        assert "total_code" in result
        assert "passed" in result
        assert "errors" in result

    def test_multiple_violations_reported(self, tmp_path):
        nb = _write_nb(tmp_path / "test.ipynb", [
            _code("raise NotImplementedError('TODO')", exec_count=None),
            _code("x = 1", exec_count=1),
        ])
        result = validate_notebook(nb)
        assert result["passed"] is False
        # Both C.1 and H.3 violations in cell 0
        violations = [e for e in result["errors"] if "cell 0" in e]
        assert len(violations) >= 2


# ---------------------------------------------------------------------------
# validate_notebook — path normalization (Windows backslash)
# ---------------------------------------------------------------------------

class TestValidateNotebookPaths:
    """Tests for path handling in validate_notebook."""

    def test_backslash_path_in_qc_cloud(self, tmp_path):
        """Windows backslash paths should match QC_CLOUD_PATHS."""
        qc_path = tmp_path / "QuantConnect" / "Python" / "test.ipynb"
        nb = _write_nb(qc_path, [
            _code("qb = QuantBook()", exec_count=None),
        ])
        result = validate_notebook(nb)
        assert result["passed"] is True

    def test_kernel_in_result(self, tmp_path):
        nb = _write_nb(tmp_path / "test.ipynb", [
            _code("x = 1", exec_count=1),
        ], kernelspec={"name": "python3", "language": "python"})
        result = validate_notebook(nb)
        assert result["kernel"] == "python3"


# ---------------------------------------------------------------------------
# validate_notebook — Lean/alectryon text-rendered errors (H.1, #5151)
# ---------------------------------------------------------------------------

class TestValidateNotebookLeanTextErrors:
    """Lean via lean4_jupyter/alectryon renders compile errors as TEXT
    (display_data / execute_result), never as output_type=="error". A whole
    Lean notebook can be red (every cell ❌) while CI stays green. The
    detector anchors on the toolchain-emitted `severity: error` message.
    Regression guard for #5151 (Sudoku-7b-Lean-Propagation: failed import ->
    48 unknown-identifier + 12 unknown-constant cascade, CI all green)."""

    def _lean_err_output(self) -> dict:
        # Shape mirrors the real lean4_jupyter/alectryon output on #5151:
        # the compiler's own JSON message is embedded in text/plain.
        return {
            "output_type": "display_data",
            "data": {
                "text/plain": [
                    "import Sudoku.Basic\n     ──────▶ ❌ unknown namespace `Sudoku`\n",
                    'Raw output:\n{"messages": [{"severity": "error", '
                    '"pos": {"line": 4, "column": 5}, "data": "unknown namespace `Sudoku`"}]}',
                ],
            },
        }

    def test_lean_text_error_blocks_even_though_skip_exec(self, tmp_path):
        """The #5151 case: lean4 kernel is skip_exec, but a text-rendered
        toolchain error is BLOCKING (never advisory — Lean compile errors are
        never 'expected', and QC notebooks are Python)."""
        nb = _write_nb(tmp_path / "Sudoku-7b.ipynb", [
            _code("import Sudoku.Basic\nopen Sudoku", exec_count=1,
                  outputs=[self._lean_err_output()]),
        ], kernelspec={"name": "lean4", "language": "lean4"})
        result = validate_notebook(nb)
        assert result["passed"] is False
        assert any("Lean toolchain error" in e for e in result["errors"])

    def test_lean_text_error_in_html_output(self, tmp_path):
        """severity:error embedded in text/html is caught too."""
        html_out = {
            "output_type": "display_data",
            "data": {"text/html": [
                '<pre class="alectryon-io">... {"severity": "error", '
                '"data": "unknown identifier"} ...</pre>'
            ]},
        }
        nb = _write_nb(tmp_path / "lean.ipynb", [
            _code("#check Foo", exec_count=1, outputs=[html_out]),
        ], kernelspec={"name": "lean4", "language": "lean4"})
        result = validate_notebook(nb)
        assert result["passed"] is False

    def test_clean_lean_output_passes(self, tmp_path):
        """A successful #check with a normal alectryon output (no severity
        error) must PASS — no false positive."""
        ok_out = {
            "output_type": "display_data",
            "data": {"text/plain": ["#check Nat\nNat : Type"]},
        }
        nb = _write_nb(tmp_path / "lean.ipynb", [
            _code("#check Nat", exec_count=1, outputs=[ok_out]),
        ], kernelspec={"name": "lean4", "language": "lean4"})
        result = validate_notebook(nb)
        assert result["passed"] is True

    def test_raises_exception_tag_opts_out(self, tmp_path):
        """A cell tagged 'raises-exception' (intentional error demo) is exempt
        from the Lean text-error gate."""
        cell = _code("import Sudoku.Basic", exec_count=1,
                     outputs=[self._lean_err_output()])
        cell["metadata"] = {"tags": ["raises-exception"]}
        nb = _write_nb(tmp_path / "lean.ipynb", [cell],
                       kernelspec={"name": "lean4", "language": "lean4"})
        result = validate_notebook(nb)
        assert result["passed"] is True

    def test_python_checkmark_emoji_no_false_positive(self, tmp_path):
        """A Python cell that prints a ❌ glyph in a legit result table (e.g.
        a pass/fail summary) must NOT be flagged — the detector keys on the
        Lean 'severity: error' string, not on the emoji."""
        out = {"output_type": "stream", "name": "stdout",
               "text": ["Test 1: ✅ passed\nTest 2: ❌ failed\n"]}
        nb = _write_nb(tmp_path / "test.ipynb", [
            _code("run_checks()", exec_count=1, outputs=[out]),
        ])
        result = validate_notebook(nb)
        assert result["passed"] is True
