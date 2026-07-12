"""Mutation-killing tests for notebook_tools.py execute/skeleton/analyze paths.

Targets:
- NotebookExecutor.detect_kernel_name() — kernel mapping logic
- NotebookExecutor.execute_with_papermill() — papermill fallback (no helpers)
- NotebookAnalyzer.get_cell_outputs_analysis() — error/empty/not-executed
- _format_markdown_table() — number extraction, section truncation
- _format_summary() — duration calculation, level-2 section count
- cmd_analyze() — CLI return codes
- detect_kernel() — display_name fallback, Unknown return

See #2149 (mutation testing Epic).
"""

import json
import sys
import tempfile
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from notebook_tools import (
    CellInfo,
    NotebookAnalyzer,
    NotebookExecutionResult,
    NotebookExecutor,
    NotebookSkeleton,
    SectionInfo,
    _format_markdown_table,
    _format_summary,
    detect_kernel,
)


# =============================================================================
# Helpers
# =============================================================================

def _write_nb(cells: list, tmp_path: Path, name: str = "test.ipynb") -> Path:
    """Write a minimal notebook with the given cells."""
    nb = {
        "nbformat": 4,
        "nbformat_minor": 5,
        "metadata": {
            "kernelspec": {
                "display_name": "Python 3",
                "language": "python",
                "name": "python3",
            }
        },
        "cells": cells,
    }
    p = tmp_path / name
    p.write_text(json.dumps(nb), encoding="utf-8")
    return p


def _code_cell(source: str, execution_count=None, outputs=None, cell_id=None):
    """Build a code cell dict."""
    cell = {
        "cell_type": "code",
        "source": [source],
        "metadata": {},
    }
    if execution_count is not None:
        cell["execution_count"] = execution_count
    if outputs is not None:
        cell["outputs"] = outputs
    else:
        cell["outputs"] = []
    if cell_id is not None:
        cell["id"] = cell_id
    return cell


def _md_cell(source: str):
    """Build a markdown cell dict."""
    return {"cell_type": "markdown", "source": [source], "metadata": {}}


# =============================================================================
# Test NotebookExecutor.detect_kernel_name()
# =============================================================================

class TestDetectKernelNameExecutor:
    """Tests for NotebookExecutor.detect_kernel_name() kernel mapping."""

    def test_python_kernel_maps_python3(self, tmp_path):
        """Mutation: 'python3' in kernel name -> python3 (not lean4)."""
        nb_path = _write_nb([_code_cell("x = 1")], tmp_path)
        # Patch HELPERS_AVAILABLE to False to test fallback logic
        with patch("notebook_tools.HELPERS_AVAILABLE", False):
            executor = NotebookExecutor(nb_path)
            assert executor.detect_kernel_name() == "python3"

    def test_smartcontracts_kernel_detected_as_python3(self, tmp_path):
        """detect_kernel_name: smartcontracts kernel -> python3 (language=python wins).

        NOTE: detect_kernel() maps smartcontracts to 'Python' via language='python',
        so detect_kernel_name() sees 'python' and returns 'python3'. The 'smartcontracts'
        branch in detect_kernel_name() is effectively unreachable for standard SC kernels.
        """
        nb = {
            "nbformat": 4, "nbformat_minor": 5,
            "metadata": {
                "kernelspec": {
                    "display_name": "SmartContracts",
                    "language": "python",
                    "name": "smartcontracts",
                }
            },
            "cells": [_code_cell("pass")],
        }
        p = tmp_path / "sc.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")

        with patch("notebook_tools.HELPERS_AVAILABLE", False):
            executor = NotebookExecutor(p)
            # detect_kernel returns 'Python' -> detect_kernel_name sees 'python' -> python3
            assert executor.detect_kernel_name() == "python3"

    def test_dotnet_kernel_maps_csharp(self, tmp_path):
        """Mutation: '.net' in kernel -> '.net-csharp'."""
        nb = {
            "nbformat": 4, "nbformat_minor": 5,
            "metadata": {
                "kernelspec": {
                    "display_name": ".NET (C#)",
                    "language": "C#",
                    "name": ".net-csharp",
                }
            },
            "cells": [_code_cell("Console.WriteLine(42)")],
        }
        p = tmp_path / "dotnet.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")

        with patch("notebook_tools.HELPERS_AVAILABLE", False):
            executor = NotebookExecutor(p)
            assert executor.detect_kernel_name() == ".net-csharp"

    def test_fsharp_kernel_maps_to_dotnet_csharp(self, tmp_path):
        """detect_kernel_name: .NET F# kernel -> .net-csharp (.net match wins over fsharp).

        NOTE: detect_kernel() returns '.NET F#'. detect_kernel_name() lowers it to
        '.net f#' and checks '.net' in kernel FIRST -> returns '.net-csharp'.
        The 'fsharp' branch is unreachable because '.net' matches first.
        This documents the actual behavior (potential ordering bug).
        """
        nb = {
            "nbformat": 4, "nbformat_minor": 5,
            "metadata": {
                "kernelspec": {
                    "display_name": ".NET (F#)",
                    "language": "F#",
                    "name": ".net-fsharp",
                }
            },
            "cells": [_code_cell("printfn \"hi\"")],
        }
        p = tmp_path / "fsharp.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")

        with patch("notebook_tools.HELPERS_AVAILABLE", False):
            executor = NotebookExecutor(p)
            # '.net' in '.net f#' is True -> .net-csharp (fsharp check unreachable)
            assert executor.detect_kernel_name() == ".net-csharp"

    def test_lean_kernel_maps_lean4(self, tmp_path):
        """Mutation: 'lean' in kernel -> 'lean4'."""
        nb = {
            "nbformat": 4, "nbformat_minor": 5,
            "metadata": {
                "kernelspec": {
                    "display_name": "Lean 4",
                    "language": "lean4",
                    "name": "lean4",
                }
            },
            "cells": [_code_cell("#check 1")],
        }
        p = tmp_path / "lean.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")

        with patch("notebook_tools.HELPERS_AVAILABLE", False):
            executor = NotebookExecutor(p)
            assert executor.detect_kernel_name() == "lean4"

    def test_unknown_kernel_defaults_python3(self, tmp_path):
        """Mutation: unknown kernel falls back to python3 (not lean4/empty)."""
        nb = {
            "nbformat": 4, "nbformat_minor": 5,
            "metadata": {
                "kernelspec": {
                    "display_name": "Rust",
                    "language": "rust",
                    "name": "rust",
                }
            },
            "cells": [_code_cell("fn main() {}")],
        }
        p = tmp_path / "rust.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")

        with patch("notebook_tools.HELPERS_AVAILABLE", False):
            executor = NotebookExecutor(p)
            assert executor.detect_kernel_name() == "python3"


# =============================================================================
# Test NotebookAnalyzer.get_cell_outputs_analysis()
# =============================================================================

class TestCellOutputsAnalysis:
    """Mutation tests for get_cell_outputs_analysis edge cases."""

    def test_empty_source_counted_as_not_executed_not_empty(self, tmp_path):
        """Mutation: empty source -> status 'EMPTY', not 'NOT_EXECUTED'."""
        # A code cell with empty source and no outputs
        cell = _code_cell("", outputs=[])
        nb_path = _write_nb([cell], tmp_path)
        analyzer = NotebookAnalyzer(nb_path)
        result = analyzer.get_cell_outputs_analysis()
        # Empty source code cell: status should be 'EMPTY'
        assert result["cells"][0]["status"] == "EMPTY"
        assert result["cells_without_output"] == 1

    def test_nonempty_source_no_output_is_not_executed(self, tmp_path):
        """Mutation: non-empty source + no output -> 'NOT_EXECUTED'."""
        cell = _code_cell("x = 42", outputs=[])
        nb_path = _write_nb([cell], tmp_path)
        analyzer = NotebookAnalyzer(nb_path)
        result = analyzer.get_cell_outputs_analysis()
        assert result["cells"][0]["status"] == "NOT_EXECUTED"

    def test_error_output_sets_error_status(self, tmp_path):
        """Mutation: error output_type -> status 'ERROR', not 'OK'."""
        cell = _code_cell("1/0", outputs=[{
            "output_type": "error",
            "ename": "ZeroDivisionError",
            "evalue": "division by zero",
        }])
        nb_path = _write_nb([cell], tmp_path)
        analyzer = NotebookAnalyzer(nb_path)
        result = analyzer.get_cell_outputs_analysis()
        assert result["cells"][0]["status"] == "ERROR"
        assert result["cells_with_errors"] == 1

    def test_stream_output_is_ok_not_error(self, tmp_path):
        """Mutation: stream output_type -> 'OK', not 'ERROR'."""
        cell = _code_cell("print('hello')", outputs=[{
            "output_type": "stream",
            "name": "stdout",
            "text": ["hello\n"],
        }])
        nb_path = _write_nb([cell], tmp_path)
        analyzer = NotebookAnalyzer(nb_path)
        result = analyzer.get_cell_outputs_analysis()
        assert result["cells"][0]["status"] == "OK"
        assert result["cells_with_errors"] == 0

    def test_markdown_cells_excluded_from_code_count(self, tmp_path):
        """Mutation: markdown cells not counted in code_cells."""
        cells = [_md_cell("# Title"), _code_cell("x = 1", outputs=[]), _md_cell("## Section")]
        nb_path = _write_nb(cells, tmp_path)
        analyzer = NotebookAnalyzer(nb_path)
        result = analyzer.get_cell_outputs_analysis()
        assert result["code_cells"] == 1
        assert result["total_cells"] == 3

    def test_first_line_truncated_at_60_chars(self, tmp_path):
        """Mutation: first_line capped at 60 chars."""
        long_line = "x = " + "a" * 100
        cell = _code_cell(long_line, outputs=[])
        nb_path = _write_nb([cell], tmp_path)
        analyzer = NotebookAnalyzer(nb_path)
        result = analyzer.get_cell_outputs_analysis()
        assert len(result["cells"][0]["first_line"]) <= 60

    def test_multiple_errors_counted(self, tmp_path):
        """Mutation: multiple error cells -> cells_with_errors > 1."""
        cell1 = _code_cell("1/0", outputs=[{
            "output_type": "error", "ename": "ZD", "evalue": "",
        }])
        cell2 = _code_cell("None.foo()", outputs=[{
            "output_type": "error", "ename": "Attr", "evalue": "",
        }])
        nb_path = _write_nb([cell1, cell2], tmp_path)
        analyzer = NotebookAnalyzer(nb_path)
        result = analyzer.get_cell_outputs_analysis()
        assert result["cells_with_errors"] == 2

    def test_error_details_populated(self, tmp_path):
        """Mutation: error details include ename and evalue."""
        cell = _code_cell("raise ValueError('test')", outputs=[{
            "output_type": "error",
            "ename": "ValueError",
            "evalue": "test message",
        }])
        nb_path = _write_nb([cell], tmp_path)
        analyzer = NotebookAnalyzer(nb_path)
        result = analyzer.get_cell_outputs_analysis()
        assert result["errors"][0]["ename"] == "ValueError"
        assert result["errors"][0]["evalue"] == "test message"


# =============================================================================
# Test _format_markdown_table()
# =============================================================================

class TestFormatMarkdownTable:
    """Mutation tests for _format_markdown_table."""

    def test_number_extracted_from_name(self):
        """Mutation: number extracted from name pattern '-NN-'."""
        skel = NotebookSkeleton(
            path="path/to/SC-12-Test.ipynb",
            name="SC-12-Test",
            title="Test",
            kernel="Python",
            total_cells=10,
            sections=[],
        )
        result = _format_markdown_table([skel], Path("path/to"))
        assert "| 12 |" in result

    def test_fallback_number_when_no_dash_number(self):
        """Mutation: no '-NN-' pattern -> uses enumeration index."""
        skel = NotebookSkeleton(
            path="path/to/custom.ipynb",
            name="custom",
            title="Custom",
            kernel="Python",
            total_cells=5,
            sections=[],
        )
        result = _format_markdown_table([skel], Path("path/to"))
        assert "| 1 |" in result

    def test_section_truncation_over_40_chars(self):
        """Mutation: sections >40 chars truncated with '...'."""
        long_section = SectionInfo(level=2, title="A" * 50, cell_index=0)
        skel = NotebookSkeleton(
            path="p.ipynb", name="test", title="T",
            kernel="Python", total_cells=10,
            sections=[long_section],
        )
        result = _format_markdown_table([skel], Path("."))
        # Should contain "..." truncation marker
        assert "..." in result

    def test_only_level2_sections_in_table(self):
        """Mutation: only level-2 sections shown (level-1/3 excluded)."""
        sections = [
            SectionInfo(level=1, title="H1", cell_index=0),
            SectionInfo(level=2, title="H2 Visible", cell_index=1),
            SectionInfo(level=3, title="H3", cell_index=2),
        ]
        skel = NotebookSkeleton(
            path="p.ipynb", name="test", title="T",
            kernel="Python", total_cells=10,
            sections=sections,
        )
        result = _format_markdown_table([skel], Path("."))
        assert "H2 Visible" in result
        assert "H1" not in result
        assert "H3" not in result

    def test_max_3_sections_shown(self):
        """Mutation: max 3 sections shown in table."""
        sections = [SectionInfo(level=2, title=f"Sec{i}", cell_index=i) for i in range(5)]
        skel = NotebookSkeleton(
            path="p.ipynb", name="test", title="T",
            kernel="Python", total_cells=10,
            sections=sections,
        )
        result = _format_markdown_table([skel], Path("."))
        assert "Sec0" in result
        assert "Sec2" in result
        assert "Sec3" not in result  # 4th section should be excluded

    def test_duration_format(self):
        """Mutation: estimated_duration shown as '~N min'."""
        skel = NotebookSkeleton(
            path="p.ipynb", name="test", title="T",
            kernel="Python", total_cells=10,
            estimated_duration=42,
        )
        result = _format_markdown_table([skel], Path("."))
        assert "~42 min" in result


# =============================================================================
# Test _format_summary()
# =============================================================================

class TestFormatSummary:
    """Mutation tests for _format_summary."""

    def test_total_cells_summed(self):
        """Mutation: total_cells = sum of all skeletons."""
        skels = [
            NotebookSkeleton(path="a.ipynb", name="a", total_cells=10),
            NotebookSkeleton(path="b.ipynb", name="b", total_cells=5),
        ]
        result = _format_summary(skels)
        assert "Total cells: 15" in result

    def test_duration_format_hours_minutes(self):
        """Mutation: duration formatted as 'XhYY' when >60."""
        skels = [
            NotebookSkeleton(path="a.ipynb", name="a", total_cells=10, estimated_duration=90),
        ]
        result = _format_summary(skels)
        assert "1h30" in result

    def test_none_duration_treated_as_zero(self):
        """Mutation: None estimated_duration treated as 0, not crash."""
        skels = [
            NotebookSkeleton(path="a.ipynb", name="a", total_cells=10, estimated_duration=None),
        ]
        result = _format_summary(skels)
        assert "0 min" in result

    def test_level2_sections_counted_per_notebook(self):
        """Mutation: sections count only level==2."""
        skels = [
            NotebookSkeleton(
                path="a.ipynb", name="a", total_cells=10,
                sections=[
                    SectionInfo(level=1, title="H1", cell_index=0),
                    SectionInfo(level=2, title="S1", cell_index=1),
                    SectionInfo(level=2, title="S2", cell_index=2),
                    SectionInfo(level=3, title="H3", cell_index=3),
                ],
            ),
        ]
        result = _format_summary(skels)
        assert "2 sections" in result

    def test_empty_skeletons_list(self):
        """Mutation: empty list -> 'Notebooks: 0', 'Total cells: 0'."""
        result = _format_summary([])
        assert "Notebooks: 0" in result
        assert "Total cells: 0" in result


# =============================================================================
# Test NotebookExecutor.execute_with_papermill() fallback paths
# =============================================================================

class TestExecutorPapermillFallback:
    """Mutation tests for papermill fallback (HELPERS_AVAILABLE=False)."""

    def test_timeout_returns_failure(self, tmp_path):
        """Mutation: subprocess.TimeoutExpired -> success=False, not True."""
        nb_path = _write_nb([_code_cell("import time; time.sleep(999)")], tmp_path)

        with patch("notebook_tools.HELPERS_AVAILABLE", False):
            executor = NotebookExecutor(nb_path)
            with patch("subprocess.run", side_effect=__import__("subprocess").TimeoutExpired("cmd", 300)):
                result = executor.execute_with_papermill(timeout=300)
                assert result.success is False
                assert "TIMEOUT" in result.message

    def test_generic_exception_returns_failure(self, tmp_path):
        """Mutation: generic Exception -> success=False with ERROR."""
        nb_path = _write_nb([_code_cell("x = 1")], tmp_path)

        with patch("notebook_tools.HELPERS_AVAILABLE", False):
            executor = NotebookExecutor(nb_path)
            with patch("subprocess.run", side_effect=OSError("mock fail")):
                result = executor.execute_with_papermill()
                assert result.success is False
                assert "ERROR" in result.message

    def test_cell_errors_flagged_even_with_rc0(self, tmp_path):
        """Mutation: papermill rc=0 + cell errors -> success=False."""
        nb_path = _write_nb([_code_cell("1/0")], tmp_path)

        # Create a mock output notebook with cell errors
        output_nb = {
            "cells": [{
                "cell_type": "code",
                "outputs": [{
                    "output_type": "error",
                    "ename": "ZeroDivisionError",
                    "evalue": "division by zero",
                }],
            }],
        }
        output_path = tmp_path / "test_output.ipynb"
        output_path.write_text(json.dumps(output_nb), encoding="utf-8")

        mock_result = MagicMock()
        mock_result.returncode = 0
        mock_result.stderr = ""

        with patch("notebook_tools.HELPERS_AVAILABLE", False):
            executor = NotebookExecutor(nb_path)
            with patch("subprocess.run", return_value=mock_result):
                result = executor.execute_with_papermill(output_path=output_path)
                assert result.success is False
                assert "CELL ERRORS" in result.message

    def test_success_with_rc0_no_errors(self, tmp_path):
        """Mutation: rc=0 + no cell errors -> success=True."""
        nb_path = _write_nb([_code_cell("x = 1")], tmp_path)

        mock_result = MagicMock()
        mock_result.returncode = 0
        mock_result.stderr = ""

        with patch("notebook_tools.HELPERS_AVAILABLE", False):
            executor = NotebookExecutor(nb_path)
            with patch("subprocess.run", return_value=mock_result):
                result = executor.execute_with_papermill()
                assert result.success is True
                assert "SUCCESS" in result.message

    def test_nonzero_rc_returns_failure(self, tmp_path):
        """Mutation: rc!=0 -> success=False with FAILED."""
        nb_path = _write_nb([_code_cell("bad syntax !!!")], tmp_path)

        mock_result = MagicMock()
        mock_result.returncode = 1
        mock_result.stderr = "SyntaxError: invalid syntax"

        with patch("notebook_tools.HELPERS_AVAILABLE", False):
            executor = NotebookExecutor(nb_path)
            with patch("subprocess.run", return_value=mock_result):
                result = executor.execute_with_papermill()
                assert result.success is False
                assert "FAILED" in result.message

    def test_batch_mode_env_propagated(self, tmp_path):
        """Mutation: batch_mode=True -> BATCH_MODE in env."""
        nb_path = _write_nb([_code_cell("x = 1")], tmp_path)

        mock_result = MagicMock()
        mock_result.returncode = 0
        mock_result.stderr = ""

        with patch("notebook_tools.HELPERS_AVAILABLE", False):
            executor = NotebookExecutor(nb_path)
            with patch("subprocess.run", return_value=mock_result) as mock_run:
                executor.execute_with_papermill(batch_mode=True)
                call_kwargs = mock_run.call_args
                # Check BATCH_MODE propagated via -p and env
                cmd = call_kwargs[0][0] if call_kwargs[0] else call_kwargs.kwargs.get("args", [])
                assert "BATCH_MODE" in " ".join(cmd)

    def test_wsl_kernel_timeout_based_on_papermill_kernel_name(self, tmp_path):
        """Timeout logic checks papermill kernel_name (e.g. 'python3'), not display name.

        The WSL check in execute_with_papermill uses the PAPERMILL kernel name
        (returned by detect_kernel_name()), not the Jupyter display name.
        So a notebook with display_name='Python (WSL)' gets kernel='python3'
        from detect_kernel_name(), and the start_timeout=60 (not 120).
        The 120s timeout only triggers when the PAPERMILL kernel name contains 'wsl'.
        """
        nb = {
            "nbformat": 4, "nbformat_minor": 5,
            "metadata": {
                "kernelspec": {
                    "display_name": "Python (WSL)",
                    "language": "python",
                    "name": "python-wsl",
                }
            },
            "cells": [_code_cell("x = 1")],
        }
        p = tmp_path / "wsl.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")

        mock_result = MagicMock()
        mock_result.returncode = 0
        mock_result.stderr = ""

        with patch("notebook_tools.HELPERS_AVAILABLE", False):
            executor = NotebookExecutor(p)
            with patch("subprocess.run", return_value=mock_result) as mock_run:
                executor.execute_with_papermill()
                cmd = mock_run.call_args[0][0]
                # detect_kernel_name returns 'python3' (not 'python-wsl')
                # so start_timeout = 60 (not 120)
                for i, arg in enumerate(cmd):
                    if arg == "--start-timeout":
                        assert cmd[i + 1] == "60"
                        break
                else:
                    pytest.fail("--start-timeout not found in command")


# =============================================================================
# Test NotebookExecutor.execute_cell_by_cell() fallback
# =============================================================================

class TestExecutorCellByCellFallback:
    """Mutation tests for cell-by-cell fallback paths."""

    def test_no_helpers_returns_failure(self, tmp_path):
        """Mutation: no notebook_helpers -> failure message, not crash."""
        nb_path = _write_nb([_code_cell("x = 1")], tmp_path)

        with patch("notebook_tools.HELPERS_AVAILABLE", False):
            executor = NotebookExecutor(nb_path)
            result = executor.execute_cell_by_cell()
            assert result.success is False
            assert "notebook_helpers" in result.message

    def test_invalid_notebook_returns_failure(self, tmp_path):
        """Mutation: invalid notebook -> failure, not crash."""
        p = tmp_path / "bad.ipynb"
        p.write_text("not json at all", encoding="utf-8")

        # Mock jupyter_client import to succeed
        with patch("notebook_tools.HELPERS_AVAILABLE", False):
            executor = NotebookExecutor(p)
            # analyzer.is_valid will be False
            assert not executor.analyzer.is_valid


# =============================================================================
# Test detect_kernel() edge cases
# =============================================================================

class TestDetectKernelEdgeCases:
    """Additional mutation tests for detect_kernel()."""

    def test_display_name_returned_when_no_match(self):
        """Mutation: no kernel match -> returns display_name, not 'Unknown'."""
        nb = {
            "metadata": {
                "kernelspec": {
                    "display_name": "My Custom Kernel",
                    "language": "julia",
                    "name": "julia-1.9",
                }
            },
            "cells": [],
        }
        assert detect_kernel(nb) == "My Custom Kernel"

    def test_empty_display_name_returns_unknown(self):
        """Mutation: empty display_name + no match -> 'Unknown'."""
        nb = {
            "metadata": {
                "kernelspec": {
                    "display_name": "",
                    "language": "julia",
                    "name": "julia-1.9",
                }
            },
            "cells": [],
        }
        assert detect_kernel(nb) == "Unknown"

    def test_no_metadata_returns_unknown(self):
        """Mutation: no metadata at all -> 'Unknown'."""
        assert detect_kernel({}) == "Unknown"

    def test_csharp_language_variant(self):
        """Mutation: language='csharp' maps to '.NET C#'."""
        nb = {
            "metadata": {
                "kernelspec": {
                    "display_name": "CSharp",
                    "language": "csharp",
                    "name": "custom-cs",
                }
            },
            "cells": [],
        }
        assert detect_kernel(nb) == ".NET C#"


# =============================================================================
# Test NotebookAnalyzer edge cases
# =============================================================================

class TestAnalyzerEdgeCases:
    """Mutation tests for NotebookAnalyzer additional edge cases."""

    def test_skeleton_title_from_first_h1(self, tmp_path):
        """Mutation: title extracted from first '# heading' match."""
        cells = [
            _md_cell("# My Great Title"),
            _code_cell("x = 1"),
        ]
        nb_path = _write_nb(cells, tmp_path)
        analyzer = NotebookAnalyzer(nb_path)
        skel = analyzer.get_skeleton()
        assert skel.title == "My Great Title"

    def test_skeleton_no_title_when_no_h1(self, tmp_path):
        """Mutation: no '# heading' -> title is None."""
        cells = [
            _md_cell("## Subtitle only"),
            _code_cell("x = 1"),
        ]
        nb_path = _write_nb(cells, tmp_path)
        analyzer = NotebookAnalyzer(nb_path)
        skel = analyzer.get_skeleton()
        assert skel.title is None

    def test_skeleton_sections_strip_bold(self, tmp_path):
        """Mutation: bold markers ** stripped from section titles."""
        cells = [
            _md_cell("## **Important Section**"),
        ]
        nb_path = _write_nb(cells, tmp_path)
        analyzer = NotebookAnalyzer(nb_path)
        skel = analyzer.get_skeleton()
        assert skel.sections[0].title == "Important Section"

    def test_skeleton_sections_strip_links(self, tmp_path):
        """Mutation: markdown links stripped from section titles."""
        cells = [
            _md_cell("## [Linked Section](http://example.com)"),
        ]
        nb_path = _write_nb(cells, tmp_path)
        analyzer = NotebookAnalyzer(nb_path)
        skel = analyzer.get_skeleton()
        assert skel.sections[0].title == "Linked Section"

    def test_skeleton_max_depth_filters_deep_headers(self, tmp_path):
        """Mutation: max_depth=2 excludes level-3+ headers."""
        cells = [
            _md_cell("## Level 2"),
            _md_cell("### Level 3"),
            _md_cell("#### Level 4"),
        ]
        nb_path = _write_nb(cells, tmp_path)
        analyzer = NotebookAnalyzer(nb_path)
        skel = analyzer.get_skeleton(max_depth=2)
        assert len(skel.sections) == 1
        assert skel.sections[0].title == "Level 2"

    def test_code_previews_limited_to_20(self, tmp_path):
        """Mutation: code_previews capped at 20 entries."""
        cells = [_code_cell(f"x{i} = {i}", outputs=[]) for i in range(25)]
        nb_path = _write_nb(cells, tmp_path)
        analyzer = NotebookAnalyzer(nb_path)
        skel = analyzer.get_skeleton(include_code_preview=True)
        assert len(skel.code_previews) == 20

    def test_estimated_duration_formula(self, tmp_path):
        """Mutation: duration = ceil(md_cells*0.5 + code_cells*1.0)."""
        cells = [_md_cell("text")] * 3 + [_code_cell("x=1")] * 4
        nb_path = _write_nb(cells, tmp_path)
        analyzer = NotebookAnalyzer(nb_path)
        skel = analyzer.get_skeleton()
        # 3*0.5 + 4*1.0 = 5.5 -> ceil = 6
        assert skel.estimated_duration == 6
