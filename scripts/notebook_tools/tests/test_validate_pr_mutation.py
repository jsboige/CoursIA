"""Mutation-resistant tests for validate_pr_notebooks.py.

These tests target code paths and boundary conditions that a mutation testing
tool would exploit. Each test is designed so that if the implementation is
mutated (boundary changed, condition flipped, operator replaced), the test
fails — proving the test suite catches the regression.

Covers:
- skip_exec logic (kernel + QC path OR-combination)
- Advisory vs hard-fail on error outputs (H.1 severity)
- get_kernel_name defaults and error handling
- get_changed_notebooks path filtering
- total_code counting (empty, comment-only, real code)
- main() exit codes and report output
- Edge: multiple C.1 violations in one cell
- Edge: execution_count=0 (valid int, not None)
- Edge: mixed skip-exec kernels
"""

import json
import subprocess
import sys
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from validate_pr_notebooks import (
    get_changed_notebooks,
    get_kernel_name,
    main,
    validate_notebook,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _write_nb(cells, tmp_path, name="test.ipynb", kernel="python3"):
    """Write a notebook dict to a temp file and return its Path."""
    nb = {
        "cells": cells,
        "metadata": {"kernelspec": {"name": kernel}},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    p = tmp_path / name
    p.write_text(json.dumps(nb), encoding="utf-8")
    return p


def _code(source, execution_count=1, outputs=None):
    """Build an executed code cell."""
    if isinstance(source, str):
        source = [source + "\n"]
    return {
        "cell_type": "code",
        "source": source,
        "execution_count": execution_count,
        "outputs": outputs or [],
    }


# ---------------------------------------------------------------------------
# Mutation test: skip_exec OR-combination (kernel OR path)
# ---------------------------------------------------------------------------


class TestSkipExecOrCombination:
    """If either condition is true, skip_exec must be True.

    A mutation swapping `or` to `and` would make these fail.
    """

    def test_dotnet_kernel_skips_exec(self, tmp_path):
        """Kernel in SKIP_EXEC_KERNELS → H.3 skipped."""
        cell = {
            "cell_type": "code",
            "source": ["print('hi')\n"],
            "execution_count": None,
            "outputs": [],
        }
        nb = _write_nb([cell], tmp_path, kernel=".net-csharp")
        result = validate_notebook(nb)
        # H.3 not flagged (kernel skip)
        assert result["passed"]
        h3_errors = [e for e in result["errors"] if "H.3" in e]
        assert h3_errors == []

    def test_qc_cloud_path_skips_exec(self, tmp_path):
        """Path in QC_CLOUD_PATHS → H.3 skipped, even with python3 kernel."""
        cell = {
            "cell_type": "code",
            "source": ["qb = QuantBook()\n"],
            "execution_count": None,
            "outputs": [],
        }
        qc_dir = tmp_path / "QuantConnect" / "Python"
        qc_dir.mkdir(parents=True)
        nb = _write_nb([cell], qc_dir, name="test.ipynb", kernel="python3")
        result = validate_notebook(nb)
        assert result["passed"]
        h3_errors = [e for e in result["errors"] if "H.3" in e]
        assert h3_errors == []

    def test_normal_kernel_normal_path_does_not_skip(self, tmp_path):
        """python3 kernel + normal path → H.3 NOT skipped."""
        cell = {
            "cell_type": "code",
            "source": ["print('hi')\n"],
            "execution_count": None,
            "outputs": [],
        }
        nb = _write_nb([cell], tmp_path, kernel="python3")
        result = validate_notebook(nb)
        assert not result["passed"]
        h3_errors = [e for e in result["errors"] if "H.3" in e]
        assert len(h3_errors) == 1


# ---------------------------------------------------------------------------
# Mutation test: H.1 advisory vs hard-fail boundary
# ---------------------------------------------------------------------------


class TestH1AdvisoryVsHardFail:
    """Error output with skip_exec = advisory; without = hard fail.

    A mutation removing the skip_exec branch check would conflate the two.
    """

    def test_error_hard_fail_python3(self, tmp_path):
        """Error output on python3 → passed=False."""
        cell = {
            "cell_type": "code",
            "source": ["raise ValueError\n"],
            "execution_count": 1,
            "outputs": [{"output_type": "error", "ename": "ValueError", "evalue": "x"}],
        }
        nb = _write_nb([cell], tmp_path, kernel="python3")
        result = validate_notebook(nb)
        assert not result["passed"]

    def test_error_advisory_dotnet(self, tmp_path):
        """Error output on .net-csharp → advisory only, passed=True."""
        cell = {
            "cell_type": "code",
            "source": ["invalid\n"],
            "execution_count": 1,
            "outputs": [{"output_type": "error", "ename": "SyntaxError", "evalue": "x"}],
        }
        nb = _write_nb([cell], tmp_path, kernel=".net-csharp")
        result = validate_notebook(nb)
        assert result["passed"]
        # But advisory message still present
        assert any("advisory" in e for e in result["errors"])

    def test_error_advisory_qc_cloud(self, tmp_path):
        """Error output in QC Cloud path → advisory only."""
        cell = {
            "cell_type": "code",
            "source": ["qb = QuantBook()\n"],
            "execution_count": 1,
            "outputs": [{"output_type": "error", "ename": "NameError", "evalue": "x"}],
        }
        qc_dir = tmp_path / "QuantConnect" / "projects"
        qc_dir.mkdir(parents=True)
        nb = _write_nb([cell], qc_dir, name="test.ipynb", kernel="python3")
        result = validate_notebook(nb)
        assert result["passed"]


# ---------------------------------------------------------------------------
# Mutation test: get_kernel_name defaults and error handling
# ---------------------------------------------------------------------------


class TestGetKernelName:
    """Tests that mutations to default values or error handling are caught."""

    def test_missing_kernelspec_defaults_to_python3(self, tmp_path):
        """No kernelspec → default 'python3'."""
        nb_data = {
            "cells": [],
            "metadata": {},
            "nbformat": 4,
            "nbformat_minor": 5,
        }
        p = tmp_path / "test.ipynb"
        p.write_text(json.dumps(nb_data), encoding="utf-8")
        assert get_kernel_name(p) == "python3"

    def test_invalid_json_returns_unknown(self, tmp_path):
        """Malformed JSON → 'unknown'."""
        p = tmp_path / "bad.ipynb"
        p.write_text("{not json}", encoding="utf-8")
        assert get_kernel_name(p) == "unknown"

    def test_valid_kernel_returned(self, tmp_path):
        """Valid kernelspec name is returned exactly."""
        nb_data = {
            "cells": [],
            "metadata": {"kernelspec": {"name": ".net-csharp"}},
            "nbformat": 4,
            "nbformat_minor": 5,
        }
        p = tmp_path / "test.ipynb"
        p.write_text(json.dumps(nb_data), encoding="utf-8")
        assert get_kernel_name(p) == ".net-csharp"

    def test_kernelspec_no_name_defaults(self, tmp_path):
        """kernelspec exists but no 'name' key → default 'python3'."""
        nb_data = {
            "cells": [],
            "metadata": {"kernelspec": {"display_name": "Python 3"}},
            "nbformat": 4,
            "nbformat_minor": 5,
        }
        p = tmp_path / "test.ipynb"
        p.write_text(json.dumps(nb_data), encoding="utf-8")
        assert get_kernel_name(p) == "python3"


# ---------------------------------------------------------------------------
# Mutation test: execution_count=0 (valid int)
# ---------------------------------------------------------------------------


class TestExecCountZero:
    """execution_count=0 is a valid integer, must NOT be treated as None."""

    def test_exec_count_zero_passes_h3(self, tmp_path):
        """0 is not None — H.3 must pass."""
        cell = {
            "cell_type": "code",
            "source": ["x = 1\n"],
            "execution_count": 0,
            "outputs": [],
        }
        nb = _write_nb([cell], tmp_path)
        result = validate_notebook(nb)
        h3 = [e for e in result["errors"] if "H.3" in e]
        assert h3 == []


# ---------------------------------------------------------------------------
# Mutation test: multiple C.1 violations in single cell
# ---------------------------------------------------------------------------


class TestMultipleC1InOneCell:
    """One cell with both raise NotImplementedError and assert False."""

    def test_both_patterns_flagged(self, tmp_path):
        """Both violations must appear in errors."""
        cell = _code("raise NotImplementedError\nassert False\n")
        nb = _write_nb([cell], tmp_path)
        result = validate_notebook(nb)
        c1 = [e for e in result["errors"] if "C.1" in e]
        assert len(c1) == 2


# ---------------------------------------------------------------------------
# Mutation test: total_code counting accuracy
# ---------------------------------------------------------------------------


class TestTotalCodeCounting:
    """Verify total_code counts only real code cells (not empty/comment-only)."""

    def test_mixed_cells_counted_correctly(self, tmp_path):
        cells = [
            {"cell_type": "code", "source": ["print('a')\n"], "execution_count": 1, "outputs": []},
            {"cell_type": "code", "source": [""], "execution_count": None, "outputs": []},  # empty
            {"cell_type": "markdown", "source": ["# Title\n"]},
            {"cell_type": "code", "source": ["# comment only\n"], "execution_count": None, "outputs": []},
            {"cell_type": "code", "source": ["x = 42\n"], "execution_count": 2, "outputs": []},
        ]
        nb = _write_nb(cells, tmp_path)
        result = validate_notebook(nb)
        # Only cells 0 and 4 are real code
        assert result["total_code"] == 2

    def test_no_code_cells_total_zero(self, tmp_path):
        nb = _write_nb(
            [{"cell_type": "markdown", "source": ["# Title\n"]}],
            tmp_path,
        )
        result = validate_notebook(nb)
        assert result["total_code"] == 0


# ---------------------------------------------------------------------------
# Mutation test: get_changed_notebooks path filtering
# ---------------------------------------------------------------------------


class TestGetChangedNotebooks:
    """Verify .ipynb filtering and existence check."""

    def test_only_ipynb_returned(self, tmp_path):
        """Non-.ipynb files are filtered out."""
        py_file = tmp_path / "script.py"
        py_file.write_text("print('hi')", encoding="utf-8")
        nb_file = tmp_path / "test.ipynb"
        nb_file.write_text("{}", encoding="utf-8")
        result = get_changed_notebooks("origin/main", [str(py_file), str(nb_file)])
        assert len(result) == 1
        assert result[0].suffix == ".ipynb"

    def test_nonexistent_files_filtered(self, tmp_path):
        """Paths that don't exist on disk are excluded."""
        result = get_changed_notebooks(
            "origin/main",
            [str(tmp_path / "nonexistent.ipynb")],
        )
        assert result == []

    def test_git_diff_called_when_no_paths(self):
        """Without explicit paths, git diff is invoked."""
        with patch("validate_pr_notebooks.subprocess.run") as mock_run:
            # Return a path that exists on disk so the filter passes
            nb_path = Path(__file__).resolve().parent.parent.parent / "MyIA.AI.Notebooks" / "Search" / "Part1-Foundations" / "Search-1-Introduction.ipynb"
            mock_run.return_value = MagicMock(
                stdout=str(nb_path) + "\n", stderr=""
            )
            result = get_changed_notebooks("origin/main")
            mock_run.assert_called_once()
            if nb_path.exists():
                assert len(result) >= 1
            else:
                # Path doesn't exist in this checkout — just verify git diff was called
                assert mock_run.called

    def test_git_diff_failure_returns_empty(self):
        """git diff failure returns empty list (not crash)."""
        with patch("validate_pr_notebooks.subprocess.run") as mock_run:
            mock_run.side_effect = subprocess.CalledProcessError(1, "git", stderr="error")
            result = get_changed_notebooks("origin/main")
            assert result == []


# ---------------------------------------------------------------------------
# Mutation test: main() exit codes
# ---------------------------------------------------------------------------


class TestMainExitCodes:
    """Verify main() returns correct exit codes: 0 pass, 1 fail."""

    def test_main_returns_1_on_failure(self, tmp_path):
        """A notebook with violations → exit code 1."""
        cell = {
            "cell_type": "code",
            "source": ["raise NotImplementedError\n"],
            "execution_count": 1,
            "outputs": [],
        }
        p = _write_nb([cell], tmp_path)
        with patch("sys.argv", ["validate_pr_notebooks.py", "origin/main", str(p)]):
            exit_code = main()
        assert exit_code == 1

    def test_main_returns_0_on_pass(self, tmp_path):
        """A clean notebook → exit code 0."""
        cell = _code("x = 1\nprint(x)")
        p = _write_nb([cell], tmp_path)
        with patch("sys.argv", ["validate_pr_notebooks.py", "origin/main", str(p)]):
            exit_code = main()
        assert exit_code == 0

    def test_main_returns_0_no_notebooks(self):
        """No notebooks changed → exit code 0 (not error)."""
        with patch("sys.argv", ["validate_pr_notebooks.py", "origin/main"]):
            with patch(
                "validate_pr_notebooks.get_changed_notebooks", return_value=[]
            ):
                exit_code = main()
        assert exit_code == 0

    def test_main_json_output(self, tmp_path):
        """--json flag produces valid JSON with correct structure."""
        cell = _code("x = 1\n")
        p = _write_nb([cell], tmp_path)
        with patch("sys.argv", ["validate_pr_notebooks.py", "--json", "origin/main", str(p)]):
            with patch("builtins.print") as mock_print:
                exit_code = main()
            # Extract the JSON string that was printed
            json_arg = mock_print.call_args[0][0]
            data = json.loads(json_arg)
            assert "notebooks" in data
            assert "passed" in data
            assert data["passed"] is True


# ---------------------------------------------------------------------------
# Mutation test: JSON parse error in validate_notebook
# ---------------------------------------------------------------------------


class TestJsonParseError:
    """Malformed notebook file must be caught gracefully."""

    def test_json_parse_error_sets_passed_false(self, tmp_path):
        p = tmp_path / "broken.ipynb"
        p.write_text("{not valid json}", encoding="utf-8")
        result = validate_notebook(p)
        assert not result["passed"]
        assert any("Cannot parse JSON" in e for e in result["errors"])


# ---------------------------------------------------------------------------
# Mutation test: Windows path backslash normalization for QC paths
# ---------------------------------------------------------------------------


class TestWindowsPathNormalization:
    """QC Cloud path check must work with Windows backslashes."""

    def test_backslash_qc_path_detected(self, tmp_path):
        """On Windows, rel_path may contain \\ — must still detect QC Cloud."""
        cell = {
            "cell_type": "code",
            "source": ["print('qc')\n"],
            "execution_count": None,
            "outputs": [],
        }
        qc_dir = tmp_path / "QuantConnect" / "Python"
        qc_dir.mkdir(parents=True)
        nb = _write_nb([cell], qc_dir, kernel="python3")
        result = validate_notebook(nb)
        # QC Cloud path → skip_exec → H.3 not flagged
        h3 = [e for e in result["errors"] if "H.3" in e]
        assert h3 == []


# ---------------------------------------------------------------------------
# Mutation test: mixed outputs (stream + error in same cell)
# ---------------------------------------------------------------------------


class TestMixedOutputs:
    """Cell with both stream and error outputs → error takes precedence for H.1."""

    def test_stream_and_error_flags_h1(self, tmp_path):
        cell = {
            "cell_type": "code",
            "source": ["x = 1\n"],
            "execution_count": 1,
            "outputs": [
                {"output_type": "stream", "text": "ok\n"},
                {"output_type": "error", "ename": "RuntimeError", "evalue": "boom"},
            ],
        }
        nb = _write_nb([cell], tmp_path)
        result = validate_notebook(nb)
        assert not result["passed"]
        assert any("error output" in e for e in result["errors"])


# ---------------------------------------------------------------------------
# Mutation test: validate_notebook returns correct structure
# ---------------------------------------------------------------------------


class TestResultStructure:
    """Verify the result dict has all expected keys."""

    def test_result_keys(self, tmp_path):
        cell = _code("x = 1\nprint(x)")
        nb = _write_nb([cell], tmp_path)
        result = validate_notebook(nb)
        assert "path" in result
        assert "kernel" in result
        assert "total_code" in result
        assert "passed" in result
        assert "errors" in result
        assert isinstance(result["errors"], list)

    def test_passed_bool_not_int(self, tmp_path):
        """passed must be bool, not 0/1 (mutation: `passed = 0` survives)."""
        cell = _code("x = 1\n")
        nb = _write_nb([cell], tmp_path)
        result = validate_notebook(nb)
        assert result["passed"] is True
        assert isinstance(result["passed"], bool)
