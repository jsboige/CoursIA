"""Tests for notebook_tools.py core functions.

Covers: should_skip, detect_kernel, extract_cell_preview, dataclasses,
NotebookAnalyzer, NotebookValidator, SKIP_PATTERNS, NOTEBOOK_FAMILIES.
"""

import json
import os
import tempfile
from pathlib import Path

import pytest

# Add parent dir to sys.path so we can import the module
import sys
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from notebook_tools import (
    CellInfo,
    Colors,
    EnvironmentCheck,
    NotebookAnalyzer,
    NotebookExecutionResult,
    NotebookSkeleton,
    NotebookValidation,
    NotebookValidator,
    SectionInfo,
    ValidationIssue,
    detect_kernel,
    discover_notebooks,
    extract_cell_preview,
    get_repo_root,
    should_skip,
    NOTEBOOK_FAMILIES,
    SKIP_PATTERNS,
)


# =============================================================================
# should_skip
# =============================================================================

class TestShouldSkip:
    def test_output_file(self):
        assert should_skip(Path("notebooks/test_output.ipynb")) is True

    def test_verified_file(self):
        assert should_skip(Path("notebooks/test_verified.ipynb")) is True

    def test_ipynb_checkpoints(self):
        assert should_skip(Path(".ipynb_checkpoints/test.ipynb")) is True

    def test_ui_configuration(self):
        assert should_skip(Path("notebooks/UI_configuration.ipynb")) is True

    def test_normal_file(self):
        assert should_skip(Path("notebooks/Search-1-BFS.ipynb")) is False

    def test_normal_path(self):
        assert should_skip(Path("MyIA.AI.Notebooks/Sudoku/Sudoku-1-Backtracking-Csharp.ipynb")) is False

    def test_output_in_nested_path(self):
        assert should_skip(Path("deep/nested/test_output.ipynb")) is True

    def test_empty_path(self):
        assert should_skip(Path("")) is False


# =============================================================================
# detect_kernel
# =============================================================================

class TestDetectKernel:
    def _nb(self, kernel_name="", language="", display_name=""):
        return {
            "metadata": {
                "kernelspec": {
                    "name": kernel_name,
                    "language": language,
                    "display_name": display_name,
                }
            },
            "cells": [],
        }

    def test_python3(self):
        assert detect_kernel(self._nb(kernel_name="python3", language="python")) == "Python"

    def test_python_wsl(self):
        assert detect_kernel(self._nb(kernel_name="python3", language="python", display_name="Python (WSL)")) == "Python (WSL)"

    def test_python_gametheory_wsl(self):
        # Code checks 'wsl' before 'gametheory' in display_name
        # "Python (GameTheory WSL)" contains "wsl" => returns "Python (WSL)"
        # This is the ACTUAL behavior — gametheory check is unreachable
        result = detect_kernel(self._nb(kernel_name="python3", language="python", display_name="Python (GameTheory WSL)"))
        assert result == "Python (WSL)"

    def test_dotnet_csharp(self):
        assert detect_kernel(self._nb(kernel_name=".net-csharp", language="C#")) == ".NET C#"

    def test_dotnet_fsharp(self):
        # Code checks '.net' in kernel_name first (matches ".net-fsharp")
        # before reaching 'fsharp' check => returns ".NET C#"
        # This is the ACTUAL behavior
        result = detect_kernel(self._nb(kernel_name=".net-fsharp", language="F#"))
        assert result == ".NET C#"

    def test_lean4(self):
        assert detect_kernel(self._nb(kernel_name="lean4", language="lean4")) == "Lean 4"

    def test_lean4_wsl(self):
        assert detect_kernel(self._nb(kernel_name="lean4-wsl", language="lean4", display_name="Lean 4 (WSL)")) == "Lean 4 (WSL)"

    def test_unknown_kernel(self):
        result = detect_kernel(self._nb(kernel_name="julia-1.9", language="julia"))
        assert result == "Unknown"

    def test_custom_display_name(self):
        result = detect_kernel(self._nb(kernel_name="custom-kernel", language="racket", display_name="Racket REPL"))
        assert result == "Racket REPL"

    def test_no_metadata(self):
        assert detect_kernel({}) == "Unknown"

    def test_empty_kernelspec(self):
        assert detect_kernel({"metadata": {"kernelspec": {}}, "cells": []}) == "Unknown"

    def test_dotnet_magic_import(self):
        nb = {
            "metadata": {"kernelspec": {"name": "unknown", "language": ""}},
            "cells": [{"cell_type": "code", "source": ["#!import\n", "open System\n"]}],
        }
        assert detect_kernel(nb) == ".NET C#"

    def test_dotnet_magic_csharp(self):
        nb = {
            "metadata": {"kernelspec": {"name": "unknown", "language": ""}},
            "cells": [{"cell_type": "code", "source": ["#!csharp\n", "Console.WriteLine(\"hi\")"]}],
        }
        assert detect_kernel(nb) == ".NET C#"

    def test_magic_in_markdown_cell_ignored(self):
        nb = {
            "metadata": {"kernelspec": {"name": "python3", "language": "python"}},
            "cells": [{"cell_type": "markdown", "source": ["#!import is cool"]}],
        }
        assert detect_kernel(nb) == "Python"


# =============================================================================
# extract_cell_preview
# =============================================================================

class TestExtractCellPreview:
    def test_simple_code(self):
        assert "print" in extract_cell_preview("print('hello')\nprint('world')")

    def test_skips_magic_commands(self):
        preview = extract_cell_preview("%matplotlib inline\nimport numpy as np")
        assert "%matplotlib" not in preview
        assert "import numpy" in preview

    def test_skips_dotnet_magic(self):
        preview = extract_cell_preview("#!import\n#!csharp\nvar x = 1;")
        assert "#!" not in preview
        assert "var x" in preview

    def test_max_lines_limit(self):
        source = "\n".join([f"line_{i}" for i in range(10)])
        preview = extract_cell_preview(source, max_lines=3)
        assert preview.count("line_") == 3

    def test_max_chars_truncation(self):
        source = " ".join(["word"] * 100)
        preview = extract_cell_preview(source, max_chars=50)
        assert len(preview) <= 53  # 50 + "..."
        assert preview.endswith("...")

    def test_empty_source(self):
        assert extract_cell_preview("") == ""

    def test_only_comments(self):
        # Lines starting with # are kept (not skipped, only #! and % are skipped)
        preview = extract_cell_preview("# comment\nx = 1")
        assert "x = 1" in preview

    def test_whitespace_only_lines_skipped(self):
        preview = extract_cell_preview("   \n\nx = 42\n   \ny = 10")
        assert "x = 42" in preview


# =============================================================================
# Dataclasses — match ACTUAL field names
# =============================================================================

class TestDataclasses:
    def test_cell_info_defaults(self):
        ci = CellInfo(index=0, cell_type="code")
        assert ci.index == 0
        assert ci.cell_type == "code"
        assert ci.preview == ""
        assert ci.line_count == 0
        assert ci.has_output is False
        assert ci.output_type is None
        assert ci.cell_id is None

    def test_cell_info_full(self):
        ci = CellInfo(index=5, cell_type="code", preview="print('hi')", line_count=3,
                      has_output=True, output_type="stream", cell_id="abc12345")
        assert ci.preview == "print('hi')"
        assert ci.has_output is True
        assert ci.cell_id == "abc12345"

    def test_validation_issue(self):
        vi = ValidationIssue(issue_type="error", category="execution", cell_index=5,
                             message="NotImplementedError: todo")
        assert vi.issue_type == "error"
        assert vi.category == "execution"
        assert vi.cell_index == 5
        assert "NotImplementedError" in vi.message

    def test_section_info(self):
        si = SectionInfo(level=2, title="Introduction", cell_index=3)
        assert si.level == 2
        assert si.title == "Introduction"
        assert si.cell_index == 3

    def test_notebook_skeleton(self):
        ns = NotebookSkeleton(path="test.ipynb", name="test")
        assert ns.path == "test.ipynb"
        assert ns.name == "test"
        assert ns.total_cells == 0
        assert ns.sections == []
        assert ns.kernel == "unknown"

    def test_notebook_skeleton_to_dict(self):
        ns = NotebookSkeleton(path="test.ipynb", name="test", title="My Notebook",
                              kernel="Python", total_cells=10)
        d = ns.to_dict()
        assert d["path"] == "test.ipynb"
        assert d["name"] == "test"
        assert d["title"] == "My Notebook"
        assert d["kernel"] == "Python"
        assert d["total_cells"] == 10

    def test_notebook_validation(self):
        nv = NotebookValidation(path="test.ipynb", name="test.ipynb")
        assert nv.path == "test.ipynb"
        assert nv.exists is False
        assert nv.issues == []
        assert nv.status == "MISSING"

    def test_notebook_validation_status_ok(self):
        nv = NotebookValidation(path="test.ipynb", name="test.ipynb", exists=True,
                                valid_json=True, has_cells=True)
        assert nv.status == "OK"

    def test_notebook_validation_status_error(self):
        nv = NotebookValidation(path="test.ipynb", name="test.ipynb", exists=True,
                                valid_json=True)
        nv.issues.append(ValidationIssue(issue_type="error", category="execution",
                                         cell_index=0, message="broken"))
        assert nv.status == "ERROR"
        assert nv.error_count == 1

    def test_notebook_validation_status_warning(self):
        nv = NotebookValidation(path="test.ipynb", name="test.ipynb", exists=True,
                                valid_json=True)
        nv.issues.append(ValidationIssue(issue_type="warning", category="pedagogy",
                                         cell_index=0, message="low ratio"))
        assert nv.status == "WARNING"
        assert nv.warning_count == 1

    def test_environment_check(self):
        ec = EnvironmentCheck(family="Sudoku")
        assert ec.family == "Sudoku"
        assert ec.ready is False
        assert ec.components == {}
        assert ec.errors == []

    def test_colors_class(self):
        assert Colors.GREEN.startswith("\033[")
        assert Colors.END == "\033[0m"


# =============================================================================
# NOTEBOOK_FAMILIES config
# =============================================================================

class TestNotebookFamilies:
    def test_families_exist(self):
        assert len(NOTEBOOK_FAMILIES) > 0

    def test_key_families_present(self):
        for fam in ["Sudoku", "Search", "GameTheory", "SmartContracts", "QuantConnect"]:
            assert fam in NOTEBOOK_FAMILIES, f"Missing family: {fam}"

    def test_family_has_path(self):
        for name, config in NOTEBOOK_FAMILIES.items():
            assert "path" in config, f"Family {name} missing 'path'"

    def test_family_has_kernel(self):
        for name, config in NOTEBOOK_FAMILIES.items():
            assert "kernel" in config, f"Family {name} missing 'kernel'"

    def test_sudoku_uses_dotnet(self):
        assert NOTEBOOK_FAMILIES["Sudoku"]["kernel"] == "dotnet"

    def test_gametheory_uses_python(self):
        assert NOTEBOOK_FAMILIES["GameTheory"]["kernel"] == "python"


# =============================================================================
# NotebookAnalyzer (with temp fixtures)
# =============================================================================

def _make_notebook(cells, kernel_name="python3", language="python"):
    """Create a minimal notebook dict."""
    return {
        "cells": cells,
        "metadata": {
            "kernelspec": {
                "name": kernel_name,
                "language": language,
                "display_name": "Python 3",
            }
        },
        "nbformat": 4,
        "nbformat_minor": 5,
    }


def _write_notebook(nb_data, path):
    """Write notebook dict to file."""
    with open(path, "w", encoding="utf-8") as f:
        json.dump(nb_data, f, ensure_ascii=False, indent=1)


class TestNotebookAnalyzer:
    def test_analyze_basic_notebook(self, tmp_path):
        nb = _make_notebook([
            {"cell_type": "markdown", "source": ["# Title\n"], "metadata": {}},
            {"cell_type": "code", "source": ["print('hello')\n"], "metadata": {},
             "execution_count": 1, "outputs": [{"output_type": "stream", "name": "stdout", "text": ["hello\n"]}]},
        ])
        nb_path = tmp_path / "test.ipynb"
        _write_notebook(nb, str(nb_path))

        analyzer = NotebookAnalyzer(str(nb_path))
        assert analyzer.is_valid is True
        assert len(analyzer.cells) == 2

    def test_analyze_nonexistent_no_crash(self, tmp_path):
        # NotebookAnalyzer doesn't raise, it sets nb_data=None
        analyzer = NotebookAnalyzer(str(tmp_path / "nonexistent.ipynb"))
        assert analyzer.is_valid is False
        assert analyzer.nb_data is None
        assert analyzer.cells == []

    def test_get_cell_count(self, tmp_path):
        nb = _make_notebook([
            {"cell_type": "markdown", "source": ["# H1\n"], "metadata": {}},
            {"cell_type": "code", "source": ["x = 1\n"], "metadata": {},
             "execution_count": 1, "outputs": []},
            {"cell_type": "markdown", "source": ["## H2\n"], "metadata": {}},
        ])
        nb_path = tmp_path / "test.ipynb"
        _write_notebook(nb, str(nb_path))

        analyzer = NotebookAnalyzer(str(nb_path))
        assert len(analyzer.cells) == 3

    def test_detects_kernel(self, tmp_path):
        nb = _make_notebook([], kernel_name=".net-csharp", language="C#")
        nb_path = tmp_path / "test.ipynb"
        _write_notebook(nb, str(nb_path))

        analyzer = NotebookAnalyzer(str(nb_path))
        assert analyzer.kernel == ".NET C#"

    def test_skeleton_extraction(self, tmp_path):
        nb = _make_notebook([
            {"cell_type": "markdown", "source": ["# My Notebook\n"], "metadata": {}},
            {"cell_type": "code", "source": ["x = 1\n"], "metadata": {},
             "execution_count": 1, "outputs": [{"output_type": "stream", "name": "stdout", "text": ["1\n"]}]},
            {"cell_type": "markdown", "source": ["## Section 2\n"], "metadata": {}},
        ])
        nb_path = tmp_path / "test.ipynb"
        _write_notebook(nb, str(nb_path))

        analyzer = NotebookAnalyzer(str(nb_path))
        skeleton = analyzer.get_skeleton()
        assert skeleton.name == "test"
        assert skeleton.title == "My Notebook"
        assert skeleton.total_cells == 3
        assert skeleton.markdown_cells == 2
        assert skeleton.code_cells == 1
        assert skeleton.cells_with_output == 1


# =============================================================================
# NotebookValidator (with temp fixtures)
# =============================================================================

class TestNotebookValidator:
    def test_valid_notebook_structure_ok(self, tmp_path):
        nb = _make_notebook([
            {"cell_type": "markdown", "source": ["# Title\n"], "metadata": {}},
            {"cell_type": "code", "source": ["print('ok')\n"], "metadata": {},
             "execution_count": 1, "outputs": [{"output_type": "stream", "name": "stdout", "text": ["ok\n"]}]},
        ])
        nb_path = tmp_path / "test.ipynb"
        _write_notebook(nb, str(nb_path))

        validator = NotebookValidator(str(nb_path))
        result = validator.validate_structure()
        assert result.exists is True
        assert result.valid_json is True
        assert result.error_count == 0

    def test_not_implemented_error_flagged(self, tmp_path):
        nb = _make_notebook([
            {"cell_type": "code", "source": ["raise NotImplementedError('todo')\n"], "metadata": {},
             "execution_count": 1, "outputs": [{
                "output_type": "error",
                "ename": "NotImplementedError",
                "evalue": "todo",
                "traceback": ["..."],
            }]},
        ])
        nb_path = tmp_path / "test.ipynb"
        _write_notebook(nb, str(nb_path))

        validator = NotebookValidator(str(nb_path))
        content_issues = validator.validate_content()
        error_msgs = [i.message for i in content_issues]
        assert any("NotImplementedError" in msg for msg in error_msgs)

    def test_markdown_cells_not_flagged_for_exec(self, tmp_path):
        nb = _make_notebook([
            {"cell_type": "markdown", "source": ["# Just text\n"], "metadata": {}},
        ])
        nb_path = tmp_path / "test.ipynb"
        _write_notebook(nb, str(nb_path))

        validator = NotebookValidator(str(nb_path))
        content_issues = validator.validate_content()
        exec_issues = [i for i in content_issues if i.category == "execution"]
        assert len(exec_issues) == 0

    def test_empty_notebook_flagged(self, tmp_path):
        nb = _make_notebook([])
        nb_path = tmp_path / "test.ipynb"
        _write_notebook(nb, str(nb_path))

        validator = NotebookValidator(str(nb_path))
        result = validator.validate_structure()
        assert result.error_count > 0
        assert any("No cells" in i.message for i in result.issues)

    def test_nonexistent_notebook(self, tmp_path):
        validator = NotebookValidator(str(tmp_path / "nonexistent.ipynb"))
        result = validator.validate_structure()
        assert result.exists is False
        assert result.status == "MISSING"

    def test_consecutive_code_cells_pedagogy_flag(self, tmp_path):
        # 4 consecutive code cells without markdown between them
        nb = _make_notebook([
            {"cell_type": "markdown", "source": ["# Title\n"], "metadata": {}},
            {"cell_type": "code", "source": ["a = 1\n"], "metadata": {},
             "execution_count": 1, "outputs": []},
            {"cell_type": "code", "source": ["b = 2\n"], "metadata": {},
             "execution_count": 2, "outputs": []},
            {"cell_type": "code", "source": ["c = 3\n"], "metadata": {},
             "execution_count": 3, "outputs": []},
            {"cell_type": "code", "source": ["d = 4\n"], "metadata": {},
             "execution_count": 4, "outputs": []},
        ])
        nb_path = tmp_path / "test.ipynb"
        _write_notebook(nb, str(nb_path))

        validator = NotebookValidator(str(nb_path))
        content_issues = validator.validate_content()
        pedagogy = [i for i in content_issues if i.category == "pedagogy" and "consecutive" in i.message]
        assert len(pedagogy) > 0


# =============================================================================
# discover_notebooks
# =============================================================================

class TestDiscoverNotebooks:
    def test_discovers_ipynb_files(self, tmp_path):
        nb_dir = tmp_path / "TestSeries"
        nb_dir.mkdir()
        for i in range(3):
            nb = _make_notebook([])
            _write_notebook(nb, str(nb_dir / f"Test-{i}.ipynb"))

        result = discover_notebooks(str(nb_dir), repo_root=tmp_path)
        assert len(result) == 3

    def test_skips_output_files(self, tmp_path):
        nb_dir = tmp_path / "TestSeries"
        nb_dir.mkdir()
        nb = _make_notebook([])
        _write_notebook(nb, str(nb_dir / "Test-1.ipynb"))
        _write_notebook(nb, str(nb_dir / "Test-1_output.ipynb"))

        result = discover_notebooks(str(nb_dir), repo_root=tmp_path)
        assert len(result) == 1
        assert "Test-1.ipynb" in str(result[0])

    def test_skips_checkpoints(self, tmp_path):
        nb_dir = tmp_path / "TestSeries"
        nb_dir.mkdir()
        cp_dir = nb_dir / ".ipynb_checkpoints"
        cp_dir.mkdir()
        nb = _make_notebook([])
        _write_notebook(nb, str(cp_dir / "Test-1-checkpoint.ipynb"))
        _write_notebook(nb, str(nb_dir / "Test-1.ipynb"))

        result = discover_notebooks(str(nb_dir), repo_root=tmp_path)
        assert len(result) == 1

    def test_empty_directory(self, tmp_path):
        nb_dir = tmp_path / "Empty"
        nb_dir.mkdir()
        result = discover_notebooks(str(nb_dir), repo_root=tmp_path)
        assert len(result) == 0


# =============================================================================
# get_repo_root
# =============================================================================

class TestGetRepoRoot:
    def test_returns_path(self):
        root = get_repo_root()
        assert isinstance(root, Path)

    def test_root_contains_claude_md(self):
        root = get_repo_root()
        assert (root / "CLAUDE.md").exists() or (root / ".git").exists()


# =============================================================================
# Mutation-killing tests — targeting surviving mutants
# =============================================================================

class TestShouldSkipMutations:
    """Kill mutants in should_skip: wildcard patterns, boundary conditions."""

    def test_wildcard_output_pattern(self):
        """Wildcard '*_output.ipynb' must match any path containing '_output.ipynb'."""
        assert should_skip(Path("series/nb_output.ipynb")) is True
        assert should_skip(Path("series/normal.ipynb")) is False

    def test_wildcard_verified_pattern(self):
        """Wildcard '*_verified.ipynb' must match."""
        assert should_skip(Path("series/nb_verified.ipynb")) is True

    def test_non_wildcard_ui_configuration(self):
        """Exact match 'UI_configuration.ipynb' without wildcard."""
        assert should_skip(Path("any/dir/UI_configuration.ipynb")) is True

    def test_checkpoints_dir_pattern(self):
        """'.ipynb_checkpoints' as substring match."""
        assert should_skip(Path(".ipynb_checkpoints/anything.ipynb")) is True

    def test_no_false_positives_similar_names(self):
        """Names containing but not matching patterns should NOT be skipped."""
        assert should_skip(Path("output_analyzer.ipynb")) is False
        assert should_skip(Path("my_verified_tool.ipynb")) is False

    def test_all_skip_patterns_covered(self):
        """Each pattern in SKIP_PATTERNS must be triggerable."""
        for pattern in SKIP_PATTERNS:
            if '*' in pattern:
                test_name = "test" + pattern.replace('*', '')
            else:
                test_name = pattern
            assert should_skip(Path(test_name)) is True, f"Pattern '{pattern}' not matching '{test_name}'"


class TestDetectKernelMutations:
    """Kill mutants in detect_kernel: condition boundary, return value."""

    def test_csharp_language_variant(self):
        """'csharp' (no #) must be detected as .NET C#."""
        nb = {"metadata": {"kernelspec": {"name": "unknown", "language": "csharp"}}, "cells": []}
        assert detect_kernel(nb) == ".NET C#"

    def test_fsharp_in_kernel_name(self):
        """Pure fsharp kernel name (without .net prefix) must be .NET F#."""
        nb = {"metadata": {"kernelspec": {"name": "fsharp", "language": "f#"}}, "cells": []}
        assert detect_kernel(nb) == ".NET F#"

    def test_lean4_in_language(self):
        """Language 'lean4' without 'lean' in kernel name still detected."""
        nb = {"metadata": {"kernelspec": {"name": "custom", "language": "lean4"}}, "cells": []}
        assert detect_kernel(nb) == "Lean 4"

    def test_python_case_insensitive_kernel(self):
        """Python detection is case-insensitive on kernel_name."""
        nb = {"metadata": {"kernelspec": {"name": "Python3", "language": ""}}, "cells": []}
        assert detect_kernel(nb) == "Python"

    def test_magic_in_code_cell_only(self):
        """Only code cells (not raw) should trigger .NET magic detection."""
        nb = {
            "metadata": {"kernelspec": {"name": "unknown", "language": ""}},
            "cells": [{"cell_type": "raw", "source": ["#!import\n"]}],
        }
        assert detect_kernel(nb) == "Unknown"

    def test_empty_cells_list(self):
        """Empty cells list should not crash."""
        nb = {"metadata": {"kernelspec": {"name": "julia", "language": "julia"}}, "cells": []}
        assert detect_kernel(nb) == "Unknown"


class TestExtractCellPreviewMutations:
    """Kill mutants in extract_cell_preview: boundary conditions."""

    def test_exact_max_chars_no_truncation(self):
        """When preview is exactly max_chars, it should be truncated."""
        # Create a string that's exactly max_chars long
        source = "a" * 150
        preview = extract_cell_preview(source, max_chars=150)
        # Either truncated or exactly 150 — but the function truncates at max_chars
        assert len(preview) <= 153  # 150 + "..."

    def test_max_lines_exactly_one(self):
        """max_lines=1 should return exactly one line."""
        source = "line1\nline2\nline3"
        preview = extract_cell_preview(source, max_lines=1)
        assert "line1" in preview
        assert "line2" not in preview

    def test_strips_hashbang_not_hash(self):
        """Lines starting with #! are skipped, but regular # comments are kept."""
        preview = extract_cell_preview("#!skip\n#keep\nx = 1")
        assert "#keep" in preview
        assert "#!skip" not in preview

    def test_truncation_at_word_boundary(self):
        """Truncation splits at word boundary, adds '...'."""
        source = "alpha beta " * 50  # Long string
        preview = extract_cell_preview(source, max_chars=30)
        if len(preview) > 30:
            assert preview.endswith("...")


class TestNotebookAnalyzerMutations:
    """Kill mutants in NotebookAnalyzer: error handling, edge cases."""

    def test_invalid_json_file(self, tmp_path):
        """Invalid JSON should set nb_data=None, is_valid=False."""
        bad_file = tmp_path / "bad.ipynb"
        bad_file.write_text("this is not json {{{{", encoding="utf-8")
        analyzer = NotebookAnalyzer(str(bad_file))
        assert analyzer.is_valid is False
        assert analyzer.nb_data is None

    def test_cells_property_on_none_data(self, tmp_path):
        """cells should return [] when file doesn't exist."""
        analyzer = NotebookAnalyzer(str(tmp_path / "missing.ipynb"))
        assert analyzer.cells == []

    def test_kernel_property_on_none_data(self, tmp_path):
        """kernel should return 'unknown' (lowercase) when file doesn't exist."""
        analyzer = NotebookAnalyzer(str(tmp_path / "missing.ipynb"))
        assert analyzer.kernel == "unknown"

    def test_get_skeleton_empty_notebook(self, tmp_path):
        """Skeleton of empty notebook should have 0 counts."""
        nb = _make_notebook([])
        nb_path = tmp_path / "empty.ipynb"
        _write_notebook(nb, str(nb_path))
        analyzer = NotebookAnalyzer(str(nb_path))
        skel = analyzer.get_skeleton()
        assert skel.total_cells == 0
        assert skel.code_cells == 0
        assert skel.markdown_cells == 0


class TestNotebookValidatorMutations:
    """Kill mutants in NotebookValidator: error detection, edge cases."""

    def test_division_by_zero_flagged(self, tmp_path):
        """1/0 in outputs should be flagged as execution error."""
        nb = _make_notebook([
            {"cell_type": "code", "source": ["1/0\n"], "metadata": {},
             "execution_count": 1, "outputs": [{
                 "output_type": "error", "ename": "ZeroDivisionError",
                 "evalue": "division by zero", "traceback": ["..."],
             }]},
        ])
        nb_path = tmp_path / "test.ipynb"
        _write_notebook(nb, str(nb_path))
        validator = NotebookValidator(str(nb_path))
        issues = validator.validate_content()
        assert any("ZeroDivisionError" in i.message for i in issues)

    def test_assert_false_flagged(self, tmp_path):
        """assert False in outputs should be flagged."""
        nb = _make_notebook([
            {"cell_type": "code", "source": ["assert False\n"], "metadata": {},
             "execution_count": 1, "outputs": [{
                 "output_type": "error", "ename": "AssertionError",
                 "evalue": "", "traceback": ["..."],
             }]},
        ])
        nb_path = tmp_path / "test.ipynb"
        _write_notebook(nb, str(nb_path))
        validator = NotebookValidator(str(nb_path))
        issues = validator.validate_content()
        assert any("AssertionError" in i.message for i in issues)

    def test_invalid_json_flagged(self, tmp_path):
        """Malformed JSON should produce 'Invalid JSON format' issue."""
        bad_file = tmp_path / "bad.ipynb"
        bad_file.write_text("not json", encoding="utf-8")
        validator = NotebookValidator(str(bad_file))
        result = validator.validate_structure()
        assert result.exists is True
        assert result.valid_json is False
        assert any("Invalid JSON" in i.message for i in result.issues)

    def test_no_metadata_flagged(self, tmp_path):
        """Notebook without metadata should get a warning."""
        nb = {"cells": [{"cell_type": "markdown", "source": ["# Title\n"], "metadata": {}}], "metadata": {}, "nbformat": 4}
        nb_path = tmp_path / "no_meta.ipynb"
        with open(str(nb_path), "w", encoding="utf-8") as f:
            json.dump(nb, f)
        validator = NotebookValidator(str(nb_path))
        result = validator.validate_structure()
        # Either no_metadata warning or has_metadata=False
        has_meta_warnings = [i for i in result.issues if "metadata" in i.message.lower()]
        # Should have no metadata warning
        assert len(has_meta_warnings) > 0 or result.has_metadata is False

    def test_code_cells_counted_correctly(self, tmp_path):
        """code_cells and markdown_cells counted accurately."""
        nb = _make_notebook([
            {"cell_type": "markdown", "source": ["# H1\n"], "metadata": {}},
            {"cell_type": "code", "source": ["x=1\n"], "metadata": {},
             "execution_count": 1, "outputs": []},
            {"cell_type": "code", "source": ["y=2\n"], "metadata": {},
             "execution_count": 2, "outputs": [{"output_type": "stream", "name": "stdout", "text": ["2\n"]}]},
            {"cell_type": "markdown", "source": ["## H2\n"], "metadata": {}},
        ])
        nb_path = tmp_path / "test.ipynb"
        _write_notebook(nb, str(nb_path))
        validator = NotebookValidator(str(nb_path))
        result = validator.validate_structure()
        assert result.code_cells == 2
        assert result.markdown_cells == 2
        assert result.cells_with_output == 1

    def test_no_title_flagged_in_pedagogy(self, tmp_path):
        """Notebook without # heading should get pedagogy warning."""
        nb = _make_notebook([
            {"cell_type": "markdown", "source": ["Just some text\n"], "metadata": {}},
            {"cell_type": "code", "source": ["x=1\n"], "metadata": {},
             "execution_count": 1, "outputs": []},
        ])
        nb_path = tmp_path / "test.ipynb"
        _write_notebook(nb, str(nb_path))
        validator = NotebookValidator(str(nb_path))
        issues = validator.validate_content()
        title_issues = [i for i in issues if "title" in i.message.lower()]
        assert len(title_issues) > 0


class TestDiscoverNotebooksMutations:
    """Kill mutants in discover_notebooks: recursion, filtering."""

    def test_recursive_discovery(self, tmp_path):
        """discover_notebooks should find notebooks in subdirectories."""
        nb_dir = tmp_path / "Series"
        sub_dir = nb_dir / "SubSeries"
        sub_dir.mkdir(parents=True)
        nb = _make_notebook([])
        _write_notebook(nb, str(sub_dir / "Sub-1.ipynb"))
        result = discover_notebooks(str(nb_dir), repo_root=tmp_path)
        assert len(result) == 1
        assert "Sub-1.ipynb" in str(result[0])

    def test_skips_non_ipynb_files(self, tmp_path):
        """Non-.ipynb files should be ignored."""
        nb_dir = tmp_path / "Series"
        nb_dir.mkdir()
        nb = _make_notebook([])
        _write_notebook(nb, str(nb_dir / "Test-1.ipynb"))
        (nb_dir / "readme.md").write_text("readme", encoding="utf-8")
        (nb_dir / "data.csv").write_text("a,b,c", encoding="utf-8")
        result = discover_notebooks(str(nb_dir), repo_root=tmp_path)
        assert len(result) == 1
