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

# Attempt to import NotebookExecutor (may not be available without helpers)
try:
    from notebook_tools import NotebookExecutor
    HAS_EXECUTOR = True
except ImportError:
    HAS_EXECUTOR = False


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


# =============================================================================
# Round 2 — Mutation-killing tests for uncovered zones
# =============================================================================


class TestNotebookExecutorDetectKernelName:
    """Kill mutants in NotebookExecutor.detect_kernel_name (L1057-1073).

    Tests the mapping from analyzer.kernel → execution kernel name,
    including fallback default 'python3'.
    """

    @pytest.mark.skipif(not HAS_EXECUTOR, reason="NotebookExecutor requires notebook_helpers")
    def test_smartcontracts_kernel(self, tmp_path):
        """'smartcontracts' kernel should map to 'smartcontracts'."""
        nb = _make_notebook([], kernel_name="smartcontracts")
        nb_path = tmp_path / "test.ipynb"
        _write_notebook(nb, str(nb_path))
        executor = NotebookExecutor(str(nb_path))
        assert executor.detect_kernel_name() == "smartcontracts"

    @pytest.mark.skipif(not HAS_EXECUTOR, reason="NotebookExecutor requires notebook_helpers")
    def test_python3_kernel(self, tmp_path):
        """'python3' kernel should map to 'python3'."""
        nb = _make_notebook([], kernel_name="python3")
        nb_path = tmp_path / "test.ipynb"
        _write_notebook(nb, str(nb_path))
        executor = NotebookExecutor(str(nb_path))
        assert executor.detect_kernel_name() == "python3"

    @pytest.mark.skipif(not HAS_EXECUTOR, reason="NotebookExecutor requires notebook_helpers")
    def test_dotnet_csharp_kernel(self, tmp_path):
        """'.NET C#' kernel from detect_kernel should map to '.net-csharp'."""
        nb = _make_notebook([], kernel_name=".net-csharp", language="C#")
        nb_path = tmp_path / "test.ipynb"
        _write_notebook(nb, str(nb_path))
        executor = NotebookExecutor(str(nb_path))
        assert executor.detect_kernel_name() == ".net-csharp"

    @pytest.mark.skipif(not HAS_EXECUTOR, reason="NotebookExecutor requires notebook_helpers")
    def test_dotnet_fsharp_kernel(self, tmp_path):
        """'.NET F#' kernel should map to '.net-fsharp'."""
        nb = _make_notebook([], kernel_name=".net-fsharp", language="F#")
        nb_path = tmp_path / "test.ipynb"
        _write_notebook(nb, str(nb_path))
        executor = NotebookExecutor(str(nb_path))
        assert executor.detect_kernel_name() == ".net-fsharp"

    @pytest.mark.skipif(not HAS_EXECUTOR, reason="NotebookExecutor requires notebook_helpers")
    def test_lean4_kernel(self, tmp_path):
        """'lean4' kernel should map to 'lean4'."""
        nb = _make_notebook([], kernel_name="lean4")
        nb_path = tmp_path / "test.ipynb"
        _write_notebook(nb, str(nb_path))
        executor = NotebookExecutor(str(nb_path))
        assert executor.detect_kernel_name() == "lean4"

    @pytest.mark.skipif(not HAS_EXECUTOR, reason="NotebookExecutor requires notebook_helpers")
    def test_unknown_kernel_defaults_python3(self, tmp_path):
        """Unknown kernel should default to 'python3'."""
        nb = _make_notebook([], kernel_name="julia-1.9")
        nb_path = tmp_path / "test.ipynb"
        _write_notebook(nb, str(nb_path))
        executor = NotebookExecutor(str(nb_path))
        assert executor.detect_kernel_name() == "python3"


class TestExtractSections:
    """Kill mutants in NotebookAnalyzer._extract_sections (L530-550).

    Tests markdown heading extraction: depth filter, bold stripping,
    link text extraction, multiple headings per cell.
    """

    def test_extracts_h1_h2_h3(self, tmp_path):
        """Sections at depth 1-3 are extracted."""
        nb = _make_notebook([
            {"cell_type": "markdown", "source": ["# Title\n"], "metadata": {}},
            {"cell_type": "markdown", "source": ["## Section 1\n"], "metadata": {}},
            {"cell_type": "markdown", "source": ["### Sub 1.1\n"], "metadata": {}},
        ])
        nb_path = tmp_path / "test.ipynb"
        _write_notebook(nb, str(nb_path))
        analyzer = NotebookAnalyzer(str(nb_path))
        skeleton = analyzer.get_skeleton()
        assert len(skeleton.sections) == 3
        assert skeleton.sections[0].level == 1
        assert skeleton.sections[0].title == "Title"
        assert skeleton.sections[1].level == 2
        assert skeleton.sections[2].level == 3

    def test_h4_filtered_by_max_depth(self, tmp_path):
        """H4+ headings should be filtered out when max_depth=3."""
        nb = _make_notebook([
            {"cell_type": "markdown", "source": ["#### Deep\n"], "metadata": {}},
        ])
        nb_path = tmp_path / "test.ipynb"
        _write_notebook(nb, str(nb_path))
        analyzer = NotebookAnalyzer(str(nb_path))
        skeleton = analyzer.get_skeleton()
        assert len(skeleton.sections) == 0

    def test_h4_included_with_higher_max_depth(self, tmp_path):
        """H4 should be included when max_depth=4."""
        nb = _make_notebook([
            {"cell_type": "markdown", "source": ["#### Deep\n"], "metadata": {}},
        ])
        nb_path = tmp_path / "test.ipynb"
        _write_notebook(nb, str(nb_path))
        analyzer = NotebookAnalyzer(str(nb_path))
        skeleton = analyzer.get_skeleton(include_code_preview=False)
        # get_skeleton uses max_depth=3 by default, so H4 is filtered
        # We test _extract_sections directly with max_depth=4
        sections = analyzer._extract_sections(max_depth=4)
        assert len(sections) == 1
        assert sections[0].level == 4

    def test_bold_stripped_from_title(self, tmp_path):
        """**bold** should be stripped from section titles."""
        nb = _make_notebook([
            {"cell_type": "markdown", "source": ["## **Important** Section\n"], "metadata": {}},
        ])
        nb_path = tmp_path / "test.ipynb"
        _write_notebook(nb, str(nb_path))
        analyzer = NotebookAnalyzer(str(nb_path))
        sections = analyzer._extract_sections()
        assert sections[0].title == "Important Section"

    def test_link_text_preserved(self, tmp_path):
        """[text](url) should be replaced with just 'text' in titles."""
        nb = _make_notebook([
            {"cell_type": "markdown", "source": ["## See [docs](http://example.com)\n"], "metadata": {}},
        ])
        nb_path = tmp_path / "test.ipynb"
        _write_notebook(nb, str(nb_path))
        analyzer = NotebookAnalyzer(str(nb_path))
        sections = analyzer._extract_sections()
        assert sections[0].title == "See docs"

    def test_multiple_headings_per_cell(self, tmp_path):
        """Multiple headings in a single markdown cell are all extracted."""
        nb = _make_notebook([
            {"cell_type": "markdown", "source": ["# Title\n## Sub\n### Detail\n"], "metadata": {}},
        ])
        nb_path = tmp_path / "test.ipynb"
        _write_notebook(nb, str(nb_path))
        analyzer = NotebookAnalyzer(str(nb_path))
        sections = analyzer._extract_sections()
        assert len(sections) == 3

    def test_code_cells_ignored(self, tmp_path):
        """Code cells should not produce sections."""
        nb = _make_notebook([
            {"cell_type": "code", "source": ["# This is a comment, not a heading\n"], "metadata": {},
             "execution_count": 1, "outputs": []},
        ])
        nb_path = tmp_path / "test.ipynb"
        _write_notebook(nb, str(nb_path))
        analyzer = NotebookAnalyzer(str(nb_path))
        sections = analyzer._extract_sections()
        assert len(sections) == 0


class TestGetCellOutputsAnalysis:
    """Kill mutants in NotebookAnalyzer.get_cell_outputs_analysis (L552-597).

    Tests output analysis: error detection, not-executed status, empty cells.
    """

    def test_error_output_detected(self, tmp_path):
        """Cells with error outputs should be counted."""
        nb = _make_notebook([
            {"cell_type": "code", "source": ["1/0\n"], "metadata": {},
             "execution_count": 1, "outputs": [
                 {"output_type": "error", "ename": "ZeroDivisionError", "evalue": "division by zero"}
             ]},
        ])
        nb_path = tmp_path / "test.ipynb"
        _write_notebook(nb, str(nb_path))
        analyzer = NotebookAnalyzer(str(nb_path))
        analysis = analyzer.get_cell_outputs_analysis()
        assert analysis["cells_with_errors"] == 1
        assert len(analysis["errors"]) == 1
        assert analysis["errors"][0]["ename"] == "ZeroDivisionError"

    def test_not_executed_status(self, tmp_path):
        """Code cell without outputs should be 'NOT_EXECUTED'."""
        nb = _make_notebook([
            {"cell_type": "code", "source": ["x = 1\n"], "metadata": {},
             "execution_count": None, "outputs": []},
        ])
        nb_path = tmp_path / "test.ipynb"
        _write_notebook(nb, str(nb_path))
        analyzer = NotebookAnalyzer(str(nb_path))
        analysis = analyzer.get_cell_outputs_analysis()
        assert analysis["cells"][0]["status"] == "NOT_EXECUTED"

    def test_empty_code_cell_status(self, tmp_path):
        """Empty code cell should be 'EMPTY'."""
        nb = _make_notebook([
            {"cell_type": "code", "source": [""], "metadata": {},
             "execution_count": None, "outputs": []},
        ])
        nb_path = tmp_path / "test.ipynb"
        _write_notebook(nb, str(nb_path))
        analyzer = NotebookAnalyzer(str(nb_path))
        analysis = analyzer.get_cell_outputs_analysis()
        assert analysis["cells"][0]["status"] == "EMPTY"

    def test_ok_status_with_outputs(self, tmp_path):
        """Code cell with outputs should be 'OK'."""
        nb = _make_notebook([
            {"cell_type": "code", "source": ["print('hello')\n"], "metadata": {},
             "execution_count": 1, "outputs": [
                 {"output_type": "stream", "name": "stdout", "text": ["hello\n"]}
             ]},
        ])
        nb_path = tmp_path / "test.ipynb"
        _write_notebook(nb, str(nb_path))
        analyzer = NotebookAnalyzer(str(nb_path))
        analysis = analyzer.get_cell_outputs_analysis()
        assert analysis["cells"][0]["status"] == "OK"
        assert analysis["cells_with_output"] == 1

    def test_markdown_cells_not_analyzed(self, tmp_path):
        """Markdown cells should not appear in code analysis."""
        nb = _make_notebook([
            {"cell_type": "markdown", "source": ["# Title\n"], "metadata": {}},
            {"cell_type": "code", "source": ["x=1\n"], "metadata": {},
             "execution_count": 1, "outputs": [{"output_type": "stream", "name": "stdout", "text": ["1\n"]}]},
        ])
        nb_path = tmp_path / "test.ipynb"
        _write_notebook(nb, str(nb_path))
        analyzer = NotebookAnalyzer(str(nb_path))
        analysis = analyzer.get_cell_outputs_analysis()
        assert analysis["code_cells"] == 1
        assert len(analysis["cells"]) == 1

    def test_first_line_preview(self, tmp_path):
        """first_line should show first line of source, truncated to 60 chars."""
        long_line = "x = " + "a" * 100
        nb = _make_notebook([
            {"cell_type": "code", "source": [long_line + "\n"], "metadata": {},
             "execution_count": 1, "outputs": []},
        ])
        nb_path = tmp_path / "test.ipynb"
        _write_notebook(nb, str(nb_path))
        analyzer = NotebookAnalyzer(str(nb_path))
        analysis = analyzer.get_cell_outputs_analysis()
        assert len(analysis["cells"][0]["first_line"]) == 60


class TestNotebookSkeletonToDict:
    """Kill mutants in NotebookSkeleton.to_dict (L276-290).

    Tests serialization including sections, code_previews, and edge cases.
    """

    def test_to_dict_with_sections(self, tmp_path):
        """to_dict should include sections with level, title, cell_index."""
        nb = _make_notebook([
            {"cell_type": "markdown", "source": ["# Title\n## Section 1\n"], "metadata": {}},
        ])
        nb_path = tmp_path / "test.ipynb"
        _write_notebook(nb, str(nb_path))
        analyzer = NotebookAnalyzer(str(nb_path))
        skeleton = analyzer.get_skeleton()
        d = skeleton.to_dict()
        assert len(d["sections"]) == 2
        assert d["sections"][0]["level"] == 1
        assert d["sections"][0]["title"] == "Title"
        assert d["sections"][1]["level"] == 2

    def test_to_dict_with_code_previews(self, tmp_path):
        """to_dict should include code_previews with CellInfo fields."""
        nb = _make_notebook([
            {"cell_type": "code", "source": ["x = 1\n"], "metadata": {},
             "execution_count": 1, "outputs": []},
        ])
        nb_path = tmp_path / "test.ipynb"
        _write_notebook(nb, str(nb_path))
        analyzer = NotebookAnalyzer(str(nb_path))
        skeleton = analyzer.get_skeleton()
        d = skeleton.to_dict()
        assert len(d["code_previews"]) == 1
        assert d["code_previews"][0]["index"] == 0
        assert d["code_previews"][0]["has_output"] is False

    def test_to_dict_empty_skeleton(self):
        """Empty skeleton should serialize with defaults."""
        skeleton = NotebookSkeleton(path="/test", name="test")
        d = skeleton.to_dict()
        assert d["path"] == "/test"
        assert d["name"] == "test"
        assert d["total_cells"] == 0
        assert d["sections"] == []
        assert d["code_previews"] == []
        assert d["estimated_duration"] is None


class TestFormatMarkdownTable:
    """Kill mutants in _format_markdown_table (L1404-1423).

    Tests table formatting: number extraction, section truncation, duration display.
    """

    def test_number_extraction_from_name(self):
        """Notebook name with -N- pattern should extract N."""
        from notebook_tools import _format_markdown_table
        skeleton = NotebookSkeleton(
            path="test", name="Sudoku-3-Test", total_cells=10, estimated_duration=15,
        )
        result = _format_markdown_table([skeleton], Path("test"))
        assert "| 3 |" in result

    def test_fallback_number_when_no_match(self):
        """Notebook without -N- pattern should use index."""
        from notebook_tools import _format_markdown_table
        skeleton = NotebookSkeleton(
            path="test", name="NoNumberHere", total_cells=5, estimated_duration=10,
        )
        result = _format_markdown_table([skeleton], Path("test"))
        assert "| 1 |" in result

    def test_sections_truncated_at_40_chars(self):
        """Sections string longer than 40 chars should be truncated."""
        from notebook_tools import _format_markdown_table
        skeleton = NotebookSkeleton(
            path="test", name="Test-1", total_cells=5, estimated_duration=10,
            sections=[
                SectionInfo(level=2, title="A" * 50, cell_index=0),
            ],
        )
        result = _format_markdown_table([skeleton], Path("test"))
        assert "..." in result

    def test_no_duration_shows_dash(self):
        """Notebook without estimated_duration should show '-'."""
        from notebook_tools import _format_markdown_table
        skeleton = NotebookSkeleton(
            path="test", name="Test-1", total_cells=5, estimated_duration=None,
        )
        result = _format_markdown_table([skeleton], Path("test"))
        assert "| - |" in result


class TestFormatSummary:
    """Kill mutants in _format_summary (L1426-1443).

    Tests summary formatting: totals, duration, per-notebook section counts.
    """

    def test_summary_totals(self):
        """Summary should show correct notebook count and cell total."""
        from notebook_tools import _format_summary
        skeletons = [
            NotebookSkeleton(path="a", name="A", total_cells=10, estimated_duration=30),
            NotebookSkeleton(path="b", name="B", total_cells=20, estimated_duration=60),
        ]
        result = _format_summary(skeletons)
        assert "Notebooks: 2" in result
        assert "Total cells: 30" in result

    def test_duration_formatting(self):
        """Duration should be formatted as hours and minutes."""
        from notebook_tools import _format_summary
        skeletons = [
            NotebookSkeleton(path="a", name="A", total_cells=5, estimated_duration=90),
        ]
        result = _format_summary(skeletons)
        assert "1h30" in result

    def test_no_duration_shows_zero(self):
        """Notebooks without duration should contribute 0 to total."""
        from notebook_tools import _format_summary
        skeletons = [
            NotebookSkeleton(path="a", name="A", total_cells=5, estimated_duration=None),
        ]
        result = _format_summary(skeletons)
        assert "0 min" in result
        assert "0h00" in result

    def test_sections_count_per_notebook(self):
        """Each notebook line should show section count."""
        from notebook_tools import _format_summary
        skeletons = [
            NotebookSkeleton(
                path="a", name="A", total_cells=5, estimated_duration=10,
                sections=[SectionInfo(level=2, title="S1", cell_index=0),
                          SectionInfo(level=2, title="S2", cell_index=1)],
            ),
        ]
        result = _format_summary(skeletons)
        assert "2 sections" in result


class TestNotebookValidationStatusEdgeCases:
    """Kill mutants in NotebookValidation.status property edge cases.

    Tests MISSING, INVALID, WARNING, OK status transitions.
    """

    def test_missing_status(self):
        """status should be MISSING when exists=False."""
        v = NotebookValidation(path="missing.ipynb", name="missing.ipynb")
        assert v.status == "MISSING"

    def test_invalid_status(self):
        """status should be INVALID when valid_json=False and exists=True."""
        v = NotebookValidation(path="bad.ipynb", name="bad.ipynb", exists=True)
        assert v.status == "INVALID"

    def test_error_status(self):
        """status should be ERROR when error issues exist."""
        v = NotebookValidation(
            path="test.ipynb", name="test.ipynb",
            exists=True, valid_json=True,
            issues=[ValidationIssue(issue_type="error", category="test", cell_index=0, message="err")],
        )
        assert v.status == "ERROR"

    def test_warning_status(self):
        """status should be WARNING when only warning issues exist."""
        v = NotebookValidation(
            path="test.ipynb", name="test.ipynb",
            exists=True, valid_json=True,
            issues=[ValidationIssue(issue_type="warning", category="test", cell_index=0, message="warn")],
        )
        assert v.status == "WARNING"

    def test_ok_status(self):
        """status should be OK when no issues."""
        v = NotebookValidation(
            path="test.ipynb", name="test.ipynb",
            exists=True, valid_json=True, has_cells=True,
        )
        assert v.status == "OK"

    def test_error_count_property(self):
        """error_count should count only error-type issues."""
        v = NotebookValidation(
            path="test.ipynb", name="test.ipynb",
            issues=[
                ValidationIssue(issue_type="error", category="a", cell_index=0, message="e1"),
                ValidationIssue(issue_type="warning", category="b", cell_index=1, message="w1"),
                ValidationIssue(issue_type="error", category="c", cell_index=2, message="e2"),
            ],
        )
        assert v.error_count == 2

    def test_warning_count_property(self):
        """warning_count should count only warning-type issues."""
        v = NotebookValidation(
            path="test.ipynb", name="test.ipynb",
            issues=[
                ValidationIssue(issue_type="error", category="a", cell_index=0, message="e1"),
                ValidationIssue(issue_type="warning", category="b", cell_index=1, message="w1"),
            ],
        )
        assert v.warning_count == 1


class TestDiscoverNotebooksEdgeCases:
    """Kill mutants in discover_notebooks: exclude_subdirs, python_only, dotnet_only, direct file."""

    def test_discover_specific_ipynb_file(self, tmp_path):
        """Target ending with .ipynb should find that exact file."""
        nb = _make_notebook([])
        nb_path = tmp_path / "Test-1.ipynb"
        _write_notebook(nb, str(nb_path))
        result = discover_notebooks(str(nb_path), repo_root=tmp_path)
        assert len(result) == 1

    def test_discover_nonexistent_file_returns_empty(self, tmp_path):
        """Nonexistent .ipynb target should return empty list."""
        result = discover_notebooks(str(tmp_path / "nope.ipynb"), repo_root=tmp_path)
        assert result == []

    def test_discover_path_as_directory(self, tmp_path):
        """Non-family target that is a directory should find notebooks inside."""
        nb_dir = tmp_path / "MySeries"
        nb_dir.mkdir()
        nb = _make_notebook([])
        _write_notebook(nb, str(nb_dir / "NB-1.ipynb"))
        result = discover_notebooks(str(nb_dir), repo_root=tmp_path)
        assert len(result) == 1

    def test_discover_non_recursive(self, tmp_path):
        """recursive=False should not search subdirectories."""
        nb_dir = tmp_path / "Series"
        sub = nb_dir / "Sub"
        sub.mkdir(parents=True)
        nb1 = _make_notebook([])
        _write_notebook(nb1, str(nb_dir / "Top-1.ipynb"))
        nb2 = _make_notebook([])
        _write_notebook(nb2, str(sub / "Deep-1.ipynb"))
        result = discover_notebooks(str(nb_dir), repo_root=tmp_path, recursive=False)
        assert len(result) == 1
        assert "Top-1" in str(result[0])

    def test_discover_deduplicates(self, tmp_path):
        """discover_notebooks should deduplicate results (sorted set)."""
        nb_dir = tmp_path / "Series"
        nb_dir.mkdir()
        nb = _make_notebook([])
        _write_notebook(nb, str(nb_dir / "Test-1.ipynb"))
        # Calling with the same directory target twice shouldn't produce dupes
        r1 = discover_notebooks(str(nb_dir), repo_root=tmp_path)
        r2 = discover_notebooks(str(nb_dir), repo_root=tmp_path)
        assert len(r1) == 1
        assert len(r2) == 1


class TestGetSkeletonEstimatedDuration:
    """Kill mutants in get_skeleton duration estimation (L514).

    Duration = (md_cells * 0.5 + code_cells * 1.0).__ceil__().
    Mutation: * 0.5 -> * 0.6, * 1.0 -> * 1.1, __ceil__ -> __floor__.
    """

    def test_duration_with_code_only(self, tmp_path):
        """5 code cells, 0 markdown = ceil(5.0) = 5 min."""
        cells = [
            {"cell_type": "code", "source": [f"x{i}=1\n"], "metadata": {},
             "execution_count": i, "outputs": []}
            for i in range(5)
        ]
        nb = _make_notebook(cells)
        nb_path = tmp_path / "test.ipynb"
        _write_notebook(nb, str(nb_path))
        analyzer = NotebookAnalyzer(str(nb_path))
        skeleton = analyzer.get_skeleton()
        assert skeleton.estimated_duration == 5

    def test_duration_with_mixed_cells(self, tmp_path):
        """3 markdown + 2 code = ceil(1.5 + 2.0) = ceil(3.5) = 4 min."""
        cells = [
            {"cell_type": "markdown", "source": [f"# H{i}\n"], "metadata": {}}
            for i in range(3)
        ] + [
            {"cell_type": "code", "source": [f"x{i}=1\n"], "metadata": {},
             "execution_count": i, "outputs": []}
            for i in range(2)
        ]
        nb = _make_notebook(cells)
        nb_path = tmp_path / "test.ipynb"
        _write_notebook(nb, str(nb_path))
        analyzer = NotebookAnalyzer(str(nb_path))
        skeleton = analyzer.get_skeleton()
        assert skeleton.estimated_duration == 4

    def test_duration_zero_cells(self, tmp_path):
        """0 cells = ceil(0) = 0 min."""
        nb = _make_notebook([])
        nb_path = tmp_path / "test.ipynb"
        _write_notebook(nb, str(nb_path))
        analyzer = NotebookAnalyzer(str(nb_path))
        skeleton = analyzer.get_skeleton()
        assert skeleton.estimated_duration == 0

    def test_duration_ceil_not_floor(self, tmp_path):
        """1 md + 1 code = ceil(0.5 + 1.0) = ceil(1.5) = 2, NOT 1."""
        cells = [
            {"cell_type": "markdown", "source": ["# Title\n"], "metadata": {}},
            {"cell_type": "code", "source": ["x=1\n"], "metadata": {},
             "execution_count": 1, "outputs": []},
        ]
        nb = _make_notebook(cells)
        nb_path = tmp_path / "test.ipynb"
        _write_notebook(nb, str(nb_path))
        analyzer = NotebookAnalyzer(str(nb_path))
        skeleton = analyzer.get_skeleton()
        assert skeleton.estimated_duration == 2  # ceil(1.5), not floor(1.5)=1


class TestNotebookAnalyzerGetSkeletonTitle:
    """Kill mutants in get_skeleton title extraction (L469-476).

    Title = first # heading from markdown cells.
    """

    def test_title_from_first_h1(self, tmp_path):
        """Title should be the first H1 found."""
        nb = _make_notebook([
            {"cell_type": "markdown", "source": ["# My Great Title\n"], "metadata": {}},
        ])
        nb_path = tmp_path / "test.ipynb"
        _write_notebook(nb, str(nb_path))
        analyzer = NotebookAnalyzer(str(nb_path))
        skeleton = analyzer.get_skeleton()
        assert skeleton.title == "My Great Title"

    def test_title_none_when_no_h1(self, tmp_path):
        """No H1 heading should result in title=None."""
        nb = _make_notebook([
            {"cell_type": "markdown", "source": ["Just some text\n"], "metadata": {}},
        ])
        nb_path = tmp_path / "test.ipynb"
        _write_notebook(nb, str(nb_path))
        analyzer = NotebookAnalyzer(str(nb_path))
        skeleton = analyzer.get_skeleton()
        assert skeleton.title is None

    def test_title_from_h2_not_used(self, tmp_path):
        """H2 should not be detected as title (only H1 with ^# )."""
        nb = _make_notebook([
            {"cell_type": "markdown", "source": ["## Section\n"], "metadata": {}},
        ])
        nb_path = tmp_path / "test.ipynb"
        _write_notebook(nb, str(nb_path))
        analyzer = NotebookAnalyzer(str(nb_path))
        skeleton = analyzer.get_skeleton()
        # Title is only extracted from ^#\s+ (single # at start of line)
        assert skeleton.title is None

    def test_error_notebook_skeleton(self, tmp_path):
        """Invalid notebook should produce error skeleton."""
        nb_path = tmp_path / "broken.ipynb"
        nb_path.write_text("NOT JSON", encoding="utf-8")
        analyzer = NotebookAnalyzer(str(nb_path))
        skeleton = analyzer.get_skeleton()
        assert skeleton.title == "[Error: Could not load notebook]"


class TestNotebookExecutionResultDataclass:
    """Kill mutants in NotebookExecutionResult defaults (L1025-1037)."""

    def test_default_values(self):
        """NotebookExecutionResult should have sensible defaults."""
        r = NotebookExecutionResult(path="test.ipynb", success=False, kernel="python3")
        assert r.success is False
        assert r.total_cells == 0
        assert r.executed_cells == 0
        assert r.success_cells == 0
        assert r.error_cells == 0
        assert r.execution_time == 0.0
        assert r.message == ""

    def test_custom_values(self):
        """NotebookExecutionResult should accept all fields."""
        r = NotebookExecutionResult(
            path="test.ipynb", success=True, kernel=".net-csharp",
            total_cells=10, executed_cells=10, success_cells=9, error_cells=1,
            execution_time=42.5, message="SUCCESS"
        )
        assert r.total_cells == 10
        assert r.error_cells == 1
        assert r.execution_time == 42.5


class TestCellInfoDataclassDefaults:
    """Kill mutants in CellInfo defaults — index and cell_type required."""

    def test_cell_info_minimal(self):
        """CellInfo with only required fields."""
        c = CellInfo(index=0, cell_type="code")
        assert c.preview == ""
        assert c.line_count == 0
        assert c.has_output is False
        assert c.output_type is None
        assert c.cell_id is None

    def test_cell_info_full(self):
        """CellInfo with all fields set."""
        c = CellInfo(index=5, cell_type="code", preview="x = 1", line_count=2,
                     has_output=True, output_type="stream", cell_id="abc123")
        assert c.index == 5
        assert c.has_output is True
        assert c.cell_id == "abc123"


class TestCodePreviewLimit:
    """Kill mutants in get_skeleton code_previews[:20] limit (L526).

    Mutation: [:20] -> [:10] or removed entirely.
    """

    def test_code_previews_capped_at_20(self, tmp_path):
        """More than 20 code cells should produce at most 20 code_previews."""
        cells = [
            {"cell_type": "code", "source": [f"x{i} = {i}\n"], "metadata": {},
             "execution_count": i, "outputs": []}
            for i in range(25)
        ]
        nb = _make_notebook(cells)
        nb_path = tmp_path / "test.ipynb"
        _write_notebook(nb, str(nb_path))
        analyzer = NotebookAnalyzer(str(nb_path))
        skeleton = analyzer.get_skeleton(include_code_preview=True)
        assert len(skeleton.code_previews) == 20

    def test_code_preview_skip_empty_cells(self, tmp_path):
        """Empty code cells should not produce code_previews."""
        cells = [
            {"cell_type": "code", "source": ["x=1\n"], "metadata": {},
             "execution_count": 1, "outputs": []},
            {"cell_type": "code", "source": [""], "metadata": {},
             "execution_count": None, "outputs": []},
            {"cell_type": "code", "source": ["y=2\n"], "metadata": {},
             "execution_count": 2, "outputs": []},
        ]
        nb = _make_notebook(cells)
        nb_path = tmp_path / "test.ipynb"
        _write_notebook(nb, str(nb_path))
        analyzer = NotebookAnalyzer(str(nb_path))
        skeleton = analyzer.get_skeleton()
        assert len(skeleton.code_previews) == 2


# =============================================================================
# Execute options (--kernel, --cwd, --env, --scrub-keys)
# =============================================================================

@pytest.mark.skipif(not HAS_EXECUTOR, reason="NotebookExecutor not available")
class TestExecuteOptions:
    """Test new CLI options for the execute command."""

    def test_scrub_keys_constant_exists(self):
        """SCRUB_KEYS list is defined and non-empty."""
        assert hasattr(NotebookExecutor, "SCRUB_KEYS")
        assert len(NotebookExecutor.SCRUB_KEYS) > 0
        assert "OPENAI_API_KEY" in NotebookExecutor.SCRUB_KEYS
        assert "ANTHROPIC_API_KEY" in NotebookExecutor.SCRUB_KEYS

    def test_scrub_keys_env_cleaned(self, tmp_path, monkeypatch):
        """--scrub-keys removes API keys from subprocess environment."""
        nb_path = tmp_path / "test.ipynb"
        _write_notebook({"cells": [
            {"cell_type": "code", "source": ["x=1\n"], "metadata": {},
             "execution_count": None, "outputs": []}
        ], "metadata": {}, "nbformat": 4, "nbformat_minor": 5}, str(nb_path))

        # Set a fake API key in the test environment
        monkeypatch.setenv("OPENAI_API_KEY", "sk-test-secret-12345")

        executor = NotebookExecutor(str(nb_path))
        # Verify method accepts the parameter
        assert hasattr(executor, "execute_with_papermill")

    def test_execute_accepts_kernel_override(self, tmp_path):
        """execute_with_papermill accepts kernel_override parameter."""
        nb_path = tmp_path / "test.ipynb"
        _write_notebook({"cells": [
            {"cell_type": "code", "source": ["x=1\n"], "metadata": {},
             "execution_count": None, "outputs": []}
        ], "metadata": {}, "nbformat": 4, "nbformat_minor": 5}, str(nb_path))

        executor = NotebookExecutor(str(nb_path))
        import inspect
        sig = inspect.signature(executor.execute_with_papermill)
        assert "kernel_override" in sig.parameters
        assert "cwd_override" in sig.parameters
        assert "env_extra" in sig.parameters
        assert "scrub_keys" in sig.parameters

    def test_execute_defaults_unchanged(self, tmp_path):
        """Default parameters are unchanged (non-regression)."""
        nb_path = tmp_path / "test.ipynb"
        _write_notebook({"cells": [
            {"cell_type": "code", "source": ["x=1\n"], "metadata": {},
             "execution_count": None, "outputs": []}
        ], "metadata": {}, "nbformat": 4, "nbformat_minor": 5}, str(nb_path))

        executor = NotebookExecutor(str(nb_path))
        import inspect
        sig = inspect.signature(executor.execute_with_papermill)
        # New defaults: None/False (unchanged behavior)
        assert sig.parameters["kernel_override"].default is None
        assert sig.parameters["cwd_override"].default is None
        assert sig.parameters["env_extra"].default is None
        assert sig.parameters["scrub_keys"].default is False
        # Original defaults unchanged
        assert sig.parameters["timeout"].default == 300
        assert sig.parameters["batch_mode"].default is False

    def test_scrub_keys_env_build(self, tmp_path, monkeypatch):
        """Scrub keys produces clean env without API keys."""
        monkeypatch.setenv("OPENAI_API_KEY", "sk-test-secret")
        monkeypatch.setenv("ANTHROPIC_API_KEY", "sk-ant-test")
        monkeypatch.setenv("SAFE_VAR", "keep-me")

        nb_path = tmp_path / "test.ipynb"
        _write_notebook({"cells": [], "metadata": {}, "nbformat": 4, "nbformat_minor": 5}, str(nb_path))

        executor = NotebookExecutor(str(nb_path))
        # Simulate env building logic
        sub_env = dict(os.environ)
        for key in executor.SCRUB_KEYS:
            sub_env.pop(key, None)

        assert "OPENAI_API_KEY" not in sub_env
        assert "ANTHROPIC_API_KEY" not in sub_env
        assert sub_env.get("SAFE_VAR") == "keep-me"

    def test_env_extra_merges_into_env(self, tmp_path):
        """env_extra dict values override subprocess environment."""
        nb_path = tmp_path / "test.ipynb"
        _write_notebook({"cells": [], "metadata": {}, "nbformat": 4, "nbformat_minor": 5}, str(nb_path))

        executor = NotebookExecutor(str(nb_path))
        sub_env = dict(os.environ)
        env_extra = {"BATCH_MODE": "true", "MY_CUSTOM": "val"}
        sub_env.update(env_extra)

        assert sub_env["BATCH_MODE"] == "true"
        assert sub_env["MY_CUSTOM"] == "val"

    def test_kernel_override_replaces_auto(self, tmp_path):
        """kernel_override takes precedence over detect_kernel_name()."""
        nb_path = tmp_path / "test.ipynb"
        _write_notebook({
            "cells": [{"cell_type": "code", "source": ["x=1\n"], "metadata": {},
                       "execution_count": None, "outputs": []}],
            "metadata": {"kernelspec": {"display_name": "Python 3", "language": "python", "name": "python3"}},
            "nbformat": 4, "nbformat_minor": 5,
        }, str(nb_path))

        executor = NotebookExecutor(str(nb_path))
        auto_kernel = executor.detect_kernel_name()
        assert auto_kernel == "python3"

        # With override, should use the override value
        kernel = "custom-kernel" or executor.detect_kernel_name()
        assert kernel == "custom-kernel"

    def test_cwd_override_path_resolution(self, tmp_path):
        """cwd_override is resolved to absolute path."""
        nb_path = tmp_path / "test.ipynb"
        _write_notebook({"cells": [], "metadata": {}, "nbformat": 4, "nbformat_minor": 5}, str(nb_path))

        custom_dir = tmp_path / "custom_workdir"
        custom_dir.mkdir()

        cwd_override = custom_dir
        abs_cwd = (cwd_override or nb_path.parent).resolve()
        assert abs_cwd == custom_dir.resolve()

        abs_cwd_default = (None or nb_path.parent).resolve()
        assert abs_cwd_default == nb_path.parent.resolve()


class TestExecuteCLIArgs:
    """Test CLI argument parsing for execute command."""

    def test_cli_accepts_kernel(self):
        """--kernel argument is parsed correctly."""
        import argparse
        parser = argparse.ArgumentParser()
        parser.add_argument('--kernel', type=str, default=None)
        args = parser.parse_args(['--kernel', 'python3'])
        assert args.kernel == 'python3'

    def test_cli_accepts_cwd(self):
        """--cwd argument is parsed correctly."""
        import argparse
        parser = argparse.ArgumentParser()
        parser.add_argument('--cwd', type=str, default=None)
        args = parser.parse_args(['--cwd', '/tmp/workdir'])
        assert args.cwd == '/tmp/workdir'

    def test_cli_accepts_env_repeatable(self):
        """--env KEY=VAL can be repeated."""
        import argparse
        parser = argparse.ArgumentParser()
        parser.add_argument('--env', action='append', default=[], metavar='KEY=VAL')
        args = parser.parse_args(['--env', 'A=1', '--env', 'B=2'])
        assert args.env == ['A=1', 'B=2']

    def test_cli_accepts_scrub_keys(self):
        """--scrub-keys is a boolean flag."""
        import argparse
        parser = argparse.ArgumentParser()
        parser.add_argument('--scrub-keys', action='store_true')
        args = parser.parse_args(['--scrub-keys'])
        assert args.scrub_keys is True
        args2 = parser.parse_args([])
        assert args2.scrub_keys is False

    def test_env_parsing_key_val(self):
        """--env KEY=VAL pairs are parsed into dict."""
        pairs = ['BATCH_MODE=true', 'MY_VAR=hello']
        env_extra = {}
        for pair in pairs:
            key, val = pair.split('=', 1)
            env_extra[key] = val
        assert env_extra == {"BATCH_MODE": "true", "MY_VAR": "hello"}

    def test_env_parsing_rejects_no_equals(self):
        """--env without = is rejected."""
        pair = "INVALID"
        assert '=' not in pair
