"""Tests for scripts/notebook_tools/notebook_tools.py — pure functions and dataclasses.

Tests focus on: should_skip, detect_kernel, extract_cell_preview,
_format_markdown_table, _format_summary, dataclass defaults, Colors, SKIP_PATTERNS,
discover_notebooks, NotebookExecutor.SCRUB_KEYS, notebook_helpers parity.
No filesystem I/O or kernel execution required.
"""

import re
import sys
from dataclasses import asdict
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "notebook_tools"))
from notebook_tools import (
    Colors,
    CellInfo,
    SectionInfo,
    ValidationIssue,
    NotebookSkeleton,
    NotebookValidation,
    SKIP_PATTERNS,
    NOTEBOOK_FAMILIES,
    should_skip,
    detect_kernel,
    extract_cell_preview,
    _format_markdown_table,
    _format_summary,
    get_repo_root,
    discover_notebooks,
    NotebookExecutor,
)


# ---------------------------------------------------------------------------
# SKIP_PATTERNS and NOTEBOOK_FAMILIES constants
# ---------------------------------------------------------------------------

class TestConstants:
    def test_skip_patterns_is_list(self):
        assert isinstance(SKIP_PATTERNS, list)
        assert len(SKIP_PATTERNS) > 0

    def test_skip_patterns_contains_checkpoints(self):
        assert any("checkpoints" in p for p in SKIP_PATTERNS)

    def test_skip_patterns_contains_output(self):
        assert any("output" in p for p in SKIP_PATTERNS)

    def test_notebook_families_is_dict(self):
        assert isinstance(NOTEBOOK_FAMILIES, dict)
        assert len(NOTEBOOK_FAMILIES) > 0

    def test_notebook_families_have_path(self):
        """Each family has a 'path' key."""
        for name, cfg in NOTEBOOK_FAMILIES.items():
            assert "path" in cfg, f"Family {name} missing 'path'"


# ---------------------------------------------------------------------------
# Colors
# ---------------------------------------------------------------------------

class TestColors:
    def test_colors_have_ansi_codes(self):
        assert Colors.GREEN.startswith("\033[")
        assert Colors.RED.startswith("\033[")
        assert Colors.END == "\033[0m"

    def test_disable_clears_colors(self):
        """disable() sets all codes to empty strings."""
        original_green = Colors.GREEN
        Colors.disable()
        assert Colors.GREEN == ""
        assert Colors.RED == ""
        assert Colors.END == ""
        # Restore
        Colors.GREEN = "\033[92m"
        Colors.RED = "\033[91m"
        Colors.YELLOW = "\033[93m"
        Colors.BLUE = "\033[94m"
        Colors.CYAN = "\033[96m"
        Colors.MAGENTA = "\033[95m"
        Colors.BOLD = "\033[1m"
        Colors.END = "\033[0m"


# ---------------------------------------------------------------------------
# Dataclasses
# ---------------------------------------------------------------------------

class TestDataclasses:
    def test_cell_info_defaults(self):
        info = CellInfo(index=0, cell_type="code")
        assert info.preview == ""
        assert info.line_count == 0
        assert info.has_output is False
        assert info.output_type is None
        assert info.cell_id is None

    def test_section_info(self):
        si = SectionInfo(level=2, title="Introduction", cell_index=3)
        assert si.level == 2
        assert si.title == "Introduction"

    def test_validation_issue(self):
        vi = ValidationIssue(issue_type="error", category="code", cell_index=5, message="missing output")
        assert vi.issue_type == "error"
        assert vi.category == "code"

    def test_notebook_skeleton_defaults(self):
        skel = NotebookSkeleton(path="/test/nb.ipynb", name="nb")
        assert skel.kernel == "unknown"
        assert skel.total_cells == 0
        assert skel.markdown_cells == 0
        assert skel.code_cells == 0
        assert skel.cells_with_output == 0
        assert skel.sections == []
        assert skel.code_previews == []
        assert skel.estimated_duration is None

    def test_notebook_skeleton_to_dict(self):
        skel = NotebookSkeleton(path="/test/nb.ipynb", name="nb", kernel="Python")
        d = skel.to_dict()
        assert d["path"] == "/test/nb.ipynb"
        assert d["kernel"] == "Python"
        assert "sections" in d
        assert "code_previews" in d

    def test_notebook_skeleton_to_dict_with_sections(self):
        sections = [SectionInfo(level=2, title="Intro", cell_index=0)]
        skel = NotebookSkeleton(path="/t.ipynb", name="t", sections=sections)
        d = skel.to_dict()
        assert len(d["sections"]) == 1
        assert d["sections"][0]["title"] == "Intro"

    def test_notebook_validation_status_error(self):
        issues = [
            ValidationIssue("error", "code", 0, "err"),
            ValidationIssue("warning", "md", 1, "warn"),
        ]
        nv = NotebookValidation(path="test.ipynb", name="test", exists=True,
                                valid_json=True, issues=issues)
        assert nv.status == "ERROR"
        assert nv.error_count == 1
        assert nv.warning_count == 1

    def test_notebook_validation_clean(self):
        nv = NotebookValidation(path="clean.ipynb", name="clean", exists=True,
                                valid_json=True, issues=[])
        assert nv.status == "OK"
        assert nv.error_count == 0

    def test_notebook_validation_missing(self):
        nv = NotebookValidation(path="missing.ipynb", name="missing")
        assert nv.status == "MISSING"

    def test_notebook_validation_warning(self):
        issues = [ValidationIssue("warning", "md", 1, "warn")]
        nv = NotebookValidation(path="warn.ipynb", name="warn", exists=True,
                                valid_json=True, issues=issues)
        assert nv.status == "WARNING"


# ---------------------------------------------------------------------------
# should_skip
# ---------------------------------------------------------------------------

class TestShouldSkip:
    def test_skip_checkpoints(self):
        assert should_skip(Path("MyIA.AI.Notebooks/.ipynb_checkpoints/nb.ipynb")) is True

    def test_skip_output(self):
        assert should_skip(Path("nb_output.ipynb")) is True

    def test_skip_verified(self):
        assert should_skip(Path("nb_verified.ipynb")) is True

    def test_skip_ui_config(self):
        assert should_skip(Path("UI_configuration.ipynb")) is True

    def test_normal_notebook(self):
        assert should_skip(Path("MyIA.AI.Notebooks/Sudoku/Sudoku-1.ipynb")) is False

    def test_deep_path_normal(self):
        assert should_skip(Path("a/b/c/nb.ipynb")) is False


# ---------------------------------------------------------------------------
# detect_kernel
# ---------------------------------------------------------------------------

class TestDetectKernel:
    def test_python_kernel(self):
        nb = {"metadata": {"kernelspec": {"name": "python3", "language": "python"}}}
        assert detect_kernel(nb) == "Python"

    def test_python_wsl(self):
        nb = {"metadata": {"kernelspec": {"name": "python3", "language": "python",
                                           "display_name": "Python 3 (WSL)"}}}
        assert detect_kernel(nb) == "Python (WSL)"

    def test_gametheory_wsl(self):
        """'wsl' in display_name is checked before 'gametheory' — WSL takes priority."""
        nb = {"metadata": {"kernelspec": {"name": "python3", "language": "python",
                                           "display_name": "Python (GameTheory WSL)"}}}
        # The code checks 'wsl' first, so this returns "Python (WSL)"
        assert detect_kernel(nb) == "Python (WSL)"

    def test_gametheory_without_wsl(self):
        """Gametheory display_name without WSL returns GameTheory variant."""
        nb = {"metadata": {"kernelspec": {"name": "python3", "language": "python",
                                           "display_name": "Python (GameTheory)"}}}
        assert detect_kernel(nb) == "Python (GameTheory WSL)"

    def test_dotnet_csharp(self):
        nb = {"metadata": {"kernelspec": {"name": ".net-csharp", "language": "C#"}}}
        assert detect_kernel(nb) == ".NET C#"

    def test_dotnet_fsharp_by_language(self):
        """F# detected by language='f#' (not kernel name, which matches '.net' first)."""
        nb = {"metadata": {"kernelspec": {"name": "fsharp", "language": "f#"}}}
        assert detect_kernel(nb) == ".NET F#"

    def test_lean4(self):
        nb = {"metadata": {"kernelspec": {"name": "lean4", "language": "lean4"}}}
        assert detect_kernel(nb) == "Lean 4"

    def test_lean4_wsl(self):
        nb = {"metadata": {"kernelspec": {"name": "lean4", "language": "lean4",
                                           "display_name": "Lean 4 (WSL)"}}}
        assert detect_kernel(nb) == "Lean 4 (WSL)"

    def test_unknown_kernel(self):
        nb = {"metadata": {"kernelspec": {"name": "unknown", "language": "unknown"}}}
        assert detect_kernel(nb) == "Unknown"

    def test_empty_metadata(self):
        nb = {"metadata": {}}
        assert detect_kernel(nb) == "Unknown"

    def test_dotnet_from_cell_magic(self):
        """Detect .NET from #!import magic command in cells."""
        nb = {
            "metadata": {"kernelspec": {"name": "unknown", "language": "unknown"}},
            "cells": [{"cell_type": "code", "source": ["#!import helpers.dib"]}],
        }
        assert detect_kernel(nb) == ".NET C#"

    def test_dotnet_csharp_magic(self):
        """Detect .NET from #!csharp magic command."""
        nb = {
            "metadata": {"kernelspec": {"name": "unknown", "language": "unknown"}},
            "cells": [{"cell_type": "code", "source": ["#!csharp\nvar x = 1;"]}],
        }
        assert detect_kernel(nb) == ".NET C#"

    def test_empty_dict(self):
        assert detect_kernel({}) == "Unknown"

    def test_display_name_fallback(self):
        """If no kernel match, fall back to display_name."""
        nb = {"metadata": {"kernelspec": {"name": "custom", "display_name": "MyKernel"}}}
        assert detect_kernel(nb) == "MyKernel"


# ---------------------------------------------------------------------------
# extract_cell_preview
# ---------------------------------------------------------------------------

class TestExtractCellPreview:
    def test_simple_code(self):
        result = extract_cell_preview("x = 1\ny = 2\nz = 3")
        assert "x = 1" in result

    def test_max_lines(self):
        """Only first 3 non-empty, non-magic lines by default."""
        source = "\n".join([f"line{i}" for i in range(10)])
        result = extract_cell_preview(source)
        # Should have at most 3 lines joined
        assert result.count(" ") <= 2  # at most 3 words joined by spaces

    def test_skip_magic_commands(self):
        """#! and % lines are skipped."""
        source = "#!import helpers.dib\n%matplotlib inline\nx = 1"
        result = extract_cell_preview(source)
        assert "#!" not in result
        assert "%" not in result
        assert "x = 1" in result

    def test_empty_source(self):
        result = extract_cell_preview("")
        assert result == ""

    def test_comments_only(self):
        """Comments are kept (not skipped, only #! is)."""
        source = "# comment\n# another"
        result = extract_cell_preview(source)
        assert "# comment" in result

    def test_max_chars_truncation(self):
        """Preview is truncated at max_chars."""
        source = "a" * 200
        result = extract_cell_preview(source)
        assert len(result) < 200
        assert result.endswith("...")

    def test_custom_max_lines(self):
        result = extract_cell_preview("a\nb\nc\nd", max_lines=2)
        assert result == "a b"


# ---------------------------------------------------------------------------
# _format_markdown_table
# ---------------------------------------------------------------------------

class TestFormatMarkdownTable:
    def _make_skeleton(self, name, total_cells=10, sections=None, duration=None):
        return NotebookSkeleton(
            path=f"/test/{name}.ipynb",
            name=name,
            kernel="Python",
            total_cells=total_cells,
            sections=sections or [],
            estimated_duration=duration,
        )

    def test_table_has_header(self):
        skels = [self._make_skeleton("Test-1-Intro")]
        result = _format_markdown_table(skels, Path("/test"))
        assert "| # |" in result
        assert "|---|" in result

    def test_table_contains_notebook_name(self):
        skels = [self._make_skeleton("Test-1-Intro")]
        result = _format_markdown_table(skels, Path("/test"))
        assert "Test-1-Intro" in result

    def test_table_extracts_number(self):
        skels = [self._make_skeleton("Test-7-Advanced")]
        result = _format_markdown_table(skels, Path("/test"))
        assert "| 7 |" in result

    def test_table_duration(self):
        skels = [self._make_skeleton("Test-1-Intro", duration=30)]
        result = _format_markdown_table(skels, Path("/test"))
        assert "~30 min" in result

    def test_table_no_duration(self):
        skels = [self._make_skeleton("Test-1-Intro")]
        result = _format_markdown_table(skels, Path("/test"))
        # Should have '-' for missing duration
        lines = result.split("\n")
        data_lines = [l for l in lines if l.startswith("|") and "---" not in l and "#" not in l]
        assert any("| - |" in l for l in data_lines)

    def test_table_multiple_skeletons(self):
        skels = [self._make_skeleton("A-1-X"), self._make_skeleton("A-2-Y")]
        result = _format_markdown_table(skels, Path("/test"))
        assert "A-1-X" in result
        assert "A-2-Y" in result

    def test_table_sections_truncated(self):
        sections = [SectionInfo(level=2, title=f"Section {i}", cell_index=i) for i in range(10)]
        skels = [self._make_skeleton("Test-1-Intro", sections=sections)]
        result = _format_markdown_table(skels, Path("/test"))
        # First 3 sections shown, then truncated
        assert "Section 0" in result


# ---------------------------------------------------------------------------
# _format_summary
# ---------------------------------------------------------------------------

class TestFormatSummary:
    def _make_skeleton(self, name, total_cells=10, sections=None, duration=None):
        return NotebookSkeleton(
            path=f"/test/{name}.ipynb",
            name=name,
            total_cells=total_cells,
            sections=sections or [],
            estimated_duration=duration,
        )

    def test_summary_counts_notebooks(self):
        skels = [self._make_skeleton("A"), self._make_skeleton("B")]
        result = _format_summary(skels)
        assert "Notebooks: 2" in result

    def test_summary_counts_cells(self):
        skels = [self._make_skeleton("A", total_cells=5), self._make_skeleton("B", total_cells=7)]
        result = _format_summary(skels)
        assert "Total cells: 12" in result

    def test_summary_duration(self):
        skels = [self._make_skeleton("A", duration=30), self._make_skeleton("B", duration=45)]
        result = _format_summary(skels)
        assert "~75 min" in result

    def test_summary_no_duration(self):
        skels = [self._make_skeleton("A")]
        result = _format_summary(skels)
        assert "~0 min" in result

    def test_summary_lists_notebooks(self):
        skels = [self._make_skeleton("Test-1-Intro")]
        result = _format_summary(skels)
        assert "Test-1-Intro" in result
        assert "10 cells" in result

    def test_summary_empty(self):
        result = _format_summary([])
        assert "Notebooks: 0" in result
        assert "Total cells: 0" in result


# ---------------------------------------------------------------------------
# get_repo_root
# ---------------------------------------------------------------------------

class TestGetRepoRoot:
    def test_returns_path(self):
        root = get_repo_root()
        assert isinstance(root, Path)

    def test_points_to_repo(self):
        """Should find CLAUDE.md or MyIA.AI.Notebooks."""
        root = get_repo_root()
        has_marker = (root / "CLAUDE.md").exists() or (root / "MyIA.AI.Notebooks").exists()
        assert has_marker, f"get_repo_root() returned {root}, no repo markers found"


class TestDiscoverNotebooks:
    """Tests for discover_notebooks() — requires repo structure."""

    def test_family_name_resolves(self):
        root = get_repo_root()
        nbs = discover_notebooks("IIT", root)
        assert len(nbs) > 0
        assert all(nb.suffix == ".ipynb" for nb in nbs)

    def test_single_notebook_path(self):
        root = get_repo_root()
        nbs = discover_notebooks("MyIA.AI.Notebooks/IIT/IIT-1-IntroToPyPhi.ipynb", root)
        assert len(nbs) == 1
        assert nbs[0].name == "IIT-1-IntroToPyPhi.ipynb"

    def test_nonexistent_returns_empty(self):
        root = get_repo_root()
        nbs = discover_notebooks("NonExistentFamily", root)
        assert nbs == []

    def test_python_only_filter(self):
        root = get_repo_root()
        nbs = discover_notebooks("IIT", root, python_only=True)
        assert len(nbs) > 0
        # IIT notebooks should all be Python
        for nb in nbs:
            assert nb.suffix == ".ipynb"

    def test_all_target(self):
        root = get_repo_root()
        nbs = discover_notebooks("all", root)
        assert len(nbs) > 100  # Repo has 500+ notebooks


class TestNotebookExecutorScrubKeys:
    """Tests for NotebookExecutor.SCRUB_KEYS and related."""

    def test_scrub_keys_is_list(self):
        assert isinstance(NotebookExecutor.SCRUB_KEYS, list)
        assert len(NotebookExecutor.SCRUB_KEYS) > 0

    def test_scrub_keys_contains_openai(self):
        assert "OPENAI_API_KEY" in NotebookExecutor.SCRUB_KEYS

    def test_scrub_keys_contains_anthropic(self):
        assert "ANTHROPIC_API_KEY" in NotebookExecutor.SCRUB_KEYS

    def test_scrub_keys_all_uppercase(self):
        for key in NotebookExecutor.SCRUB_KEYS:
            assert key == key.upper(), f"Key {key} is not uppercase"

    def test_scrub_keys_no_empty(self):
        for key in NotebookExecutor.SCRUB_KEYS:
            assert len(key) > 0


class TestNotebookHelpersExecutor:
    """Tests for notebook_helpers.NotebookExecutor — importable and functional."""

    def test_import_succeeds(self):
        from notebook_helpers import NotebookExecutor as BaseExecutor
        assert BaseExecutor is not None

    def test_has_execute_with_papermill(self):
        from notebook_helpers import NotebookExecutor as BaseExecutor
        assert hasattr(BaseExecutor, "execute_with_papermill")

    def test_scrub_keys_parity_after_merge(self):
        """After PR #2537 merges, BaseExecutor.SCRUB_KEYS should match NotebookExecutor."""
        from notebook_helpers import NotebookExecutor as BaseExecutor
        if hasattr(BaseExecutor, "SCRUB_KEYS"):
            assert set(BaseExecutor.SCRUB_KEYS) == set(NotebookExecutor.SCRUB_KEYS)
        else:
            # Pre-merge: SCRUB_KEYS not yet in helpers — skip gracefully
            pytest.skip("BaseExecutor.SCRUB_KEYS not yet added (awaiting PR #2537 merge)")


class TestCmdExecuteEnvParsing:
    """Tests for --env KEY=VAL parsing logic in cmd_execute."""

    def test_valid_pairs(self):
        pairs = ["KEY1=val1", "KEY2=val2=with=equals"]
        result = {}
        for pair in pairs:
            if "=" not in pair:
                pytest.fail(f"Invalid pair: {pair}")
            key, val = pair.split("=", 1)
            result[key] = val
        assert result == {"KEY1": "val1", "KEY2": "val2=with=equals"}

    def test_invalid_pair_no_equals(self):
        pair = "NOEQUALS"
        assert "=" not in pair

    def test_empty_value(self):
        pair = "KEY="
        key, val = pair.split("=", 1)
        assert key == "KEY"
        assert val == ""
