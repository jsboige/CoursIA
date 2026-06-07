"""Tests for scripts/notebook_tools/extract_notebook_skeleton.py — notebook skeleton extractor.

Tests focus on pure functions: extract_cell_preview, detect_kernel,
extract_sections, estimate_duration, analyze_notebook, discover_notebooks,
format_summary.
"""

import json
import math
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from extract_notebook_skeleton import (
    CellInfo,
    NotebookSkeleton,
    SectionInfo,
    analyze_notebook,
    detect_kernel,
    discover_notebooks,
    estimate_duration,
    extract_cell_preview,
    extract_sections,
    format_summary,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _code(source: str, outputs: list | None = None) -> dict:
    return {
        "cell_type": "code",
        "source": [source],
        "execution_count": 1,
        "outputs": outputs or [],
    }


def _md(source: str) -> dict:
    return {"cell_type": "markdown", "source": [source]}


def _write_nb(path: Path, cells: list[dict], metadata: dict | None = None) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    nb = {"cells": cells, "metadata": metadata or {}, "nbformat": 4, "nbformat_minor": 5}
    path.write_text(json.dumps(nb), encoding="utf-8")
    return path


# ---------------------------------------------------------------------------
# extract_cell_preview
# ---------------------------------------------------------------------------

class TestExtractCellPreview:
    """Tests for cell preview extraction."""

    def test_simple_code(self):
        result = extract_cell_preview("x = 1\ny = 2")
        assert "x = 1" in result
        assert "y = 2" in result

    def test_empty_source(self):
        result = extract_cell_preview("")
        assert result == ""

    def test_magic_commands_filtered(self):
        """Lines starting with #! or % are filtered out."""
        result = extract_cell_preview("#!import foo\nx = 1")
        assert "#!" not in result
        assert "x = 1" in result

    def test_percent_magic_filtered(self):
        result = extract_cell_preview("%matplotlib inline\nx = 1")
        assert "%" not in result
        assert "x = 1" in result

    def test_max_lines_limit(self):
        """Only max_lines (default 3) lines included."""
        code = "\n".join(f"line{i}" for i in range(10))
        result = extract_cell_preview(code)
        # Should have at most 3 code lines joined
        assert result.count("line") <= 3

    def test_max_chars_truncation(self):
        """Preview truncated at max_chars (default 150)."""
        code = "x = " + "a" * 200
        result = extract_cell_preview(code, max_chars=50)
        assert len(result) <= 53  # 50 + "..."
        assert result.endswith("...")

    def test_comment_lines_included(self):
        """Regular comments (not #! or %) are included."""
        result = extract_cell_preview("# This is a comment\nx = 1")
        assert "comment" in result

    def test_blank_lines_skipped(self):
        result = extract_cell_preview("\n\nx = 1\n\n")
        assert result.strip() == "x = 1"


# ---------------------------------------------------------------------------
# detect_kernel
# ---------------------------------------------------------------------------

class TestDetectKernel:
    """Tests for kernel detection from notebook metadata."""

    def test_python_kernel(self):
        nb = {"metadata": {"kernelspec": {"name": "python3", "language": "python"}}}
        assert detect_kernel(nb) == "Python"

    def test_dotnet_csharp_kernel(self):
        nb = {"metadata": {"kernelspec": {"name": ".net-csharp", "language": "C#"}}}
        assert detect_kernel(nb) == ".NET C#"

    def test_fsharp_kernel(self):
        nb = {"metadata": {"kernelspec": {"name": ".net-fsharp", "language": "F#"}}}
        # .net-fsharp contains ".net" so it matches .NET C# first (implementation order)
        assert detect_kernel(nb) == ".NET C#"

    def test_lean_kernel(self):
        nb = {"metadata": {"kernelspec": {"name": "lean4", "language": "lean4"}}}
        assert detect_kernel(nb) == "Lean 4"

    def test_wsl_python(self):
        nb = {"metadata": {"kernelspec": {
            "name": "python3", "language": "python",
            "display_name": "Python 3 (WSL)"
        }}}
        assert detect_kernel(nb) == "Python (WSL)"

    def test_unknown_kernel(self):
        nb = {"metadata": {"kernelspec": {"name": "julia", "language": "julia"}}}
        assert detect_kernel(nb) == "Unknown"

    def test_no_metadata(self):
        assert detect_kernel({}) == "Unknown"

    def test_dotnet_from_cell_magic(self):
        """Detect .NET C# from #!import magic in code cells."""
        nb = {
            "metadata": {},
            "cells": [{"cell_type": "code", "source": ["#!import foo\n"]}],
        }
        assert detect_kernel(nb) == ".NET C#"

    def test_display_name_fallback(self):
        nb = {"metadata": {"kernelspec": {"name": "custom", "display_name": "My Custom Kernel"}}}
        assert detect_kernel(nb) == "My Custom Kernel"


# ---------------------------------------------------------------------------
# extract_sections
# ---------------------------------------------------------------------------

class TestExtractSections:
    """Tests for section extraction from markdown cells."""

    def test_h1_section(self):
        cells = [_md("# Title")]
        sections = extract_sections(cells)
        assert len(sections) == 1
        assert sections[0].level == 1
        assert sections[0].title == "Title"

    def test_multiple_headings(self):
        cells = [_md("# Title\n## Subtitle\n### Detail")]
        sections = extract_sections(cells)
        assert len(sections) == 3
        assert sections[0].level == 1
        assert sections[1].level == 2
        assert sections[2].level == 3

    def test_max_depth_filter(self):
        """Only headings up to max_depth are included."""
        cells = [_md("# H1\n## H2\n### H3\n#### H4")]
        sections = extract_sections(cells, max_depth=2)
        assert len(sections) == 2
        assert sections[0].level == 1
        assert sections[1].level == 2

    def test_code_cells_ignored(self):
        cells = [_code("x = 1")]
        sections = extract_sections(cells)
        assert sections == []

    def test_no_headings(self):
        cells = [_md("Just some text\nwithout headings")]
        sections = extract_sections(cells)
        assert sections == []

    def test_bold_removed_from_title(self):
        cells = [_md("# **Bold Title**")]
        sections = extract_sections(cells)
        assert sections[0].title == "Bold Title"

    def test_link_removed_from_title(self):
        cells = [_md("# [Linked Title](http://example.com)")]
        sections = extract_sections(cells)
        assert sections[0].title == "Linked Title"

    def test_cell_index_correct(self):
        cells = [_md("# First"), _code("x = 1"), _md("## Second")]
        sections = extract_sections(cells)
        assert sections[0].cell_index == 0
        assert sections[1].cell_index == 2

    def test_empty_cells(self):
        sections = extract_sections([])
        assert sections == []


# ---------------------------------------------------------------------------
# estimate_duration
# ---------------------------------------------------------------------------

class TestEstimateDuration:
    """Tests for duration estimation."""

    def test_empty_notebook(self):
        assert estimate_duration({"cells": []}) == 0

    def test_markdown_only(self):
        nb = {"cells": [_md("text")] * 4}
        result = estimate_duration(nb)
        assert result == 2  # 4 * 0.5 = 2.0, ceil = 2

    def test_code_only(self):
        nb = {"cells": [_code("x = 1")] * 3}
        result = estimate_duration(nb)
        assert result == 3  # 3 * 1.0 = 3.0, ceil = 3

    def test_mixed_cells(self):
        nb = {"cells": [_md("text"), _code("x = 1"), _code("y = 2")]}
        result = estimate_duration(nb)
        # 1*0.5 + 2*1.0 = 2.5, ceil = 3
        assert result == 3

    def test_returns_int(self):
        nb = {"cells": [_md("a"), _code("b")]}
        result = estimate_duration(nb)
        assert isinstance(result, int)


# ---------------------------------------------------------------------------
# analyze_notebook
# ---------------------------------------------------------------------------

class TestAnalyzeNotebook:
    """Tests for full notebook analysis."""

    def test_complete_notebook(self, tmp_path):
        nb_path = _write_nb(tmp_path / "test.ipynb", [
            _md("# My Notebook"),
            _md("## Section 1"),
            _code("x = 1", outputs=[{"output_type": "stream"}]),
            _code("y = 2"),
            _md("### Detail"),
        ], metadata={"kernelspec": {"name": "python3", "language": "python"}})

        skel = analyze_notebook(nb_path)
        assert skel.title == "My Notebook"
        assert skel.kernel == "Python"
        assert skel.total_cells == 5
        assert skel.markdown_cells == 3
        assert skel.code_cells == 2
        assert skel.cells_with_output == 1
        assert len(skel.sections) == 3  # H1, H2, H3
        assert skel.estimated_duration > 0

    def test_no_title(self, tmp_path):
        nb_path = _write_nb(tmp_path / "notitle.ipynb", [
            _md("Some text"),
            _code("x = 1"),
        ])
        skel = analyze_notebook(nb_path)
        assert skel.title is None

    def test_invalid_file(self, tmp_path):
        bad = tmp_path / "bad.ipynb"
        bad.write_text("not json{{{", encoding="utf-8")
        skel = analyze_notebook(bad)
        assert skel.title is not None
        assert "Error" in skel.title

    def test_no_code_preview(self, tmp_path):
        nb_path = _write_nb(tmp_path / "test.ipynb", [
            _code("x = 1"),
        ])
        skel = analyze_notebook(nb_path, include_code_preview=False)
        assert skel.code_previews == []

    def test_code_preview_populated(self, tmp_path):
        nb_path = _write_nb(tmp_path / "test.ipynb", [
            _code("x = 1 + 2"),
        ])
        skel = analyze_notebook(nb_path, include_code_preview=True)
        assert len(skel.code_previews) == 1
        assert skel.code_previews[0].line_count == 1

    def test_empty_code_cell_skipped(self, tmp_path):
        nb_path = _write_nb(tmp_path / "test.ipynb", [
            _code(""),
        ])
        skel = analyze_notebook(nb_path, include_code_preview=True)
        assert skel.code_previews == []

    def test_to_dict(self, tmp_path):
        nb_path = _write_nb(tmp_path / "test.ipynb", [
            _md("# Title"),
            _code("x = 1", outputs=[{"output_type": "stream"}]),
        ])
        skel = analyze_notebook(nb_path)
        d = skel.to_dict()
        assert d["title"] == "Title"
        assert d["total_cells"] == 2
        assert isinstance(d["sections"], list)
        assert isinstance(d["code_previews"], list)

    def test_code_previews_limited_to_20(self, tmp_path):
        """Code previews are capped at 20."""
        nb_path = _write_nb(tmp_path / "test.ipynb", [
            _code(f"x{i} = {i}") for i in range(30)
        ])
        skel = analyze_notebook(nb_path)
        assert len(skel.code_previews) == 20


# ---------------------------------------------------------------------------
# discover_notebooks
# ---------------------------------------------------------------------------

class TestDiscoverNotebooks:
    """Tests for notebook discovery."""

    def test_single_file(self, tmp_path):
        nb = tmp_path / "test.ipynb"
        nb.write_text("{}", encoding="utf-8")
        result = discover_notebooks(nb)
        assert len(result) == 1

    def test_directory_scan(self, tmp_path):
        for name in ["a.ipynb", "b.ipynb", "c.txt"]:
            (tmp_path / name).write_text("{}", encoding="utf-8")
        result = discover_notebooks(tmp_path, recursive=False)
        assert len(result) == 2

    def test_recursive_scan(self, tmp_path):
        (tmp_path / "sub").mkdir()
        (tmp_path / "root.ipynb").write_text("{}", encoding="utf-8")
        (tmp_path / "sub" / "nested.ipynb").write_text("{}", encoding="utf-8")
        result = discover_notebooks(tmp_path, recursive=True)
        assert len(result) == 2

    def test_non_recursive_skips_subdirs(self, tmp_path):
        (tmp_path / "sub").mkdir()
        (tmp_path / "root.ipynb").write_text("{}", encoding="utf-8")
        (tmp_path / "sub" / "nested.ipynb").write_text("{}", encoding="utf-8")
        result = discover_notebooks(tmp_path, recursive=False)
        assert len(result) == 1

    def test_exclude_checkpoints(self, tmp_path):
        (tmp_path / "good.ipynb").write_text("{}", encoding="utf-8")
        cp = tmp_path / ".ipynb_checkpoints"
        cp.mkdir()
        (cp / "bad.ipynb").write_text("{}", encoding="utf-8")
        result = discover_notebooks(tmp_path, recursive=True)
        names = [p.name for p in result]
        assert "good.ipynb" in names
        assert "bad.ipynb" not in names

    def test_default_exclusions_added(self, tmp_path):
        """Default exclusions (.ipynb_checkpoints, _output, archive) are always applied."""
        base = tmp_path / "nbdir"
        base.mkdir()
        (base / "good.ipynb").write_text("{}", encoding="utf-8")
        cp = base / ".ipynb_checkpoints"
        cp.mkdir()
        (cp / "bad.ipynb").write_text("{}", encoding="utf-8")
        result = discover_notebooks(base, recursive=True)
        assert len(result) == 1

    def test_custom_exclude_patterns(self, tmp_path):
        """Custom exclude patterns filter matching directories."""
        base = tmp_path / "nbdir"
        base.mkdir()
        (base / "good.ipynb").write_text("{}", encoding="utf-8")
        excluded = base / "myexcluded"
        excluded.mkdir()
        (excluded / "bad.ipynb").write_text("{}", encoding="utf-8")
        result = discover_notebooks(base, recursive=True, exclude_patterns=["myexcluded"])
        assert len(result) == 1

    def test_nonexistent_path(self, tmp_path):
        result = discover_notebooks(tmp_path / "missing")
        assert result == []


# ---------------------------------------------------------------------------
# format_summary
# ---------------------------------------------------------------------------

class TestFormatSummary:
    """Tests for summary formatting."""

    def test_empty_list(self):
        result = format_summary([])
        assert "Notebooks: 0" in result

    def test_single_notebook(self):
        skel = NotebookSkeleton(
            path="/path/test.ipynb", name="test",
            title="Test NB", kernel="Python",
            total_cells=5, markdown_cells=2, code_cells=3,
            cells_with_output=2, estimated_duration=10,
        )
        result = format_summary([skel])
        assert "Notebooks: 1" in result
        assert "Cellules totales: 5" in result
        assert "test" in result

    def test_multiple_notebooks(self):
        skels = [
            NotebookSkeleton(path=f"/p/{i}.ipynb", name=f"nb{i}", total_cells=i + 1,
                           markdown_cells=1, code_cells=i,
                           estimated_duration=i * 2)
            for i in range(3)
        ]
        result = format_summary(skels)
        assert "Notebooks: 3" in result
        assert "Cellules totales: 6" in result


# ---------------------------------------------------------------------------
# Dataclasses
# ---------------------------------------------------------------------------

class TestDataclasses:
    """Tests for dataclass structure."""

    def test_cell_info_creation(self):
        ci = CellInfo(cell_type="code", index=0, preview="x = 1", line_count=1)
        assert ci.cell_type == "code"
        assert ci.has_output is False
        assert ci.output_type is None

    def test_section_info_creation(self):
        si = SectionInfo(level=2, title="Section", cell_index=3)
        assert si.level == 2
        assert si.title == "Section"

    def test_notebook_skeleton_defaults(self):
        skel = NotebookSkeleton(path="test.ipynb", name="test")
        assert skel.total_cells == 0
        assert skel.kernel == "unknown"
        assert skel.title is None
        assert skel.sections == []
        assert skel.code_previews == []
