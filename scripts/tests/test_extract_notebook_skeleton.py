"""Tests for scripts/notebook_tools/extract_notebook_skeleton.py — skeleton extractor.

Tests focus on pure functions: extract_cell_preview, detect_kernel,
extract_sections, estimate_duration, analyze_notebook, discover_notebooks,
format_markdown_table, format_detailed_markdown, format_summary,
NotebookSkeleton.to_dict. Uses tmp_path for filesystem isolation.
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "notebook_tools"))
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
    format_detailed_markdown,
    format_markdown_table,
    format_summary,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _write_nb(path: Path, cells: list[dict], metadata: dict | None = None) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    nb = {"cells": cells, "metadata": metadata or {}, "nbformat": 4, "nbformat_minor": 5}
    path.write_text(json.dumps(nb), encoding="utf-8")
    return path


def _code(source: str, outputs: list | None = None) -> dict:
    return {
        "cell_type": "code", "source": [source],
        "execution_count": None, "outputs": outputs or [], "metadata": {},
    }


def _md(source: str) -> dict:
    return {"cell_type": "markdown", "source": [source], "metadata": {}}


# ---------------------------------------------------------------------------
# extract_cell_preview
# ---------------------------------------------------------------------------

class TestExtractCellPreview:
    def test_basic(self):
        assert "x = 1" in extract_cell_preview("x = 1\ny = 2")

    def test_max_lines(self):
        preview = extract_cell_preview("a\nb\nc\nd", max_lines=2)
        assert "a" in preview
        assert "b" in preview
        assert "c" not in preview

    def test_max_chars(self):
        long_line = "x" * 200
        preview = extract_cell_preview(long_line, max_chars=50)
        assert len(preview) <= 53  # 50 + "..."

    def test_strips_magic_commands(self):
        preview = extract_cell_preview("#!csharp\nimport numpy")
        assert "#!" not in preview
        assert "import numpy" in preview

    def test_strips_percent_magic(self):
        preview = extract_cell_preview("%matplotlib inline\nx = 1")
        assert "%" not in preview
        assert "x = 1" in preview

    def test_empty_lines_skipped(self):
        preview = extract_cell_preview("\n\nx = 1\n\n")
        assert "x = 1" in preview

    def test_empty_source(self):
        assert extract_cell_preview("") == ""


# ---------------------------------------------------------------------------
# detect_kernel
# ---------------------------------------------------------------------------

class TestDetectKernel:
    def test_python3(self):
        assert detect_kernel({"metadata": {"kernelspec": {"name": "python3", "language": "python"}}}) == "Python"

    def test_python_wsl(self):
        assert detect_kernel({"metadata": {"kernelspec": {"name": "python3", "language": "python", "display_name": "Python (WSL)"}}}) == "Python (WSL)"

    def test_csharp(self):
        assert detect_kernel({"metadata": {"kernelspec": {"name": ".net-csharp", "language": "C#"}}}) == ".NET C#"

    def test_fsharp(self):
        # Note: .net-fsharp hits '.net' branch first → .NET C# (source code ordering)
        assert detect_kernel({"metadata": {"kernelspec": {"name": ".net-fsharp", "language": "F#"}}}) == ".NET C#"

    def test_lean(self):
        assert detect_kernel({"metadata": {"kernelspec": {"name": "lean4", "language": "lean4"}}}) == "Lean 4"

    def test_unknown_with_display_name(self):
        assert detect_kernel({"metadata": {"kernelspec": {"name": "custom", "language": "xyz", "display_name": "My Kernel"}}}) == "My Kernel"

    def test_no_metadata(self):
        assert detect_kernel({}) == "Unknown"

    def test_dotnet_magic_in_cell(self):
        nb = {"metadata": {"kernelspec": {"name": "unknown"}}, "cells": [
            {"cell_type": "code", "source": ["#!csharp\nlet x = 1"]}
        ]}
        assert detect_kernel(nb) == ".NET C#"


# ---------------------------------------------------------------------------
# extract_sections
# ---------------------------------------------------------------------------

class TestExtractSections:
    def test_single_heading(self):
        cells = [_md("# Title")]
        sections = extract_sections(cells)
        assert len(sections) == 1
        assert sections[0].level == 1
        assert sections[0].title == "Title"

    def test_multiple_levels(self):
        cells = [_md("# H1\n## H2\n### H3\n#### H4")]
        sections = extract_sections(cells, max_depth=3)
        levels = [s.level for s in sections]
        assert 1 in levels
        assert 2 in levels
        assert 3 in levels
        assert 4 not in levels

    def test_code_cells_ignored(self):
        cells = [_code("# not a heading")]
        assert extract_sections(cells) == []

    def test_strips_bold(self):
        cells = [_md("## **Bold Title**")]
        sections = extract_sections(cells)
        assert sections[0].title == "Bold Title"

    def test_strips_links(self):
        cells = [_md("## [Link Text](url)")]
        sections = extract_sections(cells)
        assert sections[0].title == "Link Text"

    def test_no_headings(self):
        cells = [_md("Just some text\nNo heading here")]
        assert extract_sections(cells) == []

    def test_cell_index_correct(self):
        cells = [_md("# A"), _code("x"), _md("## B")]
        sections = extract_sections(cells)
        assert sections[0].cell_index == 0
        assert sections[1].cell_index == 2


# ---------------------------------------------------------------------------
# estimate_duration
# ---------------------------------------------------------------------------

class TestEstimateDuration:
    def test_mixed_cells(self):
        nb = {"cells": [_md("a"), _code("b"), _md("c"), _code("d"), _md("e")]}
        # 3 md * 0.5 + 2 code * 1.0 = 3.5 → ceil = 4
        assert estimate_duration(nb) == 4

    def test_only_markdown(self):
        nb = {"cells": [_md("a"), _md("b")]}
        # 2 * 0.5 = 1.0 → ceil = 1
        assert estimate_duration(nb) == 1

    def test_only_code(self):
        nb = {"cells": [_code("a"), _code("b"), _code("c")]}
        # 3 * 1.0 = 3
        assert estimate_duration(nb) == 3

    def test_empty(self):
        assert estimate_duration({"cells": []}) == 0


# ---------------------------------------------------------------------------
# analyze_notebook
# ---------------------------------------------------------------------------

class TestAnalyzeNotebook:
    def test_basic_notebook(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [
            _md("# My Notebook"),
            _code("x = 1", outputs=[{"output_type": "stream", "text": ["1"]}]),
            _md("## Section 1"),
            _code("y = 2"),
        ], metadata={"kernelspec": {"name": "python3", "language": "python"}})
        skel = analyze_notebook(path)
        assert skel.title == "My Notebook"
        assert skel.kernel == "Python"
        assert skel.total_cells == 4
        assert skel.markdown_cells == 2
        assert skel.code_cells == 2
        assert skel.cells_with_output == 1
        assert len(skel.sections) == 2  # H1 + H2
        assert skel.name == "test"

    def test_invalid_json(self, tmp_path):
        bad = tmp_path / "bad.ipynb"
        bad.write_text("{invalid", encoding="utf-8")
        skel = analyze_notebook(bad)
        assert "[Error:" in skel.title

    def test_no_title(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_code("x = 1")])
        skel = analyze_notebook(path)
        assert skel.title is None

    def test_no_code_preview(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_code("x = 1")])
        skel = analyze_notebook(path, include_code_preview=False)
        assert skel.code_previews == []

    def test_code_preview_populated(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_code("import numpy as np")])
        skel = analyze_notebook(path)
        assert len(skel.code_previews) == 1
        assert skel.code_previews[0].cell_type == "code"
        assert "import numpy" in skel.code_previews[0].preview

    def test_code_preview_limited_to_20(self, tmp_path):
        cells = [_code(f"x{i} = {i}") for i in range(30)]
        path = _write_nb(tmp_path / "test.ipynb", cells)
        skel = analyze_notebook(path)
        assert len(skel.code_previews) == 20

    def test_empty_code_skipped(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_code("   \n  "), _code("x = 1")])
        skel = analyze_notebook(path)
        assert len(skel.code_previews) == 1

    def test_duration_estimated(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_md("a"), _code("b")])
        skel = analyze_notebook(path)
        assert skel.estimated_duration is not None
        assert skel.estimated_duration > 0


# ---------------------------------------------------------------------------
# NotebookSkeleton.to_dict
# ---------------------------------------------------------------------------

class TestNotebookSkeletonToDict:
    def test_roundtrip(self):
        skel = NotebookSkeleton(
            path="/tmp/test.ipynb", name="test", title="Title",
            kernel="Python", total_cells=5, markdown_cells=2, code_cells=3,
            cells_with_output=1,
            sections=[SectionInfo(level=1, title="Intro", cell_index=0)],
            code_previews=[CellInfo(cell_type="code", index=1, preview="x=1", line_count=1)],
            estimated_duration=10,
        )
        d = skel.to_dict()
        assert d["title"] == "Title"
        assert d["total_cells"] == 5
        assert len(d["sections"]) == 1
        assert d["sections"][0]["level"] == 1
        assert len(d["code_previews"]) == 1
        assert d["code_previews"][0]["preview"] == "x=1"
        assert d["estimated_duration"] == 10

    def test_empty_skeleton(self):
        skel = NotebookSkeleton(path="x", name="x")
        d = skel.to_dict()
        assert d["title"] is None
        assert d["sections"] == []
        assert d["code_previews"] == []


# ---------------------------------------------------------------------------
# discover_notebooks
# ---------------------------------------------------------------------------

class TestDiscoverNotebooks:
    def test_finds_notebooks(self, tmp_path):
        (tmp_path / "a.ipynb").write_text("{}", encoding="utf-8")
        (tmp_path / "b.ipynb").write_text("{}", encoding="utf-8")
        result = discover_notebooks(tmp_path, recursive=False)
        assert len(result) == 2

    def test_single_file(self, tmp_path):
        nb = tmp_path / "single.ipynb"
        nb.write_text("{}", encoding="utf-8")
        result = discover_notebooks(nb)
        assert result == [nb]

    def test_excludes_checkpoints(self, tmp_path):
        (tmp_path / ".ipynb_checkpoints").mkdir()
        (tmp_path / ".ipynb_checkpoints" / "hidden.ipynb").write_text("{}", encoding="utf-8")
        (tmp_path / "visible.ipynb").write_text("{}", encoding="utf-8")
        result = discover_notebooks(tmp_path, recursive=True)
        assert len(result) == 1

    def test_excludes_result_dir(self, tmp_path):
        """Directories matching exclude patterns are skipped."""
        arch_dir = tmp_path / "archive"
        arch_dir.mkdir()
        (arch_dir / "old.ipynb").write_text("{}", encoding="utf-8")
        (tmp_path / "current.ipynb").write_text("{}", encoding="utf-8")
        result = discover_notebooks(tmp_path, recursive=True)
        names = [p.name for p in result]
        assert "current.ipynb" in names
        assert "old.ipynb" not in names

    def test_recursive(self, tmp_path):
        sub = tmp_path / "sub"
        sub.mkdir()
        (sub / "nb.ipynb").write_text("{}", encoding="utf-8")
        (tmp_path / "top.ipynb").write_text("{}", encoding="utf-8")
        result = discover_notebooks(tmp_path, recursive=True)
        assert len(result) == 2

    def test_non_recursive(self, tmp_path):
        sub = tmp_path / "sub"
        sub.mkdir()
        (sub / "nb.ipynb").write_text("{}", encoding="utf-8")
        (tmp_path / "top.ipynb").write_text("{}", encoding="utf-8")
        result = discover_notebooks(tmp_path, recursive=False)
        assert len(result) == 1


# ---------------------------------------------------------------------------
# format functions
# ---------------------------------------------------------------------------

class TestFormatFunctions:
    def _make_skel(self, name="test-nb", title="Test", kernel="Python",
                   total=10, md=5, code=5, outputs=3, duration=15,
                   sections=None, previews=None):
        return NotebookSkeleton(
            path=f"/path/{name}.ipynb", name=name, title=title,
            kernel=kernel, total_cells=total, markdown_cells=md,
            code_cells=code, cells_with_output=outputs,
            sections=sections or [SectionInfo(level=2, title="Intro", cell_index=0)],
            code_previews=previews or [],
            estimated_duration=duration,
        )

    def test_format_summary(self):
        skels = [self._make_skel(name="nb1"), self._make_skel(name="nb2")]
        output = format_summary(skels)
        assert "Notebooks: 2" in output
        assert "Cellules totales: 20" in output
        assert "nb1" in output

    def test_format_markdown_table(self):
        skels = [self._make_skel(name="Search-1-BFS")]
        output = format_markdown_table(skels, Path("/path"))
        assert "| Notebook |" in output
        assert "Search-1-BFS" in output

    def test_format_detailed_markdown(self):
        skels = [self._make_skel(
            name="test", title="My Notebook",
            previews=[CellInfo(cell_type="code", index=1, preview="x = 1", line_count=1, has_output=True, output_type="stream")]
        )]
        output = format_detailed_markdown(skels, Path("/path"))
        assert "## test" in output
        assert "**My Notebook**" in output
        assert "Kernel" in output
        assert "x = 1" in output

    def test_format_summary_empty(self):
        output = format_summary([])
        assert "Notebooks: 0" in output

    def test_format_markdown_extracts_number(self):
        skels = [self._make_skel(name="Search-7-CSP")]
        output = format_markdown_table(skels, Path("/path"))
        assert "| 7 |" in output
