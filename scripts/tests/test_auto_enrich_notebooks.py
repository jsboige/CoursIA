"""Tests for scripts/notebook_tools/auto_enrich_notebooks.py — auto enrichment.

Tests focus on pure functions: calculate_ratio, create_interpretation_cell,
load_notebook, save_notebook, enrich_notebook — covering ratio calculation,
cell creation, skip/success/no_change status, insertion order, edge cases.
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "notebook_tools"))
from auto_enrich_notebooks import (
    calculate_ratio,
    create_interpretation_cell,
    enrich_notebook,
    load_notebook,
    save_notebook,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _code(source: str | list, outputs: list | None = None, cell_id: str | None = None) -> dict:
    cell = {
        "cell_type": "code",
        "source": [source] if isinstance(source, str) else source,
        "execution_count": 1,
        "outputs": outputs or [],
    }
    if cell_id is not None:
        cell["id"] = cell_id
    return cell


def _md(source: str, cell_id: str | None = None) -> dict:
    cell = {"cell_type": "markdown", "source": [source], "metadata": {}}
    if cell_id is not None:
        cell["id"] = cell_id
    return cell


def _write_nb(path: Path, cells: list[dict], metadata: dict | None = None) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    nb = {"cells": cells, "metadata": metadata or {}, "nbformat": 4, "nbformat_minor": 5}
    path.write_text(json.dumps(nb), encoding="utf-8")
    return path


# ---------------------------------------------------------------------------
# load_notebook / save_notebook
# ---------------------------------------------------------------------------

class TestLoadSaveNotebook:
    """Tests for notebook I/O."""

    def test_load_notebook(self, tmp_path):
        nb_path = _write_nb(tmp_path / "test.ipynb", [_code("x = 1")])
        nb = load_notebook(nb_path)
        assert len(nb["cells"]) == 1
        assert nb["cells"][0]["cell_type"] == "code"

    def test_load_notebook_preserves_metadata(self, tmp_path):
        nb_path = _write_nb(tmp_path / "test.ipynb", [], metadata={"kernelspec": {"name": "python3"}})
        nb = load_notebook(nb_path)
        assert nb["metadata"]["kernelspec"]["name"] == "python3"

    def test_save_notebook_creates_file(self, tmp_path):
        nb_path = tmp_path / "output.ipynb"
        nb = {"cells": [_md("# Title")], "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
        save_notebook(nb_path, nb)
        assert nb_path.exists()

        loaded = json.loads(nb_path.read_text(encoding="utf-8"))
        assert len(loaded["cells"]) == 1

    def test_save_load_roundtrip(self, tmp_path):
        original = {"cells": [_code("a = 1"), _md("text")], "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
        nb_path = tmp_path / "roundtrip.ipynb"
        save_notebook(nb_path, original)
        loaded = load_notebook(nb_path)
        assert len(loaded["cells"]) == len(original["cells"])

    def test_save_notebook_utf8_encoding(self, tmp_path):
        nb_path = tmp_path / "unicode.ipynb"
        nb = {"cells": [_md("# Titre avec accents: ecaud")], "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
        save_notebook(nb_path, nb)
        content = nb_path.read_text(encoding="utf-8")
        assert "ecaud" in content


# ---------------------------------------------------------------------------
# calculate_ratio
# ---------------------------------------------------------------------------

class TestCalculateRatio:
    """Tests for markdown/code ratio calculation."""

    def test_equal_mix(self):
        nb = {"cells": [_code("x = 1"), _md("text"), _code("y = 2"), _md("more")]}
        assert calculate_ratio(nb) == 50.0

    def test_all_markdown(self):
        nb = {"cells": [_md("a"), _md("b"), _md("c")]}
        assert calculate_ratio(nb) == 100.0

    def test_all_code(self):
        nb = {"cells": [_code("x = 1"), _code("y = 2")]}
        assert calculate_ratio(nb) == 0.0

    def test_empty_notebook(self):
        nb = {"cells": []}
        assert calculate_ratio(nb) == 0.0

    def test_single_markdown(self):
        nb = {"cells": [_md("only md")]}
        assert calculate_ratio(nb) == 100.0

    def test_single_code(self):
        nb = {"cells": [_code("only code")]}
        assert calculate_ratio(nb) == 0.0

    def test_three_markdown_one_code(self):
        nb = {"cells": [_md("a"), _md("b"), _md("c"), _code("x = 1")]}
        assert calculate_ratio(nb) == 75.0

    def test_raw_cells_ignored(self):
        """Raw cells don't count as markdown or code."""
        nb = {"cells": [
            {"cell_type": "raw", "source": ["raw content"], "metadata": {}},
            _code("x = 1"),
        ]}
        assert calculate_ratio(nb) == 0.0


# ---------------------------------------------------------------------------
# create_interpretation_cell
# ---------------------------------------------------------------------------

class TestCreateInterpretationCell:
    """Tests for interpretation cell creation."""

    def test_returns_markdown_cell(self):
        cell = create_interpretation_cell("Test", "Some content")
        assert cell["cell_type"] == "markdown"

    def test_title_included(self):
        cell = create_interpretation_cell("My Analysis", "content")
        sources = "".join(cell["source"])
        assert "My Analysis" in sources

    def test_content_included(self):
        cell = create_interpretation_cell("Title", "Line 1\nLine 2")
        sources = "".join(cell["source"])
        assert "Line 1" in sources
        assert "Line 2" in sources

    def test_source_is_list(self):
        cell = create_interpretation_cell("Title", "Content")
        assert isinstance(cell["source"], list)

    def test_has_metadata(self):
        cell = create_interpretation_cell("Title", "Content")
        assert "metadata" in cell

    def test_empty_content(self):
        cell = create_interpretation_cell("Title", "")
        assert cell["cell_type"] == "markdown"

    def test_multiline_content(self):
        content = "First line\nSecond line\nThird line"
        cell = create_interpretation_cell("Title", content)
        sources = "".join(cell["source"])
        assert "First line" in sources
        assert "Third line" in sources

    def test_separator_present(self):
        cell = create_interpretation_cell("Title", "Content")
        sources = "".join(cell["source"])
        assert "---" in sources


# ---------------------------------------------------------------------------
# enrich_notebook
# ---------------------------------------------------------------------------

class TestEnrichNotebook:
    """Tests for notebook enrichment logic."""

    def test_skip_when_ratio_sufficient(self, tmp_path):
        """Notebook with ratio >= min_ratio is skipped."""
        nb_path = _write_nb(tmp_path / "test.ipynb", [
            _md("text"), _md("more text"), _md("even more"),
            _code("x = 1"),
        ])
        result = enrich_notebook(nb_path, min_ratio=40.0)
        assert result["status"] == "skip"
        assert result["cells_added"] == 0

    def test_enrich_low_ratio_notebook(self, tmp_path):
        """Notebook with low ratio gets enriched."""
        nb_path = _write_nb(tmp_path / "test.ipynb", [
            _code("x = 1", outputs=[{"output_type": "stream"}]),
            _code("y = 2", outputs=[{"output_type": "stream"}]),
            _code("z = 3"),
        ])
        result = enrich_notebook(nb_path, min_ratio=40.0)
        assert result["status"] == "success"
        assert result["cells_added"] > 0
        assert result["final_ratio"] > result["initial_ratio"]

    def test_no_change_when_no_significant_cells(self, tmp_path):
        """Notebook with no significant code cells -> no_change."""
        nb_path = _write_nb(tmp_path / "test.ipynb", [
            _code("x = 1"),  # short, no output
            _code("y = 2"),  # short, no output
        ])
        result = enrich_notebook(nb_path, min_ratio=40.0)
        # No cells have output or >5 source lines, so none qualify
        assert result["status"] in ("skip", "no_change")

    def test_file_modified_on_success(self, tmp_path):
        """File is written back when enrichment succeeds."""
        nb_path = _write_nb(tmp_path / "test.ipynb", [
            _code("x = 1", outputs=[{"output_type": "stream"}]),
            _code("y = 2"),
            _code("z = 3"),
        ])
        original = nb_path.read_text(encoding="utf-8")
        enrich_notebook(nb_path, min_ratio=40.0)
        # File should be different after enrichment
        modified = nb_path.read_text(encoding="utf-8")
        assert modified != original

    def test_file_not_modified_on_skip(self, tmp_path):
        """File is NOT written when ratio already sufficient."""
        nb_path = _write_nb(tmp_path / "test.ipynb", [
            _md("a"), _md("b"), _md("c"),
            _code("x = 1"),
        ])
        original = nb_path.read_text(encoding="utf-8")
        enrich_notebook(nb_path, min_ratio=40.0)
        assert nb_path.read_text(encoding="utf-8") == original

    def test_insertion_preserves_order(self, tmp_path):
        """Enriched cells are inserted after the corresponding code cell."""
        nb_path = _write_nb(tmp_path / "test.ipynb", [
            _code("x = 1", outputs=[{"output_type": "stream"}], cell_id="c1"),
            _code("y = 2"),
        ])
        enrich_notebook(nb_path, min_ratio=10.0)
        nb = load_notebook(nb_path)
        # First cell should still be code, second should be markdown interpretation
        assert nb["cells"][0]["cell_type"] == "code"
        assert nb["cells"][1]["cell_type"] == "markdown"

    def test_long_source_qualifies(self, tmp_path):
        """Code cell with >5 source lines qualifies even without output."""
        long_source = [f"line{i}" for i in range(7)]  # 7 lines > 5
        nb_path = _write_nb(tmp_path / "test.ipynb", [
            {"cell_type": "code", "source": long_source, "outputs": [], "execution_count": 1},
            _code("short"),
        ])
        result = enrich_notebook(nb_path, min_ratio=40.0)
        assert result["cells_added"] >= 1

    def test_returns_stats(self, tmp_path):
        """Result dict contains required keys."""
        nb_path = _write_nb(tmp_path / "test.ipynb", [
            _code("x = 1", outputs=[{"output_type": "stream"}]),
        ])
        result = enrich_notebook(nb_path, min_ratio=10.0)
        assert "status" in result
        assert "initial_ratio" in result
        assert "final_ratio" in result
        assert "cells_added" in result

    def test_min_ratio_custom(self, tmp_path):
        """Custom min_ratio threshold works."""
        nb_path = _write_nb(tmp_path / "test.ipynb", [
            _md("a"), _code("x = 1"),
        ])
        # 50% ratio, min_ratio=60 -> should try to enrich
        result = enrich_notebook(nb_path, min_ratio=60.0)
        assert result["initial_ratio"] == 50.0

    def test_all_markdown_notebook_skip(self, tmp_path):
        """Notebook with only markdown cells has ratio 100%, skips."""
        nb_path = _write_nb(tmp_path / "test.ipynb", [
            _md("a"), _md("b"), _md("c"),
        ])
        result = enrich_notebook(nb_path, min_ratio=40.0)
        assert result["status"] == "skip"

    def test_enrich_with_multiple_outputs(self, tmp_path):
        """Multiple code cells with outputs all get enriched."""
        nb_path = _write_nb(tmp_path / "test.ipynb", [
            _code("x = 1", outputs=[{"output_type": "stream"}]),
            _code("y = 2", outputs=[{"output_type": "stream"}]),
        ])
        result = enrich_notebook(nb_path, min_ratio=10.0)
        assert result["cells_added"] == 2

    def test_works_backwards_insertion(self, tmp_path):
        """Cells are inserted from end to start (reversed) to preserve indices."""
        nb_path = _write_nb(tmp_path / "test.ipynb", [
            _code("a = 1", outputs=[{"output_type": "stream"}], cell_id="c1"),
            _code("b = 2", outputs=[{"output_type": "stream"}], cell_id="c2"),
        ])
        enrich_notebook(nb_path, min_ratio=10.0)
        nb = load_notebook(nb_path)
        # Should have 4 cells: code, md, code, md
        assert len(nb["cells"]) == 4
        assert nb["cells"][0]["cell_type"] == "code"
        assert nb["cells"][1]["cell_type"] == "markdown"
        assert nb["cells"][2]["cell_type"] == "code"
        assert nb["cells"][3]["cell_type"] == "markdown"
