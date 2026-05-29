"""Tests for auto_enrich_notebooks.py — notebook enrichment ratio and cell creation."""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).parent.parent))
from auto_enrich_notebooks import (
    calculate_ratio,
    create_interpretation_cell,
    load_notebook,
    save_notebook,
)


def _nb(cells: list[dict]) -> dict:
    """Build a minimal notebook dict."""
    return {
        "cells": cells,
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }


# --- calculate_ratio ---


class TestCalculateRatio:
    def test_all_markdown(self):
        nb = _nb([
            {"cell_type": "markdown", "source": ["# Title"]},
            {"cell_type": "markdown", "source": ["## Section"]},
        ])
        assert calculate_ratio(nb) == 100.0

    def test_all_code(self):
        nb = _nb([
            {"cell_type": "code", "source": ["x = 1"]},
            {"cell_type": "code", "source": ["y = 2"]},
        ])
        assert calculate_ratio(nb) == 0.0

    def test_balanced(self):
        nb = _nb([
            {"cell_type": "markdown", "source": ["text"]},
            {"cell_type": "code", "source": ["x = 1"]},
        ])
        assert calculate_ratio(nb) == 50.0

    def test_empty_notebook(self):
        nb = _nb([])
        assert calculate_ratio(nb) == 0.0

    def test_three_code_one_md(self):
        nb = _nb([
            {"cell_type": "markdown", "source": ["text"]},
            {"cell_type": "code", "source": ["x = 1"]},
            {"cell_type": "code", "source": ["y = 2"]},
            {"cell_type": "code", "source": ["z = 3"]},
        ])
        assert calculate_ratio(nb) == 25.0

    def test_ignores_raw_cells(self):
        """Non-markdown, non-code cells are not counted in total."""
        nb = _nb([
            {"cell_type": "markdown", "source": ["text"]},
            {"cell_type": "raw", "source": ["raw content"]},
        ])
        # md=1, code=0, total=1 -> 100%
        assert calculate_ratio(nb) == 100.0


# --- create_interpretation_cell ---


class TestCreateInterpretationCell:
    def test_returns_markdown(self):
        cell = create_interpretation_cell("Test", "Some content")
        assert cell["cell_type"] == "markdown"

    def test_contains_title(self):
        cell = create_interpretation_cell("My Analysis", "Body text")
        source = "".join(cell["source"])
        assert "My Analysis" in source

    def test_contains_content(self):
        cell = create_interpretation_cell("Title", "Line1\nLine2")
        source = "".join(cell["source"])
        assert "Line1" in source
        assert "Line2" in source

    def test_source_is_list(self):
        cell = create_interpretation_cell("Title", "Content")
        assert isinstance(cell["source"], list)

    def test_has_metadata(self):
        cell = create_interpretation_cell("Title", "Content")
        assert "metadata" in cell

    def test_interpretation_header_prefix(self):
        cell = create_interpretation_cell("Plot", "desc")
        source = "".join(cell["source"])
        assert "Interprétation - Plot" in source


# --- load_notebook / save_notebook ---


class TestLoadSaveNotebook:
    def test_roundtrip(self, tmp_path):
        nb = _nb([
            {"cell_type": "code", "source": ["x = 1"]},
        ])
        p = tmp_path / "test.ipynb"
        save_notebook(p, nb)
        loaded = load_notebook(p)
        assert loaded["cells"] == nb["cells"]

    def test_save_creates_file(self, tmp_path):
        p = tmp_path / "new.ipynb"
        save_notebook(p, _nb([]))
        assert p.exists()

    def test_load_nonexistent_raises(self, tmp_path):
        with pytest.raises(FileNotFoundError):
            load_notebook(tmp_path / "nope.ipynb")

    def test_save_preserves_unicode(self, tmp_path):
        nb = _nb([
            {"cell_type": "markdown", "source": ["# Résumé\nInterprétation"]},
        ])
        p = tmp_path / "unicode.ipynb"
        save_notebook(p, nb)
        loaded = load_notebook(p)
        assert "Résumé" in "".join(loaded["cells"][0]["source"])
