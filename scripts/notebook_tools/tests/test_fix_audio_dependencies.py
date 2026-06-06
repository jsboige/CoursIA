"""Tests for fix_audio_dependencies.py — GPU dependency detection cell creation."""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).parent.parent))
from fix_audio_dependencies import (
    create_dependency_cell,
    find_insert_position,
    fix_notebook,
)


def _config(
    packages=("kokoro-onnx",),
    primary="kokoro-onnx",
    fallback=None,
    secondary=None,
    install="pip install kokoro-onnx",
    description="Test package",
    optional=True,
) -> dict:
    """Build a dependency config dict."""
    cfg = {
        "packages": list(packages),
        "primary": primary,
        "install": install,
        "description": description,
        "optional": optional,
    }
    if fallback:
        cfg["fallback"] = fallback
    if secondary:
        cfg["secondary"] = secondary
    return cfg


# --- create_dependency_cell ---


class TestCreateDependencyCell:
    def test_returns_code_cell(self):
        cell = create_dependency_cell(_config())
        assert cell["cell_type"] == "code"

    def test_source_is_list(self):
        cell = create_dependency_cell(_config())
        assert isinstance(cell["source"], list)

    def test_contains_package_name(self):
        cell = create_dependency_cell(_config(packages=("kokoro-onnx",)))
        source = "".join(cell["source"])
        assert "kokoro_onnx" in source  # import name (dashes -> underscores)

    def test_contains_install_command(self):
        cell = create_dependency_cell(_config(install="pip install kokoro-onnx"))
        source = "".join(cell["source"])
        assert "pip install kokoro-onnx" in source

    def test_contains_description(self):
        cell = create_dependency_cell(_config(description="Kokoro TTS local"))
        source = "".join(cell["source"])
        assert "Kokoro TTS local" in source

    def test_fallback_included(self):
        cell = create_dependency_cell(
            _config(primary="kokoro-onnx", fallback="kokoro", packages=("kokoro-onnx", "kokoro"))
        )
        source = "".join(cell["source"])
        assert "fallback" in source.lower()

    def test_no_outputs(self):
        cell = create_dependency_cell(_config())
        assert cell["outputs"] == []

    def test_execution_count_none(self):
        cell = create_dependency_cell(_config())
        assert cell["execution_count"] is None

    def test_multi_package(self):
        cell = create_dependency_cell(
            _config(packages=("demucs", "torchaudio"), primary="demucs")
        )
        source = "".join(cell["source"])
        assert "demucs" in source
        assert "torchaudio" in source


# --- find_insert_position ---


class TestFindInsertPosition:
    def test_inserts_before_section_header(self):
        cells = [
            {"cell_type": "markdown", "source": ["# Title"]},
            {"cell_type": "code", "source": ["import os"]},
            {"cell_type": "markdown", "source": ["## Section 1"]},
            {"cell_type": "code", "source": ["x = 1"]},
        ]
        pos = find_insert_position(cells)
        assert pos == 2

    def test_fallback_when_no_section(self):
        cells = [
            {"cell_type": "markdown", "source": ["# Title"]},
            {"cell_type": "code", "source": ["x = 1"]},
        ]
        pos = find_insert_position(cells)
        assert pos == 1  # min(3, len(cells) - 1) = min(3, 1) = 1

    def test_empty_cells(self):
        pos = find_insert_position([])
        # min(3, -1) -> -1? No: min(3, len(cells)-1) = min(3, -1)
        # But wait, empty list means no cells, for loop does nothing
        # returns min(3, len(cells) - 1) = min(3, -1) = -1
        assert pos == -1

    def test_single_cell(self):
        cells = [{"cell_type": "markdown", "source": ["# Title"]}]
        pos = find_insert_position(cells)
        assert pos == 0  # min(3, 0) = 0

    def test_many_cells_no_section(self):
        cells = [{"cell_type": "code", "source": [f"x = {i}"]} for i in range(10)]
        pos = find_insert_position(cells)
        assert pos == 3  # min(3, 9) = 3


# --- fix_notebook ---


class TestFixNotebook:
    def test_inserts_dependency_cell(self, tmp_path):
        nb = {
            "cells": [
                {"cell_type": "markdown", "source": ["# Title"]},
                {"cell_type": "code", "source": ["x = 1"]},
                {"cell_type": "markdown", "source": ["## Section 1"]},
            ],
        }
        p = tmp_path / "test.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        result = fix_notebook(p, _config())
        assert result is True
        data = json.loads(p.read_text(encoding="utf-8"))
        assert len(data["cells"]) == 4
        # Check the inserted cell has the marker
        inserted = data["cells"][2]
        source = "".join(inserted["source"])
        assert "VERIFICATION DES DEPENDANCES GPU" in source

    def test_skip_if_already_exists(self, tmp_path):
        dep_cell = create_dependency_cell(_config())
        nb = {
            "cells": [
                dep_cell,
                {"cell_type": "code", "source": ["x = 1"]},
            ],
        }
        p = tmp_path / "test.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        result = fix_notebook(p, _config())
        assert result is False
        data = json.loads(p.read_text(encoding="utf-8"))
        assert len(data["cells"]) == 2  # No new cell added
