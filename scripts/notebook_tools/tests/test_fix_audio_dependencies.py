"""Tests for scripts/notebook_tools/fix_audio_dependencies.py — GPU dependency cell injector.

Tests focus on pure functions: create_dependency_cell, find_insert_position,
fix_notebook. Uses tmp_path for filesystem isolation.
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from fix_audio_dependencies import (
    GPU_DEPENDENCIES,
    create_dependency_cell,
    find_insert_position,
    fix_notebook,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _write_nb(path: Path, cells: list[dict]) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    nb = {"cells": cells, "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
    path.write_text(json.dumps(nb), encoding="utf-8")
    return path


def _md(source: str) -> dict:
    return {"cell_type": "markdown", "source": [source]}


def _code(source: str) -> dict:
    return {"cell_type": "code", "source": [source], "outputs": [], "execution_count": None}


# ---------------------------------------------------------------------------
# GPU_DEPENDENCIES constant
# ---------------------------------------------------------------------------

class TestGpuDependencies:
    def test_structure(self):
        assert len(GPU_DEPENDENCIES) >= 4
        for key, cfg in GPU_DEPENDENCIES.items():
            assert "packages" in cfg
            assert "primary" in cfg
            assert "install" in cfg
            assert "description" in cfg
            assert "optional" in cfg

    def test_paths_are_relative(self):
        for key in GPU_DEPENDENCIES:
            assert not Path(key).is_absolute()

    def test_packages_are_lists(self):
        for cfg in GPU_DEPENDENCIES.values():
            assert isinstance(cfg["packages"], list)
            assert len(cfg["packages"]) >= 1


# ---------------------------------------------------------------------------
# create_dependency_cell
# ---------------------------------------------------------------------------

class TestCreateDependencyCell:
    def test_basic_structure(self):
        config = {
            "packages": ["numpy"],
            "primary": "numpy",
            "install": "pip install numpy",
            "description": "NumPy",
            "optional": True,
        }
        cell = create_dependency_cell(config)
        assert cell["cell_type"] == "code"
        assert isinstance(cell["source"], list)
        assert cell["execution_count"] is None
        assert cell["outputs"] == []

    def test_contains_import_check(self):
        config = {
            "packages": ["demucs"],
            "primary": "demucs",
            "install": "pip install demucs",
            "description": "Demucs",
            "optional": True,
        }
        cell = create_dependency_cell(config)
        source = "".join(cell["source"])
        assert "import demucs" in source

    def test_hyphen_replaced_in_import(self):
        config = {
            "packages": ["chatterbox-tts"],
            "primary": "chatterbox-tts",
            "install": "pip install chatterbox-tts",
            "description": "Chatterbox",
            "optional": True,
        }
        cell = create_dependency_cell(config)
        source = "".join(cell["source"])
        assert "import chatterbox_tts" in source

    def test_install_command_in_output(self):
        config = {
            "packages": ["kokoro"],
            "primary": "kokoro",
            "install": "pip install kokoro-onnx",
            "description": "Kokoro TTS",
            "optional": True,
        }
        cell = create_dependency_cell(config)
        source = "".join(cell["source"])
        assert "pip install kokoro-onnx" in source

    def test_fallback_included(self):
        config = {
            "packages": ["kokoro-onnx", "kokoro"],
            "primary": "kokoro-onnx",
            "fallback": "kokoro",
            "install": "pip install kokoro-onnx",
            "description": "Kokoro",
            "optional": True,
        }
        cell = create_dependency_cell(config)
        source = "".join(cell["source"])
        assert "fallback" in source.lower()

    def test_no_fallback(self):
        config = {
            "packages": ["numpy"],
            "primary": "numpy",
            "install": "pip install numpy",
            "description": "NumPy",
            "optional": True,
        }
        cell = create_dependency_cell(config)
        source = "".join(cell["source"])
        assert "fallback" not in source.lower()

    def test_multi_package(self):
        config = {
            "packages": ["demucs", "torchaudio"],
            "primary": "demucs",
            "secondary": ["torchaudio"],
            "install": "pip install demucs torchaudio",
            "description": "Demucs + torchaudio",
            "optional": True,
        }
        cell = create_dependency_cell(config)
        source = "".join(cell["source"])
        assert "import demucs" in source
        assert "import torchaudio" in source

    def test_source_lines_have_newlines(self):
        config = {
            "packages": ["numpy"],
            "primary": "numpy",
            "install": "pip install numpy",
            "description": "NumPy",
            "optional": True,
        }
        cell = create_dependency_cell(config)
        for line in cell["source"][:-1]:
            assert line.endswith("\n")


# ---------------------------------------------------------------------------
# find_insert_position
# ---------------------------------------------------------------------------

class TestFindInsertPosition:
    def test_finds_section_header(self):
        cells = [
            _md("# Title"),
            _md("Some intro"),
            _md("## Section 1"),
            _code("x = 1"),
        ]
        assert find_insert_position(cells) == 2

    def test_no_section_fallback(self):
        cells = [
            _md("# Title"),
            _code("x = 1"),
        ]
        assert find_insert_position(cells) == min(3, len(cells) - 1)

    def test_empty_cells(self):
        # Edge case: min(3, len([])-1) = min(3, -1) = -1
        assert find_insert_position([]) == -1

    def test_first_cell_is_section(self):
        cells = [_md("## Section 1"), _code("x = 1")]
        assert find_insert_position(cells) == 0

    def test_code_cells_not_matched(self):
        cells = [
            _code("## Section 1"),  # code cell, not markdown
            _md("## Section 2"),
        ]
        assert find_insert_position(cells) == 1

    def test_h3_not_matched(self):
        cells = [
            _md("### Section detail"),
            _md("## Section 1"),
        ]
        assert find_insert_position(cells) == 1


# ---------------------------------------------------------------------------
# fix_notebook
# ---------------------------------------------------------------------------

class TestFixNotebook:
    def test_inserts_dependency_cell(self, tmp_path):
        config = {
            "packages": ["numpy"],
            "primary": "numpy",
            "install": "pip install numpy",
            "description": "NumPy",
            "optional": True,
        }
        path = _write_nb(tmp_path / "test.ipynb", [
            _md("# Title"),
            _md("## Section 1"),
            _code("x = 1"),
        ])
        result = fix_notebook(path, config)
        assert result is True
        nb = json.loads(path.read_text(encoding="utf-8"))
        assert len(nb["cells"]) == 4  # 3 original + 1 new
        # The inserted cell should contain GPU check
        sources = ["".join(c.get("source", [])) for c in nb["cells"]]
        assert any("VERIFICATION DES DEPENDANCES GPU" in s for s in sources)

    def test_skip_if_already_exists(self, tmp_path):
        config = {
            "packages": ["numpy"],
            "primary": "numpy",
            "install": "pip install numpy",
            "description": "NumPy",
            "optional": True,
        }
        path = _write_nb(tmp_path / "test.ipynb", [
            _code("VERIFICATION DES DEPENDANCES GPU\nprint('exists')"),
            _md("## Section 1"),
        ])
        result = fix_notebook(path, config)
        assert result is False

    def test_insert_position_before_section(self, tmp_path):
        config = {
            "packages": ["numpy"],
            "primary": "numpy",
            "install": "pip install numpy",
            "description": "NumPy",
            "optional": True,
        }
        path = _write_nb(tmp_path / "test.ipynb", [
            _md("# Title"),
            _md("Setup info"),
            _md("## Section 1"),
            _code("x = 1"),
        ])
        fix_notebook(path, config)
        nb = json.loads(path.read_text(encoding="utf-8"))
        # Inserted at index 2 (before ## Section 1)
        inserted_source = "".join(nb["cells"][2].get("source", []))
        assert "VERIFICATION DES DEPENDANCES GPU" in inserted_source
        # Section 1 shifted to index 3
        section_source = "".join(nb["cells"][3].get("source", []))
        assert "## Section 1" in section_source

    def test_notebook_valid_json_after_fix(self, tmp_path):
        config = {
            "packages": ["numpy"],
            "primary": "numpy",
            "install": "pip install numpy",
            "description": "NumPy",
            "optional": True,
        }
        path = _write_nb(tmp_path / "test.ipynb", [
            _md("# Title"),
            _md("## Section 1"),
        ])
        fix_notebook(path, config)
        data = json.loads(path.read_text(encoding="utf-8"))
        assert "cells" in data
        assert "metadata" in data
