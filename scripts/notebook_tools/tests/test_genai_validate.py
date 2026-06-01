"""Tests for genai-stack commands/validate.py — BatchNotebookValidator pure methods."""

import importlib.util
import json
import sys
import types
from pathlib import Path

import pytest
from unittest.mock import MagicMock

# Stub config module so validate.py `from config import ...` resolves without env
_saved_config = sys.modules.get("config")
if not isinstance(_saved_config, types.ModuleType) or not hasattr(_saved_config, "COMFYUI_URL"):
    sys.modules["config"] = types.SimpleNamespace(
        COMFYUI_URL="http://localhost:8188",
        FORGE_URL="http://localhost:17861",
        VLLM_ZIMAGE_URL="http://localhost:8001",
        WHISPER_URL="http://localhost:8190",
        COMFYUI_VIDEO_URL="http://localhost:8189",
        EXPECTED_QWEN_NODES=[],
        EXPECTED_NUNCHAKU_NODES=[],
        REQUIRED_NATIVE_NODES=[],
        NOTEBOOK_SERVICE_MAP={},
        NOTEBOOK_SERIES={},
        NOTEBOOK_SEARCH_DIRS=[],
        MODEL_CONFIGS={},
        WORKFLOWS_DIR=Path("/tmp/workflows"),
        GENAI_DIR=Path("/tmp/genai"),
        SERVICES={},
        GPU_PROFILES={},
        GROUP_GPU_PROFILE={},
        load_env=lambda: {},
    )

# Stub auth_manager and comfyui_client so validate.py imports succeed
for _mod_name in ("core", "core.auth_manager", "core.comfyui_client"):
    sys.modules.setdefault(_mod_name, types.ModuleType(_mod_name))
sys.modules["core"].auth_manager = sys.modules["core.auth_manager"]
sys.modules["core"].comfyui_client = sys.modules["core.comfyui_client"]
sys.modules["core.auth_manager"].GenAIAuthManager = MagicMock
sys.modules["core.comfyui_client"].ComfyUIClient = MagicMock
sys.modules["core.comfyui_client"].ComfyUIConfig = MagicMock
sys.modules["core.comfyui_client"].WorkflowManager = MagicMock

# Load module by file path
_MOD_PATH = Path(__file__).resolve().parent.parent.parent / "genai-stack" / "commands" / "validate.py"
_spec = importlib.util.spec_from_file_location("genai_validate", _MOD_PATH)
_mod = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_mod)

# Restore original config if it was saved
if _saved_config is not None:
    sys.modules["config"] = _saved_config

BatchNotebookValidator = _mod.BatchNotebookValidator


class _DummySwitcher:
    """Minimal model switcher stub for BatchNotebookValidator init."""
    current_model = None
    def switch_to(self, m):
        return True


def _make_validator(tmp_path):
    """Create a BatchNotebookValidator with dummy switcher and tmp_path as notebooks_dir."""
    return BatchNotebookValidator(_DummySwitcher(), notebooks_dir=tmp_path)


def _write_nb(path: Path, cells=None, metadata=None, **extra):
    """Write a minimal .ipynb JSON file."""
    nb = {
        "cells": cells or [],
        "metadata": metadata or {"kernelspec": {"name": "python3"}},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    nb.update(extra)
    path.write_text(json.dumps(nb), encoding="utf-8")
    return path


def _code(source: str, **extra):
    """Build a code cell dict."""
    cell = {"cell_type": "code", "source": [source], "metadata": {}, "outputs": None, "execution_count": None}
    cell.update(extra)
    return cell


def _md(source: str, **extra):
    """Build a markdown cell dict."""
    cell = {"cell_type": "markdown", "source": [source], "metadata": {}}
    cell.update(extra)
    return cell


# --- _validate_notebook_syntax ---


class TestValidateNotebookSyntax:
    def test_valid_notebook(self, tmp_path):
        nb_path = _write_nb(tmp_path / "test.ipynb", cells=[
            _code("print('hello')"),
            _md("# Title"),
        ])
        validator = _make_validator(tmp_path)
        result = validator._validate_notebook_syntax(nb_path)
        assert result["valid"] is True
        assert result["cell_count"] == 2
        assert result["code_cells"] == 1

    def test_missing_cells_key(self, tmp_path):
        nb_path = tmp_path / "test.ipynb"
        nb_path.write_text(json.dumps({"metadata": {}}), encoding="utf-8")
        validator = _make_validator(tmp_path)
        result = validator._validate_notebook_syntax(nb_path)
        assert result["valid"] is False
        assert "cells" in result["error"]

    def test_missing_metadata_key(self, tmp_path):
        nb_path = tmp_path / "test.ipynb"
        nb_path.write_text(json.dumps({"cells": []}), encoding="utf-8")
        validator = _make_validator(tmp_path)
        result = validator._validate_notebook_syntax(nb_path)
        assert result["valid"] is False
        assert "metadata" in result["error"]

    def test_invalid_json(self, tmp_path):
        nb_path = tmp_path / "test.ipynb"
        nb_path.write_text("{not valid json}", encoding="utf-8")
        validator = _make_validator(tmp_path)
        result = validator._validate_notebook_syntax(nb_path)
        assert result["valid"] is False
        assert "JSON" in result["error"]

    def test_empty_cells_list(self, tmp_path):
        nb_path = _write_nb(tmp_path / "test.ipynb", cells=[])
        validator = _make_validator(tmp_path)
        result = validator._validate_notebook_syntax(nb_path)
        assert result["valid"] is True
        assert result["cell_count"] == 0
        assert result["code_cells"] == 0

    def test_all_code_cells(self, tmp_path):
        nb_path = _write_nb(tmp_path / "test.ipynb", cells=[
            _code("a = 1"),
            _code("b = 2"),
            _code("c = a + b"),
        ])
        validator = _make_validator(tmp_path)
        result = validator._validate_notebook_syntax(nb_path)
        assert result["valid"] is True
        assert result["cell_count"] == 3
        assert result["code_cells"] == 3

    def test_all_markdown_cells(self, tmp_path):
        nb_path = _write_nb(tmp_path / "test.ipynb", cells=[
            _md("# Title"),
            _md("Some text"),
        ])
        validator = _make_validator(tmp_path)
        result = validator._validate_notebook_syntax(nb_path)
        assert result["valid"] is True
        assert result["cell_count"] == 2
        assert result["code_cells"] == 0

    def test_mixed_cells(self, tmp_path):
        nb_path = _write_nb(tmp_path / "test.ipynb", cells=[
            _md("# Intro"),
            _code("x = 1"),
            _md("## Section"),
            _code("y = 2"),
            _code("z = x + y"),
        ])
        validator = _make_validator(tmp_path)
        result = validator._validate_notebook_syntax(nb_path)
        assert result["valid"] is True
        assert result["cell_count"] == 5
        assert result["code_cells"] == 3

    def test_path_in_result(self, tmp_path):
        nb_path = _write_nb(tmp_path / "test.ipynb", cells=[])
        validator = _make_validator(tmp_path)
        result = validator._validate_notebook_syntax(nb_path)
        assert str(nb_path) == result["path"]

    def test_nonexistent_file(self, tmp_path):
        nb_path = tmp_path / "does_not_exist.ipynb"
        validator = _make_validator(tmp_path)
        result = validator._validate_notebook_syntax(nb_path)
        assert result["valid"] is False
        assert "error" in result

    def test_cells_without_cell_type_key(self, tmp_path):
        """Cells missing 'cell_type' should not be counted as code cells."""
        nb_path = _write_nb(tmp_path / "test.ipynb", cells=[
            {"source": ["x = 1"], "metadata": {}},
        ])
        validator = _make_validator(tmp_path)
        result = validator._validate_notebook_syntax(nb_path)
        assert result["valid"] is True
        assert result["cell_count"] == 1
        assert result["code_cells"] == 0  # no cell_type → not counted as code


# --- _find_notebook ---


class TestFindNotebook:
    def test_exact_name_match(self, tmp_path):
        nb = tmp_path / "01-Intro.ipynb"
        _write_nb(nb, cells=[])
        validator = _make_validator(tmp_path)
        result = validator._find_notebook("01-Intro.ipynb")
        assert result is not None
        assert result.name == "01-Intro.ipynb"

    def test_fuzzy_match(self, tmp_path):
        """Fuzzy match uses *{name}* glob — the full filename must appear as substring."""
        nb = tmp_path / "copy-01-Intro.ipynb"
        _write_nb(nb, cells=[])
        validator = _make_validator(tmp_path)
        result = validator._find_notebook("01-Intro.ipynb")
        assert result is not None

    def test_not_found(self, tmp_path):
        validator = _make_validator(tmp_path)
        result = validator._find_notebook("does-not-exist.ipynb")
        assert result is None

    def test_nested_directory(self, tmp_path):
        sub = tmp_path / "subdir"
        sub.mkdir()
        _write_nb(sub / "nested.ipynb", cells=[])
        validator = _make_validator(tmp_path)
        result = validator._find_notebook("nested.ipynb")
        assert result is not None


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
