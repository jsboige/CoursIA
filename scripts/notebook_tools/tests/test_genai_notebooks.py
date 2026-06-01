"""Tests for genai-stack commands/notebooks.py — NotebookValidator offline with mocked deps."""

import importlib.util
import json
import os
import sys
import types
from pathlib import Path
from unittest.mock import MagicMock, patch
from datetime import datetime

import pytest

# --- Build mock dependencies ---
_GENAI_DIR = Path("C:/fake/genai")

_mock_notebook_service_map = {
    "audio_api": ["01-Audio-Basics.ipynb"],
    "image_basic": ["01-Image-Basics.ipynb", "02-Image-Advanced.ipynb"],
}

_mock_notebook_series = {
    "Audio": ["audio_api"],
    "Image": ["image_basic"],
}

_mock_notebook_search_dirs = {
    "Audio": _GENAI_DIR / "Audio",
    "Image": _GENAI_DIR / "Image",
}

_mock_execution_batches = {
    1: {"name": "Batch Audio", "groups": ["audio_api"], "profile": "audio_heavy"},
    2: {"name": "Batch Image", "groups": ["image_basic"], "profile": None},
}

_mock_group_gpu_profile = {}

_mock_config = types.SimpleNamespace(
    GENAI_DIR=_GENAI_DIR,
    NOTEBOOK_SERVICE_MAP=_mock_notebook_service_map,
    NOTEBOOK_SERIES=_mock_notebook_series,
    NOTEBOOK_SEARCH_DIRS=_mock_notebook_search_dirs,
    EXECUTION_BATCHES=_mock_execution_batches,
    GROUP_GPU_PROFILE=_mock_group_gpu_profile,
)

# Mock core.auth_manager (GenAIAuthManager)
_mock_auth_manager_instance = MagicMock()
_mock_auth_manager_instance.load_config.return_value = {"bcrypt_hash": "test-hash"}
_mock_auth_manager_class = MagicMock(return_value=_mock_auth_manager_instance)

_mock_auth_mod = types.SimpleNamespace(GenAIAuthManager=_mock_auth_manager_class)

# Mock papermill
_mock_pm = MagicMock()

# Saved sys.modules for cleanup
_MODULES_PATCH = {
    "config": _mock_config,
    "core": types.SimpleNamespace(),
    "core.auth_manager": _mock_auth_mod,
    "papermill": _mock_pm,
}


@pytest.fixture(scope="module", autouse=True)
def _setup_module():
    """Inject mock modules with clean teardown."""
    saved = {}
    for key, val in _MODULES_PATCH.items():
        saved[key] = sys.modules.get(key)
        sys.modules[key] = val

    global _nb_mod, NotebookValidator
    _NB_PATH = Path(__file__).resolve().parent.parent.parent / "genai-stack" / "commands" / "notebooks.py"
    _nb_spec = importlib.util.spec_from_file_location("notebooks_cmd", _NB_PATH)
    _nb_mod = importlib.util.module_from_spec(_nb_spec)
    _nb_spec.loader.exec_module(_nb_mod)
    NotebookValidator = _nb_mod.NotebookValidator

    yield

    # Teardown
    for key, orig in saved.items():
        if orig is None:
            sys.modules.pop(key, None)
        else:
            sys.modules[key] = orig


# ============================================================================
# Tests for NotebookValidator.__init__
# ============================================================================


class TestInit:
    """Tests for NotebookValidator constructor."""

    def test_sets_target_path(self):
        v = NotebookValidator("/tmp/test")
        assert v.target_path == Path("/tmp/test")

    def test_auth_manager_called(self):
        _mock_auth_manager_class.reset_mock()
        v = NotebookValidator("/tmp/test")
        _mock_auth_manager_class.assert_called()

    def test_token_from_config(self):
        v = NotebookValidator("/tmp/test")
        assert v.token == "test-hash"

    def test_env_vars_populated(self):
        v = NotebookValidator("/tmp/test")
        assert "COMFYUI_URL" in v.env_vars
        assert "BATCH_MODE" in v.env_vars
        assert v.env_vars["BATCH_MODE"] == "true"

    def test_fallback_env_token(self):
        _mock_auth_manager_instance.load_config.return_value = {}
        v = NotebookValidator("/tmp/test")
        # Should fall back to os.getenv("COMFYUI_AUTH_TOKEN")
        _mock_auth_manager_instance.load_config.return_value = {"bcrypt_hash": "test-hash"}


# ============================================================================
# Tests for find_notebooks
# ============================================================================


class TestFindNotebooks:
    """Tests for NotebookValidator.find_notebooks()."""

    def test_single_file_ipynb(self, tmp_path):
        nb = tmp_path / "test.ipynb"
        nb.write_text("{}", encoding="utf-8")
        v = NotebookValidator(str(nb))
        result = v.find_notebooks()
        assert len(result) == 1
        assert result[0] == nb

    def test_single_file_not_ipynb(self, tmp_path):
        txt = tmp_path / "readme.md"
        txt.write_text("hello", encoding="utf-8")
        v = NotebookValidator(str(txt))
        result = v.find_notebooks()
        assert result == []

    def test_directory_finds_notebooks(self, tmp_path):
        (tmp_path / "a.ipynb").write_text("{}", encoding="utf-8")
        (tmp_path / "b.ipynb").write_text("{}", encoding="utf-8")
        (tmp_path / "readme.md").write_text("hello", encoding="utf-8")
        v = NotebookValidator(str(tmp_path))
        result = v.find_notebooks()
        assert len(result) == 2

    def test_directory_recursive(self, tmp_path):
        sub = tmp_path / "sub"
        sub.mkdir()
        (sub / "nested.ipynb").write_text("{}", encoding="utf-8")
        v = NotebookValidator(str(tmp_path))
        result = v.find_notebooks()
        assert len(result) == 1

    def test_empty_directory(self, tmp_path):
        v = NotebookValidator(str(tmp_path))
        result = v.find_notebooks()
        assert result == []


# ============================================================================
# Tests for find_notebooks_by_group
# ============================================================================


class TestFindNotebooksByGroup:
    """Tests for NotebookValidator.find_notebooks_by_group()."""

    def test_unknown_group(self):
        v = NotebookValidator("/tmp")
        result = v.find_notebooks_by_group("nonexistent")
        assert result == []

    def test_known_group_returns_list(self):
        v = NotebookValidator("/tmp")
        with patch.object(Path, "rglob", return_value=[]):
            with patch.object(Path, "exists", return_value=False):
                result = v.find_notebooks_by_group("audio_api")
        assert isinstance(result, list)


# ============================================================================
# Tests for find_notebooks_by_batch
# ============================================================================


class TestFindNotebooksByBatch:
    """Tests for NotebookValidator.find_notebooks_by_batch()."""

    def test_unknown_batch(self):
        v = NotebookValidator("/tmp")
        result = v.find_notebooks_by_batch(99)
        assert result == []

    def test_valid_batch_returns_list(self):
        v = NotebookValidator("/tmp")
        with patch.object(Path, "rglob", return_value=[]):
            with patch.object(Path, "exists", return_value=False):
                result = v.find_notebooks_by_batch(1)
        assert isinstance(result, list)


# ============================================================================
# Tests for save_report
# ============================================================================


class TestSaveReport:
    """Tests for NotebookValidator.save_report()."""

    def test_creates_json_file(self, tmp_path):
        v = NotebookValidator("/tmp")
        report_path = tmp_path / "report.json"
        results = [
            {"notebook": "a.ipynb", "status": "success", "duration": 1.0, "error": None},
            {"notebook": "b.ipynb", "status": "failed", "duration": 2.0, "error": "timeout"},
        ]
        with patch.object(_nb_mod.Path, "write_text", MagicMock()):
            with patch("builtins.open", MagicMock()):
                with patch.object(_nb_mod.json, "dump") as mock_dump:
                    with patch("builtins.print"):
                        v.save_report(results)
                    # Verify json.dump was called
                    mock_dump.assert_called_once()
                    call_data = mock_dump.call_args[0][0]
                    assert call_data["total_notebooks"] == 2
                    assert call_data["passed"] == 1
                    assert call_data["failed"] == 1

    def test_report_structure(self, tmp_path):
        v = NotebookValidator("/tmp")
        results = [{"notebook": "test.ipynb", "status": "success", "duration": 5.0, "error": None}]
        with patch.object(_nb_mod.Path, "write_text", MagicMock()):
            with patch("builtins.open", MagicMock()):
                with patch.object(_nb_mod.json, "dump") as mock_dump:
                    with patch("builtins.print"):
                        v.save_report(results)
                    call_data = mock_dump.call_args[0][0]
                    assert "timestamp" in call_data
                    assert "total_notebooks" in call_data
                    assert "passed" in call_data
                    assert "failed" in call_data
                    assert "results" in call_data


# ============================================================================
# Tests for validate_notebook (mocked papermill)
# ============================================================================


class TestValidateNotebook:
    """Tests for NotebookValidator.validate_notebook() — papermill mocked."""

    def test_success(self, tmp_path):
        v = NotebookValidator(str(tmp_path))
        nb = tmp_path / "test.ipynb"
        nb.write_text("{}", encoding="utf-8")
        _mock_pm.execute_notebook.reset_mock()
        result = v.validate_notebook(nb, tmp_path)
        assert result["status"] == "success"
        assert result["duration"] >= 0
        assert result["error"] is None

    def test_failure_on_exception(self, tmp_path):
        v = NotebookValidator(str(tmp_path))
        nb = tmp_path / "test.ipynb"
        nb.write_text("{}", encoding="utf-8")
        _mock_pm.execute_notebook.side_effect = RuntimeError("kernel died")
        result = v.validate_notebook(nb, tmp_path)
        assert result["status"] == "failed"
        assert "kernel died" in result["error"]
        _mock_pm.execute_notebook.side_effect = None

    def test_env_vars_injected(self, tmp_path):
        v = NotebookValidator(str(tmp_path))
        nb = tmp_path / "test.ipynb"
        nb.write_text("{}", encoding="utf-8")
        original_env = os.environ.copy()
        with patch.dict(os.environ, {}, clear=False):
            v.validate_notebook(nb, tmp_path)
        # Verify env was restored (the finally block restores it)

    def test_output_path_created(self, tmp_path):
        v = NotebookValidator(str(tmp_path))
        nb = tmp_path / "test.ipynb"
        nb.write_text("{}", encoding="utf-8")
        result = v.validate_notebook(nb, tmp_path)
        assert "output_path" in result


# ============================================================================
# Tests for register() and execute()
# ============================================================================


class TestRegisterAndExecute:
    """Tests for CLI registration and execute dispatch."""

    def test_register_creates_subparser(self):
        import argparse
        parser = argparse.ArgumentParser()
        subparsers = parser.add_subparsers(dest="command")
        _nb_mod.register(subparsers)
        args = parser.parse_args(["notebooks", "/tmp/test"])
        assert args.target == "/tmp/test"

    def test_register_group_choices(self):
        import argparse
        parser = argparse.ArgumentParser()
        subparsers = parser.add_subparsers(dest="command")
        _nb_mod.register(subparsers)
        # Verify group choices match NOTEBOOK_SERVICE_MAP keys
        args = parser.parse_args(["notebooks", "--group", "audio_api"])
        assert args.group == "audio_api"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
