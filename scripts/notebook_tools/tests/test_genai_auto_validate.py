"""Tests for genai-stack commands/auto_validate.py — offline with mocked filesystem/config."""

import importlib.util
import json
import sys
import types
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

# --- Build mock config ---
_GENAI_DIR = Path("C:/fake/genai")

_mock_notebook_service_map = {
    "audio_api": ["01-Audio-Basics.ipynb", "02-Audio-Advanced.ipynb"],
    "image_basic": ["01-Image-Basics.ipynb"],
    "video_gen": ["01-Video-Intro.ipynb", "02-Video-Gen.ipynb"],
}

_mock_execution_batches = {
    1: {"groups": ["audio_api"], "profile": "audio_heavy"},
    2: {"groups": ["image_basic", "video_gen"], "profile": None},
}

_mock_group_gpu_profile = {
    "audio_api": "audio_heavy",
    "image_basic": "image_light",
}

_mock_gpu_profiles = {
    "audio_heavy": {"gpu": 1, "services": ["whisper-api", "tts-api"]},
    "image_light": {"gpu": 0, "services": ["comfyui-qwen"]},
}

_mock_notebook_series = {
    "Audio": ["audio_api"],
    "Image": ["image_basic"],
    "Video": ["video_gen"],
}

_mock_config = types.SimpleNamespace(
    GENAI_DIR=_GENAI_DIR,
    EXECUTION_BATCHES=_mock_execution_batches,
    NOTEBOOK_SERVICE_MAP=_mock_notebook_service_map,
    GROUP_GPU_PROFILE=_mock_group_gpu_profile,
    GPU_PROFILES=_mock_gpu_profiles,
    NOTEBOOK_SERIES=_mock_notebook_series,
)

# Mock submodules needed by auto_validate
_mock_notebooks_mod = types.SimpleNamespace(
    NotebookValidator=MagicMock,
)
_mock_gpu_mod = types.SimpleNamespace(
    profile_apply=MagicMock(),
    profile_current=MagicMock(),
)

# Inject mocks into sys.modules with patch.dict for clean teardown
_MODULES_PATCH = {
    "config": _mock_config,
    "commands": types.SimpleNamespace(),
    "commands.notebooks": _mock_notebooks_mod,
    "commands.gpu": _mock_gpu_mod,
}

# --- Load auto_validate.py ---
_AV_PATH = Path(__file__).resolve().parent.parent.parent / "genai-stack" / "commands" / "auto_validate.py"


@pytest.fixture(scope="module", autouse=True)
def _setup_module():
    """Inject mock modules with clean teardown — prevents sys.modules pollution."""
    saved = {}
    for key, val in _MODULES_PATCH.items():
        saved[key] = sys.modules.get(key)
        sys.modules[key] = val

    # Load the module under test
    global _av_mod, extract_images, get_batch_notebooks, get_group_notebooks, validate_single_notebook
    _av_spec = importlib.util.spec_from_file_location("auto_validate", _AV_PATH)
    _av_mod = importlib.util.module_from_spec(_av_spec)
    _av_spec.loader.exec_module(_av_mod)

    extract_images = _av_mod.extract_images_from_notebook
    get_batch_notebooks = _av_mod.get_batch_notebooks
    get_group_notebooks = _av_mod.get_group_notebooks
    validate_single_notebook = _av_mod.validate_single_notebook

    yield

    # Teardown: restore original sys.modules entries
    for key, orig in saved.items():
        if orig is None:
            sys.modules.pop(key, None)
        else:
            sys.modules[key] = orig


# ============================================================================
# Tests for extract_images_from_notebook
# ============================================================================


class TestExtractImages:
    """Tests for extract_images_from_notebook() — JSON parsing."""

    def test_empty_notebook(self, tmp_path):
        nb = tmp_path / "test.ipynb"
        nb.write_text(json.dumps({"cells": []}), encoding="utf-8")
        result = extract_images(nb)
        assert result == []

    def test_no_code_cells(self, tmp_path):
        nb = tmp_path / "test.ipynb"
        nb.write_text(json.dumps({
            "cells": [{"cell_type": "markdown", "outputs": []}]
        }), encoding="utf-8")
        result = extract_images(nb)
        assert result == []

    def test_code_cell_no_outputs(self, tmp_path):
        nb = tmp_path / "test.ipynb"
        nb.write_text(json.dumps({
            "cells": [{"cell_type": "code", "outputs": []}]
        }), encoding="utf-8")
        result = extract_images(nb)
        assert result == []

    def test_code_cell_with_image_reference(self, tmp_path):
        # Create the image file so .exists() check passes
        img_dir = tmp_path / "outputs"
        img_dir.mkdir()
        img_file = img_dir / "plot.png"
        img_file.write_bytes(b"fake png")

        nb = tmp_path / "test.ipynb"
        nb.write_text(json.dumps({
            "cells": [{
                "cell_type": "code",
                "outputs": [{"text": ["<img src='outputs/plot.png'>"]}]
            }]
        }), encoding="utf-8")
        result = extract_images(nb)
        assert len(result) == 1
        assert result[0].name == "plot.png"

    def test_deduplication(self, tmp_path):
        img_dir = tmp_path / "outputs"
        img_dir.mkdir()
        img_file = img_dir / "plot.png"
        img_file.write_bytes(b"fake png")

        nb = tmp_path / "test.ipynb"
        nb.write_text(json.dumps({
            "cells": [
                {"cell_type": "code", "outputs": [{"text": ["outputs/plot.png"]}]},
                {"cell_type": "code", "outputs": [{"text": ["outputs/plot.png"]}]},
            ]
        }), encoding="utf-8")
        result = extract_images(nb)
        assert len(result) == 1  # Deduplicated

    def test_jpg_extension(self, tmp_path):
        img_dir = tmp_path / "outputs"
        img_dir.mkdir()
        img_file = img_dir / "photo.jpg"
        img_file.write_bytes(b"fake jpg")

        nb = tmp_path / "test.ipynb"
        nb.write_text(json.dumps({
            "cells": [{
                "cell_type": "code",
                "outputs": [{"text": ["outputs/photo.jpg"]}]
            }]
        }), encoding="utf-8")
        result = extract_images(nb)
        assert len(result) == 1
        assert result[0].suffix == ".jpg"

    def test_nonexistent_image_excluded(self, tmp_path):
        nb = tmp_path / "test.ipynb"
        nb.write_text(json.dumps({
            "cells": [{
                "cell_type": "code",
                "outputs": [{"text": ["outputs/missing.png"]}]
            }]
        }), encoding="utf-8")
        result = extract_images(nb)
        assert result == []  # Image doesn't exist on disk

    def test_sorted_output(self, tmp_path):
        img_dir = tmp_path / "outputs"
        img_dir.mkdir()
        for name in ["b_plot.png", "a_plot.png"]:
            (img_dir / name).write_bytes(b"fake")

        nb = tmp_path / "test.ipynb"
        nb.write_text(json.dumps({
            "cells": [{
                "cell_type": "code",
                "outputs": [{"text": ["outputs/b_plot.png"]}]
            }, {
                "cell_type": "code",
                "outputs": [{"text": ["outputs/a_plot.png"]}]
            }]
        }), encoding="utf-8")
        result = extract_images(nb)
        assert len(result) == 2
        assert result[0].name <= result[1].name  # Sorted

    def test_mp4_video_reference(self, tmp_path):
        vid_dir = tmp_path / "outputs"
        vid_dir.mkdir()
        vid_file = vid_dir / "animation.mp4"
        vid_file.write_bytes(b"fake mp4")

        nb = tmp_path / "test.ipynb"
        nb.write_text(json.dumps({
            "cells": [{
                "cell_type": "code",
                "outputs": [{"text": ["outputs/animation.mp4"]}]
            }]
        }), encoding="utf-8")
        result = extract_images(nb)
        assert len(result) == 1
        assert result[0].suffix == ".mp4"


# ============================================================================
# Tests for get_batch_notebooks
# ============================================================================


class TestGetBatchNotebooks:
    """Tests for get_batch_notebooks() — config lookup."""

    def test_unknown_batch(self):
        with pytest.raises(KeyError):
            get_batch_notebooks(99)

    def test_batch_with_files(self):
        """Returns sorted unique notebooks from batch config."""
        with patch.object(_av_mod, "GENAI_DIR", Path("/fake")):
            with patch.object(Path, "rglob", return_value=[Path("/fake/Audio/01-Audio-Basics.ipynb")]):
                result = get_batch_notebooks(1)
                assert isinstance(result, list)

    def test_batch_empty_group(self):
        """Batch with groups not in NOTEBOOK_SERVICE_MAP returns empty."""
        # Use a local copy to avoid mutating the shared mock config
        original = _mock_config.EXECUTION_BATCHES
        test_batches = dict(original)
        test_batches[99] = {"groups": ["nonexistent_group"]}
        with patch.object(_av_mod, "EXECUTION_BATCHES", test_batches):
            result = get_batch_notebooks(99)
        assert result == []


# ============================================================================
# Tests for get_group_notebooks
# ============================================================================


class TestGetGroupNotebooks:
    """Tests for get_group_notebooks() — group-based lookup."""

    def test_unknown_group(self):
        result = get_group_notebooks("nonexistent_group")
        assert result == []

    def test_known_group_returns_list(self):
        with patch.object(_av_mod, "GENAI_DIR", Path("/fake")):
            with patch.object(Path, "rglob", return_value=[]):
                result = get_group_notebooks("audio_api")
        assert isinstance(result, list)

    def test_deduplicates(self):
        """Same notebook found in multiple dirs is deduplicated."""
        fake_path = Path("/fake/Audio/01-Audio-Basics.ipynb")
        with patch.object(_av_mod, "GENAI_DIR", Path("/fake")):
            with patch.object(Path, "rglob", return_value=[fake_path]):
                result = get_group_notebooks("audio_api")
        # Should be deduplicated even if rglob returns same file
        assert len(result) <= len(_mock_notebook_service_map["audio_api"])


# ============================================================================
# Tests for validate_single_notebook
# ============================================================================


class TestValidateSingleNotebook:
    """Tests for validate_single_notebook() — path validation."""

    def test_nonexistent_notebook(self, tmp_path):
        nb = tmp_path / "nonexistent.ipynb"
        result = validate_single_notebook(nb)
        assert result["status"] == "failed"
        assert "trouv" in result["error"].lower()  # "trouvé" contains "trouv"

    def test_existing_notebook_calls_execute(self, tmp_path):
        nb = tmp_path / "test.ipynb"
        nb.write_text(json.dumps({"cells": []}), encoding="utf-8")
        with patch.object(_av_mod, "execute_notebook", return_value={"status": "success", "duration": 1.0}):
            result = validate_single_notebook(nb)
        assert result["status"] == "success"


# ============================================================================
# Tests for print_status (smoke test)
# ============================================================================


class TestPrintStatus:
    """Smoke tests for print_status() — captures output."""

    def test_prints_without_error(self, capsys):
        with patch.object(_av_mod, "GENAI_DIR", Path("/fake")):
            with patch.object(Path, "exists", return_value=False):
                _av_mod.print_status()
        captured = capsys.readouterr()
        assert "STATUT" in captured.out


# ============================================================================
# Tests for main() argument parsing
# ============================================================================


class TestMainArgParsing:
    """Tests for main() CLI dispatch."""

    def test_status_flag(self, capsys):
        with patch("sys.argv", ["auto_validate.py", "--status"]):
            with patch.object(_av_mod, "GENAI_DIR", Path("/fake")):
                with patch.object(Path, "exists", return_value=False):
                    _av_mod.main()
        captured = capsys.readouterr()
        assert "STATUT" in captured.out

    def test_batch_list(self, capsys):
        with patch("sys.argv", ["auto_validate.py", "--batch", "1", "--list"]):
            with patch.object(_av_mod, "GENAI_DIR", Path("/fake")):
                with patch.object(Path, "rglob", return_value=[]):
                    _av_mod.main()
        # Should not crash, even with no files found

    def test_unknown_group(self, capsys):
        with patch("sys.argv", ["auto_validate.py", "--group", "nonexistent"]):
            _av_mod.main()
        captured = capsys.readouterr()
        assert "inconnu" in captured.out.lower()

    def test_no_args_prints_help(self, capsys):
        with patch("sys.argv", ["auto_validate.py"]):
            with patch.object(_av_mod, "GENAI_DIR", Path("/fake")):
                with patch.object(Path, "exists", return_value=False):
                    _av_mod.main()
        captured = capsys.readouterr()
        # Should print usage help


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
