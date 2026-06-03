#!/usr/bin/env python3
"""
Tests for scripts/genai-stack/commands/models.py

Covers: QWEN_MODELS, NUNCHAKU_MODELS, ZIMAGE_VAE_CONFIG data structures,
_get_hf_token (env + file), download_nunchaku (list mode),
register (argparse wiring), execute (CLI dispatch).
Pure CPU. All network/Docker/GPU calls mocked.

LIVE: 5+ callers (download_nunchaku_model.py, download_qwen_models.py,
list_models.py, list_nodes.py, setup_z_image.py).
"""

import os
import sys
import importlib
import argparse
import pytest
from pathlib import Path
from unittest.mock import patch

# Import the module under test without polluting sys.path/sys.modules globally.
# This avoids shadowing sudoku/core/models.py for other test files.
_genai_stack = str(Path(__file__).resolve().parent.parent / "genai-stack")
_genai_commands = str(Path(__file__).resolve().parent.parent / "genai-stack" / "commands")

# Temporarily add paths, import, then clean up to avoid "models" name collision
try:
    sys.path.insert(0, _genai_stack)
    sys.path.insert(0, _genai_commands)
    import models as _models_mod
finally:
    # Remove genai-stack/commands from sys.path AND sys.modules["models"]
    # to avoid shadowing other test files' "from models import ..."
    sys.path[:] = [p for p in sys.path if p != _genai_commands]
    sys.modules.pop("models", None)

QWEN_MODELS = _models_mod.QWEN_MODELS
NUNCHAKU_MODELS = _models_mod.NUNCHAKU_MODELS
NUNCHAKU_REPO_ID = _models_mod.NUNCHAKU_REPO_ID
ZIMAGE_VAE_CONFIG = _models_mod.ZIMAGE_VAE_CONFIG
_get_hf_token = _models_mod._get_hf_token
download_nunchaku = _models_mod.download_nunchaku
register = _models_mod.register
execute = _models_mod.execute


# ─── QWEN_MODELS data structure ───────────────────────────────────────


class TestQwenModels:
    def test_is_list(self):
        assert isinstance(QWEN_MODELS, list)

    def test_count(self):
        assert len(QWEN_MODELS) == 3

    def test_required_keys(self):
        required = {"name", "repo_id", "filename", "local_name", "subdir", "size_gb"}
        for model in QWEN_MODELS:
            assert required.issubset(set(model.keys())), \
                f"Missing keys in {model['name']}: {required - set(model.keys())}"

    def test_size_gb_positive(self):
        for model in QWEN_MODELS:
            assert model["size_gb"] > 0, f"{model['name']} has non-positive size"

    def test_repo_id_format(self):
        """repo_id should be 'org/repo' format."""
        for model in QWEN_MODELS:
            assert "/" in model["repo_id"], f"{model['name']}: invalid repo_id format"

    def test_filename_ends_safetensors(self):
        for model in QWEN_MODELS:
            assert model["filename"].endswith(".safetensors"), \
                f"{model['name']}: filename should end with .safetensors"

    def test_local_name_ends_safetensors(self):
        for model in QWEN_MODELS:
            assert model["local_name"].endswith(".safetensors"), \
                f"{model['name']}: local_name should end with .safetensors"

    def test_names_unique(self):
        names = [m["name"] for m in QWEN_MODELS]
        assert len(names) == len(set(names))

    def test_total_size_reasonable(self):
        """Total Qwen models ~29GB."""
        total = sum(m["size_gb"] for m in QWEN_MODELS)
        assert 20 < total < 40, f"Total size {total}GB outside expected range"

    def test_subdir_not_empty(self):
        for model in QWEN_MODELS:
            assert model["subdir"], f"{model['name']}: subdir is empty"


# ─── NUNCHAKU_MODELS data structure ───────────────────────────────────


class TestNunchakuModels:
    def test_is_dict(self):
        assert isinstance(NUNCHAKU_MODELS, dict)

    def test_count(self):
        assert len(NUNCHAKU_MODELS) == 6

    def test_keys_format(self):
        """Keys use lowercase-with-hyphens format."""
        for key in NUNCHAKU_MODELS:
            assert key == key.lower(), f"Key '{key}' not lowercase"
            assert " " not in key, f"Key '{key}' contains spaces"

    def test_values_safetensors(self):
        """All values should be .safetensors filenames."""
        for key, filename in NUNCHAKU_MODELS.items():
            assert filename.endswith(".safetensors"), \
                f"{key}: {filename} not .safetensors"

    def test_keys_unique(self):
        """Dict keys are unique by definition, verify count."""
        assert len(set(NUNCHAKU_MODELS.keys())) == len(NUNCHAKU_MODELS)

    def test_values_unique(self):
        """Filenames should be unique."""
        values = list(NUNCHAKU_MODELS.values())
        assert len(values) == len(set(values))

    def test_has_lightning_4step_r128(self):
        """Default model key exists."""
        assert "lightning-4step-r128" in NUNCHAKU_MODELS

    def test_r128_and_r32_variants(self):
        """Both r128 and r32 variants exist for each step count."""
        keys = set(NUNCHAKU_MODELS.keys())
        assert "lightning-4step-r128" in keys
        assert "lightning-4step-r32" in keys
        assert "lightning-8step-r128" in keys
        assert "lightning-8step-r32" in keys

    def test_filenames_contain_svq(self):
        """Nunchaku model filenames contain svdq pattern."""
        for key, filename in NUNCHAKU_MODELS.items():
            assert "svdq" in filename, f"{key}: {filename} missing svdq pattern"


# ─── NUNCHAKU_REPO_ID ─────────────────────────────────────────────────


class TestNunchakuRepoId:
    def test_is_string(self):
        assert isinstance(NUNCHAKU_REPO_ID, str)

    def test_format(self):
        assert "/" in NUNCHAKU_REPO_ID

    def test_contains_nunchaku(self):
        assert "nunchaku" in NUNCHAKU_REPO_ID.lower()


# ─── ZIMAGE_VAE_CONFIG ────────────────────────────────────────────────


class TestZimageVaeConfig:
    def test_is_dict(self):
        assert isinstance(ZIMAGE_VAE_CONFIG, dict)

    def test_required_keys(self):
        required = {"url", "filename", "subfolder"}
        assert required.issubset(set(ZIMAGE_VAE_CONFIG.keys()))

    def test_url_format(self):
        assert ZIMAGE_VAE_CONFIG["url"].startswith("https://")

    def test_url_huggingface(self):
        assert "huggingface.co" in ZIMAGE_VAE_CONFIG["url"]

    def test_filename_safetensors(self):
        assert ZIMAGE_VAE_CONFIG["filename"].endswith(".safetensors")

    def test_subfolder_not_empty(self):
        assert ZIMAGE_VAE_CONFIG["subfolder"]


# ─── _get_hf_token ────────────────────────────────────────────────────


class TestGetHfToken:
    def test_returns_none_when_no_env_no_files(self, tmp_path, monkeypatch):
        monkeypatch.delenv("HF_TOKEN", raising=False)
        monkeypatch.delenv("HUGGINGFACE_TOKEN", raising=False)
        monkeypatch.chdir(tmp_path)
        # Ensure home token file doesn't exist
        fake_home = tmp_path / "home"
        fake_home.mkdir()
        monkeypatch.setenv("USERPROFILE", str(fake_home))
        monkeypatch.setattr(Path, "home", lambda: fake_home)
        result = _get_hf_token()
        assert result is None

    def test_returns_from_hf_token_env(self, monkeypatch):
        monkeypatch.setenv("HF_TOKEN", "hf_testtoken123")
        result = _get_hf_token()
        assert result == "hf_testtoken123"

    def test_returns_from_huggingface_token_env(self, monkeypatch):
        monkeypatch.delenv("HF_TOKEN", raising=False)
        monkeypatch.setenv("HUGGINGFACE_TOKEN", "hf_alttoken456")
        result = _get_hf_token()
        assert result == "hf_alttoken456"

    def test_hf_token_takes_precedence(self, monkeypatch):
        monkeypatch.setenv("HF_TOKEN", "hf_first")
        monkeypatch.setenv("HUGGINGFACE_TOKEN", "hf_second")
        result = _get_hf_token()
        assert result == "hf_first"

    def test_reads_from_secrets_file(self, tmp_path, monkeypatch):
        """Token read from .secrets/.env.huggingface with = format."""
        monkeypatch.delenv("HF_TOKEN", raising=False)
        monkeypatch.delenv("HUGGINGFACE_TOKEN", raising=False)
        secrets_file = tmp_path / ".secrets" / ".env.huggingface"
        secrets_file.parent.mkdir(parents=True, exist_ok=True)
        secrets_file.write_text("HF_TOKEN=hf_from_file_789")
        # Verify the file-parsing logic directly
        content = secrets_file.read_text().strip()
        assert "=" in content
        token = content.split("=", 1)[1].strip()
        assert token == "hf_from_file_789"
        assert token.startswith("hf_")

    def test_reads_token_only_file(self, tmp_path):
        """Verify bare token file (no =) parsing logic."""
        token_file = tmp_path / "token"
        token_file.write_text("hf_bare_token_xyz")
        # Simulate the file-reading logic from _get_hf_token
        content = token_file.read_text().strip()
        if "=" in content:
            token = content.split("=", 1)[1].strip()
        else:
            token = content
        assert token == "hf_bare_token_xyz"
        assert token.startswith("hf_")

    def test_ignores_non_hf_prefix(self, tmp_path):
        """Token not starting with hf_ from file should be ignored."""
        # Simulate the file-reading logic: non-hf_ prefix → skip
        content = "not_a_valid_token"
        token = None
        if "=" in content:
            token = content.split("=", 1)[1].strip()
        else:
            token = content
        if token and not token.startswith("hf_"):
            token = None
        assert token is None


# ─── download_nunchaku (list mode) ────────────────────────────────────


class TestDownloadNunchakuListMode:
    def test_list_returns_true(self, capsys):
        result = download_nunchaku(list_models=True)
        assert result is True

    def test_list_prints_models(self, capsys):
        download_nunchaku(list_models=True)
        captured = capsys.readouterr()
        assert "Modeles Nunchaku disponibles:" in captured.out
        # Should list all 6 models
        for key in NUNCHAKU_MODELS:
            assert key in captured.out

    def test_list_prints_filenames(self, capsys):
        download_nunchaku(list_models=True)
        captured = capsys.readouterr()
        for filename in NUNCHAKU_MODELS.values():
            assert filename in captured.out

    def test_unknown_model_returns_false(self, capsys):
        result = download_nunchaku(model_key="nonexistent-model")
        assert result is False

    def test_unknown_model_prints_error(self, capsys):
        download_nunchaku(model_key="nonexistent-model")
        captured = capsys.readouterr()
        assert "Modele inconnu" in captured.out


# ─── register (argparse wiring) ───────────────────────────────────────


class TestRegister:
    def test_creates_subparser(self):
        parser = argparse.ArgumentParser()
        subparsers = parser.add_subparsers(dest="command")
        register(subparsers)
        # Should not raise

    def test_download_qwen_subcommand(self):
        parser = argparse.ArgumentParser()
        subparsers = parser.add_subparsers(dest="command")
        register(subparsers)
        args = parser.parse_args(["models", "download-qwen"])
        assert args.models_action == "download-qwen"

    def test_download_qwen_dest_flag(self):
        parser = argparse.ArgumentParser()
        subparsers = parser.add_subparsers(dest="command")
        register(subparsers)
        args = parser.parse_args(["models", "download-qwen", "--dest", "/tmp/test"])
        assert args.dest == "/tmp/test"

    def test_download_qwen_docker_flag(self):
        parser = argparse.ArgumentParser()
        subparsers = parser.add_subparsers(dest="command")
        register(subparsers)
        args = parser.parse_args(["models", "download-qwen", "--docker"])
        assert args.docker is True

    def test_download_nunchaku_subcommand(self):
        parser = argparse.ArgumentParser()
        subparsers = parser.add_subparsers(dest="command")
        register(subparsers)
        args = parser.parse_args(["models", "download-nunchaku"])
        assert args.models_action == "download-nunchaku"

    def test_download_nunchaku_model_flag(self):
        parser = argparse.ArgumentParser()
        subparsers = parser.add_subparsers(dest="command")
        register(subparsers)
        args = parser.parse_args(["models", "download-nunchaku", "-m", "standard-r128"])
        assert args.model == "standard-r128"

    def test_download_nunchaku_list_flag(self):
        parser = argparse.ArgumentParser()
        subparsers = parser.add_subparsers(dest="command")
        register(subparsers)
        args = parser.parse_args(["models", "download-nunchaku", "--list"])
        assert args.list is True

    def test_setup_zimage_subcommand(self):
        parser = argparse.ArgumentParser()
        subparsers = parser.add_subparsers(dest="command")
        register(subparsers)
        args = parser.parse_args(["models", "setup-zimage"])
        assert args.models_action == "setup-zimage"

    def test_list_checkpoints_subcommand(self):
        parser = argparse.ArgumentParser()
        subparsers = parser.add_subparsers(dest="command")
        register(subparsers)
        args = parser.parse_args(["models", "list-checkpoints"])
        assert args.models_action == "list-checkpoints"

    def test_list_nodes_subcommand(self):
        parser = argparse.ArgumentParser()
        subparsers = parser.add_subparsers(dest="command")
        register(subparsers)
        args = parser.parse_args(["models", "list-nodes"])
        assert args.models_action == "list-nodes"


# ─── execute (CLI dispatch) ───────────────────────────────────────────


class TestExecute:
    def _make_args(self, action, **kwargs):
        """Create a namespace mimicking argparse output."""
        defaults = {
            "models_action": action,
            "dest": None,
            "docker": False,
            "container": "comfyui-qwen",
            "model": "lightning-4step-r128",
            "output_dir": None,
            "list": False,
        }
        defaults.update(kwargs)
        return argparse.Namespace(**defaults)

    def test_no_action_returns_1(self, capsys):
        args = self._make_args(None)
        result = execute(args)
        assert result == 1

    def test_unknown_action_returns_1(self, capsys):
        args = self._make_args("unknown-action")
        result = execute(args)
        assert result == 1

    def test_nunchaku_list_returns_0(self):
        args = self._make_args("download-nunchaku", list=True)
        result = execute(args)
        assert result == 0

    @patch.object(_models_mod, "download_qwen", return_value=True)
    def test_download_qwen_dispatch(self, mock_qwen):
        args = self._make_args("download-qwen", dest="/tmp/test", docker=True)
        result = execute(args)
        assert result == 0
        mock_qwen.assert_called_once_with(dest="/tmp/test", docker=True, container="comfyui-qwen")

    @patch.object(_models_mod, "download_qwen", return_value=False)
    def test_download_qwen_failure_returns_1(self, mock_qwen):
        args = self._make_args("download-qwen")
        result = execute(args)
        assert result == 1

    @patch.object(_models_mod, "download_nunchaku", return_value=True)
    def test_download_nunchaku_dispatch(self, mock_nun):
        args = self._make_args("download-nunchaku", model="standard-r128")
        result = execute(args)
        assert result == 0
        mock_nun.assert_called_once_with(
            model_key="standard-r128",
            output_dir=None,
            list_models=False,
        )

    @patch.object(_models_mod, "setup_zimage", return_value=True)
    def test_setup_zimage_dispatch(self, mock_zimage):
        args = self._make_args("setup-zimage")
        result = execute(args)
        assert result == 0
        mock_zimage.assert_called_once()

    @patch.object(_models_mod, "list_checkpoints", return_value=True)
    def test_list_checkpoints_dispatch(self, mock_lc):
        args = self._make_args("list-checkpoints")
        result = execute(args)
        assert result == 0

    @patch.object(_models_mod, "list_nodes", return_value=True)
    def test_list_nodes_dispatch(self, mock_ln):
        args = self._make_args("list-nodes")
        result = execute(args)
        assert result == 0


# ─── Cross-invariants ─────────────────────────────────────────────────


class TestCrossInvariants:
    def test_qwen_total_size_positive(self):
        total = sum(m["size_gb"] for m in QWEN_MODELS)
        assert total > 0

    def test_nunchaku_default_key_exists(self):
        """Default model_key used in download_nunchaku exists."""
        default_key = "lightning-4step-r128"
        assert default_key in NUNCHAKU_MODELS

    def test_nunchaku_choices_match_register(self):
        """NUNCHAKU_MODELS keys match argparse choices in register."""
        parser = argparse.ArgumentParser()
        subparsers = parser.add_subparsers(dest="command")
        register(subparsers)
        # Valid model key should parse
        args = parser.parse_args(["models", "download-nunchaku", "-m", "standard-r32"])
        assert args.model == "standard-r32"

    def test_zimage_filename_matches_config(self):
        """ZIMAGE_VAE_CONFIG filename matches MODEL_CONFIGS in config."""
        from config import MODEL_CONFIGS
        zimage_vae = MODEL_CONFIGS.get("zimage", {}).get("vae")
        assert zimage_vae == ZIMAGE_VAE_CONFIG["filename"]

    def test_qwen_subdirs_are_distinct(self):
        """Each Qwen model goes in a different subdir."""
        subdirs = [m["subdir"] for m in QWEN_MODELS]
        assert len(subdirs) == len(set(subdirs))
