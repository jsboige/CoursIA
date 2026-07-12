"""Tests for validate_training_package.py — pipeline validation harness."""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from validate_training_package import (
    REQUIRED_METADATA_FIELDS,
    TRAINING_SCRIPTS,
    check_imports,
    find_latest_checkpoint,
    validate_checkpoint,
)


class TestTrainingScripts:
    """Configuration tests."""

    def test_four_scripts(self):
        assert len(TRAINING_SCRIPTS) == 4

    def test_all_py_files(self):
        for s in TRAINING_SCRIPTS:
            assert s.endswith(".py")


class TestRequiredMetadataFields:
    """Metadata field config tests."""

    def test_required_fields_present(self):
        expected = {"timestamp", "model_type", "hyperparams", "metrics", "data_hash", "files"}
        assert set(REQUIRED_METADATA_FIELDS) == expected


class TestCheckImports:
    """Import check tests."""

    def test_core_deps_available(self):
        errors = check_imports("train_classification.py")
        core_errors = [e for e in errors if "numpy" in e or "pandas" in e]
        assert len(core_errors) == 0

    def test_sklearn_required_for_classification(self):
        errors = check_imports("train_classification.py")
        sklearn_missing = [e for e in errors if "scikit-learn" in e]
        # sklearn should be installed in test env
        assert len(sklearn_missing) == 0

    def test_torch_required_for_lstm(self):
        errors = check_imports("train_lstm.py")
        torch_missing = [e for e in errors if "torch" in e]
        # torch should be installed in test env
        assert len(torch_missing) == 0

    def test_torch_required_for_transformer(self):
        errors = check_imports("train_transformer.py")
        torch_missing = [e for e in errors if "torch" in e]
        assert len(torch_missing) == 0

    def test_torch_required_for_dqn(self):
        errors = check_imports("train_dqn_rl.py")
        torch_missing = [e for e in errors if "torch" in e]
        assert len(torch_missing) == 0


class TestFindLatestCheckpoint:
    """Checkpoint discovery tests."""

    def test_nonexistent_dir(self, tmp_path):
        result = find_latest_checkpoint(tmp_path / "nonexistent")
        assert result is None

    def test_empty_dir(self, tmp_path):
        ckpt_dir = tmp_path / "checkpoints"
        ckpt_dir.mkdir()
        result = find_latest_checkpoint(ckpt_dir)
        assert result is None

    def test_finds_latest(self, tmp_path):
        ckpt_dir = tmp_path / "checkpoints"
        ckpt_dir.mkdir()
        (ckpt_dir / "20250101_000000").mkdir()
        (ckpt_dir / "20250102_120000").mkdir()
        (ckpt_dir / "20250103_060000").mkdir()
        result = find_latest_checkpoint(ckpt_dir)
        assert result is not None
        assert result.name == "20250103_060000"


class TestValidateCheckpoint:
    """Checkpoint validation tests."""

    def test_nonexistent_dir(self, tmp_path):
        errors = validate_checkpoint(tmp_path / "nope", "train_lstm.py")
        assert len(errors) > 0

    def test_missing_metadata(self, tmp_path):
        ckpt_dir = tmp_path / "ckpt"
        ckpt_dir.mkdir()
        errors = validate_checkpoint(ckpt_dir, "train_lstm.py")
        assert any("metadata.json" in e for e in errors)

    def test_invalid_json_metadata(self, tmp_path):
        ckpt_dir = tmp_path / "ckpt"
        ckpt_dir.mkdir()
        (ckpt_dir / "metadata.json").write_text("not json{")
        errors = validate_checkpoint(ckpt_dir, "train_lstm.py")
        assert any("Invalid" in e for e in errors)

    def test_missing_required_fields(self, tmp_path):
        ckpt_dir = tmp_path / "ckpt"
        ckpt_dir.mkdir()
        (ckpt_dir / "metadata.json").write_text(json.dumps({"only_field": 1}))
        errors = validate_checkpoint(ckpt_dir, "train_lstm.py")
        missing_fields = [e for e in errors if "Missing metadata field" in e]
        assert len(missing_fields) > 0

    def test_valid_checkpoint(self, tmp_path):
        ckpt_dir = tmp_path / "ckpt"
        ckpt_dir.mkdir()
        metadata = {
            "timestamp": "2026-01-01T00:00:00",
            "model_type": "lstm",
            "hyperparams": {"hidden_size": 64},
            "metrics": {"test_accuracy": 0.54},
            "data_hash": "abc123",
            "files": {"model": "model.pt"},
        }
        (ckpt_dir / "metadata.json").write_text(json.dumps(metadata))
        (ckpt_dir / "model.pt").write_bytes(b"fake model")

        errors = validate_checkpoint(ckpt_dir, "train_lstm.py")
        assert errors == []

    def test_empty_data_hash_flagged(self, tmp_path):
        ckpt_dir = tmp_path / "ckpt"
        ckpt_dir.mkdir()
        metadata = {
            "timestamp": "2026-01-01",
            "model_type": "test",
            "hyperparams": {},
            "metrics": {},
            "data_hash": "",
            "files": {},
        }
        (ckpt_dir / "metadata.json").write_text(json.dumps(metadata))
        (ckpt_dir / "model.pt").write_bytes(b"")

        errors = validate_checkpoint(ckpt_dir, "test.py")
        assert any("data_hash" in e for e in errors)

    def test_no_model_file_flagged(self, tmp_path):
        ckpt_dir = tmp_path / "ckpt"
        ckpt_dir.mkdir()
        metadata = {
            "timestamp": "t",
            "model_type": "test",
            "hyperparams": {},
            "metrics": {},
            "data_hash": "abc",
            "files": {},
        }
        (ckpt_dir / "metadata.json").write_text(json.dumps(metadata))
        # No model file

        errors = validate_checkpoint(ckpt_dir, "test.py")
        assert any("model file" in e.lower() for e in errors)
