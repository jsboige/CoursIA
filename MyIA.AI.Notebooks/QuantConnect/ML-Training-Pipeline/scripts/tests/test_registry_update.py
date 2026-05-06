"""Tests for registry_update.py — checkpoint registry management."""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from registry_update import (
    build_registry_markdown,
    scan_checkpoints,
)


class TestScanCheckpoints:
    """Checkpoint scanning tests."""

    def test_empty_dir(self, tmp_path):
        entries = scan_checkpoints(tmp_path)
        assert entries == []

    def test_nonexistent_dir(self, tmp_path):
        entries = scan_checkpoints(tmp_path / "nonexistent")
        assert entries == []

    def test_valid_checkpoint(self, tmp_path):
        ckpt_dir = tmp_path / "lstm" / "20260505_120000"
        ckpt_dir.mkdir(parents=True)
        metadata = {
            "model_type": "lstm",
            "timestamp": "2026-05-05T12:00:00",
            "data_hash": "abc123",
            "hyperparams": {"hidden_size": 64},
            "metrics": {"test_accuracy": 0.55},
        }
        (ckpt_dir / "metadata.json").write_text(json.dumps(metadata))
        (ckpt_dir / "model.pt").write_bytes(b"fake")

        entries = scan_checkpoints(tmp_path)
        assert len(entries) == 1
        assert entries[0]["status"] == "OK"
        assert entries[0]["model_type"] == "lstm"
        assert entries[0]["data_hash"] == "abc123"

    def test_missing_metadata_flagged(self, tmp_path):
        ckpt_dir = tmp_path / "transformer" / "20260505_130000"
        ckpt_dir.mkdir(parents=True)
        # No metadata.json

        entries = scan_checkpoints(tmp_path)
        assert len(entries) == 1
        assert entries[0]["status"] == "MISSING_METADATA"

    def test_invalid_json_flagged(self, tmp_path):
        ckpt_dir = tmp_path / "lstm" / "20260505_bad"
        ckpt_dir.mkdir(parents=True)
        (ckpt_dir / "metadata.json").write_text("not json{")

        entries = scan_checkpoints(tmp_path)
        assert len(entries) == 1
        assert entries[0]["status"] == "INVALID_JSON"

    def test_missing_model_flagged(self, tmp_path):
        ckpt_dir = tmp_path / "dqn" / "20260505_nomodel"
        ckpt_dir.mkdir(parents=True)
        metadata = {"model_type": "dqn", "timestamp": "2026-05-05"}
        (ckpt_dir / "metadata.json").write_text(json.dumps(metadata))
        # No model file

        entries = scan_checkpoints(tmp_path)
        assert len(entries) == 1
        assert entries[0]["status"] == "MISSING_MODEL"

    def test_multiple_checkpoints(self, tmp_path):
        for model_type in ["lstm", "transformer", "classification"]:
            ckpt_dir = tmp_path / model_type / "20260505_120000"
            ckpt_dir.mkdir(parents=True)
            metadata = {"model_type": model_type, "timestamp": "2026-05-05"}
            (ckpt_dir / "metadata.json").write_text(json.dumps(metadata))
            (ckpt_dir / "model.pt").write_bytes(b"fake")

        entries = scan_checkpoints(tmp_path)
        assert len(entries) == 3
        types = {e["model_type"] for e in entries}
        assert types == {"lstm", "transformer", "classification"}

    def test_files_listed(self, tmp_path):
        ckpt_dir = tmp_path / "lstm" / "20260505_files"
        ckpt_dir.mkdir(parents=True)
        metadata = {"model_type": "lstm"}
        (ckpt_dir / "metadata.json").write_text(json.dumps(metadata))
        (ckpt_dir / "model.pt").write_bytes(b"fake")
        (ckpt_dir / "scaler.pkl").write_bytes(b"fake")

        entries = scan_checkpoints(tmp_path)
        assert "model.pt" in entries[0]["files"]
        assert "scaler.pkl" in entries[0]["files"]


class TestBuildRegistryMarkdown:
    """Markdown generation tests."""

    def test_empty_entries(self):
        md = build_registry_markdown([])
        assert "Total checkpoints: 0" in md

    def test_header_present(self):
        md = build_registry_markdown([])
        assert "# Checkpoint Registry" in md

    def test_model_type_section(self):
        entries = [{
            "model_type": "lstm",
            "timestamp": "2026-05-05",
            "status": "OK",
            "data_hash": "abc",
            "hyperparams": {},
            "metrics": {},
            "architecture": {},
            "files": ["model.pt"],
            "path": "checkpoints/lstm/2026-05-05",
        }]
        md = build_registry_markdown(entries)
        assert "## lstm" in md
        assert "OK" in md

    def test_issues_section(self):
        entries = [
            {
                "model_type": "lstm",
                "timestamp": "2026-05-05",
                "status": "MISSING_MODEL",
                "data_hash": "",
                "hyperparams": {},
                "metrics": {},
                "architecture": {},
                "files": [],
                "path": "checkpoints/lstm/2026-05-05",
            }
        ]
        md = build_registry_markdown(entries)
        assert "## Issues" in md
        assert "MISSING_MODEL" in md

    def test_metrics_displayed(self):
        entries = [{
            "model_type": "transformer",
            "timestamp": "2026-05-05",
            "status": "OK",
            "data_hash": "",
            "hyperparams": {},
            "metrics": {"test_accuracy": 0.55, "sharpe": 1.2},
            "architecture": {},
            "files": ["model.pt"],
            "path": "checkpoints/transformer/2026-05-05",
        }]
        md = build_registry_markdown(entries)
        assert "Metrics:" in md
        assert "test_accuracy" in md
