"""Tests for checkpoint_utils.py — shared PyTorch checkpoint saving."""

from __future__ import annotations

import json
from pathlib import Path

import numpy as np
import pytest
import torch
import torch.nn as nn

from checkpoint_utils import save_pytorch_checkpoint


@pytest.fixture
def tmp_output(tmp_path):
    return tmp_path / "checkpoints"


@pytest.fixture
def simple_model():
    return nn.Linear(4, 2)


@pytest.fixture
def result():
    return {
        "metrics": {"sharpe": 1.5, "dir_acc": 0.55, "mse": 0.001},
        "history": {"train_loss": [0.1, 0.05, 0.01], "val_loss": [0.2, 0.1, 0.05]},
    }


@pytest.fixture
def hyperparams():
    return {"model_type": "lstm", "hidden_size": 64, "lr": 0.001}


class TestSavePytorchCheckpoint:
    def test_creates_directory_structure(self, simple_model, result, hyperparams, tmp_output):
        path = save_pytorch_checkpoint(
            simple_model, result, hyperparams, "abc123", tmp_output
        )
        assert path.exists()
        assert (path / "model.pt").exists()
        assert (path / "metadata.json").exists()

    def test_model_weights_saved(self, simple_model, result, hyperparams, tmp_output):
        path = save_pytorch_checkpoint(
            simple_model, result, hyperparams, "abc123", tmp_output
        )
        state = torch.load(path / "model.pt", weights_only=True)
        assert "weight" in state
        assert "bias" in state

    def test_metadata_contains_required_fields(
        self, simple_model, result, hyperparams, tmp_output
    ):
        path = save_pytorch_checkpoint(
            simple_model, result, hyperparams, "abc123", tmp_output
        )
        meta = json.loads((path / "metadata.json").read_text(encoding="utf-8"))
        assert meta["model_type"] == "lstm"
        assert meta["hyperparams"] == hyperparams
        assert meta["metrics"] == result["metrics"]
        assert meta["data_hash"] == "abc123"
        assert "timestamp" in meta
        assert meta["files"] == ["model.pt", "metadata.json"]

    def test_history_included_when_present(
        self, simple_model, result, hyperparams, tmp_output
    ):
        path = save_pytorch_checkpoint(
            simple_model, result, hyperparams, "abc123", tmp_output
        )
        meta = json.loads((path / "metadata.json").read_text(encoding="utf-8"))
        assert "history" in meta
        assert meta["history"]["train_loss"] == [0.1, 0.05, 0.01]

    def test_history_absent_when_not_in_result(
        self, simple_model, hyperparams, tmp_output
    ):
        result = {"metrics": {"sharpe": 0.5}}
        path = save_pytorch_checkpoint(
            simple_model, result, hyperparams, "abc123", tmp_output
        )
        meta = json.loads((path / "metadata.json").read_text(encoding="utf-8"))
        assert "history" not in meta

    def test_model_type_override(self, simple_model, result, hyperparams, tmp_output):
        path = save_pytorch_checkpoint(
            simple_model, result, hyperparams, "abc123", tmp_output, model_type="custom"
        )
        meta = json.loads((path / "metadata.json").read_text(encoding="utf-8"))
        assert meta["model_type"] == "custom"

    def test_model_type_from_hyperparams_fallback(
        self, simple_model, result, tmp_output
    ):
        hyperparams = {"model_type": "transformer", "d_model": 128}
        path = save_pytorch_checkpoint(
            simple_model, result, hyperparams, "abc123", tmp_output
        )
        meta = json.loads((path / "metadata.json").read_text(encoding="utf-8"))
        assert meta["model_type"] == "transformer"

    def test_model_type_unknown_when_missing(
        self, simple_model, result, tmp_output
    ):
        hyperparams = {"lr": 0.001}
        path = save_pytorch_checkpoint(
            simple_model, result, hyperparams, "abc123", tmp_output
        )
        meta = json.loads((path / "metadata.json").read_text(encoding="utf-8"))
        assert meta["model_type"] == "unknown"

    def test_extra_metadata(self, simple_model, result, hyperparams, tmp_output):
        extra = {"architecture": {"input_size": 4, "hidden_size": 64, "num_layers": 2}}
        path = save_pytorch_checkpoint(
            simple_model, result, hyperparams, "abc123", tmp_output, extra_metadata=extra
        )
        meta = json.loads((path / "metadata.json").read_text(encoding="utf-8"))
        assert meta["architecture"]["input_size"] == 4
        assert meta["architecture"]["num_layers"] == 2

    def test_multiple_checkpoints_different_dirs(
        self, simple_model, result, hyperparams, tmp_output
    ):
        import time

        path1 = save_pytorch_checkpoint(
            simple_model, result, hyperparams, "hash1", tmp_output
        )
        time.sleep(1.1)
        path2 = save_pytorch_checkpoint(
            simple_model, result, hyperparams, "hash2", tmp_output
        )
        assert path1 != path2
        assert path1.exists() and path2.exists()

    def test_loaded_model_produces_same_output(
        self, simple_model, result, hyperparams, tmp_output
    ):
        x = torch.randn(1, 4)
        original_output = simple_model(x).detach().numpy()
        path = save_pytorch_checkpoint(
            simple_model, result, hyperparams, "abc123", tmp_output
        )
        loaded = nn.Linear(4, 2)
        loaded.load_state_dict(torch.load(path / "model.pt", weights_only=True))
        loaded_output = loaded(x).detach().numpy()
        np.testing.assert_array_almost_equal(original_output, loaded_output)
