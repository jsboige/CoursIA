"""Shared checkpoint utilities for PyTorch training scripts."""

from __future__ import annotations

import json
from datetime import datetime
from pathlib import Path

import torch


def save_pytorch_checkpoint(
    model,
    result: dict,
    hyperparams: dict,
    data_hash: str,
    output_dir: Path,
    model_type: str | None = None,
    extra_metadata: dict | None = None,
) -> Path:
    """Save PyTorch model checkpoint and metadata.

    Parameters
    ----------
    model : torch.nn.Module
        Trained model.
    result : dict
        Must contain "metrics" key. May contain "history".
    hyperparams : dict
        Training hyperparameters.
    data_hash : str
        Hash of training data.
    output_dir : Path
        Directory for checkpoint subdirectories.
    model_type : str or None
        Override model type. Defaults to hyperparams["model_type"].
    extra_metadata : dict or None
        Additional metadata fields (e.g., architecture details).

    Returns
    -------
    Path to the checkpoint directory.
    """
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    ckpt_path = output_dir / timestamp
    ckpt_path.mkdir(parents=True, exist_ok=True)

    torch.save(model.state_dict(), ckpt_path / "model.pt")

    metadata = {
        "timestamp": timestamp,
        "model_type": model_type or hyperparams.get("model_type", "unknown"),
        "hyperparams": hyperparams,
        "metrics": result["metrics"],
        "data_hash": data_hash,
        "files": ["model.pt", "metadata.json"],
    }
    if "history" in result:
        metadata["history"] = result["history"]
    if extra_metadata:
        metadata.update(extra_metadata)

    (ckpt_path / "metadata.json").write_text(
        json.dumps(metadata, indent=2, default=str), encoding="utf-8"
    )

    print(f"Checkpoint saved: {ckpt_path}")
    print(f"  Metrics: {result['metrics']}")
    return ckpt_path
