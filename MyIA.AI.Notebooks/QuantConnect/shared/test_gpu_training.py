#!/usr/bin/env python3
"""Pytest suite for `QuantConnect/shared/gpu_training.py`.

Co-located with the module under `shared/`. CPU-only, no GPU, no nvidia-smi,
no real training run. The module imports torch + torch.nn at top level (torch
is installed CPU-only on this worker), so it loads cleanly. `torch.cuda` is
never available on CPU, so every CUDA-guarded code path (thermal_check's hot
branch, batch_thermal_check's delegation, setup_amp's enabled flag) is reached
by monkeypatching `torch.cuda.is_available` -> True and mocking the
nvidia-smi subprocess + time.sleep.

The module is the GPU thermal-watchdog + checkpoint helper for ML training
(notebooks 19-27 ML/DL/AI) and had 0 dedicated Python test coverage before
this PR. This suite covers the pure/thermal/checkpoint logic; it deliberately
does NOT exercise `amp_train_step` (a real forward/backward pass) to stay a
unit test, not a training run.

Strategy: tiny torch.nn.Linear model + SGD optimizer for checkpoint round-trips
against tmp_path. get_gpu_temp is exercised by mocking subprocess.run.
"""
from __future__ import annotations

import importlib.util
import time
from pathlib import Path
from types import SimpleNamespace

import pytest
import torch
import torch.nn as nn

# Load the module by path (lives under shared/, top-level torch + stdlib only).
_MODULE_PATH = Path(__file__).resolve().parent / "gpu_training.py"
_spec = importlib.util.spec_from_file_location("gpu_training_under_test", _MODULE_PATH)
gt = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(gt)


# --------------------------------------------------------------------------
# Tiny model + optimizer fixtures for checkpoint round-trips
# --------------------------------------------------------------------------


@pytest.fixture
def tiny_model():
    torch.manual_seed(0)
    return nn.Linear(3, 1)


@pytest.fixture
def tiny_optimizer(tiny_model):
    return torch.optim.SGD(tiny_model.parameters(), lr=0.01)


# --------------------------------------------------------------------------
# get_gpu_temp — nvidia-smi subprocess parse
# --------------------------------------------------------------------------


def _smi(stdout="75", returncode=0):
    return lambda *a, **k: SimpleNamespace(stdout=stdout, stderr="", returncode=returncode)


def test_get_gpu_temp_parses_int_stdout(monkeypatch):
    monkeypatch.setattr(gt.subprocess, "run", _smi("73"))
    assert gt.get_gpu_temp() == 73


def test_get_gpu_temp_strips_whitespace(monkeypatch):
    monkeypatch.setattr(gt.subprocess, "run", _smi("  \n82\n  "))
    assert gt.get_gpu_temp() == 82


def test_get_gpu_temp_returns_zero_on_subprocess_failure(monkeypatch):
    def _raise(*a, **k):
        raise FileNotFoundError("no nvidia-smi")

    monkeypatch.setattr(gt.subprocess, "run", _raise)
    assert gt.get_gpu_temp() == 0


def test_get_gpu_temp_returns_zero_on_non_int_stdout(monkeypatch):
    # Bare except -> 0 when stdout cannot be parsed as int.
    monkeypatch.setattr(gt.subprocess, "run", _smi("N/A"))
    assert gt.get_gpu_temp() == 0


# --------------------------------------------------------------------------
# thermal_check — CPU guard + hot/cool threshold logic
# --------------------------------------------------------------------------


def test_thermal_check_returns_zero_when_no_cuda(monkeypatch):
    # On a CPU worker, torch.cuda.is_available() is False -> immediate 0,
    # get_gpu_temp must NOT be called.
    monkeypatch.setattr(gt.torch.cuda, "is_available", lambda: False)
    monkeypatch.setattr(gt, "get_gpu_temp", lambda: (_ for _ in ()).throw(AssertionError()))
    assert gt.thermal_check(max_temp=80) == 0


def test_thermal_check_hot_temp_sleeps(monkeypatch):
    monkeypatch.setattr(gt.torch.cuda, "is_available", lambda: True)
    monkeypatch.setattr(gt, "get_gpu_temp", lambda: 92)
    slept = []
    monkeypatch.setattr(gt.time, "sleep", lambda s: slept.append(s))
    temp = gt.thermal_check(max_temp=80, cool_sleep=15, verbose=False)
    assert temp == 92
    assert slept == [15]


def test_thermal_check_cool_temp_no_sleep(monkeypatch):
    monkeypatch.setattr(gt.torch.cuda, "is_available", lambda: True)
    monkeypatch.setattr(gt, "get_gpu_temp", lambda: 65)
    slept = []
    monkeypatch.setattr(gt.time, "sleep", lambda s: slept.append(s))
    temp = gt.thermal_check(max_temp=80, verbose=False)
    assert temp == 65
    assert slept == []


# --------------------------------------------------------------------------
# batch_thermal_check — modulo gate
# --------------------------------------------------------------------------


def test_batch_thermal_check_skips_when_batch_not_multiple(monkeypatch):
    # batch_idx=5, check_every=10 -> 5 % 10 != 0 -> skip, returns 0.
    monkeypatch.setattr(gt.torch.cuda, "is_available", lambda: True)
    monkeypatch.setattr(gt, "get_gpu_temp", lambda: (_ for _ in ()).throw(AssertionError()))
    assert gt.batch_thermal_check(5, check_every=10, verbose=False) == 0


def test_batch_thermal_check_delegates_on_multiple(monkeypatch):
    monkeypatch.setattr(gt.torch.cuda, "is_available", lambda: True)
    monkeypatch.setattr(gt, "get_gpu_temp", lambda: 70)
    monkeypatch.setattr(gt.time, "sleep", lambda s: None)
    # batch_idx=20, check_every=10 -> 20 % 10 == 0 -> delegates to thermal_check.
    assert gt.batch_thermal_check(20, check_every=10, verbose=False) == 70


# --------------------------------------------------------------------------
# setup_amp — CUDA-gated scaler
# --------------------------------------------------------------------------


def test_setup_amp_returns_disabled_scaler_on_cpu():
    # On CPU, use_amp must be False; GradScaler constructed disabled.
    use_amp, scaler = gt.setup_amp()
    assert use_amp is False
    assert scaler is not None
    assert scaler.is_enabled() is False


# --------------------------------------------------------------------------
# checkpoint_save — state dict shape
# --------------------------------------------------------------------------


def test_checkpoint_save_writes_required_fields(tmp_path, tiny_model, tiny_optimizer):
    path = tmp_path / "ckpt.pt"
    gt.checkpoint_save(str(path), epoch=3, model=tiny_model,
                       optimizer=tiny_optimizer, best_val_loss=0.5,
                       history={"train_loss": [1.0, 0.9]})
    state = torch.load(path, weights_only=False)
    assert state["epoch"] == 3
    assert state["best_val_loss"] == 0.5
    assert state["history"] == {"train_loss": [1.0, 0.9]}
    assert "model_state_dict" in state
    assert "optimizer_state_dict" in state
    # Optional fields absent when not provided.
    assert "scheduler_state_dict" not in state
    assert "grad_scaler_state" not in state
    assert "extra" not in state


def test_checkpoint_save_includes_optional_fields_when_provided(tmp_path, tiny_model, tiny_optimizer):
    path = tmp_path / "ckpt.pt"
    scheduler = torch.optim.lr_scheduler.StepLR(tiny_optimizer, step_size=5)
    scaler = torch.amp.GradScaler("cuda", enabled=False)
    gt.checkpoint_save(str(path), epoch=2, model=tiny_model, optimizer=tiny_optimizer,
                       scheduler=scheduler, grad_scaler=scaler, extra={"note": "run-42"})
    state = torch.load(path, weights_only=False)
    assert "scheduler_state_dict" in state
    assert "grad_scaler_state" in state
    assert state["extra"] == {"note": "run-42"}


def test_checkpoint_save_creates_nested_parent_dir(tmp_path, tiny_model, tiny_optimizer):
    # checkpoint_save now creates the parent dir (parents=True, exist_ok=True)
    # before torch.save, consistent with data_cache.get_yf_data and
    # video_helpers.frames_to_video. Previously a nested missing parent raised
    # RuntimeError and the caller had to mkdir first.
    nested = tmp_path / "deep" / "nested" / "ckpt.pt"
    assert not nested.parent.exists()
    gt.checkpoint_save(str(nested), epoch=1, model=tiny_model,
                       optimizer=tiny_optimizer)
    assert nested.exists()
    # Idempotent: re-saving to the now-existing path still succeeds (exist_ok).
    gt.checkpoint_save(str(nested), epoch=2, model=tiny_model,
                       optimizer=tiny_optimizer)
    assert nested.exists()


# --------------------------------------------------------------------------
# checkpoint_resume — 3 cases
# --------------------------------------------------------------------------


def test_checkpoint_resume_from_scratch_when_no_files(tmp_path, tiny_model):
    start, best, history, extra = gt.checkpoint_resume(
        str(tmp_path / "nope.pt"), str(tmp_path / "nofinal.pt"), tiny_model
    )
    assert start == 0
    assert best == float("inf")
    assert history == {}
    assert extra is None


def test_checkpoint_resume_from_final_model(tmp_path, tiny_model):
    # Write a "final model" save file (state_dict only + extra).
    final = tmp_path / "final.pt"
    torch.manual_seed(1)
    expected = nn.Linear(3, 1)
    torch.save({"model_state_dict": expected.state_dict(), "extra": {"acc": 0.9}}, final)
    fresh = nn.Linear(3, 1)
    start, best, history, extra = gt.checkpoint_resume(
        str(tmp_path / "nope.pt"), str(final), fresh
    )
    # Final-model case returns start=-1, extra from the save.
    assert start == -1
    assert extra == {"acc": 0.9}
    # Model weights loaded from the save.
    loaded_w = list(fresh.parameters())[0].detach().tolist()
    expected_w = list(expected.parameters())[0].detach().tolist()
    assert loaded_w == expected_w


def test_checkpoint_resume_from_checkpoint_roundtrip(tmp_path, tiny_model, tiny_optimizer):
    ckpt = tmp_path / "ckpt.pt"
    gt.checkpoint_save(str(ckpt), epoch=4, model=tiny_model, optimizer=tiny_optimizer,
                       best_val_loss=0.42, history={"val_loss": [1.0, 0.42]},
                       extra={"tag": "mid"})
    # New model/optimizer to load into.
    fresh_model = nn.Linear(3, 1)
    fresh_opt = torch.optim.SGD(fresh_model.parameters(), lr=0.01)
    start, best, history, extra = gt.checkpoint_resume(
        str(ckpt), str(tmp_path / "nofinal.pt"), fresh_model, optimizer=fresh_opt
    )
    assert start == 4
    assert best == 0.42
    assert history == {"val_loss": [1.0, 0.42]}
    assert extra == {"tag": "mid"}


# --------------------------------------------------------------------------
# TrainingCheckpoint — ctor + early-stopping patience
# --------------------------------------------------------------------------


def test_training_checkpoint_ctor_defaults():
    tc = gt.TrainingCheckpoint("c.pt", "f.pt")
    assert tc.checkpoint_path == "c.pt"
    assert tc.model_save_path == "f.pt"
    assert tc.max_temp == 80
    assert tc.cool_sleep == 15
    assert tc.patience == 7
    assert tc.thermal_check_every == 10
    assert tc.best_val_loss == float("inf")
    assert tc.patience_counter == 0
    assert tc.best_model_state is None


def test_training_checkpoint_resume_from_scratch(tmp_path, tiny_model):
    tc = gt.TrainingCheckpoint(str(tmp_path / "c.pt"), str(tmp_path / "f.pt"))
    start_epoch, history = tc.resume(tiny_model)
    assert start_epoch == 0
    assert history == {}
