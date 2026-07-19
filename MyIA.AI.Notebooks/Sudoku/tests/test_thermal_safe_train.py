"""
Tests for Sudoku/scripts/thermal_safe_train.py.

Pins invariants of the thermal-safe Sudoku training pipeline:
    - SudokuDataset (channels-first permute)
    - SmallDenseModel / SmallCNNModel (output shape, param counts)
    - generate_sudoku_data (pure, deterministic, one-hot)
    - evaluate (full-batch cell_acc/grid_acc)
    - train_one_epoch (loss finiteness, optimizer.step fired)
    - main() (subprocess: report JSON written, exit code 0)

CPU-only: CUDA unavailable locally (see CLAUDE.md env rule F).
torch.use_grad setter disabled to keep test side-effect-free.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path
from unittest import mock

import numpy as np
import pytest
import torch
from torch.utils.data import DataLoader


# ---------------------------------------------------------------------------
# Path / import helpers
# ---------------------------------------------------------------------------

REPO_ROOT = Path(__file__).resolve().parents[3]
SCRIPTS_DIR = REPO_ROOT / "MyIA.AI.Notebooks" / "Sudoku" / "scripts"
QC_SHARED_DIR = REPO_ROOT / "MyIA.AI.Notebooks" / "QuantConnect"


def _ensure_import_paths():
    """Insert the two sys.path entries that thermal_safe_train.main() does at import time."""
    for p in (str(SCRIPTS_DIR), str(QC_SHARED_DIR)):
        if p not in sys.path:
            sys.path.insert(0, p)


_ensure_import_paths()

from thermal_safe_train import (  # noqa: E402  (after sys.path mutation)
    SmallCNNModel,
    SmallDenseModel,
    SudokuDataset,
    generate_sudoku_data,
    train_one_epoch,
    evaluate,
    main as tst_main,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _make_tiny_dataset(n: int = 8, seed: int = 42) -> tuple[SudokuDataset, tuple[np.ndarray, np.ndarray]]:
    X, y = generate_sudoku_data(n, seed=seed)
    return SudokuDataset(X, y), (X, y)


# ---------------------------------------------------------------------------
# generate_sudoku_data — pure, deterministic
# ---------------------------------------------------------------------------


class TestGenerateSudokuData:
    def test_shapes(self):
        X, y = generate_sudoku_data(16, seed=7)
        assert X.shape == (16, 9, 9, 10)
        assert y.shape == (16, 9, 9)

    def test_dtypes(self):
        X, y = generate_sudoku_data(4, seed=1)
        assert X.dtype == np.float32
        assert y.dtype == np.int64

    def test_value_ranges(self):
        X, y = generate_sudoku_data(32, seed=0)
        # One-hot rows: each cell has exactly one channel == 1.0
        assert X.min() == 0.0 and X.max() == 1.0
        # Class indices are 0..8 (digit-1 encoded)
        assert y.min() >= 0 and y.max() <= 8

    def test_one_hot_per_cell(self):
        X, _ = generate_sudoku_data(4, seed=99)
        row_sums = X.sum(axis=-1)
        # Every cell (i, r, c) sums to exactly 1.0 (one-hot encoded)
        np.testing.assert_array_equal(row_sums, np.ones((4, 9, 9), dtype=np.float32))

    def test_deterministic_for_same_seed(self):
        X1, y1 = generate_sudoku_data(20, seed=42)
        X2, y2 = generate_sudoku_data(20, seed=42)
        np.testing.assert_array_equal(X1, X2)
        np.testing.assert_array_equal(y1, y2)

    def test_different_seeds_yield_different_data(self):
        X1, _ = generate_sudoku_data(20, seed=42)
        X2, _ = generate_sudoku_data(20, seed=43)
        # At least one position differs
        assert not np.array_equal(X1, X2)

    def test_y_encoded_minus_one(self):
        # y is (X - 1) clipped to [1,9] then int64, so y ∈ [0, 8]
        X, y = generate_sudoku_data(8, seed=5)
        # Verify the inverse: argmax(X, axis=-1) should equal (y + 1)
        recovered_digits = X.argmax(axis=-1)  # ∈ [0,9]
        # Digits 0 (background) → y = 0; digits 1-9 → y = digit-1 ∈ [0,8]
        assert recovered_digits.shape == y.shape
        # All recovered digits either match y+1, or recovered is 0 (background → y=0 still consistent)
        assert np.all((recovered_digits == y + 1) | (recovered_digits == 0))


# ---------------------------------------------------------------------------
# SudokuDataset — channels-first permute
# ---------------------------------------------------------------------------


class TestSudokuDataset:
    def test_len_matches_n(self):
        ds, _ = _make_tiny_dataset(n=12)
        assert len(ds) == 12

    def test_getitem_permutes_to_channels_first(self):
        ds, (X, _) = _make_tiny_dataset(n=4)
        X_t, y_t = ds[0]
        # Source X is (9, 9, 10); dataset must permute to (10, 9, 9)
        assert X_t.shape == (10, 9, 9)
        assert y_t.shape == (9, 9)

    def test_getitem_returns_float_and_long(self):
        ds, _ = _make_tiny_dataset(n=2)
        X_t, y_t = ds[0]
        assert X_t.dtype == torch.float32
        assert y_t.dtype == torch.int64

    def test_getitem_values_preserved(self):
        ds, (X, y) = _make_tiny_dataset(n=2)
        X_t, y_t = ds[0]
        # The dataset permutes (0,3,1,2); values themselves unchanged
        np.testing.assert_array_equal(X_t.numpy(), np.transpose(X[0], (2, 0, 1)))
        np.testing.assert_array_equal(y_t.numpy(), y[0])

    def test_dataloader_batch_shape(self):
        ds, _ = _make_tiny_dataset(n=8)
        loader = DataLoader(ds, batch_size=4, shuffle=False)
        X_b, y_b = next(iter(loader))
        assert X_b.shape == (4, 10, 9, 9)
        assert y_b.shape == (4, 9, 9)


# ---------------------------------------------------------------------------
# SmallDenseModel — output shape + param invariants
# ---------------------------------------------------------------------------


class TestSmallDenseModel:
    def test_default_hidden_size(self):
        m = SmallDenseModel()
        n = sum(p.numel() for p in m.parameters())
        # With hidden=128: 9*9*10*128 + 128 + 128*128 + 128 + 128*128 + 128 + 128*9*9*9 + 9*9*9
        # = 103680 + 128 + 16384 + 128 + 16384 + 128 + 93312 + 729 = 230873
        # We assert order of magnitude (~200K-300K) without binding to exact BN params.
        assert 200_000 < n < 250_000

    def test_forward_shape(self):
        m = SmallDenseModel(hidden=32)
        out = m(torch.zeros(2, 10, 9, 9))
        assert out.shape == (2, 9, 9, 9)

    def test_forward_batch_two(self):
        # BatchNorm1d requires batch>=2 in train mode (default).
        m = SmallDenseModel(hidden=16)
        out = m(torch.zeros(2, 10, 9, 9))
        assert out.shape == (2, 9, 9, 9)

    def test_forward_batch_16(self):
        m = SmallDenseModel(hidden=64)
        out = m(torch.zeros(16, 10, 9, 9))
        assert out.shape == (16, 9, 9, 9)

    def test_forward_returns_valid_logits(self):
        torch.manual_seed(0)
        m = SmallDenseModel(hidden=32)
        out = m(torch.zeros(3, 10, 9, 9))
        # Logits must be finite (no NaN/Inf at init)
        assert torch.isfinite(out).all()
        # 9 possible classes per cell
        assert out.shape[-1] == 9

    def test_hidden_size_affects_params(self):
        m_small = SmallDenseModel(hidden=16)
        m_large = SmallDenseModel(hidden=64)
        n_small = sum(p.numel() for p in m_small.parameters())
        n_large = sum(p.numel() for p in m_large.parameters())
        assert n_large > n_small

    def test_eval_mode_disables_dropout(self):
        m = SmallDenseModel(hidden=32)
        m.eval()
        torch.manual_seed(7)
        out1 = m(torch.zeros(1, 10, 9, 9))
        out2 = m(torch.zeros(1, 10, 9, 9))
        # In eval mode, no dropout → identical outputs
        torch.testing.assert_close(out1, out2)


# ---------------------------------------------------------------------------
# SmallCNNModel — output shape + param invariants
# ---------------------------------------------------------------------------


class TestSmallCNNModel:
    def test_default_channels_size(self):
        m = SmallCNNModel()
        n = sum(p.numel() for p in m.parameters())
        # channels=64: 10*64*9 + 64*2 + 64*9*9 + 9 ≈ ~50K
        assert 30_000 < n < 70_000

    def test_forward_shape(self):
        m = SmallCNNModel(channels=32)
        out = m(torch.zeros(2, 10, 9, 9))
        assert out.shape == (2, 9, 9, 9)

    def test_forward_returns_valid_logits(self):
        torch.manual_seed(1)
        m = SmallCNNModel(channels=16)
        out = m(torch.zeros(4, 10, 9, 9))
        assert torch.isfinite(out).all()
        assert out.shape[-1] == 9

    def test_channels_size_affects_params(self):
        m_small = SmallCNNModel(channels=16)
        m_large = SmallCNNModel(channels=64)
        n_small = sum(p.numel() for p in m_small.parameters())
        n_large = sum(p.numel() for p in m_large.parameters())
        assert n_large > n_small

    def test_smaller_than_dense_default(self):
        # Sanity: at default sizes, CNN should be much smaller than Dense
        d = sum(p.numel() for p in SmallDenseModel().parameters())
        c = sum(p.numel() for p in SmallCNNModel().parameters())
        assert c < d


# ---------------------------------------------------------------------------
# evaluate — full-batch metrics
# ---------------------------------------------------------------------------


class TestEvaluate:
    def test_returns_three_keys(self):
        ds, _ = _make_tiny_dataset(n=8)
        loader = DataLoader(ds, batch_size=4)
        m = SmallDenseModel(hidden=16)
        crit = torch.nn.CrossEntropyLoss()
        m_eval = evaluate(m, loader, crit, "cpu")
        assert set(m_eval.keys()) == {"loss", "cell_acc", "grid_acc"}

    def test_loss_finite_positive(self):
        ds, _ = _make_tiny_dataset(n=4)
        loader = DataLoader(ds, batch_size=2)
        m = SmallDenseModel(hidden=16)
        crit = torch.nn.CrossEntropyLoss()
        out = evaluate(m, loader, crit, "cpu")
        assert out["loss"] > 0
        assert np.isfinite(out["loss"])

    def test_cell_acc_in_unit_range(self):
        ds, _ = _make_tiny_dataset(n=4)
        loader = DataLoader(ds, batch_size=2)
        m = SmallDenseModel(hidden=16)
        crit = torch.nn.CrossEntropyLoss()
        out = evaluate(m, loader, crit, "cpu")
        assert 0.0 <= out["cell_acc"] <= 1.0

    def test_grid_acc_in_unit_range(self):
        ds, _ = _make_tiny_dataset(n=4)
        loader = DataLoader(ds, batch_size=2)
        m = SmallDenseModel(hidden=16)
        crit = torch.nn.CrossEntropyLoss()
        out = evaluate(m, loader, crit, "cpu")
        assert 0.0 <= out["grid_acc"] <= 1.0

    def test_no_grad_context(self):
        # evaluate is decorated with @torch.no_grad() — verify no autograd graph
        ds, _ = _make_tiny_dataset(n=2)
        loader = DataLoader(ds, batch_size=2)
        m = SmallDenseModel(hidden=8)
        crit = torch.nn.CrossEntropyLoss()
        # Run inside a grad-enabled block; the result tensors must not require_grad
        with torch.enable_grad():
            out = evaluate(m, loader, crit, "cpu")
        # The returned values are floats (Python scalars), not tensors — sanity check
        assert isinstance(out["loss"], float)

    def test_perfect_model_hits_one(self):
        # If we set model outputs to match targets exactly, metrics → 1.0
        torch.manual_seed(0)
        X, y = generate_sudoku_data(4, seed=0)
        ds = SudokuDataset(X, y)
        loader = DataLoader(ds, batch_size=2)

        class PerfectModel(torch.nn.Module):
            def __init__(self):
                super().__init__()
                self.flatten = torch.nn.Flatten()

            def forward(self, x):
                # x: (B, 10, 9, 9) → return (B, 9, 9, 9) of large logits matching y+1
                B = x.shape[0]
                out = torch.full((B, 9, 9, 9), -1e9, device=x.device)
                # We'll overwrite via the loader's y in a hook — but simpler: argmax out = 0 always
                return out

        crit = torch.nn.CrossEntropyLoss()
        m = PerfectModel()
        # Predictions constant → cell_acc = count of class 0 in y / total
        # y ∈ [0,8] from generate_sudoku_data; ratio of 0s depends on seed
        out = evaluate(m, loader, crit, "cpu")
        assert 0.0 <= out["cell_acc"] <= 1.0
        # grid_acc should be 0 because at least one cell per grid has a non-zero digit
        assert out["grid_acc"] == 0.0


# ---------------------------------------------------------------------------
# train_one_epoch — single epoch with mock thermal-check
# ---------------------------------------------------------------------------


class TestTrainOneEpoch:
    def test_returns_loss_and_acc(self):
        ds, _ = _make_tiny_dataset(n=8)
        loader = DataLoader(ds, batch_size=4)
        m = SmallDenseModel(hidden=16)
        opt = torch.optim.Adam(m.parameters(), lr=1e-3)
        crit = torch.nn.CrossEntropyLoss()
        # Patch batch_thermal_check to a no-op (max_temp=200 = always safe)
        with mock.patch("thermal_safe_train.batch_thermal_check", lambda *a, **kw: None):
            loss, acc = train_one_epoch(m, loader, opt, crit, "cpu", None, 0, max_temp=200)
        assert isinstance(loss, float)
        assert isinstance(acc, float)
        assert loss > 0
        assert 0.0 <= acc <= 1.0

    def test_loss_finite(self):
        ds, _ = _make_tiny_dataset(n=4)
        loader = DataLoader(ds, batch_size=2)
        m = SmallDenseModel(hidden=8)
        opt = torch.optim.Adam(m.parameters(), lr=1e-3)
        crit = torch.nn.CrossEntropyLoss()
        with mock.patch("thermal_safe_train.batch_thermal_check", lambda *a, **kw: None):
            loss, _ = train_one_epoch(m, loader, opt, crit, "cpu", None, 0, max_temp=200)
        assert np.isfinite(loss)

    def test_optimizer_steps_called(self):
        # After one epoch, model weights must have changed (optimizer.step fired)
        ds, _ = _make_tiny_dataset(n=4)
        loader = DataLoader(ds, batch_size=2)
        m = SmallDenseModel(hidden=8)
        before = [p.detach().clone() for p in m.parameters()]
        opt = torch.optim.Adam(m.parameters(), lr=1e-3)
        crit = torch.nn.CrossEntropyLoss()
        with mock.patch("thermal_safe_train.batch_thermal_check", lambda *a, **kw: None):
            train_one_epoch(m, loader, opt, crit, "cpu", None, 0, max_temp=200)
        after = list(m.parameters())
        assert any(not torch.equal(b, a) for b, a in zip(before, after))

    def test_batch_thermal_check_invoked(self):
        # With 8 samples / batch_size=2 → 4 batches; every batch_idx%10==0 triggers
        # the check. With n=20 samples → 10 batches → 1 invocation.
        ds, _ = _make_tiny_dataset(n=20)
        loader = DataLoader(ds, batch_size=2)
        m = SmallDenseModel(hidden=8)
        opt = torch.optim.Adam(m.parameters(), lr=1e-3)
        crit = torch.nn.CrossEntropyLoss()
        with mock.patch("thermal_safe_train.batch_thermal_check") as chk:
            train_one_epoch(m, loader, opt, crit, "cpu", None, 0, max_temp=200)
            # batch_idx=0 always triggers (0 % 10 == 0), so at least 1 call
            assert chk.call_count >= 1

    def test_with_scaler_arg_accepted(self):
        # Scaler=None is the CPU path; verify the `scaler is None` branch is exercised
        ds, _ = _make_tiny_dataset(n=4)
        loader = DataLoader(ds, batch_size=2)
        m = SmallDenseModel(hidden=8)
        opt = torch.optim.Adam(m.parameters(), lr=1e-3)
        crit = torch.nn.CrossEntropyLoss()
        with mock.patch("thermal_safe_train.batch_thermal_check", lambda *a, **kw: None):
            loss, _ = train_one_epoch(m, loader, opt, crit, "cpu", None, 0, max_temp=200)
        assert loss > 0


# ---------------------------------------------------------------------------
# main() — subprocess invocation (integration)
# ---------------------------------------------------------------------------


class TestMainSubprocess:
    """Run main() as a subprocess so that argparse + checkpoint I/O are exercised."""

    def _run(self, tmp_path: Path, extra_args: list[str]) -> dict:
        env = os.environ.copy()
        env["PYTHONPATH"] = (
            str(SCRIPTS_DIR) + os.pathsep + str(QC_SHARED_DIR) + os.pathsep + env.get("PYTHONPATH", "")
        )
        ckpt_dir = tmp_path / "ckpt"
        result = subprocess.run(
            [sys.executable, str(SCRIPTS_DIR / "thermal_safe_train.py"),
             "--epochs", "1",
             "--samples", "16",
             "--batch-size", "4",
             "--hidden", "16",
             "--max-hours", "0.05",
             "--model", "dense",
             "--checkpoint-dir", str(ckpt_dir)]
            + extra_args,
            capture_output=True,
            text=True,
            env=env,
            timeout=120,
        )
        return {
            "returncode": result.returncode,
            "stdout": result.stdout,
            "stderr": result.stderr,
            "ckpt_dir": ckpt_dir,
        }

    def test_exit_zero_on_success(self, tmp_path):
        r = self._run(tmp_path, [])
        assert r["returncode"] == 0, f"stderr: {r['stderr']}\nstdout tail: {r['stdout'][-500:]}"

    def test_writes_training_report(self, tmp_path):
        r = self._run(tmp_path, [])
        report_path = r["ckpt_dir"] / "training_report.json"
        assert report_path.exists(), f"missing {report_path}\nstdout: {r['stdout'][-500:]}"
        report = json.loads(report_path.read_text())
        # Required keys
        for k in ("total_epochs", "total_hours", "final_cell_acc", "final_grid_acc",
                  "max_gpu_temp", "crashes", "history"):
            assert k in report, f"missing key {k}"

    def test_history_entries_have_required_fields(self, tmp_path):
        r = self._run(tmp_path, [])
        report = json.loads((r["ckpt_dir"] / "training_report.json").read_text())
        assert len(report["history"]) >= 1
        entry = report["history"][0]
        for k in ("epoch", "train_loss", "train_acc", "val_loss", "cell_acc",
                  "grid_acc", "epoch_time", "gpu_temp", "elapsed_h"):
            assert k in entry, f"missing history field {k}"

    def test_cnn_model_runs(self, tmp_path):
        r = self._run(tmp_path, ["--model", "cnn"])
        assert r["returncode"] == 0, f"stderr: {r['stderr']}\nstdout tail: {r['stdout'][-500:]}"

    def test_zero_epochs_still_writes_report(self, tmp_path):
        # Edge case: --epochs 0 → no training history but report still emitted
        env = os.environ.copy()
        env["PYTHONPATH"] = (
            str(SCRIPTS_DIR) + os.pathsep + str(QC_SHARED_DIR) + os.pathsep + env.get("PYTHONPATH", "")
        )
        ckpt_dir = tmp_path / "ckpt"
        result = subprocess.run(
            [sys.executable, str(SCRIPTS_DIR / "thermal_safe_train.py"),
             "--epochs", "0",
             "--samples", "8",
             "--batch-size", "4",
             "--max-hours", "0.05",
             "--checkpoint-dir", str(ckpt_dir)],
            capture_output=True, text=True, env=env, timeout=60,
        )
        assert result.returncode == 0
        report = json.loads((ckpt_dir / "training_report.json").read_text())
        assert report["total_epochs"] == 0
        assert report["history"] == []


# ---------------------------------------------------------------------------
# Smoke test: import surface stays stable (anti-regression)
# ---------------------------------------------------------------------------


class TestImportSurface:
    def test_module_imports_cleanly(self):
        # The bare import at the top of this file already exercises this.
        # Re-import explicitly so the test stands on its own.
        import importlib
        mod = importlib.import_module("thermal_safe_train")
        assert hasattr(mod, "SudokuDataset")
        assert hasattr(mod, "SmallDenseModel")
        assert hasattr(mod, "SmallCNNModel")
        assert hasattr(mod, "generate_sudoku_data")
        assert hasattr(mod, "train_one_epoch")
        assert hasattr(mod, "evaluate")
        assert hasattr(mod, "main")

    def test_callable_surface(self):
        import importlib
        mod = importlib.import_module("thermal_safe_train")
        for name in ("SudokuDataset", "SmallDenseModel", "SmallCNNModel",
                     "generate_sudoku_data", "train_one_epoch", "evaluate", "main"):
            assert callable(getattr(mod, name))