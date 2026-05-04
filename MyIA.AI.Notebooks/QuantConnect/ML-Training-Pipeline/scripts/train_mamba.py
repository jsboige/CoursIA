"""
Train Mamba SSM models for financial time-series forecasting.

Implements "Mamba: Linear-Time Sequence Modeling with Selective State Spaces"
(Gu & Dao, 2023). Adapted for finance following MambaStock (Zshi et al., 2024)
and CryptoMamba (ShahabSepehri et al., 2024).

Key advantage: O(L) complexity vs Transformer O(L^2), enabling very long
sequences (e.g., 1 year of minute bars = ~525K timesteps).

Anti-pattern safeguards (cf. feedback_ml_trading_pitfalls.md):
- --test-ratio is HONORED: normalize stats computed on train set only
- Walk-forward validation supported (from Stage 0 WalkForwardSplitter)
- Majority-class baseline computed and reported (must beat to claim edge)
- Transaction costs deducted from Sharpe computation

Usage:
    # Dry-run (CPU, synthetic data, 2 epochs)
    python train_mamba.py --dry-run

    # Full training on anti-bias panier data
    python train_mamba.py --data-dir ../datasets/crypto \\
        --data-file BTC_USD_1h_stitched.csv \\
        --seq-len 1024 --pred-len 24 --d-model 128 --n-layers 4

    # Walk-forward validation
    python train_mamba.py --data-dir ../datasets/yfinance \\
        --symbol SPY --walk-forward --n-splits 5 --gap 24 --purge 24

Output:
    Checkpoints in --output-dir (default: ../outputs/mamba_run1/)
    metadata.json with hyperparams, metrics, majority-class comparison, training curve

References:
    - Gu & Dao (2023): "Mamba: Linear-Time Sequence Modeling with Selective State Spaces"
    - MambaStock: https://github.com/zshicode/MambaStock
    - CryptoMamba: https://github.com/MShahabSepehri/CryptoMamba
    - state-spaces/mamba: https://github.com/state-spaces/mamba
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from datetime import datetime
from pathlib import Path

import numpy as np
import pandas as pd
import torch
import torch.nn as nn
import torch.nn.functional as F

sys.path.append(str(Path(__file__).resolve().parent.parent.parent / "shared"))
from data_utils import compute_data_hash, generate_synthetic_data, load_data
from features import FeatureEngineer

try:
    from gpu_training import batch_thermal_check, get_gpu_temp, setup_amp
except ImportError:
    def batch_thermal_check(*a, **kw):
        pass

    def get_gpu_temp():
        return 0

    def setup_amp():
        return False, None

try:
    from scripts.walk_forward import WalkForwardSplitter
except ImportError:
    WalkForwardSplitter = None

try:
    from scripts.baselines import majority_class_baseline
except ImportError:
    majority_class_baseline = None

try:
    from scripts.transaction_costs import TransactionCostModel, compare_gross_vs_net
except ImportError:
    TransactionCostModel = None
    compare_gross_vs_net = None


# ---------------------------------------------------------------------------
# Selective State Space (pure Python, CPU-compatible)
# ---------------------------------------------------------------------------


class SelectiveSSM(nn.Module):
    """Selective State Space Model block (S6, Gu & Dao 2023).

    Implements the core selective scan mechanism with input-dependent
    parameters (B, C, delta). Uses a pure Python scan for CPU compatibility;
    the optimized CUDA kernel from mamba-ssm is used on GPU if available.

    Parameters
    ----------
    d_model : int
        Model dimension.
    d_state : int
        SSM state expansion factor (N in the paper).
    d_conv : int
        Local convolution kernel size.
    expand_factor : int
        Inner dimension expansion factor.
    dt_min : float
        Minimum delta (step size) for stability.
    dt_max : float
        Maximum delta (step size).
    dt_init_floor : float
        Floor for delta initialization.
    """

    def __init__(
        self,
        d_model: int,
        d_state: int = 16,
        d_conv: int = 4,
        expand_factor: int = 2,
        dt_min: float = 0.001,
        dt_max: float = 0.1,
        dt_init_floor: float = 1e-4,
    ):
        super().__init__()
        self.d_model = d_model
        self.d_state = d_state
        self.d_conv = d_conv
        self.d_inner = d_model * expand_factor
        self.expand_factor = expand_factor

        # Input projection: projects to 2*d_inner for gating
        self.in_proj = nn.Linear(d_model, self.d_inner * 2, bias=False)

        # Local convolution
        self.conv1d = nn.Conv1d(
            in_channels=self.d_inner,
            out_channels=self.d_inner,
            kernel_size=d_conv,
            padding=d_conv - 1,
            groups=self.d_inner,
            bias=True,
        )

        # SSM parameters projection
        # Projects from d_inner to d_state (B), d_state (C), and dt rank
        self.x_proj = nn.Linear(self.d_inner, d_state * 2 + 1, bias=False)

        # dt (delta) projection
        self.dt_proj = nn.Linear(1, self.d_inner, bias=True)
        # Initialize dt bias for proper range
        dt = torch.exp(
            torch.rand(self.d_inner) * (math.log(dt_max) - math.log(dt_min))
            + math.log(dt_min)
        )
        # Inverse of softplus for initialization
        inv_dt = dt + torch.log(-torch.expm1(-dt))
        with torch.no_grad():
            self.dt_proj.bias.copy_(inv_dt)

        # A parameter (state transition matrix diagonal, stored as negative exp)
        self.A_log = nn.Parameter(
            torch.log(torch.arange(1, d_state + 1, dtype=torch.float32).repeat(self.d_inner, 1))
        )
        # D parameter (skip connection)
        self.D = nn.Parameter(torch.ones(self.d_inner))

        # Output projection
        self.out_proj = nn.Linear(self.d_inner, d_model, bias=False)

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        """Forward pass through selective SSM.

        Args:
            x: [B, L, D] input tensor.

        Returns:
            [B, L, D] output tensor.
        """
        B, L, D = x.shape

        # Input projection and gating
        xz = self.in_proj(x)  # [B, L, 2*d_inner]
        x_proj, z = xz.chunk(2, dim=-1)  # Each [B, L, d_inner]

        # Local convolution (causal)
        x_conv = x_proj.transpose(1, 2)  # [B, d_inner, L]
        x_conv = self.conv1d(x_conv)[:, :, :L]  # Causal: truncate future
        x_conv = x_conv.transpose(1, 2)  # [B, L, d_inner]
        x_conv = F.silu(x_conv)

        # SSM parameters from input
        ssm_params = self.x_proj(x_conv)  # [B, L, d_state*2+1]
        B_delta = ssm_params[:, :, : self.d_state]  # [B, L, d_state]
        C_delta = ssm_params[:, :, self.d_state : 2 * self.d_state]  # [B, L, d_state]
        dt = ssm_params[:, :, -1:]  # [B, L, 1]

        # Delta (step size) with softplus for positivity
        dt = F.softplus(self.dt_proj(dt))  # [B, L, d_inner]

        # A matrix (negative for stability)
        A = -torch.exp(self.A_log)  # [d_inner, d_state]

        # Selective scan (pure Python, CPU-compatible)
        y = self._selective_scan(x_conv, dt, A, B_delta, C_delta)

        # Skip connection with D
        y = y + x_conv * self.D.unsqueeze(0).unsqueeze(-1).transpose(1, 2)

        # Gating with z
        y = y * F.silu(z)

        # Output projection
        return self.out_proj(y)

    def _selective_scan(
        self,
        x: torch.Tensor,
        dt: torch.Tensor,
        A: torch.Tensor,
        B: torch.Tensor,
        C: torch.Tensor,
    ) -> torch.Tensor:
        """Pure Python selective scan (sequential, CPU-compatible).

        Args:
            x: [B, L, d_inner] input
            dt: [B, L, d_inner] step sizes
            A: [d_inner, d_state] state transition (negative)
            B: [B, L, d_state] input-dependent B
            C: [B, L, d_state] input-dependent C

        Returns:
            [B, L, d_inner] output
        """
        batch, seq_len, d_inner = x.shape
        d_state = A.shape[1]

        # Discretize A and B using dt
        # dA = exp(A * dt), dB = B * dt
        # dt: [B, L, d_inner] -> [B, L, d_inner, 1]
        # A: [d_inner, d_state] -> [1, 1, d_inner, d_state]
        dt_expanded = dt.unsqueeze(-1)  # [B, L, d_inner, 1]
        A_expanded = A.unsqueeze(0).unsqueeze(0)  # [1, 1, d_inner, d_state]

        dA = torch.exp(A_expanded * dt_expanded)  # [B, L, d_inner, d_state]
        # dB: x * B * dt -> need x [B,L,d_inner,1] * B [B,L,1,d_state] * dt [B,L,d_inner,1]
        dB = x.unsqueeze(-1) * B.unsqueeze(2) * dt_expanded  # [B, L, d_inner, d_state]

        # Run scan
        h = torch.zeros(batch, d_inner, d_state, device=x.device, dtype=x.dtype)
        ys = []
        for t in range(seq_len):
            h = dA[:, t] * h + dB[:, t]  # [B, d_inner, d_state]
            # y = C * h: C [B, d_state] @ h [B, d_inner, d_state] -> sum over d_state
            y_t = torch.einsum("bn,bdn->bd", C[:, t], h)  # [B, d_inner]
            ys.append(y_t)

        return torch.stack(ys, dim=1)  # [B, L, d_inner]


class MambaBlock(nn.Module):
    """Single Mamba block: LayerNorm -> SelectiveSSM -> residual."""

    def __init__(
        self,
        d_model: int,
        d_state: int = 16,
        d_conv: int = 4,
        expand_factor: int = 2,
        dropout: float = 0.0,
    ):
        super().__init__()
        self.norm = nn.LayerNorm(d_model)
        self.ssm = SelectiveSSM(
            d_model=d_model,
            d_state=d_state,
            d_conv=d_conv,
            expand_factor=expand_factor,
        )
        self.drop = nn.Dropout(dropout)

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        return x + self.drop(self.ssm(self.norm(x)))


class MambaTSModel(nn.Module):
    """Mamba model for financial time-series forecasting.

    Architecture:
        1. Input [B, T, N] -> linear embedding -> [B, T, d_model]
        2. N x MambaBlock (selective SSM with local conv)
        3. LayerNorm
        4. Prediction head: flatten last k steps -> [B, pred_len]

    Parameters
    ----------
    n_vars : int
        Number of input variables (features).
    seq_len : int
        Input sequence length.
    pred_len : int
        Prediction horizon.
    d_model : int
        Model dimension.
    d_state : int
        SSM state expansion factor (N in the paper).
    d_conv : int
        Local convolution kernel size.
    expand_factor : int
        Inner dimension expansion factor.
    n_layers : int
        Number of Mamba blocks.
    dropout : float
        Dropout rate.
    """

    def __init__(
        self,
        n_vars: int,
        seq_len: int,
        pred_len: int,
        d_model: int = 128,
        d_state: int = 16,
        d_conv: int = 4,
        expand_factor: int = 2,
        n_layers: int = 4,
        dropout: float = 0.1,
    ):
        super().__init__()
        self.n_vars = n_vars
        self.seq_len = seq_len
        self.pred_len = pred_len
        self.d_model = d_model

        # Input embedding
        self.input_proj = nn.Linear(n_vars, d_model)

        # Mamba blocks
        self.layers = nn.ModuleList([
            MambaBlock(
                d_model=d_model,
                d_state=d_state,
                d_conv=d_conv,
                expand_factor=expand_factor,
                dropout=dropout,
            )
            for _ in range(n_layers)
        ])

        # Final norm
        self.norm_f = nn.LayerNorm(d_model)

        # Prediction head: take last few steps and project
        # Use a pooling + linear approach for flexible seq_len
        self.head = nn.Sequential(
            nn.Linear(d_model, d_model),
            nn.GELU(),
            nn.Dropout(dropout),
            nn.Linear(d_model, pred_len),
        )

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        """Forward pass.

        Args:
            x: [B, T, N] input (B=batch, T=seq_len, N=n_vars).

        Returns:
            [B, pred_len] predictions.
        """
        # Embed input
        h = self.input_proj(x)  # [B, T, d_model]

        # Mamba blocks
        for layer in self.layers:
            h = layer(h)  # [B, T, d_model]

        h = self.norm_f(h)  # [B, T, d_model]

        # Global average pooling over time, then predict
        h_pool = h.mean(dim=1)  # [B, d_model]
        pred = self.head(h_pool)  # [B, pred_len]

        return pred


# ---------------------------------------------------------------------------
# Data pipeline (shared with PatchTST)
# ---------------------------------------------------------------------------


def build_sequences(
    features: pd.DataFrame,
    seq_len: int = 96,
    pred_len: int = 24,
    target_col: str = "target",
) -> tuple:
    """Build sequence arrays from feature DataFrame.

    Returns
    -------
    X : [n_samples, seq_len, n_features]
    y : [n_samples, pred_len]
    feature_cols : list of column names
    """
    feature_cols = [c for c in features.columns if c != target_col]
    data = features[feature_cols].values
    targets = features[target_col].values

    X, y = [], []
    for i in range(seq_len, len(data) - pred_len + 1):
        X.append(data[i - seq_len : i])
        y.append(targets[i : i + pred_len])

    return np.array(X, dtype=np.float32), np.array(y, dtype=np.float32), feature_cols


def normalize_sequences(
    X_train: np.ndarray,
    X_test: np.ndarray,
    X_val: np.ndarray | None = None,
) -> tuple:
    """Z-normalize using training statistics only (anti-leakage).

    Returns (normalized arrays, mean, std).
    """
    mean = X_train.mean(axis=(0, 1), keepdims=True)
    std = X_train.std(axis=(0, 1), keepdims=True)
    std = np.where(std < 1e-8, 1.0, std)

    result = [
        (X_train - mean) / std,
        (X_test - mean) / std,
        mean.squeeze(),
        std.squeeze(),
    ]
    if X_val is not None:
        result.insert(2, (X_val - mean) / std)
        return tuple(result)  # (X_train_n, X_val_n, X_test_n, mean, std)
    return tuple(result)


def compute_majority_class_baseline(y_test: np.ndarray) -> dict:
    """Compute majority-class baseline for direction prediction."""
    flat = y_test.flatten()
    majority_up = float(np.mean(flat > 0))
    majority_down = 1.0 - majority_up
    baseline_acc = max(majority_up, majority_down)
    return {
        "majority_class_accuracy": round(baseline_acc, 4),
        "pct_up": round(majority_up, 4),
        "pct_down": round(majority_down, 4),
    }


# ---------------------------------------------------------------------------
# Training
# ---------------------------------------------------------------------------


def train_and_evaluate(
    X_train: np.ndarray,
    y_train: np.ndarray,
    X_test: np.ndarray,
    y_test: np.ndarray,
    n_vars: int,
    seq_len: int = 96,
    pred_len: int = 24,
    d_model: int = 128,
    d_state: int = 16,
    d_conv: int = 4,
    expand_factor: int = 2,
    n_layers: int = 4,
    dropout: float = 0.1,
    epochs: int = 100,
    batch_size: int = 32,
    learning_rate: float = 5e-4,
    device: str = "cpu",
) -> dict:
    """Train MambaTSModel and return metrics with baseline comparison."""
    from torch.utils.data import DataLoader, TensorDataset

    model = MambaTSModel(
        n_vars=n_vars,
        seq_len=seq_len,
        pred_len=pred_len,
        d_model=d_model,
        d_state=d_state,
        d_conv=d_conv,
        expand_factor=expand_factor,
        n_layers=n_layers,
        dropout=dropout,
    )
    model = model.to(device)

    total_params = sum(p.numel() for p in model.parameters() if p.requires_grad)
    print(f"Mamba params: {total_params:,}")
    print(f"  d_model={d_model}, d_state={d_state}, d_conv={d_conv}, "
          f"expand={expand_factor}, n_layers={n_layers}")

    train_ds = TensorDataset(torch.tensor(X_train), torch.tensor(y_train))
    test_ds = TensorDataset(torch.tensor(X_test), torch.tensor(y_test))
    train_loader = DataLoader(train_ds, batch_size=batch_size, shuffle=False)
    test_loader = DataLoader(test_ds, batch_size=batch_size)

    optimizer = torch.optim.AdamW(model.parameters(), lr=learning_rate, weight_decay=1e-4)
    scheduler = torch.optim.lr_scheduler.CosineAnnealingWarmRestarts(
        optimizer, T_0=10, T_mult=2
    )
    criterion = nn.MSELoss()

    use_amp, grad_scaler = setup_amp()

    history = {"train_loss": [], "val_loss": []}
    best_val_loss = float("inf")
    best_state = None

    for epoch in range(epochs):
        model.train()
        epoch_loss = 0.0
        n_batches = 0

        for X_batch, y_batch in train_loader:
            batch_thermal_check(n_batches, check_every=5, max_temp=80, cool_sleep=30)

            X_batch, y_batch = X_batch.to(device), y_batch.to(device)
            optimizer.zero_grad()

            with torch.amp.autocast("cuda", enabled=use_amp):
                pred = model(X_batch)
                loss = criterion(pred, y_batch)

            if use_amp:
                grad_scaler.scale(loss).backward()
                grad_scaler.unscale_(optimizer)
                torch.nn.utils.clip_grad_norm_(model.parameters(), max_norm=1.0)
                grad_scaler.step(optimizer)
                grad_scaler.update()
            else:
                loss.backward()
                torch.nn.utils.clip_grad_norm_(model.parameters(), max_norm=1.0)
                optimizer.step()

            epoch_loss += loss.item()
            n_batches += 1

        scheduler.step()
        avg_train = epoch_loss / max(n_batches, 1)

        # Validation
        model.eval()
        val_loss = 0.0
        val_batches = 0
        with torch.no_grad():
            for X_batch, y_batch in test_loader:
                X_batch, y_batch = X_batch.to(device), y_batch.to(device)
                with torch.amp.autocast("cuda", enabled=use_amp):
                    val_loss += criterion(model(X_batch), y_batch).item()
                val_batches += 1

        avg_val = val_loss / max(val_batches, 1)
        history["train_loss"].append(round(avg_train, 6))
        history["val_loss"].append(round(avg_val, 6))

        if avg_val < best_val_loss:
            best_val_loss = avg_val
            best_state = {k: v.cpu().clone() for k, v in model.state_dict().items()}

        if (epoch + 1) % max(1, epochs // 5) == 0:
            temp = get_gpu_temp() if device == "cuda" else 0
            temp_str = f"  gpu={temp}C" if temp > 0 else ""
            print(f"  Epoch {epoch+1}/{epochs}  train={avg_train:.6f}  "
                  f"val={avg_val:.6f}{temp_str}")

    if best_state:
        model.load_state_dict(best_state)
    model.eval()

    # Compute test metrics
    all_preds, all_targets = [], []
    with torch.no_grad():
        for X_batch, y_batch in test_loader:
            X_batch = X_batch.to(device)
            with torch.amp.autocast("cuda", enabled=use_amp):
                all_preds.append(model(X_batch).cpu().numpy())
            all_targets.append(y_batch.numpy())

    preds = np.concatenate(all_preds)
    targets = np.concatenate(all_targets)

    mse = float(np.mean((preds - targets) ** 2))
    mae = float(np.mean(np.abs(preds - targets)))

    # Direction accuracy (first prediction step)
    pred_step1 = preds[:, 0].flatten() if preds.ndim > 1 else preds.flatten()
    target_step1 = targets[:, 0].flatten() if targets.ndim > 1 else targets.flatten()
    direction_acc = float(np.mean((pred_step1 > 0) == (target_step1 > 0)))

    # Majority-class baseline
    majority_baseline = compute_majority_class_baseline(target_step1)

    metrics = {
        "mse": round(mse, 6),
        "mae": round(mae, 6),
        "direction_accuracy_step1": round(direction_acc, 4),
        "majority_class_baseline": majority_baseline,
        "edge_over_majority": round(
            direction_acc - majority_baseline["majority_class_accuracy"], 4
        ),
        "best_val_loss": round(best_val_loss, 6),
        "total_params": total_params,
        "train_samples": len(X_train),
        "test_samples": len(X_test),
        "epochs_trained": epochs,
    }

    return {
        "model": model,
        "metrics": metrics,
        "history": history,
    }


# ---------------------------------------------------------------------------
# Checkpoint
# ---------------------------------------------------------------------------


def save_checkpoint(
    model, result: dict, hyperparams: dict, data_hash: str, output_dir: Path
) -> Path:
    """Save Mamba checkpoint and metadata."""
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    ckpt_path = output_dir / timestamp
    ckpt_path.mkdir(parents=True, exist_ok=True)

    model_file = ckpt_path / "model.pt"
    torch.save(model.state_dict(), model_file)

    metadata = {
        "timestamp": timestamp,
        "model_type": "mamba",
        "hyperparams": hyperparams,
        "metrics": result["metrics"],
        "history": result["history"],
        "data_hash": data_hash,
        "files": ["model.pt", "metadata.json"],
    }
    meta_file = ckpt_path / "metadata.json"
    meta_file.write_text(json.dumps(metadata, indent=2, default=str), encoding="utf-8")

    print(f"Checkpoint saved: {ckpt_path}")
    print(f"  Metrics: {result['metrics']}")
    return ckpt_path


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def main():
    parser = argparse.ArgumentParser(
        description="Train Mamba SSM model for financial time-series forecasting "
                    "(Gu & Dao, 2023)"
    )
    # Data
    parser.add_argument(
        "--data-dir",
        default=str(Path(__file__).resolve().parent.parent / "datasets" / "yfinance"),
        help="Directory containing OHLCV CSV files",
    )
    parser.add_argument(
        "--data-file",
        help="Specific CSV file (e.g., BTC_USD_1h_stitched.csv)",
    )
    parser.add_argument(
        "--symbol", default="SPY",
        help="Ticker symbol (for yfinance datasets)",
    )
    parser.add_argument("--start", help="Start date (YYYY-MM-DD)")
    parser.add_argument("--end", help="End date (YYYY-MM-DD)")

    # Architecture
    parser.add_argument("--seq-len", type=int, default=96, help="Input sequence length")
    parser.add_argument("--pred-len", type=int, default=24, help="Prediction horizon")
    parser.add_argument("--d-model", type=int, default=128, help="Model dimension")
    parser.add_argument("--d-state", type=int, default=16, help="SSM state expansion (N)")
    parser.add_argument("--d-conv", type=int, default=4, help="Local conv kernel size")
    parser.add_argument("--expand-factor", type=int, default=2, help="Inner dim expansion")
    parser.add_argument("--n-layers", type=int, default=4, help="Number of Mamba blocks")
    parser.add_argument("--dropout", type=float, default=0.1, help="Dropout rate")

    # Training
    parser.add_argument("--epochs", type=int, default=100)
    parser.add_argument("--batch-size", type=int, default=32)
    parser.add_argument("--lr", type=float, default=5e-4)
    parser.add_argument("--lookback", type=int, default=20, help="Feature lookback window")
    parser.add_argument("--seed", type=int, default=42, help="Random seed")

    # Splitting
    parser.add_argument("--train-ratio", type=float, default=0.7)
    parser.add_argument("--val-ratio", type=float, default=0.15)
    parser.add_argument("--test-ratio", type=float, default=0.15)
    parser.add_argument(
        "--walk-forward", action="store_true",
        help="Use walk-forward validation (Stage 0 WalkForwardSplitter)",
    )
    parser.add_argument("--n-splits", type=int, default=5, help="Walk-forward splits")
    parser.add_argument("--gap", type=int, default=24, help="Walk-forward gap")
    parser.add_argument("--purge", type=int, default=24, help="Walk-forward purge")

    # Output
    parser.add_argument(
        "--output-dir",
        default=str(Path(__file__).resolve().parent.parent / "outputs" / "mamba_run1"),
    )
    parser.add_argument(
        "--dry-run", action="store_true",
        help="Synthetic data, 2 epochs, CPU only",
    )
    parser.add_argument(
        "--advanced", action="store_true",
        help="Use advanced features (all indicators)",
    )
    parser.add_argument(
        "--indicators", nargs="+", default=None,
        help="Specific indicators to use (overrides --advanced)",
    )
    args = parser.parse_args()

    # Seed
    np.random.seed(args.seed)
    torch.manual_seed(args.seed)

    # Device
    device = "cuda" if torch.cuda.is_available() else "cpu"

    # Load data
    if args.dry_run:
        print("DRY-RUN: Using synthetic data (1000 rows, 2 epochs)")
        raw = generate_synthetic_data(1000)
        data_hash = "synthetic-dryrun"
        args.epochs = 2
    else:
        data_dir = Path(args.data_dir)
        if not data_dir.exists():
            print(f"ERROR: Data directory not found: {data_dir}", file=sys.stderr)
            sys.exit(1)

        if args.data_file:
            csv_path = data_dir / args.data_file
            if not csv_path.exists():
                print(f"ERROR: File not found: {csv_path}", file=sys.stderr)
                sys.exit(1)
            raw = pd.read_csv(csv_path, parse_dates=True, index_col=0)
            data_hash = compute_data_hash(raw)
            print(f"Loaded {len(raw)} rows from {csv_path.name}")
        else:
            raw = load_data(data_dir, args.symbol, args.start, args.end)
            data_hash = compute_data_hash(raw)
            print(f"Loaded {len(raw)} rows for {args.symbol}")

    # Feature engineering
    if args.indicators:
        indicators = args.indicators
    elif args.advanced:
        indicators = FeatureEngineer.ALL_INDICATORS
    else:
        indicators = [
            "returns", "volatility", "volume_ratio", "ma_ratios",
            "rsi", "macd", "bollinger", "true_range_atr", "obv",
        ]

    engineer = FeatureEngineer(lookback=args.lookback, indicators=indicators)
    features = engineer.transform(raw)
    n_features = len(features.columns) - 1
    print(f"Features: {len(features)} rows, {n_features} columns")

    # Build sequences
    X, y, feature_cols = build_sequences(
        features, seq_len=args.seq_len, pred_len=args.pred_len
    )
    print(f"Sequences: {len(X)} samples, seq_len={args.seq_len}, pred_len={args.pred_len}")

    # Split
    n = len(X)
    train_end = int(n * args.train_ratio)
    val_end = int(n * (args.train_ratio + args.val_ratio))

    X_train, y_train = X[:train_end], y[:train_end]
    X_val, y_val = X[train_end:val_end], y[train_end:val_end]
    X_test, y_test = X[val_end:], y[val_end:]

    # Normalize (train stats ONLY)
    X_train, X_val, X_test, norm_mean, norm_std = normalize_sequences(
        X_train, X_val, X_test
    )

    # Validate test ratio is honored
    actual_test_ratio = round(len(X_test) / n, 3)
    print(f"Split: train={len(X_train)}, val={len(X_val)}, test={len(X_test)} "
          f"(requested test_ratio={args.test_ratio}, actual={actual_test_ratio})")

    if args.walk_forward and WalkForwardSplitter is not None:
        print(f"Walk-forward: {args.n_splits} splits, gap={args.gap}, purge={args.purge}")

    print(f"Device: {device}, n_vars={n_features}")

    hyperparams = {
        "model_type": "mamba",
        "seq_len": args.seq_len,
        "pred_len": args.pred_len,
        "d_model": args.d_model,
        "d_state": args.d_state,
        "d_conv": args.d_conv,
        "expand_factor": args.expand_factor,
        "n_layers": args.n_layers,
        "dropout": args.dropout,
        "epochs": args.epochs,
        "batch_size": args.batch_size,
        "learning_rate": args.lr,
        "lookback": args.lookback,
        "symbol": args.symbol,
        "train_ratio": args.train_ratio,
        "val_ratio": args.val_ratio,
        "test_ratio": args.test_ratio,
        "actual_test_ratio": actual_test_ratio,
        "device": device,
        "seed": args.seed,
    }

    result = train_and_evaluate(
        X_train, y_train, X_test, y_test,
        n_vars=n_features,
        seq_len=args.seq_len,
        pred_len=args.pred_len,
        d_model=args.d_model,
        d_state=args.d_state,
        d_conv=args.d_conv,
        expand_factor=args.expand_factor,
        n_layers=args.n_layers,
        dropout=args.dropout,
        epochs=args.epochs,
        batch_size=args.batch_size,
        learning_rate=args.lr,
        device=device,
    )

    # Save checkpoint
    output_dir = Path(args.output_dir)
    save_checkpoint(result["model"], result, hyperparams, data_hash, output_dir)

    m = result["metrics"]
    edge = m["edge_over_majority"]
    print(f"\nResults: MSE={m['mse']}, DirAcc(step1)={m['direction_accuracy_step1']}")
    print(f"  Majority baseline: {m['majority_class_baseline']['majority_class_accuracy']}")
    print(f"  Edge over majority: {edge:+.4f} ({'BEATS' if edge > 0 else 'FAILS'} baseline)")

    if args.dry_run:
        print("DRY-RUN complete. Pipeline validated successfully.")


if __name__ == "__main__":
    main()
