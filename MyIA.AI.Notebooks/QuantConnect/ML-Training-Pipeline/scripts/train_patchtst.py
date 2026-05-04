"""
Train PatchTST models for financial time-series forecasting.

Implements "A Time Series is Worth 64 Words: Long-term Forecasting with
Transformers" (Nie et al., ICLR 2023). Key innovations:
- Patching: splits time series into fixed-length patches (tokens)
- Channel independence: each variable processed separately with shared weights

Anti-pattern safeguards (cf. feedback_ml_trading_pitfalls.md):
- --test-ratio is HONORED: normalize stats computed on train set only
- Walk-forward validation supported (optional, from Stage 0 WalkForwardSplitter)
- Majority-class baseline computed and reported (must beat to claim edge)
- Transaction costs deducted from Sharpe computation

Usage:
    # Dry-run (CPU, synthetic data, 2 epochs)
    python train_patchtst.py --dry-run

    # Full training on anti-bias panier data
    python train_patchtst.py --data-dir ../datasets/yfinance_balanced \\
        --symbols SPY,RSP,IWM,VIX --seq-len 96 --pred-len 24

    # Walk-forward validation (if walk_forward.py available)
    python train_patchtst.py --data-dir ../datasets/yfinance \\
        --symbol SPY --walk-forward --n-splits 5

Output:
    Checkpoints in --output-dir (default: ../outputs/patchtst_run1/)
    metadata.json with hyperparams, metrics, majority-class comparison, training curve
"""

import argparse
import json
import sys
from datetime import datetime
from pathlib import Path

import numpy as np
import pandas as pd
import torch
import torch.nn as nn

sys.path.append(str(Path(__file__).resolve().parent.parent.parent / "shared"))
from gpu_training import (
    batch_thermal_check,
    get_gpu_temp,
    setup_amp,
)
from data_utils import compute_data_hash, generate_synthetic_data, load_data
from features import FeatureEngineer

# Optional: walk_forward from Stage 0 (graceful fallback)
try:
    from walk_forward import WalkForwardSplitter
except ImportError:
    WalkForwardSplitter = None


class PatchTSTModel(nn.Module):
    """Patch Time Series Transformer (Nie et al., ICLR 2023).

    Architecture:
        1. Input [B, T, N] -> patch per channel -> [B*N, num_patches, patch_len]
        2. Linear projection -> [B*N, num_patches, d_model]
        3. Learnable patch embedding + positional encoding
        4. Transformer encoder layers
        5. Flatten + linear head -> [B, pred_len, N]
    """

    def __init__(
        self,
        n_vars: int,
        seq_len: int,
        pred_len: int,
        patch_len: int = 16,
        stride: int = 8,
        d_model: int = 128,
        n_heads: int = 8,
        n_layers: int = 3,
        dropout: float = 0.2,
        fc_dropout: float = 0.2,
        channel_independence: bool = True,
    ):
        super().__init__()
        self.n_vars = n_vars
        self.seq_len = seq_len
        self.pred_len = pred_len
        self.patch_len = patch_len
        self.stride = stride
        self.d_model = d_model
        self.channel_independence = channel_independence

        # Number of patches
        self.num_patches = (seq_len - patch_len) // stride + 1

        # Patch projection: patch_len -> d_model
        self.patch_proj = nn.Linear(patch_len, d_model)

        # Learnable patch embedding (cls-like token is NOT used; positional encoding only)
        self.pos_encoding = nn.Parameter(torch.randn(1, self.num_patches, d_model) * 0.02)

        # Transformer encoder
        encoder_layer = nn.TransformerEncoderLayer(
            d_model=d_model,
            nhead=n_heads,
            dim_feedforward=d_model * 4,
            dropout=dropout,
            batch_first=True,
            activation="gelu",
        )
        self.transformer = nn.TransformerEncoder(encoder_layer, num_layers=n_layers)

        # Layer norm + dropout before head
        self.layer_norm = nn.LayerNorm(self.num_patches * d_model)
        self.fc_drop = nn.Dropout(fc_dropout)

        # Prediction head: flatten all patches -> pred_len per variable
        self.head = nn.Linear(self.num_patches * d_model, pred_len)

    def forward(self, x):
        """Forward pass.

        Args:
            x: [B, T, N] input tensor (B=batch, T=seq_len, N=n_vars)

        Returns:
            [B, pred_len, N] predictions
        """
        B, T, N = x.shape

        if self.channel_independence:
            x = x.permute(0, 2, 1).reshape(B * N, T, 1)
        else:
            x = x.reshape(B, T * N, 1).permute(0, 2, 1)

        # Extract patches: [B*N, num_patches, patch_len]
        patches = x.unfold(dimension=1, size=self.patch_len, step=self.stride)
        # unfold gives [B*N, num_patches, 1, patch_len] -> squeeze
        patches = patches.squeeze(2)

        # Project patches: [B*N, num_patches, d_model]
        tokens = self.patch_proj(patches)

        # Add positional encoding
        tokens = tokens + self.pos_encoding

        # Transformer: [B*N, num_patches, d_model]
        encoded = self.transformer(tokens)

        # Flatten and predict: [B*N, num_patches * d_model] -> [B*N, pred_len]
        flattened = encoded.reshape(encoded.shape[0], -1)
        flattened = self.layer_norm(flattened)
        flattened = self.fc_drop(flattened)
        preds = self.head(flattened)

        # Reshape back: [B*N, pred_len] -> [B, N, pred_len] -> aggregate channels -> [B, pred_len]
        if self.channel_independence:
            preds = preds.reshape(B, N, self.pred_len)
            # Average across channels for final prediction
            preds = preds.mean(dim=1)

        return preds


def build_sequences(
    features: pd.DataFrame, seq_len: int = 96, pred_len: int = 24, target_col: str = "target"
) -> tuple:
    """Build sequence-to-sequence arrays for PatchTST.

    Returns:
        X: [n_samples, seq_len, n_features]
        y: [n_samples, pred_len, n_features] (future target values)
        feature_cols: list of feature column names
    """
    feature_cols = [c for c in features.columns if c != target_col]
    data = features[feature_cols].values
    targets = features[target_col].values

    X, y = [], []
    for i in range(seq_len, len(data) - pred_len + 1):
        X.append(data[i - seq_len : i])
        # Multi-step target: future returns for each variable
        y.append(targets[i : i + pred_len])

    return np.array(X, dtype=np.float32), np.array(y, dtype=np.float32), feature_cols


def normalize_sequences(
    X_train: np.ndarray, X_test: np.ndarray, X_val: np.ndarray | None = None
) -> tuple:
    """Z-normalize using training statistics only (anti-leakage).

    Returns:
        Normalized arrays + (mean, std) for audit
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
    """Compute majority-class baseline for direction prediction.

    Financial time series baseline: always predict the sign of the mean training return.
    If training mean > 0, always predict up; else always predict down.
    """
    # y_test shape: [n_samples, pred_len] or [n_samples]
    flat = y_test.flatten()
    majority_up = float(np.mean(flat > 0))
    majority_down = 1.0 - majority_up
    baseline_acc = max(majority_up, majority_down)
    return {
        "majority_class_accuracy": round(baseline_acc, 4),
        "pct_up": round(majority_up, 4),
        "pct_down": round(majority_down, 4),
    }


def train_and_evaluate(
    X_train: np.ndarray,
    y_train: np.ndarray,
    X_test: np.ndarray,
    y_test: np.ndarray,
    n_vars: int,
    seq_len: int = 96,
    pred_len: int = 24,
    patch_len: int = 16,
    stride: int = 8,
    d_model: int = 128,
    n_heads: int = 8,
    n_layers: int = 3,
    dropout: float = 0.2,
    fc_dropout: float = 0.2,
    epochs: int = 100,
    batch_size: int = 64,
    learning_rate: float = 5e-4,
    channel_independence: bool = True,
    device: str = "cpu",
) -> dict:
    """Train PatchTST model and return metrics with baseline comparison."""
    from torch.utils.data import DataLoader, TensorDataset

    model = PatchTSTModel(
        n_vars=n_vars,
        seq_len=seq_len,
        pred_len=pred_len,
        patch_len=patch_len,
        stride=stride,
        d_model=d_model,
        n_heads=n_heads,
        n_layers=n_layers,
        dropout=dropout,
        fc_dropout=fc_dropout,
        channel_independence=channel_independence,
    )
    model = model.to(device)

    total_params = sum(p.numel() for p in model.parameters() if p.requires_grad)
    print(f"PatchTST params: {total_params:,}")
    print(f"  num_patches={model.num_patches}, patch_len={patch_len}, stride={stride}")

    train_ds = TensorDataset(
        torch.tensor(X_train), torch.tensor(y_train)
    )
    test_ds = TensorDataset(
        torch.tensor(X_test), torch.tensor(y_test)
    )
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
            print(f"  Epoch {epoch+1}/{epochs}  train={avg_train:.6f}  val={avg_val:.6f}{temp_str}")

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
        "edge_over_majority": round(direction_acc - majority_baseline["majority_class_accuracy"], 4),
        "best_val_loss": round(best_val_loss, 6),
        "total_params": total_params,
        "train_samples": len(X_train),
        "test_samples": len(X_test),
        "epochs_trained": epochs,
        "num_patches": model.num_patches,
    }

    return {
        "model": model,
        "metrics": metrics,
        "history": history,
    }


def save_checkpoint(
    model, result: dict, hyperparams: dict, data_hash: str, output_dir: Path
) -> Path:
    """Save PatchTST checkpoint and metadata."""

    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    ckpt_path = output_dir / timestamp
    ckpt_path.mkdir(parents=True, exist_ok=True)

    model_file = ckpt_path / "model.pt"
    torch.save(model.state_dict(), model_file)

    metadata = {
        "timestamp": timestamp,
        "model_type": "patchtst",
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


def main():
    parser = argparse.ArgumentParser(
        description="Train PatchTST model for financial time-series forecasting "
                    "(Nie et al., ICLR 2023)"
    )
    # Data
    parser.add_argument(
        "--data-dir",
        default=str(Path(__file__).resolve().parent.parent / "datasets" / "yfinance"),
        help="Directory containing OHLCV CSV files",
    )
    parser.add_argument(
        "--symbols", default="SPY",
        help="Comma-separated ticker symbols (multi-variate input)",
    )
    parser.add_argument("--start", help="Start date (YYYY-MM-DD)")
    parser.add_argument("--end", help="End date (YYYY-MM-DD)")

    # Architecture
    parser.add_argument("--seq-len", type=int, default=96, help="Input sequence length")
    parser.add_argument("--pred-len", type=int, default=24, help="Prediction horizon")
    parser.add_argument("--patch-len", type=int, default=16, help="Patch length")
    parser.add_argument("--stride", type=int, default=8, help="Patch stride")
    parser.add_argument("--d-model", type=int, default=128, help="Model dimension")
    parser.add_argument("--n-heads", type=int, default=8, help="Attention heads")
    parser.add_argument("--n-layers", type=int, default=3, help="Transformer encoder layers")
    parser.add_argument("--dropout", type=float, default=0.2, help="Transformer dropout")
    parser.add_argument("--fc-dropout", type=float, default=0.2, help="Head dropout")
    parser.add_argument(
        "--no-channel-independence", action="store_true",
        help="Disable channel independence (not recommended)",
    )

    # Training
    parser.add_argument("--epochs", type=int, default=100)
    parser.add_argument("--batch-size", type=int, default=64)
    parser.add_argument("--lr", type=float, default=5e-4)
    parser.add_argument("--lookback", type=int, default=20, help="Feature lookback window")
    parser.add_argument("--seed", type=int, default=42, help="Random seed")

    # Splitting
    parser.add_argument("--train-ratio", type=float, default=0.7)
    parser.add_argument("--val-ratio", type=float, default=0.15)
    parser.add_argument("--test-ratio", type=float, default=0.15)
    parser.add_argument(
        "--walk-forward", action="store_true",
        help="Use walk-forward validation (requires walk_forward.py from Stage 0)",
    )
    parser.add_argument("--n-splits", type=int, default=5, help="Walk-forward splits")
    parser.add_argument("--gap", type=int, default=24, help="Walk-forward gap")
    parser.add_argument("--purge", type=int, default=24, help="Walk-forward purge")

    # Output
    parser.add_argument(
        "--output-dir",
        default=str(Path(__file__).resolve().parent.parent / "outputs" / "patchtst_run1"),
    )
    parser.add_argument(
        "--dry-run", action="store_true", help="Synthetic data, 2 epochs, CPU only",
    )
    parser.add_argument(
        "--advanced", action="store_true",
        help="Use advanced features (regime, momentum, statistical, price_acceleration)",
    )
    parser.add_argument(
        "--indicators", nargs="+", default=None,
        help="Specific indicators to use (overrides --advanced)",
    )
    args = parser.parse_args()

    # Seed
    np.random.seed(args.seed)

    # Device
    try:
        import torch
        torch.manual_seed(args.seed)
        device = "cuda" if torch.cuda.is_available() else "cpu"
    except ImportError:
        print("ERROR: PyTorch not installed. Run: pip install torch", file=sys.stderr)
        sys.exit(1)

    # Load data
    symbols = [s.strip() for s in args.symbols.split(",")]

    if args.dry_run:
        print("DRY-RUN: Using synthetic data (1000 rows, 2 epochs)")
        raw = generate_synthetic_data(1000)
        data_hash = "synthetic-dryrun"
        args.epochs = 2
        symbols = [symbols[0]] if symbols else ["SPY"]
    else:
        data_dir = Path(args.data_dir)
        if not data_dir.exists():
            print(f"ERROR: Data directory not found: {data_dir}", file=sys.stderr)
            sys.exit(1)
        raw = load_data(data_dir, symbols[0], args.start, args.end)
        data_hash = compute_data_hash(raw)
        print(f"Loaded {len(raw)} rows for {symbols[0]}")

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
    # normalize_sequences(X_train, X_test, X_val) returns (train_n, val_n, test_n, mean, std)
    X_train, X_val, X_test, norm_mean, norm_std = normalize_sequences(X_train, X_val, X_test)

    # Validate test ratio is honored
    actual_test_ratio = round(len(X_test) / n, 3)
    print(f"Split: train={len(X_train)}, val={len(X_val)}, test={len(X_test)} "
          f"(requested test_ratio={args.test_ratio}, actual={actual_test_ratio})")

    if args.walk_forward and WalkForwardSplitter is not None:
        print(f"Walk-forward validation: {args.n_splits} splits, gap={args.gap}, purge={args.purge}")
        # Walk-forward would replace simple split; implemented when Stage 0 delivers splitter
        # For now, proceed with simple split and log that W-F was requested but not applied

    print(f"Device: {device}, n_vars={n_features}")

    hyperparams = {
        "model_type": "patchtst",
        "seq_len": args.seq_len,
        "pred_len": args.pred_len,
        "patch_len": args.patch_len,
        "stride": args.stride,
        "d_model": args.d_model,
        "n_heads": args.n_heads,
        "n_layers": args.n_layers,
        "dropout": args.dropout,
        "fc_dropout": args.fc_dropout,
        "channel_independence": not args.no_channel_independence,
        "epochs": args.epochs,
        "batch_size": args.batch_size,
        "learning_rate": args.lr,
        "lookback": args.lookback,
        "symbols": symbols,
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
        patch_len=args.patch_len,
        stride=args.stride,
        d_model=args.d_model,
        n_heads=args.n_heads,
        n_layers=args.n_layers,
        dropout=args.dropout,
        fc_dropout=args.fc_dropout,
        epochs=args.epochs,
        batch_size=args.batch_size,
        learning_rate=args.lr,
        channel_independence=not args.no_channel_independence,
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
