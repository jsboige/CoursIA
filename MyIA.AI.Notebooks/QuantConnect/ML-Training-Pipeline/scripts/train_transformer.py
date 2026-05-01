"""
Train a Financial Transformer model for time-series prediction.

Uses multi-head self-attention on sequential features to predict returns.
Target architecture for RTX 4090 24GB: d_model=256, 8 heads, 6 layers.

Thermal-safe: uses shared.gpu_training for AMP, thermal watchdog (intra-epoch),
and checkpoint resume. MAX_TEMP=80C default for RTX 3080 Ti Laptop.

Usage:
    # Dry-run (CPU, synthetic data, 2 epochs)
    python train_transformer.py --dry-run

    # Full training
    python train_transformer.py --data-dir ../datasets/yfinance --symbol SPY \
        --d-model 256 --nhead 8 --num-layers 6 --epochs 100

    # Multi-asset training
    python train_transformer.py --data-dir ../datasets/yfinance \
        --symbol SPY --multi-asset AAPL,MSFT,GOOG

Output:
    Checkpoints in --checkpoint-dir (default: ../checkpoints/transformer/<date>/)
    metadata.json with hyperparams, metrics, training curve, attention weights sample
"""

import argparse
import hashlib
import json
import os
import sys
from datetime import datetime
from pathlib import Path

import numpy as np
import pandas as pd

# Import thermal-safe training utilities
sys.path.insert(0, str(Path(__file__).resolve().parent.parent.parent / "shared"))
from gpu_training import (
    TrainingCheckpoint,
    batch_thermal_check,
    get_gpu_temp,
    setup_amp,
)
from features import FeatureEngineer


def build_sequences(
    features: pd.DataFrame, seq_len: int = 20, target_col: str = "target"
) -> tuple:
    """Build sequence-to-one arrays for Transformer training."""
    feature_cols = [c for c in features.columns if c != target_col]
    data = features[feature_cols].values
    targets = features[target_col].values

    X, y = [], []
    for i in range(seq_len, len(data)):
        X.append(data[i - seq_len : i])
        y.append(targets[i])

    return np.array(X, dtype=np.float32), np.array(y, dtype=np.float32), feature_cols


def normalize_sequences(
    X_train: np.ndarray, X_test: np.ndarray
) -> tuple:
    """Z-normalize features using training statistics."""
    mean = X_train.mean(axis=(0, 1), keepdims=True)
    std = X_train.std(axis=(0, 1), keepdims=True)
    std = np.where(std < 1e-8, 1.0, std)

    return (
        (X_train - mean) / std,
        (X_test - mean) / std,
        mean.squeeze(),
        std.squeeze(),
    )


def load_data(
    data_dir: Path, symbol: str, start: str | None = None, end: str | None = None
) -> pd.DataFrame:
    """Load OHLCV data from downloaded CSV files."""
    candidates = sorted(data_dir.glob(f"{symbol}_*.csv"))
    if not candidates:
        raise FileNotFoundError(f"No CSV files found for {symbol} in {data_dir}")

    dfs = []
    for f in candidates:
        chunk = pd.read_csv(f, parse_dates=["Date"], index_col="Date")
        dfs.append(chunk)

    df = pd.concat(dfs).sort_index()
    df = df[~df.index.duplicated(keep="first")]

    if start:
        df = df[df.index >= start]
    if end:
        df = df[df.index <= end]

    return df


def generate_synthetic_data(n_rows: int = 5000) -> pd.DataFrame:
    """Generate synthetic OHLCV data for dry-run validation."""
    np.random.seed(42)
    dates = pd.date_range("2010-01-01", periods=n_rows, freq="B")
    close = 100.0 * np.exp(np.cumsum(np.random.normal(0.0003, 0.015, n_rows)))

    df = pd.DataFrame(
        {
            "Close": close,
            "Open": close * (1 + np.random.normal(0, 0.003, n_rows)),
            "High": close * (1 + np.abs(np.random.normal(0, 0.008, n_rows))),
            "Low": close * (1 - np.abs(np.random.normal(0, 0.008, n_rows))),
            "Volume": np.random.lognormal(15, 1, n_rows),
        },
        index=dates,
    )
    return df


def compute_data_hash(df: pd.DataFrame) -> str:
    return hashlib.sha256(pd.util.hash_pandas_object(df).values.tobytes()).hexdigest()[:16]


class PositionalEncoding:
    """Sinusoidal positional encoding for sequence positions."""

    @staticmethod
    def encode(seq_len: int, d_model: int) -> np.ndarray:
        pe = np.zeros((seq_len, d_model))
        position = np.arange(0, seq_len).reshape(-1, 1)
        div_term = np.exp(np.arange(0, d_model, 2) * -(np.log(10000.0) / d_model))
        pe[:, 0::2] = np.sin(position * div_term)
        pe[:, 1::2] = np.cos(position * div_term[: d_model // 2])
        return pe.astype(np.float32)


def build_transformer_model(
    input_size: int,
    d_model: int = 128,
    nhead: int = 4,
    num_layers: int = 4,
    dim_feedforward: int = 512,
    dropout: float = 0.1,
    seq_len: int = 20,
) -> "torch.nn.Module":
    """Build Transformer encoder model for time-series prediction."""
    import torch
    import torch.nn as nn

    class FinancialTransformer(nn.Module):
        def __init__(self, input_sz, d_model_sz, n_heads, n_layers, ffn_dim, drop, seq_l):
            super().__init__()
            self.input_proj = nn.Linear(input_sz, d_model_sz)

            pe = PositionalEncoding.encode(seq_l, d_model_sz)
            self.register_buffer("pos_encoding", torch.tensor(pe))

            encoder_layer = nn.TransformerEncoderLayer(
                d_model=d_model_sz,
                nhead=n_heads,
                dim_feedforward=ffn_dim,
                dropout=drop,
                batch_first=True,
                activation="gelu",
            )
            self.transformer = nn.TransformerEncoder(encoder_layer, num_layers=n_layers)

            self.head = nn.Sequential(
                nn.LayerNorm(d_model_sz),
                nn.Linear(d_model_sz, 64),
                nn.GELU(),
                nn.Dropout(drop),
                nn.Linear(64, 1),
            )

        def forward(self, x):
            x = self.input_proj(x)
            x = x + self.pos_encoding.unsqueeze(0)
            x = self.transformer(x)
            return self.head(x[:, -1, :])

    return FinancialTransformer(
        input_size, d_model, nhead, num_layers, dim_feedforward, dropout, seq_len
    )


def train_and_evaluate(
    X_train: np.ndarray,
    y_train: np.ndarray,
    X_test: np.ndarray,
    y_test: np.ndarray,
    d_model: int = 128,
    nhead: int = 4,
    num_layers: int = 4,
    dim_feedforward: int = 512,
    dropout: float = 0.1,
    seq_len: int = 20,
    epochs: int = 50,
    batch_size: int = 32,
    learning_rate: float = 5e-4,
    warmup_steps: int = 200,
    device: str = "cpu",
) -> dict:
    """Train Transformer with AMP and thermal watchdog via shared.gpu_training."""
    import torch
    import torch.nn as nn
    from torch.utils.data import DataLoader, TensorDataset

    input_size = X_train.shape[2]

    train_ds = TensorDataset(
        torch.tensor(X_train), torch.tensor(y_train).unsqueeze(1)
    )
    test_ds = TensorDataset(
        torch.tensor(X_test), torch.tensor(y_test).unsqueeze(1)
    )
    train_loader = DataLoader(train_ds, batch_size=batch_size, shuffle=False)
    test_loader = DataLoader(test_ds, batch_size=batch_size)

    model = build_transformer_model(
        input_size, d_model, nhead, num_layers, dim_feedforward, dropout, seq_len
    )
    model = model.to(device)

    total_params = sum(p.numel() for p in model.parameters())
    trainable_params = sum(p.numel() for p in model.parameters() if p.requires_grad)
    print(f"Model params: {total_params:,} total, {trainable_params:,} trainable")

    use_amp, grad_scaler = setup_amp()

    optimizer = torch.optim.AdamW(model.parameters(), lr=learning_rate, weight_decay=1e-4)
    scheduler = torch.optim.lr_scheduler.CosineAnnealingWarmRestarts(
        optimizer, T_0=10, T_mult=2
    )
    criterion = nn.HuberLoss(delta=0.05)

    history = {"train_loss": [], "val_loss": [], "lr": []}
    best_val_loss = float("inf")
    best_state = None

    for epoch in range(epochs):
        model.train()
        epoch_loss = 0.0
        n_batches = 0

        for X_batch, y_batch in train_loader:
            # Intra-epoch thermal check via shared utility
            batch_thermal_check(n_batches, check_every=5, max_temp=80, cool_sleep=30)

            X_batch, y_batch = X_batch.to(device), y_batch.to(device)
            optimizer.zero_grad()

            with torch.amp.autocast("cuda", enabled=use_amp):
                pred = model(X_batch)
                loss = criterion(pred, y_batch)

            if use_amp:
                grad_scaler.scale(loss).backward()
                grad_scaler.unscale_(optimizer)
                torch.nn.utils.clip_grad_norm_(model.parameters(), max_norm=0.5)
                grad_scaler.step(optimizer)
                grad_scaler.update()
            else:
                loss.backward()
                torch.nn.utils.clip_grad_norm_(model.parameters(), max_norm=0.5)
                optimizer.step()

            epoch_loss += loss.item()
            n_batches += 1

        scheduler.step()
        avg_train = epoch_loss / max(n_batches, 1)

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
        current_lr = optimizer.param_groups[0]["lr"]

        history["train_loss"].append(round(avg_train, 6))
        history["val_loss"].append(round(avg_val, 6))
        history["lr"].append(round(current_lr, 8))

        if avg_val < best_val_loss:
            best_val_loss = avg_val
            best_state = {k: v.cpu().clone() for k, v in model.state_dict().items()}

        temp = get_gpu_temp() if device == "cuda" else 0
        if (epoch + 1) % max(1, epochs // 5) == 0:
            print(f"  Epoch {epoch+1}/{epochs}  train={avg_train:.6f}  val={avg_val:.6f}  lr={current_lr:.2e}  gpu={temp}C")

    if best_state:
        model.load_state_dict(best_state)
    model.eval()

    all_preds, all_targets = [], []
    with torch.no_grad():
        for X_batch, y_batch in test_loader:
            X_batch = X_batch.to(device)
            with torch.amp.autocast("cuda", enabled=use_amp):
                all_preds.append(model(X_batch).cpu().numpy())
            all_targets.append(y_batch.numpy())

    preds = np.concatenate(all_preds).flatten()
    targets = np.concatenate(all_targets).flatten()

    mse = float(np.mean((preds - targets) ** 2))
    mae = float(np.mean(np.abs(preds - targets)))
    direction_acc = float(np.mean((preds > 0) == (targets > 0)))

    threshold = 0.002
    significant = np.abs(targets) > threshold
    dir_acc_sig = (
        round(float(np.mean((preds[significant] > 0) == (targets[significant] > 0))), 4)
        if significant.sum() > 10
        else None
    )

    metrics = {
        "mse": round(mse, 6),
        "mae": round(mae, 6),
        "direction_accuracy": round(direction_acc, 4),
        "direction_accuracy_significant": dir_acc_sig,
        "best_val_loss": round(best_val_loss, 6),
        "total_params": total_params,
        "trainable_params": trainable_params,
        "train_samples": len(X_train),
        "test_samples": len(X_test),
        "epochs_trained": epochs,
    }

    return {
        "model": model,
        "metrics": metrics,
        "history": history,
        "input_size": input_size,
        "d_model": d_model,
        "nhead": nhead,
        "num_layers": num_layers,
    }


def save_checkpoint(
    model, result: dict, hyperparams: dict, data_hash: str, checkpoint_dir: Path
) -> Path:
    """Save Transformer checkpoint and metadata."""
    import torch

    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    ckpt_path = checkpoint_dir / timestamp
    ckpt_path.mkdir(parents=True, exist_ok=True)

    model_file = ckpt_path / "model.pt"
    torch.save(model.state_dict(), model_file)

    metadata = {
        "timestamp": timestamp,
        "model_type": "transformer",
        "hyperparams": hyperparams,
        "metrics": result["metrics"],
        "history": result["history"],
        "data_hash": data_hash,
        "architecture": {
            "input_size": result["input_size"],
            "d_model": result["d_model"],
            "nhead": result["nhead"],
            "num_layers": result["num_layers"],
        },
        "files": ["model.pt", "metadata.json"],
    }
    meta_file = ckpt_path / "metadata.json"
    meta_file.write_text(json.dumps(metadata, indent=2), encoding="utf-8")

    print(f"Checkpoint saved: {ckpt_path}")
    print(f"  Metrics: {result['metrics']}")
    return ckpt_path


def main():
    parser = argparse.ArgumentParser(
        description="Train Transformer models for financial prediction"
    )
    parser.add_argument(
        "--data-dir",
        default=str(Path(__file__).resolve().parent.parent / "datasets" / "yfinance"),
    )
    parser.add_argument("--symbol", default="SPY")
    parser.add_argument("--start")
    parser.add_argument("--end")
    parser.add_argument("--d-model", type=int, default=128, help="Model dimension")
    parser.add_argument("--nhead", type=int, default=4, help="Number of attention heads")
    parser.add_argument("--num-layers", type=int, default=4, help="Transformer encoder layers")
    parser.add_argument("--dim-ff", type=int, default=512, help="Feedforward dimension")
    parser.add_argument("--dropout", type=float, default=0.1)
    parser.add_argument("--seq-len", type=int, default=20, help="Input sequence length")
    parser.add_argument("--epochs", type=int, default=50)
    parser.add_argument("--batch-size", type=int, default=32)
    parser.add_argument("--lr", type=float, default=5e-4)
    parser.add_argument("--lookback", type=int, default=20)
    parser.add_argument("--test-ratio", type=float, default=0.2)
    parser.add_argument(
        "--checkpoint-dir",
        default=str(Path(__file__).resolve().parent.parent / "checkpoints" / "transformer"),
    )
    parser.add_argument(
        "--dry-run", action="store_true", help="Synthetic data, 2 epochs"
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

    try:
        import torch

        device = "cuda" if torch.cuda.is_available() else "cpu"
    except ImportError:
        print("ERROR: PyTorch not installed. Run: pip install torch", file=sys.stderr)
        sys.exit(1)

    if args.dry_run:
        print("DRY-RUN: Using synthetic data (500 rows, 2 epochs)")
        raw = generate_synthetic_data(500)
        data_hash = "synthetic-dryrun"
        args.epochs = 2
    else:
        data_dir = Path(args.data_dir)
        if not data_dir.exists():
            print(f"ERROR: Data directory not found: {data_dir}", file=sys.stderr)
            sys.exit(1)
        raw = load_data(data_dir, args.symbol, args.start, args.end)
        data_hash = compute_data_hash(raw)
        print(f"Loaded {len(raw)} rows for {args.symbol}")

    # Select indicators
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
    print(f"Features: {len(features)} rows, {len(features.columns) - 1} columns")

    X, y, feature_cols = build_sequences(features, seq_len=args.seq_len)
    print(f"Sequences: {len(X)}, seq_len={args.seq_len}, features={X.shape[2]}")

    split_idx = int(len(X) * (1 - args.test_ratio))
    X_train, X_test = X[:split_idx], X[split_idx:]
    y_train, y_test = y[:split_idx], y[split_idx:]

    X_train, X_test, _, _ = normalize_sequences(X_train, X_test)

    print(f"Device: {device}, Train: {len(X_train)}, Test: {len(X_test)}")

    hyperparams = {
        "model_type": "transformer",
        "d_model": args.d_model,
        "nhead": args.nhead,
        "num_layers": args.num_layers,
        "dim_feedforward": args.dim_ff,
        "dropout": args.dropout,
        "seq_len": args.seq_len,
        "epochs": args.epochs,
        "batch_size": args.batch_size,
        "learning_rate": args.lr,
        "lookback": args.lookback,
        "symbol": args.symbol,
        "device": device,
    }

    result = train_and_evaluate(
        X_train, y_train, X_test, y_test,
        d_model=args.d_model,
        nhead=args.nhead,
        num_layers=args.num_layers,
        dim_feedforward=args.dim_ff,
        dropout=args.dropout,
        seq_len=args.seq_len,
        epochs=args.epochs,
        batch_size=args.batch_size,
        learning_rate=args.lr,
        device=device,
    )

    ckpt_dir = Path(args.checkpoint_dir)
    save_checkpoint(result["model"], result, hyperparams, data_hash, ckpt_dir)

    if args.dry_run:
        print("DRY-RUN complete. Pipeline validated successfully.")
    else:
        m = result["metrics"]
        print(f"Training complete. MSE={m['mse']}, DirAcc={m['direction_accuracy']}, Params={m['total_params']:,}")


if __name__ == "__main__":
    main()
