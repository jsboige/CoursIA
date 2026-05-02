"""
Train PyTorch LSTM models for financial time-series prediction.

Predicts next-period returns using sequence-to-one architecture.
Designed to scale from dry-run (CPU, small data) to full GPU training.

Usage:
    # Dry-run (CPU, synthetic data, 2 epochs)
    python train_lstm.py --dry-run

    # Full training on yfinance data
    python train_lstm.py --data-dir ../datasets/yfinance --symbol SPY --start 2010-01-01

    # GPU training with custom architecture
    python train_lstm.py --data-dir ../datasets/yfinance --symbol SPY \
        --hidden-size 256 --num-layers 3 --epochs 100 --batch-size 64

Output:
    Checkpoints in --checkpoint-dir (default: ../checkpoints/lstm/<date>/)
    metadata.json with hyperparams, metrics, dataset hash, training curve
"""

import argparse
import hashlib
import json
import sys
from datetime import datetime
from pathlib import Path

import numpy as np
import pandas as pd

sys.path.append(str(Path(__file__).resolve().parent.parent.parent / "shared"))
from gpu_training import (
    batch_thermal_check,
    get_gpu_temp,
    setup_amp,
)
from features import FeatureEngineer


def build_sequences(
    features: pd.DataFrame, seq_len: int = 20, target_col: str = "target"
) -> tuple:
    """Build sequence-to-one arrays for LSTM training."""
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
    """Z-normalize features using training statistics only."""
    mean = X_train.mean(axis=(0, 1), keepdims=True)
    std = X_train.std(axis=(0, 1), keepdims=True)
    std = np.where(std < 1e-8, 1.0, std)

    X_train_norm = (X_train - mean) / std
    X_test_norm = (X_test - mean) / std
    return X_train_norm, X_test_norm, mean.squeeze(), std.squeeze()


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
    """Compute SHA256 hash of the dataset for reproducibility."""
    return hashlib.sha256(pd.util.hash_pandas_object(df).values.tobytes()).hexdigest()[:16]


def build_model(
    input_size: int,
    hidden_size: int = 128,
    num_layers: int = 2,
    dropout: float = 0.2,
    model_type: str = "lstm",
) -> "torch.nn.Module":
    """Build LSTM or GRU model."""
    import torch
    import torch.nn as nn

    rnn_cls = nn.LSTM if model_type == "lstm" else nn.GRU

    class FinancialRNN(nn.Module):
        def __init__(self, input_sz, hidden_sz, num_lyr, dropout_p, rnn_cls):
            super().__init__()
            self.rnn = rnn_cls(
                input_size=input_sz,
                hidden_size=hidden_sz,
                num_layers=num_lyr,
                batch_first=True,
                dropout=dropout_p if num_lyr > 1 else 0.0,
            )
            self.head = nn.Sequential(
                nn.Linear(hidden_sz, 64),
                nn.ReLU(),
                nn.Dropout(dropout_p),
                nn.Linear(64, 1),
            )

        def forward(self, x):
            out, _ = self.rnn(x)
            return self.head(out[:, -1, :])

    return FinancialRNN(input_size, hidden_size, num_layers, dropout, rnn_cls)


def train_and_evaluate(
    X_train: np.ndarray,
    y_train: np.ndarray,
    X_test: np.ndarray,
    y_test: np.ndarray,
    hidden_size: int = 128,
    num_layers: int = 2,
    dropout: float = 0.2,
    epochs: int = 50,
    batch_size: int = 32,
    learning_rate: float = 1e-3,
    model_type: str = "lstm",
    device: str = "cpu",
) -> dict:
    """Train LSTM/GRU model and return metrics + training history."""
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

    model = build_model(input_size, hidden_size, num_layers, dropout, model_type)
    model = model.to(device)

    optimizer = torch.optim.Adam(model.parameters(), lr=learning_rate, weight_decay=1e-5)
    scheduler = torch.optim.lr_scheduler.CosineAnnealingLR(optimizer, T_max=epochs)
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

        model.eval()
        val_loss = 0.0
        val_batches = 0
        with torch.no_grad():
            for X_batch, y_batch in test_loader:
                X_batch, y_batch = X_batch.to(device), y_batch.to(device)
                pred = model(X_batch)
                val_loss += criterion(pred, y_batch).item()
                val_batches += 1

        avg_val = val_loss / max(val_batches, 1)
        history["train_loss"].append(round(avg_train, 6))
        history["val_loss"].append(round(avg_val, 6))

        if avg_val < best_val_loss:
            best_val_loss = avg_val
            best_state = {k: v.cpu().clone() for k, v in model.state_dict().items()}

        if (epoch + 1) % max(1, epochs // 5) == 0:
            temp = get_gpu_temp()
            temp_str = f"  GPU={temp}C" if temp > 0 else ""
            print(f"  Epoch {epoch+1}/{epochs}  train={avg_train:.6f}  val={avg_val:.6f}{temp_str}")

    # Load best model for final evaluation
    if best_state:
        model.load_state_dict(best_state)
    model.eval()

    # Compute metrics on best model
    all_preds, all_targets = [], []
    with torch.no_grad():
        for X_batch, y_batch in test_loader:
            X_batch = X_batch.to(device)
            pred = model(X_batch).cpu().numpy()
            all_preds.append(pred)
            all_targets.append(y_batch.numpy())

    preds = np.concatenate(all_preds).flatten()
    targets = np.concatenate(all_targets).flatten()

    mse = float(np.mean((preds - targets) ** 2))
    mae = float(np.mean(np.abs(preds - targets)))
    direction_acc = float(np.mean((preds > 0) == (targets > 0)))

    # Direction accuracy with threshold (ignore near-zero returns)
    threshold = 0.002
    significant = np.abs(targets) > threshold
    if significant.sum() > 10:
        dir_acc_sig = float(np.mean((preds[significant] > 0) == (targets[significant] > 0)))
    else:
        dir_acc_sig = None

    metrics = {
        "mse": round(mse, 6),
        "mae": round(mae, 6),
        "direction_accuracy": round(direction_acc, 4),
        "direction_accuracy_significant": round(dir_acc_sig, 4) if dir_acc_sig else None,
        "best_val_loss": round(best_val_loss, 6),
        "train_samples": len(X_train),
        "test_samples": len(X_test),
        "epochs_trained": epochs,
    }

    return {
        "model": model,
        "metrics": metrics,
        "history": history,
        "input_size": input_size,
        "hidden_size": hidden_size,
        "num_layers": num_layers,
    }


def save_checkpoint(
    model, result: dict, hyperparams: dict, data_hash: str, checkpoint_dir: Path
) -> Path:
    """Save model checkpoint and metadata."""
    import torch

    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    ckpt_path = checkpoint_dir / timestamp
    ckpt_path.mkdir(parents=True, exist_ok=True)

    model_file = ckpt_path / "model.pt"
    torch.save(model.state_dict(), model_file)

    metadata = {
        "timestamp": timestamp,
        "model_type": hyperparams.get("model_type", "lstm"),
        "hyperparams": hyperparams,
        "metrics": result["metrics"],
        "history": result["history"],
        "data_hash": data_hash,
        "architecture": {
            "input_size": result["input_size"],
            "hidden_size": result["hidden_size"],
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
        description="Train LSTM/GRU models for financial prediction"
    )
    parser.add_argument(
        "--data-dir",
        default=str(Path(__file__).resolve().parent.parent / "datasets" / "yfinance"),
        help="Directory containing OHLCV CSV files",
    )
    parser.add_argument("--symbol", default="SPY", help="Ticker symbol to train on")
    parser.add_argument("--start", help="Start date (YYYY-MM-DD)")
    parser.add_argument("--end", help="End date (YYYY-MM-DD)")
    parser.add_argument("--model", default="lstm", choices=["lstm", "gru"], help="RNN type")
    parser.add_argument("--hidden-size", type=int, default=128, help="Hidden state size")
    parser.add_argument("--num-layers", type=int, default=2, help="Number of RNN layers")
    parser.add_argument("--dropout", type=float, default=0.2, help="Dropout rate")
    parser.add_argument("--seq-len", type=int, default=20, help="Input sequence length")
    parser.add_argument("--epochs", type=int, default=50, help="Training epochs")
    parser.add_argument("--batch-size", type=int, default=32, help="Batch size")
    parser.add_argument("--lr", type=float, default=1e-3, help="Learning rate")
    parser.add_argument("--lookback", type=int, default=20, help="Feature lookback window")
    parser.add_argument("--test-ratio", type=float, default=0.2, help="Test set ratio")
    parser.add_argument(
        "--checkpoint-dir",
        default=str(Path(__file__).resolve().parent.parent / "checkpoints" / "lstm"),
        help="Directory to save checkpoints",
    )
    parser.add_argument(
        "--dry-run", action="store_true", help="Run with synthetic data (500 rows, 2 epochs)"
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

    # Detect device
    try:
        import torch

        device = "cuda" if torch.cuda.is_available() else "cpu"
    except ImportError:
        print("ERROR: PyTorch not installed. Run: pip install torch", file=sys.stderr)
        sys.exit(1)

    # Load data
    if args.dry_run:
        print("DRY-RUN: Using synthetic data (500 rows, 2 epochs)")
        raw = generate_synthetic_data(500)
        data_hash = "synthetic-dryrun"
        args.epochs = 2
    else:
        data_dir = Path(args.data_dir)
        if not data_dir.exists():
            print(f"ERROR: Data directory not found: {data_dir}", file=sys.stderr)
            print("Run download_yfinance.py first, or use --dry-run", file=sys.stderr)
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

    # Build sequences
    X, y, feature_cols = build_sequences(features, seq_len=args.seq_len)
    print(f"Sequences: {len(X)} samples, seq_len={args.seq_len}, features={X.shape[2]}")

    # Time-series split
    split_idx = int(len(X) * (1 - args.test_ratio))
    X_train, X_test = X[:split_idx], X[split_idx:]
    y_train, y_test = y[:split_idx], y[split_idx:]

    # Normalize
    X_train, X_test, norm_mean, norm_std = normalize_sequences(X_train, X_test)

    print(f"Device: {device}")
    print(f"Train: {len(X_train)}, Test: {len(X_test)}")

    hyperparams = {
        "model_type": args.model,
        "hidden_size": args.hidden_size,
        "num_layers": args.num_layers,
        "dropout": args.dropout,
        "seq_len": args.seq_len,
        "epochs": args.epochs,
        "batch_size": args.batch_size,
        "learning_rate": args.lr,
        "lookback": args.lookback,
        "test_ratio": args.test_ratio,
        "symbol": args.symbol,
        "device": device,
    }

    result = train_and_evaluate(
        X_train,
        y_train,
        X_test,
        y_test,
        hidden_size=args.hidden_size,
        num_layers=args.num_layers,
        dropout=args.dropout,
        epochs=args.epochs,
        batch_size=args.batch_size,
        learning_rate=args.lr,
        model_type=args.model,
        device=device,
    )

    # Save checkpoint
    ckpt_dir = Path(args.checkpoint_dir)
    save_checkpoint(result["model"], result, hyperparams, data_hash, ckpt_dir)

    if args.dry_run:
        print("DRY-RUN complete. Pipeline validated successfully.")
    else:
        m = result["metrics"]
        print(f"Training complete. MSE={m['mse']}, DirAcc={m['direction_accuracy']}")


if __name__ == "__main__":
    main()
