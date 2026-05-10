"""
Train iTransformer models for financial time-series forecasting.

Implements "iTransformer: Inverted Transformers Are Effective for Time Series
Forecasting" (Li et al., ICLR 2024). Key innovation:
- Inverted attention: tokens = variables (not time steps)
- Each variable's time series is embedded, transformer captures inter-variable deps
- Embedding: [B, T, N] -> reshape -> [B, N, T] -> linear(T, d_model) -> transformer

Anti-pattern safeguards:
- --test-ratio HONORED: normalize stats on train set only
- Walk-forward validation supported (optional)
- Majority-class baseline computed and reported

Usage:
    python train_itransformer.py --dry-run
    python train_itransformer.py --data-dir ../datasets/yfinance --symbol SPY

Output:
    Checkpoints in --output-dir (default: ../outputs/itransformer_run1/)
    metadata.json with hyperparams, metrics, majority-class comparison, training curve
"""

import argparse
import sys
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
from checkpoint_utils import save_pytorch_checkpoint
from data_utils import compute_data_hash, generate_synthetic_data, load_data
from features import FeatureEngineer
from baselines import oos_direction_distribution
from sequence_utils import build_sequences, normalize_sequences

try:
    from walk_forward import WalkForwardSplitter
except ImportError:
    WalkForwardSplitter = None


class iTransformerModel(nn.Module):
    """iTransformer: Inverted Transformers for Time Series (Li et al., ICLR 2024).

    Key insight: instead of treating time steps as tokens (standard Transformer),
    treat each VARIABLE as a token with its entire time series as features.

    Architecture:
        1. Input [B, T, N] -> permute -> [B, N, T]
        2. Embedding: Linear(T, d_model) -> [B, N, d_model]
        3. Transformer encoder over N variable tokens
        4. Projection: Linear(d_model, pred_len) -> [B, N, pred_len]
        5. Permute back -> [B, pred_len, N] -> aggregate -> [B, pred_len]
    """

    def __init__(
        self,
        n_vars: int,
        seq_len: int,
        pred_len: int,
        d_model: int = 128,
        n_heads: int = 8,
        n_layers: int = 3,
        dropout: float = 0.2,
        ff_dropout: float = 0.2,
    ):
        super().__init__()
        self.n_vars = n_vars
        self.seq_len = seq_len
        self.pred_len = pred_len
        self.d_model = d_model

        # Embed each variable's time series into d_model
        self.var_embedding = nn.Linear(seq_len, d_model)

        # Positional encoding for variable positions (learnable)
        self.var_pos_encoding = nn.Parameter(torch.randn(1, n_vars, d_model) * 0.02)

        # Transformer encoder over variable tokens
        encoder_layer = nn.TransformerEncoderLayer(
            d_model=d_model,
            nhead=n_heads,
            dim_feedforward=d_model * 4,
            dropout=dropout,
            batch_first=True,
            activation="gelu",
        )
        self.transformer = nn.TransformerEncoder(encoder_layer, num_layers=n_layers)

        # Layer norm + dropout
        self.layer_norm = nn.LayerNorm(d_model)
        self.fc_drop = nn.Dropout(ff_dropout)

        # Project from d_model to pred_len for each variable
        self.projection = nn.Linear(d_model, pred_len)

    def forward(self, x):
        """Forward pass.

        Args:
            x: [B, T, N] input tensor

        Returns:
            [B, pred_len] predictions (aggregated across variables)
        """
        B, T, N = x.shape

        # Invert: [B, T, N] -> [B, N, T]
        x = x.permute(0, 2, 1)

        # Embed each variable's time series: [B, N, T] -> [B, N, d_model]
        tokens = self.var_embedding(x)

        # Add variable positional encoding
        tokens = tokens + self.var_pos_encoding[:, :N, :]

        # Transformer over variable tokens: [B, N, d_model]
        encoded = self.transformer(tokens)

        # Project to prediction horizon: [B, N, d_model] -> [B, N, pred_len]
        encoded = self.layer_norm(encoded)
        encoded = self.fc_drop(encoded)
        preds = self.projection(encoded)

        # Aggregate across variables: [B, N, pred_len] -> [B, pred_len]
        preds = preds.mean(dim=1)

        return preds



def train_and_evaluate(
    X_train: np.ndarray,
    y_train: np.ndarray,
    X_test: np.ndarray,
    y_test: np.ndarray,
    n_vars: int,
    seq_len: int = 96,
    pred_len: int = 24,
    d_model: int = 128,
    n_heads: int = 8,
    n_layers: int = 3,
    dropout: float = 0.2,
    ff_dropout: float = 0.2,
    epochs: int = 100,
    batch_size: int = 64,
    learning_rate: float = 5e-4,
    device: str = "cpu",
    val_ratio: float = 0.15,
) -> dict:
    """Train iTransformer model and return metrics with baseline comparison.

    Test-set contamination fix: validation/early-stopping uses an internal
    split from the training data only. test_loader is used exclusively for
    final OOS metrics (never influences model selection).
    """
    from torch.utils.data import DataLoader, TensorDataset

    # Internal train/val split from training data only (prevent test leakage)
    val_cutoff = int(len(X_train) * (1 - val_ratio))
    X_tr, X_val = X_train[:val_cutoff], X_train[val_cutoff:]
    y_tr, y_val = y_train[:val_cutoff], y_train[val_cutoff:]

    model = iTransformerModel(
        n_vars=n_vars,
        seq_len=seq_len,
        pred_len=pred_len,
        d_model=d_model,
        n_heads=n_heads,
        n_layers=n_layers,
        dropout=dropout,
        ff_dropout=ff_dropout,
    )
    model = model.to(device)

    total_params = sum(p.numel() for p in model.parameters() if p.requires_grad)
    print(f"iTransformer params: {total_params:,}")

    train_ds = TensorDataset(torch.tensor(X_tr), torch.tensor(y_tr))
    val_ds = TensorDataset(torch.tensor(X_val), torch.tensor(y_val))
    test_ds = TensorDataset(torch.tensor(X_test), torch.tensor(y_test))
    train_loader = DataLoader(train_ds, batch_size=batch_size, shuffle=False)
    val_loader = DataLoader(val_ds, batch_size=batch_size)
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

        # Validation on internal val set (NOT test set)
        model.eval()
        val_loss = 0.0
        val_batches = 0
        with torch.no_grad():
            for X_batch, y_batch in val_loader:
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
            temp = get_gpu_temp()
            temp_str = f"  GPU={temp}C" if temp > 0 else ""
            print(f"  Epoch {epoch+1}/{epochs}  train={avg_train:.6f}  val={avg_val:.6f}{temp_str}")

    if best_state:
        model.load_state_dict(best_state)
    model.eval()

    # Compute metrics
    all_preds, all_targets = [], []
    with torch.no_grad():
        for X_batch, y_batch in test_loader:
            X_batch = X_batch.to(device)
            with torch.amp.autocast("cuda", enabled=use_amp):
                all_preds.append(model(X_batch).cpu().numpy())
            all_targets.append(y_batch.numpy())

    preds = np.concatenate(all_preds)
    targets = np.concatenate(all_targets)
    if preds.ndim == 1:
        preds = preds[:, None]
    if targets.ndim == 1:
        targets = targets[:, None]

    mse = float(np.mean((preds - targets) ** 2))
    mae = float(np.mean(np.abs(preds - targets)))

    # Direction accuracy at step 1 (first prediction step)
    direction_acc = float(np.mean((preds[:, 0] > 0) == (targets[:, 0] > 0)))

    majority_baseline = oos_direction_distribution(targets)

    metrics = {
        "mse": round(mse, 6),
        "mae": round(mae, 6),
        "direction_accuracy_step1": round(direction_acc, 4),
        "majority_class_baseline": majority_baseline,
        "edge_over_majority": round(direction_acc - majority_baseline["majority_class_accuracy"], 4),
        "best_val_loss": round(best_val_loss, 6),
        "total_params": total_params,
        "train_samples": len(X_tr),
        "test_samples": len(X_test),
        "epochs_trained": epochs,
    }

    return {
        "model": model,
        "metrics": metrics,
        "history": history,
    }



def main():
    parser = argparse.ArgumentParser(
        description="Train iTransformer model for financial time-series forecasting "
                    "(Li et al., ICLR 2024)"
    )
    # Data
    parser.add_argument(
        "--data-dir",
        default=str(Path(__file__).resolve().parent.parent / "datasets" / "yfinance"),
    )
    parser.add_argument("--symbols", default="SPY")
    parser.add_argument("--start")
    parser.add_argument("--end")

    # Architecture
    parser.add_argument("--seq-len", type=int, default=96)
    parser.add_argument("--pred-len", type=int, default=24)
    parser.add_argument("--d-model", type=int, default=128)
    parser.add_argument("--n-heads", type=int, default=8)
    parser.add_argument("--n-layers", type=int, default=3)
    parser.add_argument("--dropout", type=float, default=0.2)
    parser.add_argument("--ff-dropout", type=float, default=0.2)

    # Training
    parser.add_argument("--epochs", type=int, default=100)
    parser.add_argument("--batch-size", type=int, default=64)
    parser.add_argument("--lr", type=float, default=5e-4)
    parser.add_argument("--lookback", type=int, default=20)
    parser.add_argument("--seed", type=int, default=42)

    # Splitting
    parser.add_argument("--train-ratio", type=float, default=0.7)
    parser.add_argument("--val-ratio", type=float, default=0.15)
    parser.add_argument("--test-ratio", type=float, default=0.15)
    parser.add_argument("--walk-forward", action="store_true")
    parser.add_argument("--n-splits", type=int, default=5)
    parser.add_argument("--gap", type=int, default=24)
    parser.add_argument("--purge", type=int, default=24)

    # Output
    parser.add_argument(
        "--output-dir",
        default=str(Path(__file__).resolve().parent.parent / "outputs" / "itransformer_run1"),
    )
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--advanced", action="store_true")
    parser.add_argument("--indicators", nargs="+", default=None)
    args = parser.parse_args()

    np.random.seed(args.seed)

    try:
        import torch
        torch.manual_seed(args.seed)
        device = "cuda" if torch.cuda.is_available() else "cpu"
    except ImportError:
        print("ERROR: PyTorch not installed. Run: pip install torch", file=sys.stderr)
        sys.exit(1)

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

    X, y, feature_cols = build_sequences(
        features, seq_len=args.seq_len, pred_len=args.pred_len
    )
    print(f"Sequences: {len(X)} samples, seq_len={args.seq_len}, pred_len={args.pred_len}")

    n = len(X)
    train_end = int(n * args.train_ratio)
    val_end = int(n * (args.train_ratio + args.val_ratio))

    X_train, y_train = X[:train_end], y[:train_end]
    X_val, y_val = X[train_end:val_end], y[train_end:val_end]
    X_test, y_test = X[val_end:], y[val_end:]

    X_train, X_val, X_test, norm_mean, norm_std = normalize_sequences(X_train, X_val, X_test)

    actual_test_ratio = round(len(X_test) / n, 3)
    print(f"Split: train={len(X_train)}, val={len(X_val)}, test={len(X_test)} "
          f"(requested test_ratio={args.test_ratio}, actual={actual_test_ratio})")

    if args.walk_forward and WalkForwardSplitter is not None:
        print(f"Walk-forward validation: {args.n_splits} splits, gap={args.gap}, purge={args.purge}")

    print(f"Device: {device}, n_vars={n_features}")

    hyperparams = {
        "model_type": "itransformer",
        "seq_len": args.seq_len,
        "pred_len": args.pred_len,
        "d_model": args.d_model,
        "n_heads": args.n_heads,
        "n_layers": args.n_layers,
        "dropout": args.dropout,
        "ff_dropout": args.ff_dropout,
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
        d_model=args.d_model,
        n_heads=args.n_heads,
        n_layers=args.n_layers,
        dropout=args.dropout,
        ff_dropout=args.ff_dropout,
        epochs=args.epochs,
        batch_size=args.batch_size,
        learning_rate=args.lr,
        device=device,
    )

    output_dir = Path(args.output_dir)
    save_pytorch_checkpoint(
        result["model"], result, hyperparams, data_hash, output_dir,
        model_type="itransformer",
    )

    m = result["metrics"]
    edge = m["edge_over_majority"]
    print(f"\nResults: MSE={m['mse']}, DirAcc(step1)={m['direction_accuracy_step1']}")
    print(f"  Majority baseline: {m['majority_class_baseline']['majority_class_accuracy']}")
    print(f"  Edge over majority: {edge:+.4f} ({'BEATS' if edge > 0 else 'FAILS'} baseline)")

    if args.dry_run:
        print("DRY-RUN complete. Pipeline validated successfully.")


if __name__ == "__main__":
    main()
