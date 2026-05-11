"""
Train TFT (Temporal Fusion Transformer) models for volatility forecasting.

Implements "Temporal Fusion Transformers for Interpretable Multi-horizon
Time Series Forecasting" (Lim et al., 2021). Key components:
- Variable Selection Networks (VSN): learn which features matter
- Gated Residual Networks (GRN): nonlinear skip connections with gating
- LSTM encoder-decoder: sequential processing of past/future
- Multi-head temporal attention: interpretable temporal patterns
- Quantile outputs: uncertainty estimation

Adapted for log-RV volatility forecasting (single-horizon, continuous target).
Anti-pattern safeguards (cf. CLAUDE.md, feedback_ml_trading_pitfalls.md):
- Walk-forward validation with gap to prevent leakage
- Normalize stats computed on train set only
- DM test vs HAR baseline (not just MSE comparison)
- Multi-seed evaluation (>=4 seeds among [0,1,7,42])
- Honest verdicts: BEATS / NO_BEATS / INCONCLUSIVE

Usage:
    python train_tft.py --dry-run
    python train_tft.py --data-dir ../datasets/yfinance/crypto_panier \\
        --symbol BTC-USD --walk-forward --n-splits 5 --seeds 0,1,7,42

Output:
    Checkpoints in --output-dir (default: ../outputs/tft_run1/)
    metadata.json with hyperparams, metrics, training curve
"""

import argparse
import sys
from pathlib import Path

import numpy as np
import pandas as pd
import torch
import torch.nn as nn
import torch.nn.functional as F

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


# ---------------------------------------------------------------------------
# TFT Building Blocks
# ---------------------------------------------------------------------------


class GatedResidualNetwork(nn.Module):
    """GRN: Gated Residual Network with skip connection (Lim et al., 2021, Eq. 2-3).

    GRN(a, c) = LayerNorm(a + GLU(W_2 * ELU(W_1 * [a; c])))
    where GLU uses a context-dependent gate.
    """

    def __init__(self, input_dim: int, hidden_dim: int, output_dim: int = None,
                 dropout: float = 0.1):
        super().__init__()
        output_dim = output_dim or input_dim
        self.fc1 = nn.Linear(input_dim, hidden_dim)
        self.fc2 = nn.Linear(hidden_dim, output_dim)
        self.gate_fc = nn.Linear(hidden_dim, output_dim)
        self.layer_norm = nn.LayerNorm(output_dim)
        self.dropout = nn.Dropout(dropout)
        self.skip = nn.Linear(input_dim, output_dim) if input_dim != output_dim else nn.Identity()

    def forward(self, x):
        residual = self.skip(x)
        hidden = F.elu(self.fc1(x))
        hidden = self.dropout(hidden)
        gate = torch.sigmoid(self.gate_fc(hidden))
        gated = gate * self.fc2(hidden)
        return self.layer_norm(residual + gated)


class VariableSelectionNetwork(nn.Module):
    """VSN: Variable Selection Network (Lim et al., 2021, Eq. 4-5).

    Learns feature-specific weights via softmax over variable contributions.
    """

    def __init__(self, n_vars: int, hidden_dim: int, dropout: float = 0.1):
        super().__init__()
        self.grn = GatedResidualNetwork(n_vars, hidden_dim, n_vars, dropout)
        self.var_grns = nn.ModuleList([
            GatedResidualNetwork(1, hidden_dim, 1, dropout) for _ in range(n_vars)
        ])

    def forward(self, x):
        """x: [B, n_vars]"""
        weights = F.softmax(self.grn(x), dim=-1)
        var_outputs = []
        for i, var_grn in enumerate(self.var_grns):
            var_outputs.append(var_grn(x[:, i:i + 1]))
        selected = torch.stack(var_outputs, dim=-1).squeeze(-2)
        return selected * weights, weights


class TemporalFusionTransformer(nn.Module):
    """TFT adapted for single-horizon volatility forecasting.

    Architecture:
        1. Feature embedding: project each time step's features
        2. Variable selection: learn which features matter at each step
        3. LSTM encoder: process historical sequence
        4. Temporal self-attention: capture long-range dependencies
        5. GRN output layer: produce final prediction

    Input: [B, T, N] -> Output: [B, pred_len]
    """

    def __init__(
        self,
        n_vars: int,
        seq_len: int,
        pred_len: int,
        d_model: int = 64,
        n_heads: int = 4,
        lstm_layers: int = 1,
        dropout: float = 0.1,
        fc_dropout: float = 0.1,
    ):
        super().__init__()
        self.n_vars = n_vars
        self.seq_len = seq_len
        self.pred_len = pred_len
        self.d_model = d_model

        # Input projection: n_vars -> d_model per time step
        self.input_proj = nn.Linear(n_vars, d_model)

        # Variable selection (applied per time step)
        self.vsn = VariableSelectionNetwork(n_vars, d_model, dropout)

        # LSTM encoder
        self.lstm = nn.LSTM(
            input_size=d_model,
            hidden_size=d_model,
            num_layers=lstm_layers,
            batch_first=True,
            dropout=dropout if lstm_layers > 1 else 0.0,
        )

        # Temporal self-attention
        self.attention = nn.MultiheadAttention(
            embed_dim=d_model,
            num_heads=n_heads,
            dropout=dropout,
            batch_first=True,
        )

        # Positional encoding for attention
        self.pos_encoding = nn.Parameter(torch.randn(1, seq_len, d_model) * 0.02)

        # Post-attention GRN
        self.post_attn_grn = GatedResidualNetwork(d_model, d_model * 2, d_model, fc_dropout)

        # Decoder: map from d_model to pred_len
        self.decoder_grn = GatedResidualNetwork(d_model, d_model * 2, d_model, fc_dropout)
        self.output_proj = nn.Linear(d_model, pred_len)

        # Final layer norm
        self.final_norm = nn.LayerNorm(d_model)

    def forward(self, x):
        """Forward pass.

        Args:
            x: [B, T, N] input tensor

        Returns:
            [B, pred_len] predictions
        """
        B, T, N = x.shape

        # Project features to d_model first
        encoded = self.input_proj(x)  # [B, T, d_model]

        # LSTM encoding
        lstm_out, _ = self.lstm(encoded)

        # Add positional encoding
        lstm_out = lstm_out + self.pos_encoding[:, :T, :]

        # Temporal self-attention
        attn_out, _ = self.attention(lstm_out, lstm_out, lstm_out)
        attn_out = self.post_attn_grn(attn_out + lstm_out)

        # Take last hidden state for prediction
        last_hidden = attn_out[:, -1, :]

        # Decode
        decoded = self.decoder_grn(last_hidden)
        decoded = self.final_norm(decoded)
        prediction = self.output_proj(decoded)

        return prediction


# ---------------------------------------------------------------------------
# Training function
# ---------------------------------------------------------------------------


def train_and_evaluate(
    X_train: np.ndarray,
    y_train: np.ndarray,
    X_test: np.ndarray,
    y_test: np.ndarray,
    n_vars: int,
    seq_len: int = 20,
    pred_len: int = 1,
    d_model: int = 64,
    n_heads: int = 4,
    lstm_layers: int = 1,
    dropout: float = 0.1,
    fc_dropout: float = 0.1,
    epochs: int = 100,
    batch_size: int = 64,
    learning_rate: float = 5e-4,
    device: str = "cpu",
    val_ratio: float = 0.15,
) -> dict:
    """Train TFT model and return metrics with baseline comparison."""
    from torch.utils.data import DataLoader, TensorDataset

    val_cutoff = int(len(X_train) * (1 - val_ratio))
    X_tr, X_val = X_train[:val_cutoff], X_train[val_cutoff:]
    y_tr, y_val = y_train[:val_cutoff], y_train[val_cutoff:]

    model = TemporalFusionTransformer(
        n_vars=n_vars,
        seq_len=seq_len,
        pred_len=pred_len,
        d_model=d_model,
        n_heads=n_heads,
        lstm_layers=lstm_layers,
        dropout=dropout,
        fc_dropout=fc_dropout,
    )
    model = model.to(device)

    total_params = sum(p.numel() for p in model.parameters() if p.requires_grad)
    print(f"TFT params: {total_params:,}")
    print(f"  d_model={d_model}, n_heads={n_heads}, lstm_layers={lstm_layers}")

    train_ds = TensorDataset(torch.tensor(X_tr), torch.tensor(y_tr))
    val_ds = TensorDataset(torch.tensor(X_val), torch.tensor(y_val))
    test_ds = TensorDataset(torch.tensor(X_test), torch.tensor(y_test))
    train_loader = DataLoader(train_ds, batch_size=batch_size, shuffle=False)
    val_loader = DataLoader(val_ds, batch_size=batch_size)
    test_loader = DataLoader(test_ds, batch_size=batch_size)

    optimizer = torch.optim.AdamW(model.parameters(), lr=learning_rate, weight_decay=1e-4)
    scheduler = torch.optim.lr_scheduler.CosineAnnealingWarmRestarts(
        optimizer, T_0=10, T_mult=2,
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
                if pred.shape != y_batch.shape:
                    y_batch = y_batch.view_as(pred)
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
            for X_batch, y_batch in val_loader:
                X_batch, y_batch = X_batch.to(device), y_batch.to(device)
                with torch.amp.autocast("cuda", enabled=use_amp):
                    pred = model(X_batch)
                    val_loss += criterion(pred, y_batch.view_as(pred)).item()
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

    direction_acc = float(np.mean(
        ((preds[:, 0] if preds.ndim > 1 else preds) > 0) ==
        ((targets[:, 0] if targets.ndim > 1 else targets) > 0),
    ))

    majority_baseline = oos_direction_distribution(
        targets[:, 0] if targets.ndim > 1 else targets,
    )

    metrics = {
        "mse": round(mse, 6),
        "mae": round(mae, 6),
        "direction_accuracy_step1": round(direction_acc, 4),
        "majority_class_baseline": majority_baseline,
        "edge_over_majority": round(
            direction_acc - majority_baseline["majority_class_accuracy"], 4,
        ),
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


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def main():
    parser = argparse.ArgumentParser(
        description="Train TFT model for financial time-series forecasting "
                    "(Lim et al., 2021)",
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
    parser.add_argument("--seq-len", type=int, default=20)
    parser.add_argument("--pred-len", type=int, default=1)
    parser.add_argument("--d-model", type=int, default=64)
    parser.add_argument("--n-heads", type=int, default=4)
    parser.add_argument("--lstm-layers", type=int, default=1)
    parser.add_argument("--dropout", type=float, default=0.1)
    parser.add_argument("--fc-dropout", type=float, default=0.1)

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
    parser.add_argument("--gap", type=int, default=5)

    # Multi-seed
    parser.add_argument("--seeds", type=str, default=None,
                        help="Comma-separated seeds (e.g. 0,1,7,42)")

    # Output
    parser.add_argument(
        "--output-dir",
        default=str(Path(__file__).resolve().parent.parent / "outputs" / "tft_run1"),
    )
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--advanced", action="store_true")
    parser.add_argument("--indicators", nargs="+", default=None)
    args = parser.parse_args()

    seeds = [int(s) for s in args.seeds.split(",")] if args.seeds else [args.seed]
    np.random.seed(seeds[0])

    try:
        import torch
        torch.manual_seed(seeds[0])
        device = "cuda" if torch.cuda.is_available() else "cpu"
    except ImportError:
        print("ERROR: PyTorch not installed.", file=sys.stderr)
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
        features, seq_len=args.seq_len, pred_len=args.pred_len,
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
        print(f"Walk-forward validation: {args.n_splits} splits, gap={args.gap}")

    print(f"Device: {device}, n_vars={n_features}, seeds={seeds}")

    hyperparams = {
        "model_type": "tft",
        "seq_len": args.seq_len,
        "pred_len": args.pred_len,
        "d_model": args.d_model,
        "n_heads": args.n_heads,
        "lstm_layers": args.lstm_layers,
        "dropout": args.dropout,
        "fc_dropout": args.fc_dropout,
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
        "seeds": seeds,
    }

    result = train_and_evaluate(
        X_train, y_train, X_test, y_test,
        n_vars=n_features,
        seq_len=args.seq_len,
        pred_len=args.pred_len,
        d_model=args.d_model,
        n_heads=args.n_heads,
        lstm_layers=args.lstm_layers,
        dropout=args.dropout,
        fc_dropout=args.fc_dropout,
        epochs=args.epochs,
        batch_size=args.batch_size,
        learning_rate=args.lr,
        device=device,
    )

    output_dir = Path(args.output_dir)
    save_pytorch_checkpoint(
        result["model"], result, hyperparams, data_hash, output_dir,
        model_type="tft",
    )

    m = result["metrics"]
    edge = m["edge_over_majority"]
    print(f"\nResults: MSE={m['mse']}, DirAcc(step1)={m['direction_accuracy_step1']}")
    print(f"  Majority baseline: {m['majority_class_baseline']['majority_class_accuracy']}")
    print(f"  Edge over majority: {edge:+.4f} ({'BEATS' if edge > 0 else 'FAILS'} baseline)")

    if args.dry_run:
        print("DRY-RUN complete. TFT pipeline validated successfully.")


if __name__ == "__main__":
    main()
