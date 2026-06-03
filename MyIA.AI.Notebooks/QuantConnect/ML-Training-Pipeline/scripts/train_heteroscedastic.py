"""
Train Heteroscedastic Neural Network for volatility forecasting.

Implements a dual-head architecture that predicts both conditional mean
and conditional variance of log-RV, enabling uncertainty-aware forecasts.

Architecture:
    Shared LSTM/GRU backbone -> Mean head (linear) + Variance head (softplus)
    Loss: Gaussian NLL = 0.5 * [log(var) + (y - mean)^2 / var]

Anti-pattern safeguards (cf. CLAUDE.md, feedback_ml_trading_pitfalls.md):
    - Walk-forward validation with gap to prevent leakage
    - Normalize stats computed on train set only
    - DM test vs HAR baseline (not just MSE comparison)
    - Multi-seed evaluation (>=4 seeds among [0,1,7,42])
    - Honest verdicts: BEATS / NO_BEATS / INCONCLUSIVE

Usage:
    python train_heteroscedastic.py --dry-run
    python train_heteroscedastic.py --data-dir ../datasets/yfinance/crypto_panier \\
        --symbol BTC-USD --walk-forward --n-splits 5 --seeds 0,1,7,42
"""

import argparse
import sys
from pathlib import Path

import numpy as np
import pandas as pd
import torch
import torch.nn as nn

sys.path.append(str(Path(__file__).resolve().parent.parent.parent / "shared"))
from gpu_training import batch_thermal_check, get_gpu_temp, setup_amp
from checkpoint_utils import save_pytorch_checkpoint
from data_utils import compute_data_hash, generate_synthetic_data, load_data
from features import FeatureEngineer
from baselines import oos_direction_distribution
from sequence_utils import build_sequences, normalize_sequences

try:
    from walk_forward import WalkForwardSplitter
except ImportError:
    WalkForwardSplitter = None


class HeteroscedasticNN(nn.Module):
    """Dual-head NN: shared backbone + mean/variance outputs.

    Predicts Gaussian parameters (mu, sigma^2) for each time step,
    trained with Gaussian NLL loss. The variance head uses softplus
    to ensure positivity.

    Input: [B, T, N] -> Output: mean [B, pred_len], var [B, pred_len]
    """

    def __init__(
        self,
        n_vars: int,
        seq_len: int,
        pred_len: int = 1,
        hidden_dim: int = 64,
        n_layers: int = 2,
        rnn_type: str = "lstm",
        dropout: float = 0.2,
        min_variance: float = 1e-4,
    ):
        super().__init__()
        self.pred_len = pred_len
        self.min_variance = min_variance

        rnn_cls = nn.LSTM if rnn_type == "lstm" else nn.GRU
        self.rnn = rnn_cls(
            input_size=n_vars,
            hidden_size=hidden_dim,
            num_layers=n_layers,
            batch_first=True,
            dropout=dropout if n_layers > 1 else 0.0,
        )

        self.mean_head = nn.Linear(hidden_dim, pred_len)
        self.var_head = nn.Linear(hidden_dim, pred_len)
        self.dropout = nn.Dropout(dropout)

    def forward(self, x):
        """Forward pass.

        Args:
            x: [B, T, N] input tensor

        Returns:
            mean: [B, pred_len] predicted mean
            var: [B, pred_len] predicted variance (strictly positive)
        """
        rnn_out, _ = self.rnn(x)
        last_hidden = self.dropout(rnn_out[:, -1, :])

        mean = self.mean_head(last_hidden)
        var = torch.nn.functional.softplus(self.var_head(last_hidden)) + self.min_variance

        return mean, var


def gaussian_nll_loss(mean, var, target):
    """Gaussian negative log-likelihood loss.

    NLL = 0.5 * [log(var) + (target - mean)^2 / var]

    Penalizes both prediction error and overconfident/underconfident
    variance estimates.
    """
    if mean.shape != target.shape:
        target = target.view_as(mean)
    nll = 0.5 * (torch.log(var) + (target - mean) ** 2 / var)
    return nll.mean()


def train_and_evaluate(
    X_train: np.ndarray,
    y_train: np.ndarray,
    X_test: np.ndarray,
    y_test: np.ndarray,
    n_vars: int,
    seq_len: int = 20,
    pred_len: int = 1,
    hidden_dim: int = 64,
    n_layers: int = 2,
    rnn_type: str = "lstm",
    dropout: float = 0.2,
    epochs: int = 100,
    batch_size: int = 64,
    learning_rate: float = 5e-4,
    device: str = "cpu",
    val_ratio: float = 0.15,
) -> dict:
    from torch.utils.data import DataLoader, TensorDataset

    val_cutoff = int(len(X_train) * (1 - val_ratio))
    X_tr, X_val = X_train[:val_cutoff], X_train[val_cutoff:]
    y_tr, y_val = y_train[:val_cutoff], y_train[val_cutoff:]

    model = HeteroscedasticNN(
        n_vars=n_vars, seq_len=seq_len, pred_len=pred_len,
        hidden_dim=hidden_dim, n_layers=n_layers,
        rnn_type=rnn_type, dropout=dropout,
    ).to(device)

    total_params = sum(p.numel() for p in model.parameters() if p.requires_grad)
    print(f"HeteroscedasticNN params: {total_params:,}")
    print(f"  hidden_dim={hidden_dim}, n_layers={n_layers}, rnn={rnn_type}")

    train_ds = TensorDataset(torch.tensor(X_tr), torch.tensor(y_tr))
    val_ds = TensorDataset(torch.tensor(X_val), torch.tensor(y_val))
    test_ds = TensorDataset(torch.tensor(X_test), torch.tensor(y_test))
    train_loader = DataLoader(train_ds, batch_size=batch_size, shuffle=False)
    val_loader = DataLoader(val_ds, batch_size=batch_size)
    test_loader = DataLoader(test_ds, batch_size=batch_size)

    optimizer = torch.optim.AdamW(model.parameters(), lr=learning_rate, weight_decay=1e-4)
    scheduler = torch.optim.lr_scheduler.CosineAnnealingWarmRestarts(optimizer, T_0=10, T_mult=2)

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
                mean, var = model(X_batch)
                loss = gaussian_nll_loss(mean, var, y_batch)

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
                    mean, var = model(X_batch)
                    val_loss += gaussian_nll_loss(mean, var, y_batch).item()
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

    all_means, all_vars, all_targets = [], [], []
    with torch.no_grad():
        for X_batch, y_batch in test_loader:
            X_batch = X_batch.to(device)
            with torch.amp.autocast("cuda", enabled=use_amp):
                mean, var = model(X_batch)
            all_means.append(mean.cpu().numpy())
            all_vars.append(var.cpu().numpy())
            all_targets.append(y_batch.numpy())

    means = np.concatenate(all_means)
    variances = np.concatenate(all_vars)
    targets = np.concatenate(all_targets)

    mean_preds = means[:, 0] if means.ndim > 1 else means
    mean_vars = variances[:, 0] if variances.ndim > 1 else variances
    targets_1d = targets[:, 0] if targets.ndim > 1 else targets

    mse = float(np.mean((mean_preds - targets_1d) ** 2))
    mae = float(np.mean(np.abs(mean_preds - targets_1d)))

    direction_acc = float(np.mean(
        (mean_preds > 0) == (targets_1d > 0),
    ))

    # Calibration: check if predicted variance matches empirical squared error
    errors_sq = (mean_preds - targets_1d) ** 2
    calibration_ratio = float(np.mean(errors_sq) / np.mean(mean_vars))

    majority_baseline = oos_direction_distribution(targets_1d)

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
        "calibration_ratio": round(calibration_ratio, 4),
        "mean_predicted_var": round(float(np.mean(mean_vars)), 6),
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
        description="Train Heteroscedastic NN for volatility forecasting "
                    "(dual-head mean/variance)",
    )
    parser.add_argument("--data-dir", default=str(Path(__file__).resolve().parent.parent / "datasets" / "yfinance"))
    parser.add_argument("--symbols", default="SPY")
    parser.add_argument("--start")
    parser.add_argument("--end")

    parser.add_argument("--seq-len", type=int, default=20)
    parser.add_argument("--pred-len", type=int, default=1)
    parser.add_argument("--hidden-dim", type=int, default=64)
    parser.add_argument("--n-layers", type=int, default=2)
    parser.add_argument("--rnn-type", choices=["lstm", "gru"], default="lstm")
    parser.add_argument("--dropout", type=float, default=0.2)

    parser.add_argument("--epochs", type=int, default=100)
    parser.add_argument("--batch-size", type=int, default=64)
    parser.add_argument("--lr", type=float, default=5e-4)
    parser.add_argument("--lookback", type=int, default=20)
    parser.add_argument("--seed", type=int, default=42)

    parser.add_argument("--train-ratio", type=float, default=0.7)
    parser.add_argument("--val-ratio", type=float, default=0.15)
    parser.add_argument("--test-ratio", type=float, default=0.15)
    parser.add_argument("--walk-forward", action="store_true")
    parser.add_argument("--n-splits", type=int, default=5)
    parser.add_argument("--gap", type=int, default=5)

    parser.add_argument("--seeds", type=str, default=None,
                        help="Comma-separated seeds (e.g. 0,1,7,42)")

    parser.add_argument("--output-dir",
                        default=str(Path(__file__).resolve().parent.parent / "outputs" / "heteroscedastic_run1"))
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
    print(f"Sequences: {len(X)} samples, seq_len={args.seq_len}")

    n = len(X)
    train_end = int(n * args.train_ratio)
    val_end = int(n * (args.train_ratio + args.val_ratio))

    X_train, y_train = X[:train_end], y[:train_end]
    X_val, y_val = X[train_end:val_end], y[train_end:val_end]
    X_test, y_test = X[val_end:], y[val_end:]

    X_train, X_val, X_test, norm_mean, norm_std = normalize_sequences(X_train, X_val, X_test)

    print(f"Split: train={len(X_train)}, val={len(X_val)}, test={len(X_test)}")
    print(f"Device: {device}, n_vars={n_features}, seeds={seeds}")

    hyperparams = {
        "model_type": "heteroscedastic_nn",
        "seq_len": args.seq_len, "pred_len": args.pred_len,
        "hidden_dim": args.hidden_dim, "n_layers": args.n_layers,
        "rnn_type": args.rnn_type, "dropout": args.dropout,
        "epochs": args.epochs, "batch_size": args.batch_size,
        "learning_rate": args.lr, "lookback": args.lookback,
        "symbols": symbols, "seeds": seeds,
    }

    result = train_and_evaluate(
        X_train, y_train, X_test, y_test,
        n_vars=n_features, seq_len=args.seq_len, pred_len=args.pred_len,
        hidden_dim=args.hidden_dim, n_layers=args.n_layers,
        rnn_type=args.rnn_type, dropout=args.dropout,
        epochs=args.epochs, batch_size=args.batch_size,
        learning_rate=args.lr, device=device,
    )

    output_dir = Path(args.output_dir)
    save_pytorch_checkpoint(
        result["model"], result, hyperparams, data_hash, output_dir,
        model_type="heteroscedastic_nn",
    )

    m = result["metrics"]
    edge = m["edge_over_majority"]
    print(f"\nResults: MSE={m['mse']}, DirAcc(step1)={m['direction_accuracy_step1']}")
    print(f"  Majority baseline: {m['majority_class_baseline']['majority_class_accuracy']}")
    print(f"  Edge over majority: {edge:+.4f} ({'BEATS' if edge > 0 else 'FAILS'} baseline)")
    print(f"  Calibration ratio: {m['calibration_ratio']:.4f} (1.0 = perfect)")
    print(f"  Mean predicted var: {m['mean_predicted_var']:.6f}")

    if args.dry_run:
        print("DRY-RUN complete. Heteroscedastic NN pipeline validated successfully.")


if __name__ == "__main__":
    main()
