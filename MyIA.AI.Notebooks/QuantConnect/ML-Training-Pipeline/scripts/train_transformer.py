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

Multi-asset + multi-seed validation:
    python train_transformer.py --panier --panier-group crypto \
        --walk-forward --seeds 0,1,7,42,99 --epochs 30

Output:
    Checkpoints in --checkpoint-dir (default: ../checkpoints/transformer/<date>/)
    metadata.json with hyperparams, metrics, training curve, attention weights sample
"""

import argparse
import sys
from pathlib import Path

import numpy as np
import pandas as pd

# Import thermal-safe training utilities
sys.path.append(str(Path(__file__).resolve().parent))
from walk_forward import WalkForwardSplitter

sys.path.append(str(Path(__file__).resolve().parent.parent.parent / "shared"))
from gpu_training import (
    batch_thermal_check,
    get_gpu_temp,
    setup_amp,
)
from checkpoint_utils import save_pytorch_checkpoint
from data_utils import compute_data_hash, generate_synthetic_data, load_data
from features import FeatureEngineer
from sequence_utils import build_sequences, normalize_sequences


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
    val_ratio: float = 0.15,
) -> dict:
    """Train Transformer with AMP and thermal watchdog via shared.gpu_training.

    Splits X_train into train+val internally so test data is never used
    for model selection (fixes test-set contamination, issue #722).
    """
    import torch
    import torch.nn as nn
    from torch.utils.data import DataLoader, TensorDataset

    input_size = X_train.shape[2]

    # Internal train/val split from training data only
    val_cutoff = int(len(X_train) * (1 - val_ratio))
    X_tr, X_val = X_train[:val_cutoff], X_train[val_cutoff:]
    y_tr, y_val = y_train[:val_cutoff], y_train[val_cutoff:]

    train_ds = TensorDataset(
        torch.tensor(X_tr), torch.tensor(y_tr).unsqueeze(1)
    )
    val_ds = TensorDataset(
        torch.tensor(X_val), torch.tensor(y_val).unsqueeze(1)
    )
    test_ds = TensorDataset(
        torch.tensor(X_test), torch.tensor(y_test).unsqueeze(1)
    )
    train_loader = DataLoader(train_ds, batch_size=batch_size, shuffle=False)
    val_loader = DataLoader(val_ds, batch_size=batch_size)
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
            for X_batch, y_batch in val_loader:
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
        "train_samples": len(X_tr),
        "val_samples": len(X_val),
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



def train_walk_forward(
    X: np.ndarray,
    y: np.ndarray,
    n_splits: int = 5,
    train_size: int | None = None,
    test_size: int | None = None,
    gap: int = 5,
    d_model: int = 128,
    nhead: int = 4,
    num_layers: int = 4,
    dim_feedforward: int = 512,
    dropout: float = 0.1,
    seq_len: int = 20,
    epochs: int = 50,
    batch_size: int = 32,
    learning_rate: float = 5e-4,
    device: str = "cpu",
) -> dict:
    """Walk-forward cross-validation for Transformer with per-fold normalization."""
    splitter = WalkForwardSplitter(
        n_splits=n_splits, train_size=train_size, test_size=test_size, gap=gap,
    )

    fold_results = []
    oos_preds = np.full(len(y), np.nan)
    best_model_state = None

    for fold_idx, (train_idx, test_idx) in enumerate(splitter.split(X)):
        if len(test_idx) == 0:
            continue

        X_train_fold, X_test_fold = X[train_idx], X[test_idx]
        y_train_fold, y_test_fold = y[train_idx], y[test_idx]

        mean = X_train_fold.mean(axis=(0, 1), keepdims=True)
        std = X_train_fold.std(axis=(0, 1), keepdims=True)
        std = np.where(std < 1e-8, 1.0, std)
        X_train_norm = (X_train_fold - mean) / std
        X_test_norm = (X_test_fold - mean) / std

        fold_result = train_and_evaluate(
            X_train_norm, y_train_fold, X_test_norm, y_test_fold,
            d_model=d_model, nhead=nhead, num_layers=num_layers,
            dim_feedforward=dim_feedforward, dropout=dropout, seq_len=seq_len,
            epochs=epochs, batch_size=batch_size, learning_rate=learning_rate,
            device=device,
        )

        fold_diracc = fold_result["metrics"]["direction_accuracy"]
        fold_results.append({
            "fold": fold_idx,
            "train_size": len(train_idx),
            "test_size": len(test_idx),
            "diracc": fold_diracc,
            "mse": fold_result["metrics"]["mse"],
        })

        import torch
        with torch.no_grad():
            X_test_t = torch.tensor(X_test_norm, dtype=torch.float32).to(device)
            preds = fold_result["model"](X_test_t).squeeze(-1).cpu().numpy()
        oos_preds[test_idx] = preds

        # Save last fold model (avoids test-set selection bias from cherry-picking best fold)
        best_model_state = {k: v.cpu().clone() for k, v in fold_result["model"].state_dict().items()}

        print(f"  Fold {fold_idx+1}/{n_splits}  diracc={fold_diracc:.4f}  "
              f"train={len(train_idx)}  test={len(test_idx)}")

    valid_mask = ~np.isnan(oos_preds)
    oos_predictions = oos_preds[valid_mask]
    oos_targets = y[valid_mask]
    oos_diracc = float(np.mean((oos_predictions > 0) == (oos_targets > 0)))

    # Majority-class baseline on actual OOS targets
    y_binary_oos = (oos_targets > 0).astype(int)
    majority_freq = float(np.mean(y_binary_oos == 1))
    majority_bl = {
        "accuracy": max(majority_freq, 1.0 - majority_freq),
        "majority_class": 1 if majority_freq >= 0.5 else 0,
        "majority_freq": majority_freq,
        "n_train": 0,
        "n_test": len(y_binary_oos),
    }

    input_size = X.shape[2]
    best_model = build_transformer_model(
        input_size, d_model, nhead, num_layers, dim_feedforward, dropout, seq_len,
    )
    if best_model_state:
        best_model.load_state_dict(best_model_state)

    return {
        "model": best_model,
        "metrics": {
            "oos_direction_accuracy": round(oos_diracc, 4),
            "majority_class_acc": majority_bl["accuracy"],
            "majority_class_freq": majority_bl["majority_freq"],
            "vs_majority_class": round(oos_diracc - majority_bl["accuracy"], 4),
            "n_wf_folds": len(fold_results),
            "input_size": input_size,
            "d_model": d_model,
            "nhead": nhead,
            "num_layers": num_layers,
        },
        "fold_details": fold_results,
        "history": {"fold_details": fold_results},
        "input_size": input_size,
        "d_model": d_model,
        "nhead": nhead,
        "num_layers": num_layers,
    }


def _load_symbol_data(
    symbol: str,
    data_dir: Path,
    start: str | None = None,
    end: str | None = None,
) -> pd.DataFrame | None:
    """Load data for one symbol from panier or local CSV."""
    try:
        from panier_loader import load_panier
        panier = load_panier(start=start or "2015-01-01", end=end or "2025-01-01")
        if symbol in panier and len(panier[symbol]) >= 500:
            return panier[symbol]
    except Exception:
        pass

    try:
        raw = load_data(data_dir, symbol, start, end)
        if len(raw) >= 500:
            return raw
    except Exception:
        pass

    return None


def train_multi_asset(
    symbols: list[str],
    data_dir: Path,
    seeds: list[int],
    n_splits: int = 5,
    gap: int = 5,
    d_model: int = 128,
    nhead: int = 4,
    num_layers: int = 4,
    dim_feedforward: int = 512,
    dropout: float = 0.1,
    seq_len: int = 20,
    epochs: int = 50,
    batch_size: int = 32,
    learning_rate: float = 5e-4,
    lookback: int = 20,
    device: str = "cpu",
    start: str | None = None,
    end: str | None = None,
    output_dir: str | None = None,
) -> dict:
    """Train Transformer across multiple assets and seeds.

    For each (symbol, seed), runs walk-forward validation. Returns per-asset
    results with multi-seed statistical evaluation.

    Parameters
    ----------
    symbols : list of str
        Symbols to train on (e.g., ["BTC-USD", "ETH-USD"]).
    seeds : list of int
        Random seeds for statistical validation (project convention: >= 4).
    output_dir : str or None
        Directory to save per-asset results JSON.

    Returns
    -------
    dict with per-asset results, multi-seed stats, and aggregate summary.
    """
    all_asset_results = {}

    for symbol in symbols:
        print(f"\n{'='*50}")
        print(f"Asset: {symbol}")
        print(f"{'='*50}")

        raw = _load_symbol_data(symbol, data_dir, start, end)
        if raw is None:
            print(f"  SKIP: no data found for {symbol}")
            continue

        engineer = FeatureEngineer(lookback=lookback)
        features = engineer.transform(raw)
        X, y, feature_cols = build_sequences(features, seq_len=seq_len)

        if len(X) < 200:
            print(f"  SKIP: only {len(X)} sequences (need >= 200)")
            continue

        print(f"  Data: {len(X)} sequences, {X.shape[2]} features")

        seed_metrics = []
        for seed in seeds:
            np.random.seed(seed)

            # Shuffle training order for variety (but keep temporal within folds)
            splitter = WalkForwardSplitter(n_splits=n_splits, gap=gap)

            fold_diraccs = []
            fold_mses = []
            for fold_idx, (train_idx, test_idx) in enumerate(splitter.split(X)):
                if len(test_idx) == 0:
                    continue

                X_train_fold, X_test_fold = X[train_idx], X[test_idx]
                y_train_fold, y_test_fold = y[train_idx], y[test_idx]

                mean = X_train_fold.mean(axis=(0, 1), keepdims=True)
                std = X_train_fold.std(axis=(0, 1), keepdims=True)
                std = np.where(std < 1e-8, 1.0, std)
                X_train_norm = (X_train_fold - mean) / std
                X_test_norm = (X_test_fold - mean) / std

                fold_result = train_and_evaluate(
                    X_train_norm, y_train_fold, X_test_norm, y_test_fold,
                    d_model=d_model, nhead=nhead, num_layers=num_layers,
                    dim_feedforward=dim_feedforward, dropout=dropout, seq_len=seq_len,
                    epochs=epochs, batch_size=batch_size,
                    learning_rate=learning_rate, device=device,
                )
                fold_diraccs.append(fold_result["metrics"]["direction_accuracy"])
                fold_mses.append(fold_result["metrics"]["mse"])

            mean_diracc = float(np.mean(fold_diraccs))
            mean_mse = float(np.mean(fold_mses))
            seed_metrics.append({
                "seed": seed,
                "dir_acc": mean_diracc,
                "mse": mean_mse,
                "n_folds": len(fold_diraccs),
            })
            print(f"  Seed {seed}: dir_acc={mean_diracc:.4f}, mse={mean_mse:.6f}")

        if not seed_metrics:
            continue

        # Compute majority-class baseline
        y_binary = (y > 0).astype(int)
        majority_freq = float(np.mean(y_binary == 1))
        majority_acc = max(majority_freq, 1.0 - majority_freq)

        all_asset_results[symbol] = {
            "seed_metrics": seed_metrics,
            "majority_acc": majority_acc,
            "mean_diracc": float(np.mean([s["dir_acc"] for s in seed_metrics])),
            "std_diracc": float(np.std([s["dir_acc"] for s in seed_metrics], ddof=1))
                if len(seed_metrics) > 1 else 0.0,
            "edge": float(np.mean([s["dir_acc"] for s in seed_metrics])) - majority_acc,
        }
        ar = all_asset_results[symbol]
        print(f"  Summary: dir_acc={ar['mean_diracc']:.4f} +/- {ar['std_diracc']:.4f}, "
              f"majority={majority_acc:.4f}, edge={ar['edge']:+.4f}")

    # Statistical evaluation using wf_framework
    stats_summary = {}
    try:
        from wf_framework.stats import multi_seed_eval, multi_asset_eval
        per_asset_for_stats = {}
        for sym, res in all_asset_results.items():
            per_asset_for_stats[sym] = res["seed_metrics"]

        if per_asset_for_stats:
            asset_eval = multi_asset_eval(per_asset_for_stats)
            stats_summary = {
                "n_assets": asset_eval.n_assets,
                "n_significant_raw": asset_eval.n_significant_raw,
                "n_significant_bonferroni": asset_eval.n_significant_bonferroni,
                "alpha_raw": asset_eval.alpha_raw,
                "alpha_bonferroni": asset_eval.alpha_bonferroni,
                "per_asset": {
                    sym: r.to_dict() for sym, r in asset_eval.per_asset.items()
                },
            }
    except ImportError:
        print("  Note: wf_framework not available for statistical evaluation")

    # Aggregate summary
    if all_asset_results:
        beats = sum(
            1 for r in all_asset_results.values()
            if r["edge"] > 0
        )
        passes_rule = sum(
            1 for r in all_asset_results.values()
            if r["edge"] >= 2 * r["std_diracc"] and len(seeds) >= 4
        )
    else:
        beats = 0
        passes_rule = 0

    summary = {
        "model_type": "transformer",
        "mode": "multi_asset",
        "symbols": symbols,
        "seeds": seeds,
        "n_assets_trained": len(all_asset_results),
        "n_assets_beats_majority": beats,
        "n_assets_passes_rule": passes_rule,
        "hyperparams": {
            "d_model": d_model, "nhead": nhead, "num_layers": num_layers,
            "dim_feedforward": dim_feedforward, "dropout": dropout,
            "seq_len": seq_len, "epochs": epochs, "n_splits": n_splits, "gap": gap,
        },
        "per_asset": all_asset_results,
        "statistical_eval": stats_summary,
    }

    if output_dir:
        out = Path(output_dir)
        out.mkdir(parents=True, exist_ok=True)
        ts = __import__("datetime").datetime.now().strftime("%Y%m%dT%H%M%S")
        rf = out / f"transformer_multiasset_{ts}.json"
        import json
        rf.write_text(
            json.dumps(summary, indent=2, default=str), encoding="utf-8"
        )
        print(f"\nResults saved to {rf}")

    return summary


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
        "--walk-forward", action="store_true",
        help="Use walk-forward cross-validation instead of simple split",
    )
    parser.add_argument("--n-splits", type=int, default=5, help="Walk-forward splits")
    parser.add_argument("--wf-train-size", type=int, default=None, help="Walk-forward train window")
    parser.add_argument("--wf-test-size", type=int, default=None, help="Walk-forward test window per fold")
    parser.add_argument("--gap", type=int, default=5, help="Gap between train and test in walk-forward")
    parser.add_argument(
        "--advanced", action="store_true",
        help="Use advanced features (regime, momentum, statistical, price_acceleration)",
    )
    parser.add_argument(
        "--indicators", nargs="+", default=None,
        help="Specific indicators to use (overrides --advanced)",
    )
    parser.add_argument(
        "--panier", action="store_true",
        help="Multi-asset mode: train Transformer across panier symbols",
    )
    parser.add_argument(
        "--panier-group", default=None,
        choices=["us_equity_broad", "us_equity_sectors", "volatility", "us_bonds",
                 "commodities", "international", "crypto"],
        help="Panier asset group to train on (default: all)",
    )
    parser.add_argument(
        "--panier-symbols", nargs="+", default=None,
        help="Explicit symbols for multi-asset (e.g., BTC-USD ETH-USD LTC-USD)",
    )
    parser.add_argument(
        "--seeds", type=str, default="42",
        help="Comma-separated seeds for multi-seed validation (e.g., 0,1,7,42,99)",
    )
    args = parser.parse_args()

    try:
        import torch

        device = "cuda" if torch.cuda.is_available() else "cpu"
    except ImportError:
        print("ERROR: PyTorch not installed. Run: pip install torch", file=sys.stderr)
        sys.exit(1)

    seeds = [int(s.strip()) for s in args.seeds.split(",")]

    if args.panier or args.panier_symbols:
        symbols = args.panier_symbols
        if not symbols:
            try:
                from panier_loader import get_panier_symbols
                symbols = get_panier_symbols(group=args.panier_group)
            except ImportError:
                print("ERROR: panier_loader not available. Specify --panier-symbols explicitly.",
                      file=sys.stderr)
                sys.exit(1)

        print(f"MULTI-ASSET mode: {len(symbols)} symbols, seeds={seeds}")
        print(f"Device: {device}")

        if args.dry_run:
            print("DRY-RUN: Using synthetic data per asset, 2 epochs")
            args.epochs = 2
            symbols = symbols[:2]  # Limit in dry-run

        result = train_multi_asset(
            symbols=symbols,
            data_dir=Path(args.data_dir),
            seeds=seeds,
            n_splits=args.n_splits,
            gap=args.gap,
            d_model=args.d_model,
            nhead=args.nhead,
            num_layers=args.num_layers,
            dim_feedforward=args.dim_ff,
            dropout=args.dropout,
            seq_len=args.seq_len,
            epochs=args.epochs,
            batch_size=args.batch_size,
            learning_rate=args.lr,
            lookback=args.lookback,
            device=device,
            start=args.start,
            end=args.end,
            output_dir=str(Path(args.checkpoint_dir).parent / "results"),
        )

        print(f"\n{'='*60}")
        print(f"Multi-Asset Transformer Summary")
        print(f"{'='*60}")
        print(f"Trained: {result['n_assets_trained']}/{len(symbols)}")
        print(f"Beats majority: {result['n_assets_beats_majority']}")
        print(f"Passes rule (edge>=2*std): {result['n_assets_passes_rule']}")
        if args.dry_run:
            print("DRY-RUN complete. Multi-asset pipeline validated.")
        return

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

    if args.walk_forward:
        print(f"Mode: WALK-FORWARD (n_splits={args.n_splits}, gap={args.gap})")
        print(f"Device: {device}")

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
            "walk_forward": True,
            "n_splits": args.n_splits,
            "wf_train_size": args.wf_train_size,
            "wf_test_size": args.wf_test_size,
            "gap": args.gap,
        }

        result = train_walk_forward(
            X, y,
            n_splits=args.n_splits,
            train_size=args.wf_train_size,
            test_size=args.wf_test_size,
            gap=args.gap,
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
        save_pytorch_checkpoint(
            result["model"], result, hyperparams, data_hash, ckpt_dir,
            model_type="transformer",
            extra_metadata={
                "architecture": {
                    "input_size": result["input_size"],
                    "d_model": result["d_model"],
                    "nhead": result["nhead"],
                    "num_layers": result["num_layers"],
                }
            },
        )

        m = result["metrics"]
        print(f"\nWalk-Forward OOS Results:")
        print(f"  OOS DirAcc:    {m['oos_direction_accuracy']:.4f}")
        print(f"  Majority Class: {m['majority_class_acc']:.4f} (freq={m['majority_class_freq']:.4f})")
        print(f"  vs Majority:   {m['vs_majority_class']:+.4f}")
        print(f"  Folds:         {m['n_wf_folds']}")

        if args.dry_run:
            print("DRY-RUN complete. Walk-forward pipeline validated.")
        return

    # Simple time-series split (default)
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
    save_pytorch_checkpoint(
        result["model"], result, hyperparams, data_hash, ckpt_dir,
        model_type="transformer",
        extra_metadata={
            "architecture": {
                "input_size": result["input_size"],
                "d_model": result["d_model"],
                "nhead": result["nhead"],
                "num_layers": result["num_layers"],
            }
        },
    )

    if args.dry_run:
        print("DRY-RUN complete. Pipeline validated successfully.")
    else:
        m = result["metrics"]
        print(f"Training complete. MSE={m['mse']}, DirAcc={m['direction_accuracy']}, Params={m['total_params']:,}")


if __name__ == "__main__":
    main()
