"""
Volatility regime classification via LSTM (Epic NN #754, Mission #779 Pivot).

3-state classifier (low/medium/high volatility regime) using LSTM h=64.
Aligned with research findings from docs/research/dl_predictability_finance_2026.md:
    - DL strength in finance is modeling variance, not direction mean
    - Regime transitions detected 2-3 days ahead (Chatzis et al. 2018)

Multi-asset features: returns, rolling vol, RSI, ATR across crypto panier.
Walk-forward 5-fold, multi-seed (>=4 seeds, accuracy edge >= 2*std for BEATS).

Thermal protocol: batch size 32 max, h=64 max, runs <2h, cool-down if T>80C.

Usage:
    python train_volatility_regime.py --walk-forward --seeds 0,1,7,42,99 --epochs 100
    python train_volatility_regime.py --walk-forward --model lstm --hidden-dim 64
    python train_volatility_regime.py --dry-run --epochs 5

References:
    - Chatzis et al. 2018 (Expert Systems with Applications 108)
    - Hands-On AI Trading with Python, Pik et al., Wiley 2025
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from datetime import datetime
from pathlib import Path

import numpy as np
import pandas as pd

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))
sys.path.insert(0, str(SCRIPT_DIR.parent.parent / "shared"))

from data_sources import fetch_data
from walk_forward import WalkForwardSplitter

RESULTS_DIR = SCRIPT_DIR.parent / "outputs" / "volatility_regime"
RESULTS_DIR.mkdir(parents=True, exist_ok=True)

CRYPTO_PANIER = ["BTC-USD", "ETH-USD", "LTC-USD", "XRP-USD", "ADA-USD",
                 "LINK-USD", "SOL-USD", "MATIC-USD", "AVAX-USD", "DOT-USD"]
DEFAULT_SEEDS = [0, 1, 7, 42, 99]
DATA_START = "2020-01-01"

REGIME_LABELS = {0: "low", 1: "medium", 2: "high"}
N_REGIMES = 3


# ---------------------------------------------------------------------------
# Technical indicators
# ---------------------------------------------------------------------------

def compute_rsi(series: pd.Series, period: int = 14) -> pd.Series:
    delta = series.diff()
    gain = delta.where(delta > 0, 0.0).rolling(period).mean()
    loss = (-delta.where(delta < 0, 0.0)).rolling(period).mean()
    rs = gain / loss.replace(0, 1e-10)
    return 100 - (100 / (1 + rs))


def compute_atr(high: pd.Series, low: pd.Series, close: pd.Series, period: int = 14) -> pd.Series:
    tr = pd.concat([
        high - low,
        (high - close.shift(1)).abs(),
        (low - close.shift(1)).abs(),
    ], axis=1).max(axis=1)
    return tr.rolling(period).mean()


# ---------------------------------------------------------------------------
# Data loading & feature engineering
# ---------------------------------------------------------------------------

def load_multi_asset_features(
    symbols: list[str],
    start: str = DATA_START,
    lookback: int = 20,
) -> tuple[pd.DataFrame, pd.DataFrame]:
    """Load multi-asset features and regime labels.

    Returns
    -------
    features : DataFrame (T, n_features)
    regime_labels : Series (T,) with values 0=low, 1=medium, 2=high
    """
    all_features = {}
    rv_series_list = []

    for sym in symbols:
        df = fetch_data(sym, start=start)
        if df is None or df.empty or len(df) < 100:
            continue

        close = df["Close"].sort_index()
        close = close[~close.index.duplicated(keep="first")]
        # Strip timezone to avoid tz-aware vs tz-naive join errors (yfinance issue)
        if hasattr(close.index, "tz") and close.index.tz is not None:
            close.index = close.index.tz_localize(None)
        high = df.get("High", close)
        low = df.get("Low", close)
        if isinstance(high, pd.DataFrame):
            high = high.iloc[:, 0]
        if isinstance(low, pd.DataFrame):
            low = low.iloc[:, 0]
        high = high.sort_index()
        low = low.sort_index()
        if hasattr(high.index, "tz") and high.index.tz is not None:
            high.index = high.index.tz_localize(None)
        if hasattr(low.index, "tz") and low.index.tz is not None:
            low.index = low.index.tz_localize(None)

        prefix = sym.replace("-USD", "").lower()

        ret = np.log(close / close.shift(1))
        vol_20 = ret.rolling(lookback).std()
        rsi = compute_rsi(close)
        atr = compute_atr(high, low, close)

        all_features[f"{prefix}_ret"] = ret
        all_features[f"{prefix}_vol20"] = vol_20
        all_features[f"{prefix}_rsi"] = rsi
        all_features[f"{prefix}_atr"] = atr

        rv_series_list.append(ret.pow(2).rolling(lookback).sum())

    features = pd.DataFrame(all_features).dropna(how="all")

    # Aggregate realized volatility across panier (mean)
    rv_df = pd.DataFrame(rv_series_list).T
    panier_rv = rv_df.mean(axis=1)

    # Regime labels via rolling quantiles (terciles)
    q_low = panier_rv.rolling(252, min_periods=60).quantile(0.33)
    q_high = panier_rv.rolling(252, min_periods=60).quantile(0.67)
    regime = pd.Series(1, index=panier_rv.index, dtype=int)
    regime[panier_rv <= q_low] = 0
    regime[panier_rv >= q_high] = 2

    # Align features and labels
    features = features.dropna()
    regime = regime.reindex(features.index).dropna()
    features = features.loc[regime.index]

    return features, regime


def build_sequences(
    features: np.ndarray,
    labels: np.ndarray,
    lookback: int = 20,
) -> tuple[np.ndarray, np.ndarray]:
    """Build sliding window sequences for LSTM.

    Returns X (N, lookback, F), y (N,)
    """
    X, y = [], []
    for i in range(lookback, len(features)):
        X.append(features[i - lookback:i])
        y.append(labels[i])
    return np.array(X, dtype=np.float32), np.array(y, dtype=np.int64)


# ---------------------------------------------------------------------------
# LSTM regime classifier
# ---------------------------------------------------------------------------

def create_regime_lstm(
    input_dim: int,
    hidden_dim: int = 64,
    num_layers: int = 2,
    dropout: float = 0.3,
) -> "torch.nn.Module":
    import torch
    import torch.nn as nn

    class RegimeLSTM(nn.Module):
        def __init__(self, input_dim, hidden_dim, num_layers, dropout):
            super().__init__()
            self.lstm = nn.LSTM(
                input_dim, hidden_dim, num_layers,
                batch_first=True,
                dropout=dropout if num_layers > 1 else 0,
            )
            self.classifier = nn.Sequential(
                nn.Linear(hidden_dim, 32),
                nn.ReLU(),
                nn.Dropout(dropout),
                nn.Linear(32, N_REGIMES),
            )

        def forward(self, x):
            lstm_out, _ = self.lstm(x)
            return self.classifier(lstm_out[:, -1, :])

    return RegimeLSTM(input_dim, hidden_dim, num_layers, dropout)


# ---------------------------------------------------------------------------
# Training with thermal protocol
# ---------------------------------------------------------------------------

def train_and_evaluate_fold(
    X_train: np.ndarray, y_train: np.ndarray,
    X_val: np.ndarray, y_val: np.ndarray,
    X_test: np.ndarray, y_test: np.ndarray,
    seed: int,
    hidden_dim: int = 64,
    num_layers: int = 2,
    dropout: float = 0.3,
    lr: float = 1e-3,
    epochs: int = 100,
    batch_size: int = 32,
    patience: int = 15,
    device: str = "cpu",
) -> dict:
    """Train regime classifier on one fold, return metrics."""
    import torch
    import torch.nn as nn
    from torch.utils.data import DataLoader, TensorDataset

    torch.manual_seed(seed)
    np.random.seed(seed)

    input_dim = X_train.shape[2]
    model = create_regime_lstm(input_dim, hidden_dim, num_layers, dropout)
    model = model.to(device)

    criterion = nn.CrossEntropyLoss()
    optimizer = torch.optim.Adam(model.parameters(), lr=lr, weight_decay=1e-5)
    scheduler = torch.optim.lr_scheduler.CosineAnnealingWarmRestarts(optimizer, T_0=10)

    train_ds = TensorDataset(
        torch.tensor(X_train, dtype=torch.float32),
        torch.tensor(y_train, dtype=torch.int64),
    )
    val_ds = TensorDataset(
        torch.tensor(X_val, dtype=torch.float32),
        torch.tensor(y_val, dtype=torch.int64),
    )
    train_loader = DataLoader(train_ds, batch_size=batch_size, shuffle=True)
    val_loader = DataLoader(val_ds, batch_size=batch_size)

    best_val_loss = float("inf")
    best_state = None
    patience_counter = 0

    for epoch in range(epochs):
        model.train()
        for X_batch, y_batch in train_loader:
            X_batch, y_batch = X_batch.to(device), y_batch.to(device)
            optimizer.zero_grad()
            logits = model(X_batch)
            loss = criterion(logits, y_batch)
            loss.backward()
            torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
            optimizer.step()
        scheduler.step()

        model.eval()
        val_loss = 0
        with torch.no_grad():
            for X_batch, y_batch in val_loader:
                X_batch, y_batch = X_batch.to(device), y_batch.to(device)
                val_loss += criterion(model(X_batch), y_batch).item() * len(X_batch)
        val_loss /= len(val_ds)

        if val_loss < best_val_loss:
            best_val_loss = val_loss
            best_state = {k: v.cpu().clone() for k, v in model.state_dict().items()}
            patience_counter = 0
        else:
            patience_counter += 1

        if patience_counter >= patience:
            break

    # Evaluate on test
    model.load_state_dict(best_state)
    model.eval()
    with torch.no_grad():
        logits = model(torch.tensor(X_test, dtype=torch.float32).to(device))
        preds = logits.argmax(dim=1).cpu().numpy()

    accuracy = (preds == y_test).mean()
    total_params = sum(p.numel() for p in model.parameters())

    # Per-class accuracy
    per_class_acc = {}
    for c in range(N_REGIMES):
        mask = y_test == c
        if mask.sum() > 0:
            per_class_acc[REGIME_LABELS[c]] = float((preds[mask] == c).mean())

    # Majority class baseline
    class_counts = np.bincount(y_test, minlength=N_REGIMES)
    majority_class = class_counts.argmax()
    majority_acc = float(class_counts[majority_class] / len(y_test))
    edge_over_majority = accuracy - majority_acc

    return {
        "accuracy": float(accuracy),
        "majority_class_baseline": float(majority_acc),
        "majority_class": int(majority_class),
        "edge_over_majority": float(edge_over_majority),
        "per_class_accuracy": per_class_acc,
        "class_distribution": {REGIME_LABELS[i]: int(c) for i, c in enumerate(class_counts)},
        "best_val_loss": float(best_val_loss),
        "total_params": total_params,
        "epochs_trained": epoch + 1,
    }


# ---------------------------------------------------------------------------
# Walk-forward multi-seed runner
# ---------------------------------------------------------------------------

def run_walk_forward_multiseed(
    features: pd.DataFrame,
    regime: pd.Series,
    seeds: list[int],
    n_splits: int = 5,
    gap: int = 10,
    lookback: int = 20,
    hidden_dim: int = 64,
    num_layers: int = 2,
    dropout: float = 0.3,
    lr: float = 1e-3,
    epochs: int = 100,
    batch_size: int = 32,
    device: str = "cpu",
    test_size: int = 126,
) -> dict:
    """Walk-forward multi-seed regime classification."""
    feat_values = features.values.astype(np.float32)
    label_values = regime.values.astype(np.int64)

    X_all, y_all = build_sequences(feat_values, label_values, lookback)
    n_samples = len(X_all)

    splitter = WalkForwardSplitter(n_splits=n_splits, gap=gap, test_size=test_size)
    all_indices = np.arange(n_samples)

    per_seed_results = []

    for seed in seeds:
        print(f"\n  Seed {seed} — walk-forward {n_splits}-fold")
        fold_results = []

        for fold_idx, (train_idx, test_idx) in enumerate(splitter.split(all_indices)):
            # Validation from last 15% of train
            val_size = max(1, int(len(train_idx) * 0.15))
            val_idx = train_idx[-val_size:]
            train_idx_inner = train_idx[:-val_size]

            if len(train_idx_inner) < 100 or len(test_idx) < 30:
                continue

            X_train, y_train = X_all[train_idx_inner], y_all[train_idx_inner]
            X_val, y_val = X_all[val_idx], y_all[val_idx]
            X_test, y_test = X_all[test_idx], y_all[test_idx]

            # Normalize using train stats only
            mean = X_train.mean(axis=(0, 1), keepdims=True)
            std = X_train.std(axis=(0, 1), keepdims=True)
            std = np.where(std < 1e-8, 1.0, std)
            X_train_n = (X_train - mean) / std
            X_val_n = (X_val - mean) / std
            X_test_n = (X_test - mean) / std

            metrics = train_and_evaluate_fold(
                X_train_n, y_train, X_val_n, y_val, X_test_n, y_test,
                seed=seed, hidden_dim=hidden_dim, num_layers=num_layers,
                dropout=dropout, lr=lr, epochs=epochs, batch_size=batch_size,
                device=device,
            )
            metrics["fold"] = fold_idx
            metrics["train_size"] = len(X_train)
            metrics["test_size"] = len(X_test)
            fold_results.append(metrics)

            print(f"    Fold {fold_idx}: acc={metrics['accuracy']:.4f} "
                  f"edge={metrics['edge_over_majority']:+.4f}")

        if not fold_results:
            continue

        mean_acc = np.mean([f["accuracy"] for f in fold_results])
        mean_edge = np.mean([f["edge_over_majority"] for f in fold_results])

        per_seed_results.append({
            "seed": seed,
            "folds": fold_results,
            "mean_dir_acc": float(mean_acc),
            "mean_edge": float(mean_edge),
        })

    if not per_seed_results:
        return {"status": "FAILED", "reason": "no valid folds"}

    # Cross-seed aggregation
    cross_seed_acc = np.mean([s["mean_dir_acc"] for s in per_seed_results])
    cross_seed_acc_std = np.std([s["mean_dir_acc"] for s in per_seed_results])
    cross_seed_edge = np.mean([s["mean_edge"] for s in per_seed_results])
    cross_seed_edge_std = np.std([s["mean_edge"] for s in per_seed_results])

    beats = cross_seed_edge >= 2 * cross_seed_edge_std

    result = {
        "model_type": "regime_lstm",
        "hidden_dim": hidden_dim,
        "n_seeds": len(per_seed_results),
        "seeds": seeds,
        "n_splits": n_splits,
        "gap": gap,
        "lookback": lookback,
        "epochs": epochs,
        "walk_forward": True,
        "cross_seed_mean_accuracy": round(float(cross_seed_acc), 6),
        "cross_seed_std_accuracy": round(float(cross_seed_acc_std), 6),
        "cross_seed_mean_edge": round(float(cross_seed_edge), 6),
        "cross_seed_std_edge": round(float(cross_seed_edge_std), 6),
        "beats_claim": bool(beats),
        "beats_criterion": f"mean_edge({cross_seed_edge:.4f}) >= 2*std_edge({2*cross_seed_edge_std:.4f})",
        "per_seed": per_seed_results,
        "timestamp": datetime.now().isoformat(),
        "n_features": features.shape[1],
        "n_samples": len(features),
    }

    return result


# ---------------------------------------------------------------------------
# Dry-run with synthetic data
# ---------------------------------------------------------------------------

def run_dry_run(epochs: int = 5, **kwargs) -> dict:
    """Quick validation with synthetic data."""
    np.random.seed(42)
    n_samples = 500
    n_features = 12

    features = pd.DataFrame(
        np.random.randn(n_samples, n_features).astype(np.float32),
        columns=[f"feat_{i}" for i in range(n_features)],
    )
    rv = features.iloc[:, 0].pow(2).rolling(20).mean().fillna(0)
    regime = pd.cut(rv, bins=3, labels=[0, 1, 2]).astype(int)
    features = features.loc[regime.index]

    return run_walk_forward_multiseed(
        features, regime,
        seeds=[0, 1],
        n_splits=2,
        lookback=10,
        epochs=epochs,
        batch_size=16,
        device="cpu",
        **kwargs,
    )


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def parse_args():
    parser = argparse.ArgumentParser(description="Volatility regime classifier LSTM")
    parser.add_argument("--walk-forward", action="store_true", help="Walk-forward validation")
    parser.add_argument("--dry-run", action="store_true", help="Synthetic data quick test")
    parser.add_argument("--seeds", type=str, default="0,1,7,42,99",
                        help="Comma-separated seeds")
    parser.add_argument("--n-splits", type=int, default=5, help="Walk-forward folds")
    parser.add_argument("--gap", type=int, default=10, help="Gap between train/test")
    parser.add_argument("--lookback", type=int, default=20, help="Sequence lookback")
    parser.add_argument("--hidden-dim", type=int, default=64, help="LSTM hidden dim")
    parser.add_argument("--num-layers", type=int, default=2, help="LSTM layers")
    parser.add_argument("--dropout", type=float, default=0.3, help="Dropout rate")
    parser.add_argument("--lr", type=float, default=1e-3, help="Learning rate")
    parser.add_argument("--epochs", type=int, default=100, help="Max epochs")
    parser.add_argument("--batch-size", type=int, default=32, help="Batch size (max 32 thermal)")
    parser.add_argument("--test-size", type=int, default=126, help="Walk-forward test set size")
    parser.add_argument("--device", type=str, default="auto", help="Device")
    parser.add_argument("--output-dir", type=str, default=None, help="Output directory")
    return parser.parse_args()


def main():
    args = parse_args()

    if args.device == "auto":
        import torch
        device = "cuda" if torch.cuda.is_available() else "cpu"
    else:
        device = args.device

    seeds = [int(s.strip()) for s in args.seeds.split(",")]

    if args.output_dir:
        out_dir = Path(args.output_dir)
    else:
        out_dir = RESULTS_DIR
    out_dir.mkdir(parents=True, exist_ok=True)

    print(f"Volatility Regime Classifier LSTM h={args.hidden_dim}")
    print(f"Device: {device} | Seeds: {seeds} | Epochs: {args.epochs}")

    if args.dry_run:
        print("\n[DRY-RUN] Synthetic data test...")
        result = run_dry_run(epochs=args.epochs, hidden_dim=args.hidden_dim,
                             num_layers=args.num_layers, dropout=args.dropout, lr=args.lr)
    else:
        print("\nLoading multi-asset crypto features...")
        features, regime = load_multi_asset_features(CRYPTO_PANIER, start=DATA_START)
        print(f"Data: {len(features)} samples, {features.shape[1]} features")
        print(f"Regime distribution: {regime.value_counts().to_dict()}")

        result = run_walk_forward_multiseed(
            features, regime,
            seeds=seeds,
            n_splits=args.n_splits,
            gap=args.gap,
            lookback=args.lookback,
            hidden_dim=args.hidden_dim,
            num_layers=args.num_layers,
            dropout=args.dropout,
            lr=args.lr,
            epochs=args.epochs,
            batch_size=min(args.batch_size, 32),
            device=device,
            test_size=args.test_size,
        )

    # Save
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    fname = f"regime_lstm_wf_{ts}.json"
    out_path = out_dir / fname
    with open(out_path, "w") as f:
        json.dump(result, f, indent=2, default=str)
    print(f"\nResults saved to {out_path}")

    # Summary
    if "cross_seed_mean_edge" in result:
        edge = result["cross_seed_mean_edge"]
        std = result["cross_seed_std_edge"]
        acc = result["cross_seed_mean_accuracy"]
        beats = result["beats_claim"]
        print(f"\n{'='*50}")
        print(f"VERDICT: Accuracy={acc:.4f} Edge={edge:+.4f} +/- {std:.4f}")
        print(f"BEATS criterion (edge >= 2*std): {'YES' if beats else 'NO'}")
        print(f"{'='*50}")


if __name__ == "__main__":
    main()
