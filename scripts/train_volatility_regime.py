"""
Volatility Regime Classifier — LSTM h=64, 3-state (low/mid/high)

Walk-forward 5-fold, multi-seed (5 seeds), thermal-prudent GPU training.
Uses shared/gpu_training.py for thermal management.

Usage:
    conda activate base
    python scripts/train_volatility_regime.py --symbol SPY --seeds 0 1 7 42 99 --n-folds 5
    python scripts/train_volatility_regime.py --symbol BTC-USD --seeds 0 1 7 42 99 --n-folds 5
"""

import argparse
import json
import os
import sys
import time
from datetime import datetime
from pathlib import Path

import numpy as np
import pandas as pd
import torch
import torch.nn as nn
from sklearn.metrics import accuracy_score, classification_report, confusion_matrix
from sklearn.preprocessing import StandardScaler

# Add project root for shared imports
PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT / "MyIA.AI.Notebooks" / "QuantConnect"))

from shared.gpu_training import TrainingCheckpoint, get_gpu_temp

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------
SEEDS = [0, 1, 7, 42, 99]
SEQUENCE_LENGTH = 20  # 20 trading days lookback
HIDDEN_DIM = 64
NUM_LAYERS = 2
NUM_CLASSES = 3  # low / mid / high
DROPOUT = 0.2
LEARNING_RATE = 1e-3
BATCH_SIZE = 64
EPOCHS = 50
PATIENCE = 10  # early stopping
VOL_WINDOW = 60  # rolling window for vol regime labels
QUANTILES = [0.33, 0.66]  # 3-state quantile boundaries
THERMAL_PAUSE_SEC = 300  # 5 min pause every 15 min training
THERMAL_TRAIN_SEC = 900  # 15 min training blocks
MAX_TEMP = 80  # Celsius, hard stop threshold
RESULTS_DIR = PROJECT_ROOT / "MyIA.AI.Notebooks" / "QuantConnect" / "results" / "volatility_regime"


# ---------------------------------------------------------------------------
# Data
# ---------------------------------------------------------------------------
def download_data(symbol: str, start: str = "2010-01-01", end: str = None) -> pd.DataFrame:
    """Download OHLCV data via yfinance."""
    import yfinance as yf

    if end is None:
        end = datetime.now().strftime("%Y-%m-%d")

    print(f"Downloading {symbol} data ({start} to {end})...")
    ticker = yf.Ticker(symbol)
    df = ticker.history(start=start, end=end, auto_adjust=True)

    if df.empty:
        raise ValueError(f"No data returned for {symbol}")

    print(f"  Downloaded {len(df)} rows, {df.index[0].date()} to {df.index[-1].date()}")
    return df


def compute_features(df: pd.DataFrame) -> pd.DataFrame:
    """Compute technical features for regime classification."""
    result = pd.DataFrame(index=df.index)
    close = df["Close"]
    high = df["High"]
    low = df["Low"]
    volume = df["Volume"]

    # Returns
    for period in [1, 5, 10, 20]:
        result[f"return_{period}d"] = close.pct_change(period)

    # Realized volatility (multiple windows)
    for window in [5, 10, 20, 60]:
        ret = close.pct_change()
        result[f"realized_vol_{window}"] = ret.rolling(window).std() * np.sqrt(252)

    # Parkinson volatility (uses H/L)
    for window in [5, 10, 20]:
        hl_ratio = np.log(high / low)
        result[f"parkinson_vol_{window}"] = (
            hl_ratio.pow(2).rolling(window).mean().pipe(np.sqrt) * np.sqrt(252 / (4 * np.log(2)))
        )

    # Volume features
    result["volume_ratio"] = volume / volume.rolling(20).mean()
    result["volume_change"] = volume.pct_change()

    # Range features
    result["intraday_range"] = (high - low) / close
    result["gap"] = (df["Open"] - close.shift(1)) / close.shift(1)

    # RSI
    delta = close.diff()
    gain = delta.where(delta > 0, 0).rolling(14).mean()
    loss = (-delta.where(delta < 0, 0)).rolling(14).mean()
    rs = gain / loss
    result["rsi_14"] = 100 - (100 / (1 + rs))

    # Moving average distances
    for window in [20, 50]:
        sma = close.rolling(window).mean()
        result[f"dist_sma_{window}"] = (close - sma) / sma

    # MACD
    ema_fast = close.ewm(span=12, adjust=False).mean()
    ema_slow = close.ewm(span=26, adjust=False).mean()
    result["macd"] = ema_fast - ema_slow
    result["macd_signal"] = result["macd"].ewm(span=9, adjust=False).mean()

    # Bollinger Band width
    sma20 = close.rolling(20).mean()
    std20 = close.rolling(20).std()
    result["bb_width"] = (2 * std20) / sma20

    return result


def create_vol_labels(df: pd.DataFrame, window: int = VOL_WINDOW) -> pd.Series:
    """Create 3-state volatility regime labels (0=low, 1=mid, 2=high)."""
    ret = df["Close"].pct_change()
    rolling_vol = ret.rolling(window).std() * np.sqrt(252)

    # Quantile-based labels (expanding to avoid lookahead bias)
    # Use rolling quantiles instead of global for time-awareness
    q_low = rolling_vol.expanding().quantile(QUANTILES[0])
    q_high = rolling_vol.expanding().quantile(QUANTILES[1])

    labels = pd.Series(1, index=df.index, dtype=int)  # default: mid
    labels[rolling_vol <= q_low] = 0  # low vol
    labels[rolling_vol > q_high] = 2  # high vol

    return labels


def prepare_sequences(
    features: np.ndarray, labels: np.ndarray, seq_len: int
) -> tuple:
    """Convert to sequence format for LSTM: (N, seq_len, n_features)."""
    X, y = [], []
    for i in range(seq_len, len(features)):
        X.append(features[i - seq_len : i])
        y.append(labels[i])
    return np.array(X), np.array(y)


# ---------------------------------------------------------------------------
# Model
# ---------------------------------------------------------------------------
class VolatilityLSTM(nn.Module):
    def __init__(
        self,
        input_dim: int,
        hidden_dim: int = HIDDEN_DIM,
        num_layers: int = NUM_LAYERS,
        num_classes: int = NUM_CLASSES,
        dropout: float = DROPOUT,
    ):
        super().__init__()
        self.lstm = nn.LSTM(
            input_dim,
            hidden_dim,
            num_layers=num_layers,
            batch_first=True,
            dropout=dropout if num_layers > 1 else 0,
        )
        self.fc = nn.Linear(hidden_dim, num_classes)

    def forward(self, x):
        out, _ = self.lstm(x)
        out = out[:, -1, :]  # last timestep
        return self.fc(out)


# ---------------------------------------------------------------------------
# Training loop with thermal management
# ---------------------------------------------------------------------------
def train_one_fold(
    X_train: np.ndarray,
    y_train: np.ndarray,
    X_test: np.ndarray,
    y_test: np.ndarray,
    seed: int,
    fold: int,
    device: torch.device,
    scaler: StandardScaler,
    max_epochs: int = EPOCHS,
) -> dict:
    """Train LSTM for one fold with thermal-prudent GPU usage."""

    torch.manual_seed(seed)
    np.random.seed(seed)

    input_dim = X_train.shape[2]
    model = VolatilityLSTM(input_dim=input_dim).to(device)
    optimizer = torch.optim.Adam(model.parameters(), lr=LEARNING_RATE)
    criterion = nn.CrossEntropyLoss()

    # Convert to tensors
    X_train_t = torch.FloatTensor(X_train).to(device)
    y_train_t = torch.LongTensor(y_train).to(device)
    X_test_t = torch.FloatTensor(X_test).to(device)
    y_test_t = torch.LongTensor(y_test).to(device)

    train_dataset = torch.utils.data.TensorDataset(X_train_t, y_train_t)
    train_loader = torch.utils.data.DataLoader(
        train_dataset, batch_size=BATCH_SIZE, shuffle=True
    )

    best_acc = 0.0
    best_state = None
    patience_counter = 0
    history = []
    train_start = time.time()
    last_thermal_pause = time.time()

    for epoch in range(max_epochs):
        # Thermal management: pause every THERMAL_TRAIN_SEC
        elapsed = time.time() - last_thermal_pause
        if elapsed >= THERMAL_TRAIN_SEC:
            temp = get_gpu_temp()
            print(f"    [Thermal] T={temp}C, pausing {THERMAL_PAUSE_SEC}s after {elapsed:.0f}s training")
            time.sleep(THERMAL_PAUSE_SEC)
            last_thermal_pause = time.time()

        # Hard thermal check
        temp = get_gpu_temp()
        if temp > MAX_TEMP:
            print(f"    [Thermal] HARD STOP: T={temp}C > {MAX_TEMP}C, cooling 10min")
            time.sleep(600)
            last_thermal_pause = time.time()

        # Train epoch
        model.train()
        epoch_loss = 0.0
        for X_batch, y_batch in train_loader:
            optimizer.zero_grad()
            output = model(X_batch)
            loss = criterion(output, y_batch)
            loss.backward()
            optimizer.step()
            epoch_loss += loss.item()

        avg_loss = epoch_loss / len(train_loader)

        # Evaluate
        model.eval()
        with torch.no_grad():
            test_output = model(X_test_t)
            preds = test_output.argmax(dim=1).cpu().numpy()
            acc = accuracy_score(y_test, preds)

        history.append({"epoch": epoch + 1, "loss": avg_loss, "val_acc": acc})

        if acc > best_acc:
            best_acc = acc
            best_state = {k: v.cpu().clone() for k, v in model.state_dict().items()}
            patience_counter = 0
        else:
            patience_counter += 1

        if (epoch + 1) % 10 == 0 or epoch == 0:
            print(f"    Fold {fold} seed={seed} epoch {epoch+1:3d}: loss={avg_loss:.4f} val_acc={acc:.4f} (best={best_acc:.4f})")

        if patience_counter >= PATIENCE:
            print(f"    Fold {fold} seed={seed}: early stopping at epoch {epoch+1}")
            break

    # Final evaluation with best model
    model.load_state_dict(best_state)
    model.eval()
    with torch.no_grad():
        test_output = model(X_test_t)
        preds = test_output.argmax(dim=1).cpu().numpy()

    report = classification_report(y_test, preds, output_dict=True, zero_division=0)
    cm = confusion_matrix(y_test, preds).tolist()

    total_time = time.time() - train_start
    print(f"    Fold {fold} seed={seed}: BEST acc={best_acc:.4f} ({total_time:.0f}s)")

    return {
        "seed": seed,
        "fold": fold,
        "best_val_acc": float(best_acc),
        "classification_report": report,
        "confusion_matrix": cm,
        "epochs_trained": len(history),
        "train_time_sec": round(total_time, 1),
        "history": history,
    }


# ---------------------------------------------------------------------------
# Walk-forward 5-fold
# ---------------------------------------------------------------------------
def walk_forward_split_expanding(
    n_samples: int, n_folds: int = 5, min_train_ratio: float = 0.5
) -> list:
    """Generate expanding window walk-forward split indices."""
    test_size = n_samples // (n_folds + 2)
    initial_train = int(n_samples * min_train_ratio)

    splits = []
    for fold in range(n_folds):
        train_end = initial_train + fold * test_size
        test_start = train_end
        test_end = min(test_start + test_size, n_samples)

        if test_start >= n_samples or test_end <= test_start:
            continue

        splits.append(
            (np.arange(0, train_end), np.arange(test_start, test_end))
        )

    return splits


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------
def main():
    parser = argparse.ArgumentParser(description="Volatility Regime Classifier")
    parser.add_argument("--symbol", type=str, default="SPY", help="Ticker symbol")
    parser.add_argument("--seeds", type=int, nargs="+", default=SEEDS, help="Random seeds")
    parser.add_argument("--n-folds", type=int, default=5, help="Walk-forward folds")
    parser.add_argument("--epochs", type=int, default=EPOCHS, help="Max epochs per fold")
    parser.add_argument("--hidden-dim", type=int, default=HIDDEN_DIM, help="LSTM hidden dim")
    parser.add_argument("--seq-length", type=int, default=SEQUENCE_LENGTH, help="Lookback window")
    parser.add_argument("--no-gpu", action="store_true", help="Force CPU")
    parser.add_argument("--dry-run", action="store_true", help="Quick test with minimal data")
    args = parser.parse_args()

    device = torch.device("cpu" if args.no_gpu or not torch.cuda.is_available() else "cuda")
    print(f"Device: {device}")
    if device.type == "cuda":
        print(f"  GPU: {torch.cuda.get_device_name(0)}")
        print(f"  Initial temp: {get_gpu_temp()}C")

    # Download data
    df = download_data(args.symbol)
    if args.dry_run:
        df = df.iloc[-500:]

    # Features and labels
    features_df = compute_features(df)
    labels = create_vol_labels(df)

    # Align: drop NaN rows
    features_df["label"] = labels
    features_df = features_df.dropna()

    labels_arr = features_df.pop("label").values.astype(int)
    feature_names = features_df.columns.tolist()
    features_arr = features_df.values

    print(f"Features: {features_arr.shape[1]} ({feature_names[:5]}...)")
    print(f"Samples: {len(features_arr)}")
    print(f"Label distribution: {dict(zip(*np.unique(labels_arr, return_counts=True)))}")

    # Create sequences
    X, y = prepare_sequences(features_arr, labels_arr, args.seq_length)
    print(f"Sequences: {X.shape[0]}, shape: {X.shape}")

    # Walk-forward 5-fold, multi-seed
    splits = walk_forward_split_expanding(len(X), n_folds=args.n_folds)
    print(f"\nWalk-forward: {len(splits)} folds")
    for i, (train_idx, test_idx) in enumerate(splits):
        print(f"  Fold {i+1}: train={len(train_idx)}, test={len(test_idx)}")

    RESULTS_DIR.mkdir(parents=True, exist_ok=True)

    all_results = []
    for seed in args.seeds:
        print(f"\n{'='*60}")
        print(f"SEED {seed}")
        print(f"{'='*60}")

        seed_results = []
        for fold_idx, (train_idx, test_idx) in enumerate(splits):
            X_train, X_test = X[train_idx], X[test_idx]
            y_train, y_test = y[train_idx], y[test_idx]

            # Normalize per fold (expanding window: fit on train only)
            n_features = X_train.shape[2]
            scaler = StandardScaler()
            X_train_2d = X_train.reshape(-1, n_features)
            X_test_2d = X_test.reshape(-1, n_features)
            X_train_2d = scaler.fit_transform(X_train_2d)
            X_test_2d = scaler.transform(X_test_2d)
            X_train = X_train_2d.reshape(X_train.shape)
            X_test = X_test_2d.reshape(X_test.shape)

            result = train_one_fold(
                X_train, y_train, X_test, y_test,
                seed=seed, fold=fold_idx + 1, device=device, scaler=scaler,
                max_epochs=args.epochs,
            )
            seed_results.append(result)
            all_results.append(result)

        # Seed summary
        avg_acc = np.mean([r["best_val_acc"] for r in seed_results])
        print(f"\n  Seed {seed} avg acc: {avg_acc:.4f}")

    # Global summary
    all_accs = [r["best_val_acc"] for r in all_results]
    mean_acc = np.mean(all_accs)
    std_acc = np.std(all_accs)

    # Per-seed averages
    seed_avgs = {}
    for seed in args.seeds:
        seed_fold_accs = [r["best_val_acc"] for r in all_results if r["seed"] == seed]
        seed_avgs[str(seed)] = {
            "mean": float(np.mean(seed_fold_accs)),
            "std": float(np.std(seed_fold_accs)),
        }

    # Cross-seed stability
    cross_seed_means = [v["mean"] for v in seed_avgs.values()]
    cross_seed_std = float(np.std(cross_seed_means))

    summary = {
        "symbol": args.symbol,
        "timestamp": datetime.now().isoformat(),
        "config": {
            "hidden_dim": args.hidden_dim,
            "seq_length": args.seq_length,
            "n_folds": args.n_folds,
            "seeds": args.seeds,
            "epochs": args.epochs,
            "feature_count": len(feature_names),
            "feature_names": feature_names,
        },
        "results": {
            "overall_mean_acc": float(mean_acc),
            "overall_std_acc": float(std_acc),
            "n_experiments": len(all_results),
            "per_seed": seed_avgs,
            "cross_seed_std": cross_seed_std,
            "beats_random": bool(mean_acc > 1.0 / NUM_CLASSES),
            "edge_vs_random": float(mean_acc - 1.0 / NUM_CLASSES),
        },
        "fold_details": [
            {
                "seed": r["seed"],
                "fold": r["fold"],
                "acc": r["best_val_acc"],
                "epochs": r["epochs_trained"],
                "time_sec": r["train_time_sec"],
            }
            for r in all_results
        ],
    }

    # Save results
    out_file = RESULTS_DIR / f"regime_{args.symbol.replace('-', '')}_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
    with open(out_file, "w") as f:
        json.dump(summary, f, indent=2, default=str)
    print(f"\nResults saved: {out_file}")

    # Print summary
    print(f"\n{'='*60}")
    print(f"SUMMARY — {args.symbol} Volatility Regime Classifier")
    print(f"{'='*60}")
    print(f"  Overall: {mean_acc:.4f} +/- {std_acc:.4f} ({len(all_results)} runs)")
    print(f"  Random baseline: {1/NUM_CLASSES:.4f}")
    print(f"  Edge vs random: {mean_acc - 1/NUM_CLASSES:+.4f}")
    print(f"  Cross-seed stability: {cross_seed_std:.4f}")
    print(f"  Beats random: {'YES' if mean_acc > 1/NUM_CLASSES else 'NO'}")

    for seed, stats in seed_avgs.items():
        print(f"  Seed {seed}: {stats['mean']:.4f} +/- {stats['std']:.4f}")

    # Dashboard report
    verdict = "BEATS RANDOM" if mean_acc > 1/NUM_CLASSES else "NO BEAT"
    print(f"\n  VERDICT: {verdict}")

    return summary


if __name__ == "__main__":
    main()
