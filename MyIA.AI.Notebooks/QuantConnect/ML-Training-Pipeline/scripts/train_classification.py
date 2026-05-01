"""
Train ML classification models (RandomForest + XGBoost) for financial prediction.

Uses features from OHLCV data to predict next-period return direction (up/down/flat).
Designed to work with datasets from the scripts/datasets/ pipeline.

Usage:
    # Full training on yfinance SPY data
    python train_classification.py --data-dir ../datasets/yfinance --symbol SPY --start 2010-01-01

    # Dry-run (1 epoch, 100 rows, validates pipeline without GPU)
    python train_classification.py --dry-run

    # Custom hyperparameters
    python train_classification.py --data-dir ../datasets/yfinance --symbol SPY \\
        --n-estimators 500 --max-depth 10 --lookback 60

Output:
    Checkpoints in --checkpoint-dir (default: ../checkpoints/classification/<date>/)
    metadata.json with hyperparams, metrics, dataset hash
"""

import argparse
import hashlib
import json
import sys
from datetime import datetime
from pathlib import Path

import numpy as np
import pandas as pd


def generate_features(df: pd.DataFrame, lookback: int = 20) -> pd.DataFrame:
    """Engineer features from OHLCV data for classification."""
    feat = pd.DataFrame(index=df.index)

    # Returns at multiple horizons
    for window in [1, 5, 10, 20]:
        feat[f"ret_{window}d"] = df["Close"].pct_change(window)

    # Volatility
    feat["vol_5d"] = df["Close"].pct_change().rolling(5).std()
    feat["vol_20d"] = df["Close"].pct_change().rolling(20).std()

    # Volume features
    feat["vol_ratio"] = df["Volume"] / df["Volume"].rolling(20).mean()

    # Moving average ratios
    for window in [5, 10, 20, 60]:
        feat[f"ma_ratio_{window}"] = df["Close"] / df["Close"].rolling(window).mean()

    # RSI
    delta = df["Close"].diff()
    gain = delta.where(delta > 0, 0.0).rolling(14).mean()
    loss = (-delta.where(delta < 0, 0.0)).rolling(14).mean()
    rs = gain / loss.replace(0, 1e-10)
    feat["rsi_14"] = 100 - (100 / (1 + rs))

    # MACD
    ema12 = df["Close"].ewm(span=12, adjust=False).mean()
    ema26 = df["Close"].ewm(span=26, adjust=False).mean()
    feat["macd"] = ema12 - ema26
    feat["macd_signal"] = feat["macd"].ewm(span=9, adjust=False).mean()

    # Bollinger Band width
    sma20 = df["Close"].rolling(20).mean()
    std20 = df["Close"].rolling(20).std()
    feat["bb_width"] = (df["Close"] - sma20) / (2 * std20.replace(0, 1e-10))

    # Target: next-period direction (1=up, 0=flat/down using threshold)
    feat["target"] = (df["Close"].pct_change().shift(-1) > 0.001).astype(int)

    feat = feat.dropna()
    return feat


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


def train_and_evaluate(
    features: pd.DataFrame,
    model_type: str = "rf",
    n_estimators: int = 200,
    max_depth: int = 8,
    test_ratio: float = 0.2,
) -> dict:
    """Train a classification model and return metrics."""
    from sklearn.ensemble import RandomForestClassifier
    from sklearn.metrics import accuracy_score, f1_score, precision_score, recall_score
    from sklearn.model_selection import TimeSeriesSplit

    X = features.drop(columns=["target"]).values
    y = features["target"].values

    # Time-series split (last test_ratio portion for test)
    split_idx = int(len(X) * (1 - test_ratio))
    X_train, X_test = X[:split_idx], X[split_idx:]
    y_train, y_test = y[:split_idx], y[split_idx:]

    if model_type == "xgb":
        try:
            from xgboost import XGBClassifier

            model = XGBClassifier(
                n_estimators=n_estimators,
                max_depth=max_depth,
                learning_rate=0.05,
                subsample=0.8,
                colsample_bytree=0.8,
                eval_metric="logloss",
                verbosity=0,
            )
        except ImportError:
            print("WARNING: xgboost not installed, falling back to RandomForest")
            model = RandomForestClassifier(
                n_estimators=n_estimators, max_depth=max_depth, random_state=42, n_jobs=-1
            )
    else:
        model = RandomForestClassifier(
            n_estimators=n_estimators, max_depth=max_depth, random_state=42, n_jobs=-1
        )

    model.fit(X_train, y_train)
    y_pred = model.predict(X_test)

    metrics = {
        "accuracy": round(accuracy_score(y_test, y_pred), 4),
        "f1": round(f1_score(y_test, y_pred, average="weighted"), 4),
        "precision": round(precision_score(y_test, y_pred, average="weighted"), 4),
        "recall": round(recall_score(y_test, y_pred, average="weighted"), 4),
        "train_samples": len(X_train),
        "test_samples": len(X_test),
    }

    return {"model": model, "metrics": metrics, "feature_names": list(features.columns[:-1])}


def save_checkpoint(
    model, metrics: dict, hyperparams: dict, data_hash: str, checkpoint_dir: Path
) -> Path:
    """Save model checkpoint and metadata."""
    import joblib

    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    ckpt_path = checkpoint_dir / timestamp
    ckpt_path.mkdir(parents=True, exist_ok=True)

    # Save model
    model_file = ckpt_path / "model.joblib"
    joblib.dump(model, model_file)

    # Save metadata
    metadata = {
        "timestamp": timestamp,
        "model_type": hyperparams.get("model_type", "rf"),
        "hyperparams": hyperparams,
        "metrics": metrics,
        "data_hash": data_hash,
        "files": ["model.joblib", "metadata.json"],
    }
    meta_file = ckpt_path / "metadata.json"
    meta_file.write_text(json.dumps(metadata, indent=2), encoding="utf-8")

    print(f"Checkpoint saved: {ckpt_path}")
    print(f"  Metrics: {metrics}")
    return ckpt_path


def main():
    parser = argparse.ArgumentParser(
        description="Train ML classification models for financial prediction"
    )
    parser.add_argument(
        "--data-dir",
        default=str(Path(__file__).resolve().parent.parent / "datasets" / "yfinance"),
        help="Directory containing OHLCV CSV files",
    )
    parser.add_argument("--symbol", default="SPY", help="Ticker symbol to train on")
    parser.add_argument("--start", help="Start date (YYYY-MM-DD)")
    parser.add_argument("--end", help="End date (YYYY-MM-DD)")
    parser.add_argument("--model", default="rf", choices=["rf", "xgb"], help="Model type")
    parser.add_argument("--n-estimators", type=int, default=200, help="Number of trees/boosting rounds")
    parser.add_argument("--max-depth", type=int, default=8, help="Max tree depth")
    parser.add_argument("--lookback", type=int, default=20, help="Feature lookback window")
    parser.add_argument("--test-ratio", type=float, default=0.2, help="Test set ratio")
    parser.add_argument(
        "--checkpoint-dir",
        default=str(Path(__file__).resolve().parent.parent / "checkpoints" / "classification"),
        help="Directory to save checkpoints",
    )
    parser.add_argument(
        "--dry-run", action="store_true", help="Run with synthetic data (100 rows, 1 pass)"
    )
    args = parser.parse_args()

    # Load data
    if args.dry_run:
        print("DRY-RUN: Using synthetic data (500 rows)")
        raw = generate_synthetic_data(500)
        data_hash = "synthetic-dryrun"
    else:
        data_dir = Path(args.data_dir)
        if not data_dir.exists():
            print(f"ERROR: Data directory not found: {data_dir}", file=sys.stderr)
            print("Run download_yfinance.py first, or use --dry-run", file=sys.stderr)
            sys.exit(1)
        raw = load_data(data_dir, args.symbol, args.start, args.end)
        data_hash = compute_data_hash(raw)
        print(f"Loaded {len(raw)} rows for {args.symbol} ({raw.index.min().date()} -> {raw.index.max().date()})")

    # Engineer features
    features = generate_features(raw, lookback=args.lookback)
    print(f"Features: {len(features)} rows, {len(features.columns) - 1} columns")

    # Train
    hyperparams = {
        "model_type": args.model,
        "n_estimators": args.n_estimators,
        "max_depth": args.max_depth,
        "lookback": args.lookback,
        "test_ratio": args.test_ratio,
        "symbol": args.symbol,
    }

    result = train_and_evaluate(
        features,
        model_type=args.model,
        n_estimators=args.n_estimators,
        max_depth=args.max_depth,
        test_ratio=args.test_ratio,
    )

    # Save checkpoint
    ckpt_dir = Path(args.checkpoint_dir)
    save_checkpoint(result["model"], result["metrics"], hyperparams, data_hash, ckpt_dir)

    if args.dry_run:
        print("DRY-RUN complete. Pipeline validated successfully.")
    else:
        print(f"Training complete. Accuracy: {result['metrics']['accuracy']}, F1: {result['metrics']['f1']}")


if __name__ == "__main__":
    main()
