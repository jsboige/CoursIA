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
import json
import sys
from datetime import datetime
from pathlib import Path

import numpy as np
import pandas as pd

from data_utils import compute_data_hash, generate_synthetic_data, load_data
from features import FeatureEngineer
from walk_forward import WalkForwardSplitter
from baselines import majority_class_baseline


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
    from sklearn.preprocessing import StandardScaler

    X = features.drop(columns=["target"]).values
    y = features["target"].values

    # Time-series split (last test_ratio portion for test)
    split_idx = int(len(X) * (1 - test_ratio))
    X_train, X_test = X[:split_idx], X[split_idx:]
    y_train, y_test = y[:split_idx], y[split_idx:]

    # Train-only normalization (prevent lookahead bias)
    scaler = StandardScaler()
    X_train = scaler.fit_transform(X_train)
    X_test = scaler.transform(X_test)

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


def train_walk_forward_classification(
    features: pd.DataFrame,
    model_type: str = "rf",
    n_estimators: int = 200,
    max_depth: int = 8,
    n_splits: int = 5,
    train_size: int | None = None,
    test_size: int | None = None,
    gap: int = 5,
) -> dict:
    """Walk-forward cross-validation with per-fold train-only normalization.

    Uses StandardScaler fitted on training fold only to prevent lookahead bias.
    Reports OOS direction accuracy, majority-class baseline, and per-fold details.
    """
    from sklearn.ensemble import RandomForestClassifier
    from sklearn.metrics import accuracy_score
    from sklearn.preprocessing import StandardScaler

    X = features.drop(columns=["target"]).values
    y = features["target"].values

    splitter = WalkForwardSplitter(
        n_splits=n_splits, train_size=train_size, test_size=test_size, gap=gap,
    )

    fold_results = []
    oos_preds = np.full(len(y), np.nan, dtype=object)
    best_model = None
    best_fold_acc = -1.0

    for fold_idx, (train_idx, test_idx) in enumerate(splitter.split(X)):
        if len(test_idx) == 0:
            continue

        X_train_fold = X[train_idx]
        X_test_fold = X[test_idx]
        y_train_fold = y[train_idx]
        y_test_fold = y[test_idx]

        # Per-fold train-only normalization (StandardScaler)
        # Internal train/val split to avoid test-set contamination (issue #722)
        val_cutoff = int(len(X_train_fold) * 0.85)
        X_tr_fold = X_train_fold[:val_cutoff]
        X_val_fold = X_train_fold[val_cutoff:]
        y_tr_fold = y_train_fold[:val_cutoff]
        y_val_fold = y_train_fold[val_cutoff:]

        scaler = StandardScaler()
        X_tr_norm = scaler.fit_transform(X_tr_fold)
        X_val_norm = scaler.transform(X_val_fold)
        X_test_norm = scaler.transform(X_test_fold)

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
                    n_estimators=n_estimators, max_depth=max_depth, random_state=42, n_jobs=-1,
                )
        else:
            model = RandomForestClassifier(
                n_estimators=n_estimators, max_depth=max_depth, random_state=42, n_jobs=-1,
            )

        model.fit(X_tr_norm, y_tr_fold)

        # Use validation accuracy for model selection (NOT test)
        val_preds = model.predict(X_val_norm)
        val_acc = accuracy_score(y_val_fold, val_preds)

        # Test predictions for OOS reporting only
        fold_preds = model.predict(X_test_norm)
        fold_acc = accuracy_score(y_test_fold, fold_preds)

        fold_results.append({
            "fold": fold_idx,
            "train_size": val_cutoff,
            "val_size": len(X_train_fold) - val_cutoff,
            "test_size": len(test_idx),
            "val_accuracy": round(val_acc, 4),
            "oos_accuracy": round(fold_acc, 4),
        })

        oos_preds[test_idx] = fold_preds

        if val_acc > best_fold_acc:
            best_fold_acc = val_acc
            import pickle
            best_model = pickle.loads(pickle.dumps(model))

        print(f"  Fold {fold_idx+1}/{n_splits}  val_acc={val_acc:.4f}  oos_acc={fold_acc:.4f}  "
              f"train={val_cutoff}  val={len(X_train_fold) - val_cutoff}  test={len(test_idx)}")

    # Aggregate OOS metrics
    valid_mask = ~np.array([p is np.nan for p in oos_preds]) if hasattr(np, 'nan') else np.array([not (isinstance(p, float) and np.isnan(p)) for p in oos_preds])
    oos_predictions = oos_preds[valid_mask].astype(int)
    oos_targets = y[valid_mask]

    oos_diracc = float(np.mean(oos_predictions == oos_targets))

    # Majority-class baseline on first half (train proxy) vs second half (test proxy)
    y_binary = y.copy()
    majority_bl = majority_class_baseline(y_binary[: len(y) // 2], y_binary[len(y) // 2 :])

    return {
        "model": best_model,
        "metrics": {
            "oos_direction_accuracy": round(oos_diracc, 4),
            "majority_class_acc": majority_bl["accuracy"],
            "majority_class_freq": majority_bl["majority_freq"],
            "vs_majority_class": round(oos_diracc - majority_bl["accuracy"], 4),
            "n_wf_folds": len(fold_results),
        },
        "fold_details": fold_results,
        "feature_names": list(features.columns[:-1]),
    }


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
    parser.add_argument(
        "--walk-forward", action="store_true",
        help="Use walk-forward cross-validation instead of simple split",
    )
    parser.add_argument("--n-splits", type=int, default=5, help="Walk-forward splits")
    parser.add_argument("--wf-train-size", type=int, default=None, help="Walk-forward train window (None=expanding)")
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
    features = engineer.transform(raw, add_target=False)
    features["target"] = (raw["Close"].pct_change().shift(-1) > 0.001).astype(int)
    features = features.dropna()
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

    if args.walk_forward:
        print(f"Mode: WALK-FORWARD (n_splits={args.n_splits}, gap={args.gap})")

        hyperparams.update({
            "walk_forward": True,
            "n_splits": args.n_splits,
            "wf_train_size": args.wf_train_size,
            "wf_test_size": args.wf_test_size,
            "gap": args.gap,
        })

        result = train_walk_forward_classification(
            features,
            model_type=args.model,
            n_estimators=args.n_estimators,
            max_depth=args.max_depth,
            n_splits=args.n_splits,
            train_size=args.wf_train_size,
            test_size=args.wf_test_size,
            gap=args.gap,
        )

        ckpt_dir = Path(args.checkpoint_dir)
        save_checkpoint(result["model"], result["metrics"], hyperparams, data_hash, ckpt_dir)

        m = result["metrics"]
        print(f"\nWalk-Forward OOS Results:")
        print(f"  OOS DirAcc:     {m['oos_direction_accuracy']:.4f}")
        print(f"  Majority Class: {m['majority_class_acc']:.4f} (freq={m['majority_class_freq']:.4f})")
        print(f"  vs Majority:    {m['vs_majority_class']:+.4f}")
        print(f"  Folds:          {m['n_wf_folds']}")

        if args.dry_run:
            print("DRY-RUN complete. Walk-forward pipeline validated.")
        return

    # Simple time-series split (default)
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
