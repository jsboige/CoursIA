"""
Evaluation harness for existing ML/Trading checkpoints.

Ties together the 4 discipline scripts (walk_forward, baselines, eval_finstsb,
transaction_costs) to produce comprehensive evaluation reports for each checkpoint.

Each checkpoint gets:
    - Walk-forward out-of-sample metrics (no in-sample leakage)
    - Comparison vs majority-class and buy-and-hold baselines
    - Per-regime evaluation (uptrend/downtrend/volatility/black_swan)
    - Transaction cost analysis (gross vs net Sharpe)

Usage:
    # Evaluate a single checkpoint
    python eval_existing_checkpoints.py --checkpoint checkpoints/transformer/20260501_134056

    # Evaluate all checkpoints
    python eval_existing_checkpoints.py --all --checkpoint-dir checkpoints

    # Dry-run (synthetic data, no real checkpoints needed)
    python eval_existing_checkpoints.py --dry-run

References:
    - AFML Ch.7-12 (Lopez de Prado): walk-forward, purged CV, CPCV
    - FinTSB: per-regime evaluation
    - Almgren-Chriss: transaction cost modeling
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

import numpy as np
import pandas as pd

from baselines import (
    buy_and_hold_baseline,
    majority_class_baseline,
    naive_momentum_baseline,
)
from data_utils import generate_synthetic_data, load_data
from eval_finstsb import eval_per_regime
from features import FeatureEngineer
from sequence_utils import build_sequences
from transaction_costs import TransactionCostModel, compare_gross_vs_net
from walk_forward import WalkForwardSplitter


def load_checkpoint_model(checkpoint_dir: Path) -> tuple:
    """Load model and metadata from a checkpoint directory.

    Returns
    -------
    (model, metadata, model_type) : tuple of model object, metadata dict, and type string.
    """
    metadata_path = checkpoint_dir / "metadata.json"
    if not metadata_path.exists():
        raise FileNotFoundError(f"No metadata.json in {checkpoint_dir}")

    with open(metadata_path) as f:
        metadata = json.load(f)

    model_type = metadata.get("model_type", "unknown")
    hp = metadata.get("hyperparams", {})

    model_path = checkpoint_dir / "model.pt"
    model_joblib = checkpoint_dir / "model.joblib"

    if model_type == "rf":
        import joblib

        model = joblib.load(model_joblib)
    elif model_type in ("transformer", "lstm"):
        import torch

        model = _build_model_from_metadata(model_type, hp)
        state = torch.load(model_path, map_location="cpu", weights_only=True)
        model.load_state_dict(state)
        model.eval()
    elif model_type == "dqn":
        import torch

        state_size = hp.get("state_size", metadata.get("architecture", {}).get("state_size", 242))
        hidden_size = hp.get("hidden_size", 256)
        from train_dqn_rl import build_dqn

        model = build_dqn(state_size, hidden_size, n_actions=3)
        state = torch.load(model_path, map_location="cpu", weights_only=True)
        model.load_state_dict(state)
        model.eval()
    else:
        raise ValueError(f"Unknown model type: {model_type}")

    return model, metadata, model_type


def _build_model_from_metadata(model_type: str, hp: dict):
    """Reconstruct model architecture from hyperparameters."""
    import torch

    if model_type == "transformer":
        from train_transformer import build_transformer_model

        return build_transformer_model(
            input_size=hp.get("input_size", 38),
            d_model=hp.get("d_model", 128),
            nhead=hp.get("nhead", 4),
            num_layers=hp.get("num_layers", 4),
            dim_feedforward=hp.get("dim_feedforward", 512),
            dropout=hp.get("dropout", 0.1),
            seq_len=hp.get("seq_len", 20),
        )
    elif model_type == "lstm":
        from train_lstm import build_model

        return build_model(
            input_size=hp.get("input_size", 38),
            hidden_size=hp.get("hidden_size", 128),
            num_layers=hp.get("num_layers", 2),
            dropout=hp.get("dropout", 0.2),
            model_type="lstm",
        )
    raise ValueError(f"Cannot build model for type: {model_type}")


def predict_sequences(model, X: np.ndarray, model_type: str) -> np.ndarray:
    """Run model inference on sequence data.

    Parameters
    ----------
    model : trained model
    X : np.ndarray, shape (n_samples, seq_len, n_features) for seq models
    model_type : str

    Returns
    -------
    np.ndarray of predicted returns (or direction probabilities).
    """
    if model_type == "rf":
        n_samples, seq_len, n_features = X.shape
        X_flat = X[:, -1, :]
        return model.predict(X_flat)
    else:
        import torch

        with torch.no_grad():
            X_t = torch.tensor(X, dtype=torch.float32)
            preds = model(X_t).squeeze(-1).numpy()
        return preds


def predict_direction(model, X: np.ndarray, model_type: str) -> np.ndarray:
    """Predict binary direction (0=down, 1=up)."""
    raw = predict_sequences(model, X, model_type)
    if model_type == "rf":
        return raw.astype(int)
    return (raw > 0).astype(int)


def evaluate_checkpoint(
    checkpoint_dir: Path,
    data_dir: Path | None = None,
    n_splits: int = 5,
    device: str = "cpu",
) -> dict:
    """Run full evaluation pipeline on a single checkpoint.

    Pipeline:
        1. Load model + metadata
        2. Load data and build features
        3. Walk-forward split evaluation
        4. Baseline comparison
        5. Per-regime evaluation (OOS only)
        6. Transaction cost analysis (OOS only)

    Returns
    -------
    dict with keys: metadata, wf_metrics, baselines, regime_eval, cost_analysis
    """
    model, metadata, model_type = load_checkpoint_model(checkpoint_dir)
    hp = metadata.get("hyperparams", {})

    symbol = hp.get("symbol", "SPY")
    seq_len = hp.get("seq_len", hp.get("lookback", 20))
    advanced = hp.get("advanced", False)

    # Load data
    if data_dir is None:
        data_dir = Path(__file__).resolve().parent.parent / "datasets" / "yfinance"

    if (checkpoint_dir / "metadata.json").exists():
        data_hash = metadata.get("data_hash", "")
        if data_hash == "synthetic-dryrun":
            df = generate_synthetic_data(2000)
        else:
            try:
                df = load_data(data_dir, symbol)
            except FileNotFoundError:
                df = generate_synthetic_data(2000)
    else:
        df = generate_synthetic_data(2000)

    # Build features
    engineer = FeatureEngineer(lookback=seq_len)
    features = engineer.transform(df, advanced=advanced)
    features = features.dropna()

    # Build sequences
    X, y, feature_cols = build_sequences(features, seq_len=seq_len)
    prices = features.index.get_level_values(0) if isinstance(features.index, pd.MultiIndex) else features.index
    close_prices = pd.Series(
        df["Close"].reindex(prices).values.flatten(),
        index=range(len(prices)),
    )

    # Align prices to sequence length
    close_prices = close_prices.iloc[seq_len:].reset_index(drop=True)
    n = min(len(X), len(y), len(close_prices))
    X, y = X[:n], y[:n]
    close_prices = close_prices[:n]

    # --- 1. Walk-forward evaluation ---
    splitter = WalkForwardSplitter(n_splits=n_splits, train_size=252 * 3, test_size=252, gap=5)

    wf_diraccs = []
    wf_predictions = np.zeros(n)
    wf_actual = y.copy()
    oos_indices = np.zeros(n, dtype=bool)

    for fold_idx, (train_idx, test_idx) in enumerate(splitter.split(X)):
        if len(test_idx) == 0:
            continue

        X_test = X[test_idx]

        # Normalize using training data stats
        X_train_fold = X[train_idx]
        mean = X_train_fold.mean(axis=(0, 1), keepdims=True)
        std = X_train_fold.std(axis=(0, 1), keepdims=True)
        std = np.where(std < 1e-8, 1.0, std)
        X_test_norm = (X_test - mean) / std

        fold_preds = predict_direction(model, X_test_norm, model_type)
        fold_actual = y[test_idx]

        diracc = np.mean(fold_preds == (fold_actual > 0).astype(int))
        wf_diraccs.append(diracc)
        wf_predictions[test_idx] = fold_preds
        oos_indices[test_idx] = True

    oos_diracc = np.mean(wf_diraccs) if wf_diraccs else float("nan")

    # --- 2. Baselines ---
    y_binary = (y > 0).astype(int)

    majority_bl = majority_class_baseline(y_binary[: n // 2], y_binary[n // 2 :])

    prices_series = pd.Series(close_prices.values)
    hold_bl = buy_and_hold_baseline(prices_series)
    momentum_bl = naive_momentum_baseline(prices_series, lookback=min(seq_len, 20))

    # --- 3. Per-regime evaluation (OOS only) ---
    X_oos = X[oos_indices]
    y_oos = y_binary[oos_indices]
    prices_oos = close_prices[oos_indices]

    if len(X_oos) > 0:
        # Normalize OOS data using global stats for regime evaluation
        global_mean = X.mean(axis=(0, 1), keepdims=True)
        global_std = X.std(axis=(0, 1), keepdims=True)
        global_std = np.where(global_std < 1e-8, 1.0, global_std)
        X_oos_norm = (X_oos - global_mean) / global_std

        regime_results = eval_per_regime(
            model=_wrap_model(model, model_type),
            X=X_oos_norm,
            y=y_oos,
            prices=prices_oos,
        )
    else:
        regime_results = {"weighted_avg": {"sharpe": float("nan"), "diracc": float("nan")}}

    # --- 4. Transaction cost analysis (OOS predictions only) ---
    gross_returns = y[oos_indices]
    positions = np.zeros(int(np.sum(oos_indices)))
    positions[wf_predictions[oos_indices] == 1] = 1.0
    positions[wf_predictions[oos_indices] == 0] = -1.0

    cost_model = TransactionCostModel()
    cost_analysis = compare_gross_vs_net(gross_returns, positions, cost_model)

    # --- 5. Compile results ---
    original_diracc = metadata.get("metrics", {}).get("direction_accuracy", float("nan"))
    vs_majority = oos_diracc - majority_bl["accuracy"] if not np.isnan(oos_diracc) else float("nan")

    results = {
        "checkpoint": str(checkpoint_dir),
        "model_type": model_type,
        "symbol": symbol,
        "original_diracc": original_diracc,
        "oos_diracc": oos_diracc,
        "oos_diracc_delta": oos_diracc - original_diracc if not np.isnan(original_diracc) else float("nan"),
        "vs_majority_class": vs_majority,
        "majority_class_acc": majority_bl["accuracy"],
        "buy_hold_sharpe": hold_bl["sharpe"],
        "momentum_acc": momentum_bl["accuracy"],
        "n_wf_folds": len(wf_diraccs),
        "regime_avg_sharpe": regime_results.get("weighted_avg", {}).get("sharpe", float("nan")),
        "regime_avg_diracc": regime_results.get("weighted_avg", {}).get("diracc", float("nan")),
        "gross_sharpe": cost_analysis["gross_sharpe"],
        "net_sharpe": cost_analysis["net_sharpe"],
        "cost_drag_bps": cost_analysis["cost_drag_bps"],
        "n_trades": cost_analysis["n_trades"],
        "regime_details": {
            r: regime_results[r]
            for r in ["uptrend", "downtrend", "volatility", "black_swan"]
            if r in regime_results
        },
    }

    return results


def _wrap_model(model, model_type: str):
    """Wrap a PyTorch/joblib model to expose a predict() method for eval_finstsb."""

    class ModelWrapper:
        def __init__(self, inner, mtype):
            self.inner = inner
            self.mtype = mtype

        def predict(self, X):
            if self.mtype == "rf":
                n_samples, seq_len, n_features = X.shape
                return self.inner.predict(X[:, -1, :])
            else:
                import torch

                with torch.no_grad():
                    X_t = torch.tensor(X, dtype=torch.float32)
                    raw = self.inner(X_t).squeeze(-1).numpy()
                return (raw > 0).astype(int)

    return ModelWrapper(model, model_type)


def evaluate_all_checkpoints(
    checkpoint_dir: Path | None = None,
    data_dir: Path | None = None,
    output_path: Path | None = None,
) -> list[dict]:
    """Evaluate all checkpoints in the checkpoint directory.

    Returns
    -------
    list of evaluation result dicts.
    """
    if checkpoint_dir is None:
        checkpoint_dir = Path(__file__).resolve().parent.parent / "checkpoints"

    results = []
    for model_dir in sorted(checkpoint_dir.iterdir()):
        if not model_dir.is_dir():
            continue
        for ckpt_dir in sorted(model_dir.iterdir()):
            if not ckpt_dir.is_dir():
                continue
            if not (ckpt_dir / "metadata.json").exists():
                continue
            try:
                result = evaluate_checkpoint(ckpt_dir, data_dir)
                results.append(result)
                print(f"  {ckpt_dir.name}: OOS DirAcc={result['oos_diracc']:.4f} vs majority={result['vs_majority_class']:+.4f}")
            except Exception as e:
                print(f"  {ckpt_dir.name}: ERROR - {e}")
                results.append({"checkpoint": str(ckpt_dir), "error": str(e)})

    if output_path:
        with open(output_path, "w") as f:
            json.dump(results, f, indent=2, default=str)

    return results


def run_dry_run() -> dict:
    """Quick dry-run evaluation with synthetic data (no real checkpoints needed)."""
    rng = np.random.default_rng(42)
    n = 500

    df = generate_synthetic_data(n)
    engineer = FeatureEngineer(lookback=10)
    features = engineer.transform(df)
    features = features.dropna()

    X, y, _ = build_sequences(features, seq_len=10)
    y_binary = (y > 0).astype(int)

    close_prices = pd.Series(df["Close"].values[-len(X):])

    # Dummy model (predicts up with 54% accuracy)
    class DummyModel:
        def __init__(self):
            self.rng = np.random.default_rng(42)

        def predict(self, X):
            return self.rng.choice([0, 1], size=len(X), p=[0.46, 0.54])

    dummy = DummyModel()

    splitter = WalkForwardSplitter(n_splits=3, train_size=100, test_size=50, gap=5)

    wf_diraccs = []
    for train_idx, test_idx in splitter.split(X):
        if len(test_idx) == 0:
            continue
        fold_preds = dummy.predict(X[test_idx])
        diracc = np.mean(fold_preds == y_binary[test_idx])
        wf_diraccs.append(diracc)

    regime_results = eval_per_regime(dummy, X, y_binary, close_prices)

    positions = np.ones(len(X))
    cost_analysis = compare_gross_vs_net(y, positions)

    majority_bl = majority_class_baseline(y_binary[: len(X) // 2], y_binary[len(X) // 2 :])

    return {
        "dry_run": True,
        "n_samples": len(X),
        "wf_oos_diracc": np.mean(wf_diraccs),
        "wf_folds": len(wf_diraccs),
        "majority_class_acc": majority_bl["accuracy"],
        "vs_majority_class": np.mean(wf_diraccs) - majority_bl["accuracy"],
        "regime_avg_sharpe": regime_results["weighted_avg"]["sharpe"],
        "gross_sharpe": cost_analysis["gross_sharpe"],
        "net_sharpe": cost_analysis["net_sharpe"],
        "cost_drag_bps": cost_analysis["cost_drag_bps"],
    }


def main():
    parser = argparse.ArgumentParser(description="Evaluate ML/Trading checkpoints")
    parser.add_argument("--checkpoint", type=str, help="Single checkpoint directory")
    parser.add_argument("--all", action="store_true", help="Evaluate all checkpoints")
    parser.add_argument("--dry-run", action="store_true", help="Quick synthetic test")
    parser.add_argument("--checkpoint-dir", type=str, help="Checkpoint root directory")
    parser.add_argument("--data-dir", type=str, help="Data directory")
    parser.add_argument("--output", type=str, help="Output JSON path")
    args = parser.parse_args()

    if args.dry_run:
        print("=== DRY RUN ===")
        result = run_dry_run()
        for k, v in result.items():
            print(f"  {k}: {v}")
        return

    data_dir = Path(args.data_dir) if args.data_dir else None

    if args.checkpoint:
        ckpt_dir = Path(args.checkpoint)
        result = evaluate_checkpoint(ckpt_dir, data_dir)
        print(json.dumps(result, indent=2, default=str))
        if args.output:
            with open(args.output, "w") as f:
                json.dump(result, f, indent=2, default=str)
    elif args.all:
        ckpt_dir = Path(args.checkpoint_dir) if args.checkpoint_dir else None
        output_path = Path(args.output) if args.output else None
        results = evaluate_all_checkpoints(ckpt_dir, data_dir, output_path)
        print(f"\nEvaluated {len(results)} checkpoints")
    else:
        parser.print_help()


if __name__ == "__main__":
    main()
