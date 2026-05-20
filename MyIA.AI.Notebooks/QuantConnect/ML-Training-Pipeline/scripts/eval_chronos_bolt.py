"""
Stage 5: Chronos-Bolt zero-shot evaluation for financial time-series forecasting.

Evaluates Amazon Chronos-Bolt (amazon/chronos-bolt-base, ~200M params) in zero-shot
mode. Chronos-Bolt uses T5 encoder-decoder with tokenization of continuous values,
trained on ~100B time series observations. 250x faster than original Chronos.

Companion to eval_kronos_zeroshot.py for cross-model comparison.

References:
    - Chronos: Learning the Language of Time Series (Rasul et al., 2024)
    - Chronos-Bolt: Amazon Science, 2025

Usage:
    # Dry-run (CPU, synthetic data)
    python eval_chronos_bolt.py --dry-run

    # Evaluate on SPY
    python eval_chronos_bolt.py --data-dir ../datasets/yfinance --symbol SPY

    # Walk-forward 5-fold evaluation
    python eval_chronos_bolt.py --data-dir ../datasets/yfinance --symbol SPY \
        --walk-forward --n-splits 5

    # Multi-seed validation (>=4 seeds, edge >= 2*std required for BEATS claim)
    python eval_chronos_bolt.py --dry-run --seeds 0,1,7,42,99

Output:
    results.json with metrics, regime breakdown, majority-class comparison
"""

from __future__ import annotations

import argparse
import json
import sys
from datetime import datetime
from pathlib import Path

import numpy as np
import pandas as pd

sys.path.append(str(Path(__file__).resolve().parent.parent.parent / "shared"))
from data_utils import load_data

from eval_kronos_zeroshot import (
    build_evaluation_windows,
    compute_majority_baseline,
    compute_transaction_cost,
    evaluate_window,
)

CHRONOS_MODEL_IDS = {
    "small": "amazon/chronos-bolt-small",
    "base": "amazon/chronos-bolt-base",
    "large": "amazon/chronos-bolt-large",
}


def load_chronos_model(
    model_size: str = "base", device: str = "auto"
) -> "ChronosBoltWrapper":
    """Load Chronos-Bolt model from HuggingFace."""
    model_id = CHRONOS_MODEL_IDS.get(model_size, CHRONOS_MODEL_IDS["base"])
    try:
        from chronos import ChronosPipeline

        pipeline = ChronosPipeline.from_pretrained(model_id, device_map=device)
        return ChronosBoltWrapper(pipeline, model_id=model_id)
    except ImportError:
        print(
            "[WARN] chronos-forecasting not installed. Using naive wrapper. "
            "Install with: pip install chronos-forecasting"
        )
        return NaiveChronosWrapper(model_id=model_id)


class ChronosBoltWrapper:
    """Wrapper for Chronos-Bolt foundation model inference."""

    def __init__(self, pipeline, model_id: str = ""):
        self.pipeline = pipeline
        self.model_id = model_id

    def predict(
        self, context: np.ndarray, pred_len: int = 24
    ) -> np.ndarray:
        """Generate zero-shot forecast via Chronos-Bolt.

        Parameters
        ----------
        context : np.ndarray, shape (seq_len,)
            Historical time series values.
        pred_len : int
            Number of future steps to predict.

        Returns
        -------
        np.ndarray, shape (pred_len,)
            Median forecast values.
        """
        import torch

        tensor = torch.tensor(context, dtype=torch.float32).unsqueeze(0)
        samples = self.pipeline.predict(tensor, prediction_length=pred_len)
        return samples.median(dim=1).values.squeeze().numpy()

    @property
    def is_mock(self) -> bool:
        return False


class NaiveChronosWrapper:
    """Naive wrapper when Chronos is not installed."""

    def __init__(self, model_id: str = ""):
        self.model_id = model_id

    def predict(
        self, context: np.ndarray, pred_len: int = 24
    ) -> np.ndarray:
        last_val = context[-1] if context.ndim == 1 else context[-1, 0]
        return np.full(pred_len, last_val)

    @property
    def is_mock(self) -> bool:
        return True


def run_evaluation(args: argparse.Namespace) -> dict:
    """Run full zero-shot evaluation."""
    print(f"Loading Chronos-Bolt model ({args.model_size})...")
    device = "cpu" if args.dry_run else "auto"
    model = load_chronos_model(args.model_size, device=device)
    print(f"  Model: {model.model_id} (mock={model.is_mock})")

    if args.dry_run:
        np.random.seed(42)
        n_points = args.seq_len + args.pred_len + args.n_windows * args.pred_len
        dates = pd.date_range("2020-01-01", periods=n_points, freq="B")
        prices = pd.Series(
            np.cumsum(np.random.randn(n_points) * 0.01 + 100), index=dates
        )
        symbol = "SYNTHETIC"
    else:
        data_path = Path(args.data_dir)
        prices_df = load_data(data_path, symbol=args.symbol)
        prices = prices_df["Close"]
        symbol = args.symbol

    print(f"Data: {symbol}, {len(prices)} points")
    baseline = compute_majority_baseline(np.asarray(prices.pct_change().dropna().values))
    print(f"  Majority baseline: {baseline['majority_class_accuracy']:.4f}")

    windows = build_evaluation_windows(
        prices, seq_len=args.seq_len, pred_len=args.pred_len, n_windows=args.n_windows
    )
    print(f"  Evaluation windows: {len(windows)}")

    results_per_window = []
    for i, window in enumerate(windows):
        metrics = evaluate_window(
            model, window, pred_len=args.pred_len, cost_bps=args.cost_bps
        )
        metrics["window"] = i
        metrics["start"] = window["start_date"]
        metrics["end"] = window["end_date"]
        results_per_window.append(metrics)
        print(
            f"  Window {i}: DirAcc={metrics['direction_accuracy']:.4f}, "
            f"MSE={metrics['mse']:.6f}, Sharpe={metrics['sharpe']:.3f}"
        )

    avg_dir_acc = np.mean([r["direction_accuracy"] for r in results_per_window])
    avg_sharpe = np.mean([r["sharpe"] for r in results_per_window])
    edge_vs_majority = avg_dir_acc - baseline["majority_class_accuracy"]

    summary = {
        "model": model.model_id,
        "is_mock": model.is_mock,
        "symbol": symbol,
        "seq_len": args.seq_len,
        "pred_len": args.pred_len,
        "n_windows": len(windows),
        "avg_direction_accuracy": float(avg_dir_acc),
        "avg_sharpe": float(avg_sharpe),
        "majority_baseline": baseline,
        "edge_vs_majority": float(edge_vs_majority),
        "windows": results_per_window,
        "timestamp": datetime.now().isoformat(),
    }

    print(f"\n=== Chronos-Bolt Results ===")
    print(f"  Avg DirAcc: {avg_dir_acc:.4f}")
    print(f"  Majority:   {baseline['majority_class_accuracy']:.4f}")
    print(f"  Edge:       {edge_vs_majority:+.4f}")
    print(f"  Avg Sharpe: {avg_sharpe:.3f}")

    if args.output_dir:
        out_path = Path(args.output_dir)
        out_path.mkdir(parents=True, exist_ok=True)
        out_file = out_path / f"chronos_zeroshot_{symbol}_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
        with open(out_file, "w") as f:
            json.dump(summary, f, indent=2)
        print(f"  Saved to: {out_file}")

    return summary


def run_walk_forward(args: argparse.Namespace) -> dict:
    """Walk-forward K-fold evaluation respecting temporal ordering.

    Each fold uses expanding window: train on [0..split_i], evaluate on
    [split_i..split_i+pred_len]. No shuffle, no data leakage.
    """
    device = "cpu" if args.dry_run else "auto"
    model = load_chronos_model(args.model_size, device=device)

    if args.dry_run:
        np.random.seed(42)
        n_points = 500
        dates = pd.date_range("2020-01-01", periods=n_points, freq="B")
        prices = pd.Series(
            np.cumsum(np.random.randn(n_points) * 0.01 + 100), index=dates
        )
        symbol = "SYNTHETIC"
    else:
        data_path = Path(args.data_dir)
        prices_df = load_data(data_path, symbol=args.symbol)
        prices = prices_df["Close"]
        symbol = args.symbol

    returns = prices.pct_change().dropna().values
    n = len(returns)
    n_splits = args.n_splits
    fold_size = n // (n_splits + 1)

    baseline = compute_majority_baseline(np.asarray(returns))
    fold_results = []

    for fold_i in range(n_splits):
        split_point = fold_size * (fold_i + 1)
        if split_point < args.seq_len:
            continue
        eval_end = min(split_point + args.pred_len + args.seq_len, n)
        if split_point + args.seq_len >= eval_end:
            continue

        ctx = prices.iloc[split_point - args.seq_len : split_point].values
        actual = prices.iloc[split_point : eval_end].values
        actual_rets = returns[split_point : eval_end - 1]

        window = {
            "context": ctx,
            "actual_prices": actual,
            "actual_returns": actual_rets,
            "start_date": str(prices.index[split_point - args.seq_len]),
            "end_date": str(prices.index[min(eval_end - 1, n - 1)]),
        }
        metrics = evaluate_window(model, window, pred_len=args.pred_len, cost_bps=args.cost_bps)  # type: ignore[arg-type]
        metrics["fold"] = fold_i
        metrics["train_size"] = split_point
        fold_results.append(metrics)
        print(
            f"  Fold {fold_i}: DirAcc={metrics['direction_accuracy']:.4f}, "
            f"Sharpe={metrics['sharpe']:.3f} (train={split_point} pts)"
        )

    if not fold_results:
        print("[WARN] No valid folds produced")
        return {"n_folds": 0, "error": "insufficient data for walk-forward"}

    avg_dir_acc = np.mean([r["direction_accuracy"] for r in fold_results])
    avg_sharpe = np.mean([r["sharpe"] for r in fold_results])
    edge = avg_dir_acc - baseline["majority_class_accuracy"]

    summary = {
        "model": model.model_id,
        "is_mock": model.is_mock,
        "symbol": symbol,
        "evaluation_type": "walk_forward",
        "n_splits": n_splits,
        "n_folds": len(fold_results),
        "avg_direction_accuracy": float(avg_dir_acc),
        "avg_sharpe": float(avg_sharpe),
        "majority_baseline": baseline,
        "edge_vs_majority": float(edge),
        "folds": fold_results,
        "timestamp": datetime.now().isoformat(),
    }

    print(f"\n=== Walk-Forward Results ({len(fold_results)} folds) ===")
    print(f"  Avg DirAcc: {avg_dir_acc:.4f}")
    print(f"  Majority:   {baseline['majority_class_accuracy']:.4f}")
    print(f"  Edge:       {edge:+.4f}")

    if args.output_dir:
        out_path = Path(args.output_dir)
        out_path.mkdir(parents=True, exist_ok=True)
        out_file = out_path / f"chronos_wf_{symbol}_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
        with open(out_file, "w") as f:
            json.dump(summary, f, indent=2)

    return summary


def run_multi_seed(args: argparse.Namespace) -> dict:
    """Multi-seed validation per feedback_multi_seed_required.md.

    BEATS claim requires >=4 seeds with edge >= 2*std cross-seed.
    """
    seeds = [int(s) for s in args.seeds.split(",")]
    if len(seeds) < 4:
        print(f"[WARN] {len(seeds)} seeds provided, >=4 recommended for BEATS claims")

    device = "cpu" if args.dry_run else "auto"
    model = load_chronos_model(args.model_size, device=device)

    if args.dry_run:
        symbol = "SYNTHETIC"
    else:
        symbol = args.symbol

    seed_results = []
    for seed in seeds:
        np.random.seed(seed)

        if args.dry_run:
            n_points = args.seq_len + args.pred_len + args.n_windows * args.pred_len
            dates = pd.date_range("2020-01-01", periods=n_points, freq="B")
            prices = pd.Series(
                np.cumsum(np.random.randn(n_points) * 0.01 + 100), index=dates
            )
        else:
            data_path = Path(args.data_dir)
            prices_df = load_data(data_path, symbol=symbol)
            prices = prices_df["Close"]

        baseline = compute_majority_baseline(
            np.asarray(prices.pct_change().dropna().values)
        )
        windows = build_evaluation_windows(
            prices, seq_len=args.seq_len, pred_len=args.pred_len, n_windows=args.n_windows
        )

        window_metrics = []
        for window in windows:
            m = evaluate_window(model, window, pred_len=args.pred_len, cost_bps=args.cost_bps)  # type: ignore[arg-type]
            window_metrics.append(m)

        avg_dir_acc = np.mean([m["direction_accuracy"] for m in window_metrics])
        edge = avg_dir_acc - baseline["majority_class_accuracy"]

        seed_results.append({
            "seed": seed,
            "avg_direction_accuracy": float(avg_dir_acc),
            "majority_baseline": baseline["majority_class_accuracy"],
            "edge_vs_majority": float(edge),
        })
        verdict = "BEATS" if edge > 0 else "FAILS"
        print(f"  Seed {seed}: DirAcc={avg_dir_acc:.4f}, Edge={edge:+.4f} [{verdict}]")

    edges = np.array([r["edge_vs_majority"] for r in seed_results])
    mean_edge = float(np.mean(edges))
    std_edge = float(np.std(edges))
    n_beats = int(np.sum(edges > 0))

    beats_valid = len(seeds) >= 4 and mean_edge > 0 and (
        std_edge < 1e-10 or mean_edge >= 2 * std_edge
    )

    summary = {
        "model": model.model_id,
        "is_mock": model.is_mock,
        "symbol": symbol,
        "evaluation_type": "multi_seed",
        "seeds": seeds,
        "n_beats": n_beats,
        "n_seeds": len(seeds),
        "mean_edge": mean_edge,
        "std_edge": std_edge,
        "beats_valid": beats_valid,
        "seed_results": seed_results,
        "timestamp": datetime.now().isoformat(),
    }

    print(f"\n=== Multi-Seed Results ({len(seeds)} seeds) ===")
    print(f"  Mean Edge: {mean_edge:+.4f} (std={std_edge:.4f})")
    print(f"  BEATS: {n_beats}/{len(seeds)} seeds")
    print(f"  Valid BEATS claim: {beats_valid}")

    if args.output_dir:
        out_path = Path(args.output_dir)
        out_path.mkdir(parents=True, exist_ok=True)
        out_file = out_path / f"chronos_multiseed_{symbol}_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
        with open(out_file, "w") as f:
            json.dump(summary, f, indent=2)

    return summary


def main():
    parser = argparse.ArgumentParser(
        description="Chronos-Bolt zero-shot evaluation on financial time series"
    )
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--data-dir", default="../datasets/yfinance", type=str)
    parser.add_argument("--symbol", default="SPY", type=str)
    parser.add_argument("--model-size", default="base", type=str,
                        choices=list(CHRONOS_MODEL_IDS.keys()))
    parser.add_argument("--seq-len", default=96, type=int)
    parser.add_argument("--pred-len", default=24, type=int)
    parser.add_argument("--n-windows", default=5, type=int)
    parser.add_argument("--n-splits", default=5, type=int,
                        help="Number of walk-forward folds")
    parser.add_argument("--cost-bps", default=10.0, type=float)
    parser.add_argument("--output-dir", default=None, type=str)
    parser.add_argument("--walk-forward", action="store_true",
                        help="Use walk-forward K-fold evaluation")
    parser.add_argument("--seeds", default=None, type=str,
                        help="Comma-separated seeds for multi-seed validation (e.g. 0,1,7,42,99)")
    args = parser.parse_args()

    if args.seeds:
        run_multi_seed(args)
    elif args.walk_forward:
        run_walk_forward(args)
    else:
        run_evaluation(args)


if __name__ == "__main__":
    main()
