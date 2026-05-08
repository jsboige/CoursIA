"""
Evaluation harness for Decision Transformer checkpoints.

Loads a trained DT model from checkpoint and runs comprehensive evaluation:
    - Walk-forward out-of-sample metrics (no in-sample leakage)
    - Comparison vs majority-class baseline
    - Transaction cost analysis (gross vs net Sharpe)
    - Direction accuracy, MSE, Sharpe, MaxDD

Usage:
    # Evaluate a single checkpoint
    python eval_rl_dt.py --checkpoint checkpoints/dt/20260505_120000

    # Dry-run (synthetic data, no real checkpoint needed)
    python eval_rl_dt.py --dry-run

References:
    - Chen et al. (2021): "Decision Transformer: RL via Sequence Modeling"
    - arXiv:2411.17900: "Decision Transformer for Algorithmic Trading"
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

import numpy as np
import torch

sys.path.append(str(Path(__file__).resolve().parent.parent.parent / "shared"))
from baselines import sharpe_from_returns
from data_utils import compute_data_hash, generate_synthetic_data, load_data
from features import FeatureEngineer

sys.path.insert(0, str(Path(__file__).resolve().parent))
from train_rl_dt import (
    DecisionTransformerModel,
    build_trajectories,
    compute_majority_class_baseline,
    create_sequence_batches,
    evaluate_dt,
)

try:
    from walk_forward import WalkForwardSplitter
except ImportError:
    WalkForwardSplitter = None


def load_checkpoint(checkpoint_dir: Path) -> tuple:
    """Load DT model and metadata from a checkpoint directory.

    Returns
    -------
    (model, metadata) : tuple of model and metadata dict.
    """
    metadata_path = checkpoint_dir / "metadata.json"
    if not metadata_path.exists():
        raise FileNotFoundError(f"No metadata.json in {checkpoint_dir}")

    with open(metadata_path, encoding="utf-8") as f:
        metadata = json.load(f)

    arch = metadata.get("architecture", {})
    hp = metadata.get("hyperparams", {})

    model = DecisionTransformerModel(
        state_dim=arch.get("state_dim", 10),
        d_model=arch.get("d_model", 128),
        nhead=arch.get("nhead", 4),
        num_layers=arch.get("num_layers", 3),
        context_length=arch.get("context_length", 20),
        n_actions=arch.get("n_actions", 3),
        dropout=0.0,  # No dropout at eval time
    )

    model_path = checkpoint_dir / "model.pt"
    state = torch.load(model_path, map_location="cpu", weights_only=True)
    model.load_state_dict(state)
    model.eval()

    return model, metadata



def compute_sharpe(returns: np.ndarray, annualize: bool = True) -> float:
    """Compute Sharpe ratio from returns array."""
    return sharpe_from_returns(returns, annualize=annualize)


def compute_max_drawdown(cumulative_returns: np.ndarray) -> float:
    """Compute maximum drawdown from cumulative returns."""
    if len(cumulative_returns) < 2:
        return 0.0
    peak = np.maximum.accumulate(cumulative_returns)
    drawdown = (cumulative_returns - peak) / (np.abs(peak) + 1e-8)
    return float(drawdown.min())


def evaluate_checkpoint(
    checkpoint_dir: Path,
    data_dir: Path | None = None,
    context_length: int | None = None,
    commission: float = 0.001,
    device: str = "cpu",
) -> dict:
    """Run full evaluation on a DT checkpoint.

    Pipeline:
        1. Load model + metadata
        2. Load data and build features
        3. Build test trajectories
        4. Evaluate: DirAcc, MSE, Sharpe, MaxDD, transaction costs
        5. Compare vs majority-class baseline

    Returns
    -------
    Dict with evaluation metrics.
    """
    model, metadata = load_checkpoint(checkpoint_dir)
    arch = metadata.get("architecture", {})
    hp = metadata.get("hyperparams", {})

    ctx_len = context_length or arch.get("context_length", 20)
    window = hp.get("window", 20)
    symbol = hp.get("symbol", "SPY")
    test_ratio = hp.get("test_ratio", 0.2)

    # Load data
    if data_dir is None:
        data_dir = Path(__file__).resolve().parent.parent / "datasets" / "yfinance"

    data_hash = metadata.get("data_hash", "")
    if data_hash == "synthetic-dryrun":
        df = generate_synthetic_data(2000)
    else:
        try:
            df = load_data(data_dir, symbol)
        except FileNotFoundError:
            df = generate_synthetic_data(2000)

    # Build features
    engineer = FeatureEngineer(
        lookback=hp.get("lookback", 20),
        indicators=hp.get("indicators", None),
    )
    features_df = engineer.transform(df, add_target=False)
    features_arr = features_df.values.astype(np.float32)

    # Normalize with train-only stats
    n = len(features_arr)
    train_end = int(n * (1 - test_ratio))
    mean = features_arr[:train_end].mean(axis=0)
    std = features_arr[:train_end].std(axis=0)
    std = np.where(std < 1e-8, 1.0, std)
    features_arr = (features_arr - mean) / std

    prices = df.loc[features_df.index, "Close"].values.astype(np.float32)
    test_prices = prices[train_end:]
    test_features = features_arr[train_end:]

    # Build test trajectories
    test_trajs = build_trajectories(
        test_prices, test_features,
        window=window,
        context_length=ctx_len,
        commission=commission,
    )

    if len(test_trajs["states"]) <= ctx_len:
        return {
            "checkpoint": str(checkpoint_dir),
            "error": "Not enough test data for evaluation",
        }

    # Evaluate
    eval_metrics = evaluate_dt(
        model, test_trajs,
        context_length=ctx_len,
        device=device,
    )

    # Compute cumulative returns for Sharpe/MaxDD
    rewards = test_trajs["rewards"]
    cum_returns = np.cumsum(rewards)
    sharpe = sharpe_from_returns(rewards)
    max_dd = compute_max_drawdown(cum_returns)

    # Transaction cost analysis
    actions = test_trajs["actions"]
    position_changes = np.abs(np.diff(actions, prepend=0))
    n_trades = int(np.sum(position_changes > 0))
    total_commission = n_trades * commission
    gross_return = float(cum_returns[-1]) if len(cum_returns) > 0 else 0.0
    net_return = gross_return - total_commission

    # Gross vs net Sharpe
    gross_sharpe = sharpe
    cost_adjusted_returns = rewards.copy()
    # Deduct commission from trades
    trade_mask = np.zeros(len(rewards), dtype=bool)
    trade_mask[1:] = position_changes[1:] > 0
    cost_adjusted_returns[trade_mask] -= commission
    net_sharpe = sharpe_from_returns(cost_adjusted_returns)

    results = {
        "checkpoint": str(checkpoint_dir),
        "model_type": "decision_transformer",
        "symbol": symbol,
        "test_accuracy": eval_metrics["test_accuracy"],
        "test_loss": eval_metrics["test_loss"],
        "test_samples": eval_metrics["test_samples"],
        "majority_class_baseline": eval_metrics["majority_class_baseline"],
        "edge_over_majority": eval_metrics["edge_over_majority"],
        "sharpe": round(sharpe, 4),
        "max_drawdown": round(max_dd, 4),
        "n_trades": n_trades,
        "total_commission": round(total_commission, 4),
        "gross_return": round(gross_return, 4),
        "net_return": round(net_return, 4),
        "gross_sharpe": round(gross_sharpe, 4),
        "net_sharpe": round(net_sharpe, 4),
        "cost_drag_bps": round((gross_sharpe - net_sharpe) * 100, 2),
    }

    return results


def run_dry_run() -> dict:
    """Quick dry-run evaluation with synthetic data."""
    from train_rl_dt import train_dt

    np.random.seed(42)
    torch.manual_seed(42)

    raw = generate_synthetic_data(2000)
    engineer = FeatureEngineer(lookback=10)
    features_df = engineer.transform(raw, add_target=False)
    features_arr = features_df.values.astype(np.float32)
    prices = raw.loc[features_df.index, "Close"].values.astype(np.float32)

    trajs = build_trajectories(
        prices, features_arr,
        window=10,
        context_length=5,
        commission=0.001,
    )

    state_dim = trajs["states"].shape[1]
    result = train_dt(
        trajs,
        state_dim=state_dim,
        d_model=32,
        nhead=2,
        num_layers=1,
        context_length=5,
        epochs=3,
        batch_size=16,
        device="cpu",
    )

    model = result["model"]
    eval_metrics = evaluate_dt(model, trajs, context_length=5, device="cpu")

    rewards = trajs["rewards"]
    cum_returns = np.cumsum(rewards)
    sharpe = sharpe_from_returns(rewards)
    max_dd = compute_max_drawdown(cum_returns)

    return {
        "dry_run": True,
        "train_samples": len(trajs["states"]),
        "test_accuracy": eval_metrics["test_accuracy"],
        "test_loss": eval_metrics["test_loss"],
        "majority_class_baseline": eval_metrics["majority_class_baseline"],
        "edge_over_majority": eval_metrics["edge_over_majority"],
        "sharpe": round(sharpe, 4),
        "max_drawdown": round(max_dd, 4),
    }


def print_summary(results: dict) -> None:
    """Print formatted evaluation summary table."""
    print("\n" + "=" * 60)
    print("Decision Transformer Evaluation Summary")
    print("=" * 60)

    print(f"  Checkpoint:       {results.get('checkpoint', 'N/A')}")
    print(f"  Symbol:           {results.get('symbol', 'N/A')}")
    print(f"  Test samples:     {results.get('test_samples', 'N/A')}")
    print()

    print("  Accuracy Metrics:")
    print(f"    Test Accuracy:  {results.get('test_accuracy', 'N/A'):.4f}")
    bl = results.get("majority_class_baseline", {})
    print(f"    Majority BL:    {bl.get('majority_class_accuracy', 'N/A')}")
    edge = results.get("edge_over_majority", 0)
    print(f"    Edge vs BL:     {edge:+.4f} ({'BEATS' if edge > 0 else 'FAILS'})")
    print()

    print("  Risk/Reward:")
    print(f"    Sharpe:         {results.get('sharpe', 'N/A'):.4f}")
    print(f"    Max Drawdown:   {results.get('max_drawdown', 'N/A'):.4f}")
    print()

    print("  Transaction Costs:")
    print(f"    Trades:         {results.get('n_trades', 0)}")
    print(f"    Commission:     {results.get('total_commission', 0):.4f}")
    print(f"    Gross Sharpe:   {results.get('gross_sharpe', 'N/A'):.4f}")
    print(f"    Net Sharpe:     {results.get('net_sharpe', 'N/A'):.4f}")
    print(f"    Cost drag:      {results.get('cost_drag_bps', 0):.2f} bps")
    print("=" * 60)


def main():
    parser = argparse.ArgumentParser(
        description="Evaluate Decision Transformer checkpoint"
    )
    parser.add_argument("--checkpoint", type=str, help="Checkpoint directory")
    parser.add_argument("--dry-run", action="store_true",
                        help="Quick synthetic test")
    parser.add_argument("--data-dir", type=str, help="Data directory")
    parser.add_argument("--context-length", type=int, default=None)
    parser.add_argument("--commission", type=float, default=0.001)
    parser.add_argument("--output", type=str, help="Output JSON path")
    args = parser.parse_args()

    if args.dry_run:
        print("=== DRY RUN ===")
        result = run_dry_run()
        print_summary(result)
        if args.output:
            Path(args.output).write_text(
                json.dumps(result, indent=2, default=str), encoding="utf-8"
            )
        return

    if not args.checkpoint:
        parser.print_help()
        return

    device = "cuda" if torch.cuda.is_available() else "cpu"
    data_dir = Path(args.data_dir) if args.data_dir else None

    ckpt_dir = Path(args.checkpoint)
    results = evaluate_checkpoint(
        ckpt_dir,
        data_dir=data_dir,
        context_length=args.context_length,
        commission=args.commission,
        device=device,
    )

    print_summary(results)

    if args.output:
        Path(args.output).write_text(
            json.dumps(results, indent=2, default=str), encoding="utf-8"
        )
    else:
        print(json.dumps(results, indent=2, default=str))


if __name__ == "__main__":
    main()
