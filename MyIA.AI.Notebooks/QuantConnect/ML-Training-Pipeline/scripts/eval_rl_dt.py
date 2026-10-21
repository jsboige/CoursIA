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

from validate_xrp_dt import (
    CAUSAL_EVAL_PROTOCOL,
    causal_eval_series,
    dt_causal_positions,
    gross_returns,
    net_returns,
    train_rtg_per_step,
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



import strategy_metrics  # noqa: E402


def compute_sharpe(returns: np.ndarray, annualize: bool = True) -> float:
    """Compute Sharpe ratio from returns series (``strategy_metrics.sharpe``).

    Returns 0.0 for fewer than 2 returns or a standard deviation below 1e-12.
    The formula used the population standard deviation (ddof=0) through
    ``baselines.sharpe_from_returns`` until #19016: the standard deviation
    grows by ``sqrt(n / (n - 1))``, so the value is multiplied by
    ``sqrt((n - 1) / n)`` -- pinned by the tranche-4 tests.
    """
    if len(returns) < 2 or float(np.std(returns, ddof=1)) < 1e-12:
        return 0.0
    return float(strategy_metrics.sharpe(
        returns, periods_per_year=252 if annualize else 1))


def compute_max_drawdown(returns: np.ndarray) -> float:
    """Max drawdown from a returns series (``strategy_metrics.max_drawdown``).

    Returns 0.0 for fewer than 2 returns. The input used to be a cumulative-sum
    path normalised by ``abs(peak) + 1e-8``; it is now the returns series, so the
    value is a fraction of wealth, like the shared definition.
    """
    if len(returns) < 2:
        return 0.0
    return strategy_metrics.max_drawdown(returns)


def dt_trading_metrics(
    model,
    prices: np.ndarray,
    features: np.ndarray,
    window: int,
    context_length: int,
    rtg_per_step: float,
    commission: float,
    device: str = "cpu",
    batch_size: int = 64,
) -> dict:
    """Trading metrics of the DT's own decisions (#21187, ``causal-v1``).

    One decision per step, computed on states up to the previous row, with the
    fixed RTG schedule ``rtg_per_step * (remaining steps)``: no input reads a
    test reward. Positions are +1 (buy) / -1 (sell) / 0 (hold), each applied to
    the next return. Costs are ``|delta position| * commission``. Buy-and-hold is
    scored on the same returns.

    Until #21187 this script reported the Sharpe, drawdown and trade count of
    ``trajectories["rewards"]``, i.e. of the momentum teacher, not of the
    model, and deducted the commission a second time from rewards that
    already carried it.
    """
    positions, first_k = dt_causal_positions(
        model, prices, features, window, context_length, rtg_per_step,
        batch_size=batch_size, device=device,
    )
    dt_pos, _mom, _bh, rets = causal_eval_series(prices, positions, first_k, window)
    gross = gross_returns(dt_pos, rets)
    net = net_returns(dt_pos, rets, commission)
    changes = np.abs(np.diff(dt_pos, prepend=0.0))
    gross_sharpe = compute_sharpe(gross)
    net_sharpe = compute_sharpe(net)
    # Cost drag in basis points of (additive) return, as ``transaction_costs``
    # reports it. Until #21187 this key held the Sharpe gap times 100.
    commission_paid = float(np.sum(gross - net))
    return {
        "n_returns": int(len(rets)),
        "sharpe": round(net_sharpe, 4),
        "max_drawdown": round(compute_max_drawdown(net), 4),
        "n_trades": int(np.sum(changes > 0)),
        "exposure": round(float(np.mean(dt_pos != 0)) if len(dt_pos) else 0.0, 4),
        "total_commission": round(commission_paid, 4),
        "gross_return": round(float(np.sum(gross)), 4),
        "net_return": round(float(np.sum(net)), 4),
        "gross_sharpe": round(gross_sharpe, 4),
        "net_sharpe": round(net_sharpe, 4),
        "cost_drag_bps": round(commission_paid * 10_000, 2),
        "bh_sharpe": round(compute_sharpe(rets), 4),
    }


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

    # RTG target fixed before the test set: mean teacher reward per step on
    # the training rows (#21187). The realized test RTG sums future rewards.
    train_trajs = build_trajectories(
        prices[:train_end], features_arr[:train_end],
        window=window,
        context_length=ctx_len,
        commission=commission,
    )
    rtg_step = train_rtg_per_step(train_trajs)

    eval_metrics = evaluate_dt(
        model, test_trajs,
        context_length=ctx_len,
        device=device,
        rtg_per_step=rtg_step,
    )
    trading = dt_trading_metrics(
        model, test_prices, test_features, window, ctx_len, rtg_step,
        commission=commission, device=device,
    )

    results = {
        "checkpoint": str(checkpoint_dir),
        "model_type": "decision_transformer",
        "symbol": symbol,
        "eval_protocol": CAUSAL_EVAL_PROTOCOL,
        "rtg_mode": eval_metrics["rtg_mode"],
        "rtg_per_step": rtg_step,
        "test_accuracy": eval_metrics["test_accuracy"],
        "test_loss": eval_metrics["test_loss"],
        "test_samples": eval_metrics["test_samples"],
        "majority_class_baseline": eval_metrics["majority_class_baseline"],
        "edge_over_majority": eval_metrics["edge_over_majority"],
        **trading,
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
    rtg_step = train_rtg_per_step(trajs)
    eval_metrics = evaluate_dt(model, trajs, context_length=5, device="cpu",
                               rtg_per_step=rtg_step)
    trading = dt_trading_metrics(model, prices, features_arr, window=10,
                                 context_length=5, rtg_per_step=rtg_step,
                                 commission=0.001, device="cpu")

    return {
        "dry_run": True,
        "eval_protocol": CAUSAL_EVAL_PROTOCOL,
        "rtg_mode": eval_metrics["rtg_mode"],
        "train_samples": len(trajs["states"]),
        "test_accuracy": eval_metrics["test_accuracy"],
        "test_loss": eval_metrics["test_loss"],
        "majority_class_baseline": eval_metrics["majority_class_baseline"],
        "edge_over_majority": eval_metrics["edge_over_majority"],
        **trading,
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

    print(f"  Protocol:         {results.get('eval_protocol', 'N/A')} "
          f"(RTG {results.get('rtg_mode', 'N/A')})")
    print("  Risk/Reward (DT decisions, net of costs):")
    print(f"    Sharpe:         {results.get('sharpe', 'N/A'):.4f}")
    print(f"    Max Drawdown:   {results.get('max_drawdown', 'N/A'):.4f}")
    print(f"    Exposure:       {results.get('exposure', 'N/A')}")
    print(f"    Buy & hold:     {results.get('bh_sharpe', 'N/A')}")
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
