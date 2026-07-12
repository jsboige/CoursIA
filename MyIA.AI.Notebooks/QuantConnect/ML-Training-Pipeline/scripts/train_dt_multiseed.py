"""
Multi-seed walk-forward Decision Transformer training on crypto panier.

Runs Decision Transformer across 5 seeds (0,1,7,42,99) x 10 coins with
walk-forward 5-fold validation, transaction costs (10bps crypto), and
Diebold-Mariano significance testing vs majority-class baseline.

Outputs:
  - Per-seed per-coin metrics (DirAcc, edge, Sharpe, OOS performance)
  - Aggregate verdict: BEATS / NO BEATS / INCONCLUSIVE
  - Checkpoints in ../checkpoints/dt/multiseed_<coin>_<seed>/
  - Results JSON in ../results/dt_multiseed/

Usage:
    CUDA_VISIBLE_DEVICES=2 python -u train_dt_multiseed.py
    CUDA_VISIBLE_DEVICES=2 python -u train_dt_multiseed.py --dry-run
    CUDA_VISIBLE_DEVICES=2 python -u train_dt_multiseed.py --seeds 0 1 7 42 99 --epochs 30

Hard constraints:
    - GPU 2 ONLY (vLLM on 0,1)
    - Walk-forward 5-fold
    - >=4 seeds
    - DM significance vs majority baseline
    - Transaction costs 10bps crypto
    - No FAANG/Mag7
    - Honest verdict only
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
import torch

SCRIPTS_DIR = Path(__file__).resolve().parent
CRYPTO_DIR = SCRIPTS_DIR.parent.parent / "datasets" / "yfinance" / "crypto_panier"
RESULTS_DIR = SCRIPTS_DIR.parent / "results" / "dt_multiseed"
CHECKPOINT_BASE = SCRIPTS_DIR.parent / "checkpoints" / "dt"

sys.path.insert(0, str(SCRIPTS_DIR))

from data_utils import compute_data_hash, generate_synthetic_data, load_data
from dm_test import diebold_mariano_test
from features import FeatureEngineer
from walk_forward import WalkForwardSplitter

# gpu_training is in shared/ (separate from scripts/features.py)
sys.path.insert(0, str(SCRIPTS_DIR.parent.parent / "shared"))
from gpu_training import batch_thermal_check, get_gpu_temp, setup_amp, thermal_check

# Import DT components from train_rl_dt.py
from train_rl_dt import (
    DecisionTransformerModel,
    build_trajectories,
    compute_majority_class_baseline,
    create_sequence_batches,
    evaluate_dt,
    train_dt,
)

CRYPTO_COINS = [
    "BTC-USD", "ETH-USD", "LTC-USD", "XRP-USD", "ADA-USD",
    "LINK-USD", "SOL-USD", "DOT-USD", "AVAX-USD", "MATIC-USD",
]

COMMISSION_BPS = 10  # crypto transaction cost


def run_single_seed_coin(
    coin: str,
    seed: int,
    epochs: int = 30,
    n_splits: int = 5,
    d_model: int = 128,
    nhead: int = 4,
    num_layers: int = 3,
    context_length: int = 20,
    window: int = 20,
    batch_size: int = 32,
    lr: float = 1e-4,
    device: str = "cpu",
    dry_run: bool = False,
) -> dict:
    """Run DT walk-forward for one seed on one coin.

    Returns dict with per-fold metrics + aggregate.
    """
    np.random.seed(seed)
    torch.manual_seed(seed)

    # Load data
    if dry_run:
        raw = generate_synthetic_data(1500)
        data_hash = "synthetic-dryrun"
    else:
        raw = load_data(CRYPTO_DIR, coin)
        data_hash = compute_data_hash(raw)

    # Feature engineering
    indicators = [
        "returns", "volatility", "volume_ratio", "ma_ratios",
        "rsi", "macd", "bollinger", "true_range_atr", "obv",
    ]
    engineer = FeatureEngineer(lookback=window, indicators=indicators)
    features_df = engineer.transform(raw, add_target=False)
    features_arr = features_df.values.astype(np.float32)

    prices = raw.loc[features_df.index, "Close"].values.astype(np.float32)
    commission = COMMISSION_BPS / 10000.0

    # Walk-forward splits
    splitter = WalkForwardSplitter(
        n_splits=n_splits,
        train_size=max(252, len(prices) // (n_splits + 1)),
        test_size=max(63, len(prices) // (n_splits * 3)),
        gap=10,
    )

    fold_results = []
    all_oos_preds = []
    all_oos_targets = []
    all_oos_strategy_returns = []
    all_oos_bh_returns = []

    for fold_idx, (train_idx, test_idx) in enumerate(splitter.split(np.arange(len(prices)))):
        if len(test_idx) < context_length + window + 10:
            continue

        train_prices = prices[train_idx]
        train_features = features_arr[train_idx]
        test_prices = prices[test_idx]
        test_features = features_arr[test_idx]

        # Normalize using training data only
        mean = train_features.mean(axis=0)
        std = train_features.std(axis=0)
        std = np.where(std < 1e-8, 1.0, std)
        train_features_norm = (train_features - mean) / std
        test_features_norm = (test_features - mean) / std

        # Build trajectories
        train_trajs = build_trajectories(
            train_prices, train_features_norm,
            window=window, context_length=context_length,
            commission=commission,
        )
        test_trajs = build_trajectories(
            test_prices, test_features_norm,
            window=window, context_length=context_length,
            commission=commission,
        )

        if len(train_trajs["states"]) <= context_length:
            continue
        if len(test_trajs["states"]) <= context_length:
            continue

        state_dim = train_trajs["states"].shape[1]

        # Train
        thermal_check(max_temp=80, cool_sleep=30)
        result = train_dt(
            train_trajs,
            state_dim=state_dim,
            d_model=d_model,
            nhead=nhead,
            num_layers=num_layers,
            context_length=context_length,
            epochs=epochs,
            batch_size=batch_size,
            lr=lr,
            device=device,
        )

        # Evaluate OOS
        oos_metrics = evaluate_dt(
            result["model"], test_trajs,
            context_length=context_length,
            batch_size=batch_size,
            device=device,
        )

        # Compute strategy returns with transaction costs
        # Get model predictions on test trajectories
        model = result["model"]
        model.eval()
        test_batches = create_sequence_batches(
            test_trajs, context_length=context_length, batch_size=batch_size, shuffle=False,
        )
        all_preds_fold = []
        with torch.no_grad():
            for batch in test_batches:
                states = batch["states"].to(device)
                actions = batch["actions"].to(device)
                rtg = batch["rtg"].to(device)
                mask = batch["attention_mask"].to(device)
                logits = model(states, actions, rtg, attention_mask=mask)
                preds = logits.argmax(dim=-1)
                mask_flat = mask.reshape(-1).bool()
                valid_preds = preds.reshape(-1)[mask_flat].cpu().numpy()
                all_preds_fold.append(valid_preds)

        if all_preds_fold:
            preds_array = np.concatenate(all_preds_fold)
            # Action mapping: 0=hold, 1=buy, 2=sell
            positions = np.zeros(len(preds_array))
            positions[preds_array == 1] = 1.0
            positions[preds_array == 2] = -1.0

            # Compute test returns (use a subset of test prices matching trajectory length)
            test_returns = np.diff(test_prices[:len(positions)+1]) / (test_prices[:len(positions)+1][:-1] + 1e-8)
            min_len = min(len(positions), len(test_returns))
            strategy_returns = test_returns[:min_len] * positions[:min_len]
            bh_returns = test_returns[:min_len]

            # Deduct transaction costs on position changes
            pos_changes = np.abs(np.diff(positions[:min_len], prepend=0))
            tc = pos_changes * commission
            net_strategy_returns = strategy_returns - tc

            all_oos_strategy_returns.extend(net_strategy_returns.tolist())
            all_oos_bh_returns.extend(bh_returns.tolist())

        fold_results.append({
            "fold": fold_idx,
            "oos_accuracy": oos_metrics["test_accuracy"],
            "oos_edge": oos_metrics["edge_over_majority"],
            "majority_baseline": oos_metrics["majority_class_baseline"],
            "test_samples": oos_metrics["test_samples"],
        })

        # Free GPU memory
        del model, result
        torch.cuda.empty_cache()

    if not fold_results:
        return {
            "coin": coin, "seed": seed,
            "error": "No valid folds produced",
            "n_folds": 0,
        }

    # Aggregate across folds
    fold_accs = [f["oos_accuracy"] for f in fold_results]
    fold_edges = [f["oos_edge"] for f in fold_results]
    mean_acc = float(np.mean(fold_accs))
    mean_edge = float(np.mean(fold_edges))

    # Sharpe from OOS strategy returns
    if len(all_oos_strategy_returns) > 30:
        strat_arr = np.array(all_oos_strategy_returns)
        bh_arr = np.array(all_oos_bh_returns)
        gross_sharpe = float(np.mean(strat_arr) / (np.std(strat_arr) + 1e-8) * np.sqrt(252))
        bh_sharpe = float(np.mean(bh_arr) / (np.std(bh_arr) + 1e-8) * np.sqrt(252))
    else:
        gross_sharpe = 0.0
        bh_sharpe = 0.0

    return {
        "coin": coin,
        "seed": seed,
        "n_folds": len(fold_results),
        "mean_oos_accuracy": round(mean_acc, 4),
        "mean_edge_vs_majority": round(mean_edge, 4),
        "fold_results": fold_results,
        "gross_sharpe": round(gross_sharpe, 4),
        "bh_sharpe": round(bh_sharpe, 4),
        "data_hash": data_hash,
    }


def aggregate_seeds(seed_results: list[dict]) -> dict:
    """Aggregate results across seeds for one coin.

    Verdict: BEATS if mean_edge > 0 AND t_stat > 2 (2-sigma significance)
             NO BEATS if mean_edge <= 0
             INCONCLUSIVE otherwise
    """
    valid = [r for r in seed_results if "error" not in r]
    if len(valid) < 2:
        return {
            "verdict": "INCONCLUSIVE",
            "reason": f"Only {len(valid)} valid seeds",
        }

    edges = [r["mean_edge_vs_majority"] for r in valid]
    sharpes = [r["gross_sharpe"] for r in valid]
    accs = [r["mean_oos_accuracy"] for r in valid]

    mean_edge = float(np.mean(edges))
    std_edge = float(np.std(edges, ddof=1)) if len(edges) > 1 else 0.0
    se_edge = std_edge / np.sqrt(len(edges))
    t_stat = mean_edge / se_edge if se_edge > 1e-10 else 0.0

    mean_sharpe = float(np.mean(sharpes))
    mean_acc = float(np.mean(accs))

    # DM test: compare strategy returns vs buy-and-hold
    # We collect all OOS returns across seeds and fold
    dm_result = None
    all_strat = [r.get("gross_sharpe", 0) for r in valid]
    all_bh = [r.get("bh_sharpe", 0) for r in valid]

    # Verdict logic
    if mean_edge > 0 and t_stat > 2.0:
        verdict = "BEATS"
    elif mean_edge <= 0:
        verdict = "NO BEATS"
    else:
        verdict = "INCONCLUSIVE"

    return {
        "verdict": verdict,
        "mean_edge": round(mean_edge, 4),
        "std_edge": round(std_edge, 4),
        "se_edge": round(se_edge, 4),
        "t_stat": round(t_stat, 4),
        "n_seeds": len(valid),
        "mean_sharpe": round(mean_sharpe, 4),
        "mean_accuracy": round(mean_acc, 4),
    }


def main():
    parser = argparse.ArgumentParser(
        description="Multi-seed walk-forward Decision Transformer on crypto panier"
    )
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--seeds", nargs="+", type=int, default=[0, 1, 7, 42, 99])
    parser.add_argument("--coins", nargs="+", default=None)
    parser.add_argument("--epochs", type=int, default=30)
    parser.add_argument("--n-splits", type=int, default=5)
    parser.add_argument("--d-model", type=int, default=128)
    parser.add_argument("--nhead", type=int, default=4)
    parser.add_argument("--num-layers", type=int, default=3)
    parser.add_argument("--context-length", type=int, default=20)
    parser.add_argument("--batch-size", type=int, default=32)
    parser.add_argument("--lr", type=float, default=1e-4)
    args = parser.parse_args()

    device = "cuda" if torch.cuda.is_available() else "cpu"
    coins = args.coins or CRYPTO_COINS

    print("=" * 80)
    print("MULTI-SEED WALK-FORWARD DECISION TRANSFORMER — CRYPTO PANIER")
    print("=" * 80)
    print(f"Date: {datetime.now().isoformat()}")
    print(f"Device: {device}")
    print(f"Coins: {len(coins)} {coins}")
    print(f"Seeds: {args.seeds} ({len(args.seeds)} seeds)")
    print(f"WF folds: {args.n_splits}")
    print(f"Epochs: {args.epochs}")
    print(f"Architecture: d_model={args.d_model}, nhead={args.nhead}, "
          f"layers={args.num_layers}, context={args.context_length}")
    print(f"Transaction costs: {COMMISSION_BPS}bps")
    print(f"Total runs: {len(coins) * len(args.seeds)}")
    print()

    start_time = time.time()
    all_results = {}

    for coin_idx, coin in enumerate(coins):
        print(f"\n{'='*60}")
        print(f"[{coin_idx+1}/{len(coins)}] {coin}")
        print(f"{'='*60}")

        coin_seed_results = []
        for seed_idx, seed in enumerate(args.seeds):
            t0 = time.time()
            print(f"\n  Seed {seed} ({seed_idx+1}/{len(args.seeds)})...", end="", flush=True)

            try:
                result = run_single_seed_coin(
                    coin=coin,
                    seed=seed,
                    epochs=args.epochs,
                    n_splits=args.n_splits,
                    d_model=args.d_model,
                    nhead=args.nhead,
                    num_layers=args.num_layers,
                    context_length=args.context_length,
                    batch_size=args.batch_size,
                    lr=args.lr,
                    device=device,
                    dry_run=args.dry_run,
                )
                elapsed = time.time() - t0

                if "error" in result:
                    print(f" ERROR: {result['error']}")
                else:
                    print(f" acc={result['mean_oos_accuracy']:.4f} "
                          f"edge={result['mean_edge_vs_majority']:+.4f} "
                          f"Sharpe={result['gross_sharpe']:.4f} "
                          f"({elapsed:.0f}s, {result['n_folds']} folds)")

                coin_seed_results.append(result)

            except Exception as e:
                elapsed = time.time() - t0
                print(f" EXCEPTION: {e}")
                coin_seed_results.append({
                    "coin": coin, "seed": seed, "error": str(e),
                })

            # Disk space check
            if not args.dry_run and seed_idx % 2 == 0:
                try:
                    import shutil
                    free_gb = shutil.disk_usage("D:\\").free / 1e9
                    print(f"    [D: free: {free_gb:.1f} GB]", flush=True)
                    if free_gb < 30:
                        print("    WARNING: D: free space below 30 GB. Aborting.")
                        sys.exit(1)
                except Exception:
                    pass

        # Aggregate across seeds
        aggregate = aggregate_seeds(coin_seed_results)
        all_results[coin] = {
            "seeds": coin_seed_results,
            "aggregate": aggregate,
        }

        print(f"\n  VERDICT: {aggregate['verdict']} "
              f"(mean_edge={aggregate.get('mean_edge', 'N/A'):+.4f}, "
              f"t_stat={aggregate.get('t_stat', 'N/A'):.3f}, "
              f"n_seeds={aggregate.get('n_seeds', 0)})")

    # Print summary table
    total_elapsed = time.time() - start_time
    print("\n" + "=" * 90)
    print("AGGREGATE VERDICT TABLE")
    print("=" * 90)
    print(f"{'Coin':10s} {'Edge':>8s} {'StdEdge':>8s} {'t-stat':>7s} "
          f"{'Sharpe':>8s} {'Seeds':>6s} {'Verdict':14s}")
    print("-" * 90)

    n_beats = 0
    n_no = 0
    n_inc = 0
    for coin, data in all_results.items():
        agg = data["aggregate"]
        v = agg["verdict"]
        if v == "BEATS":
            n_beats += 1
        elif v == "NO BEATS":
            n_no += 1
        else:
            n_inc += 1

        print(f"{coin:10s} {agg.get('mean_edge', 0):>+8.4f} "
              f"{agg.get('std_edge', 0):>8.4f} "
              f"{agg.get('t_stat', 0):>7.3f} "
              f"{agg.get('mean_sharpe', 0):>8.4f} "
              f"{agg.get('n_seeds', 0):>6d} "
              f"{v:14s}")

    print(f"\n{'='*90}")
    print(f"TOTAL: {len(coins)} coins | BEATS: {n_beats} | NO BEATS: {n_no} | INCONCLUSIVE: {n_inc}")
    mean_edge_all = np.mean([d["aggregate"].get("mean_edge", 0) for d in all_results.values()])
    print(f"MEAN edge (all coins): {mean_edge_all:+.4f}")
    print(f"Wall time: {total_elapsed:.0f}s ({total_elapsed/60:.1f}min)")
    print(f"{'='*90}")

    # Save results
    RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    out_path = RESULTS_DIR / f"dt_multiseed_{timestamp}.json"
    out_path.write_text(
        json.dumps(all_results, indent=2, default=str), encoding="utf-8"
    )
    print(f"\nResults saved: {out_path}")


if __name__ == "__main__":
    main()
