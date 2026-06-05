"""
Ablation study: RTG information leak in Decision Transformer trading eval.

PURPOSE:
    Determine whether the "BEATS" verdict in L4/L6 Decision Transformer sweeps
    is driven by genuine learned skill or by the forward-looking Return-To-Go
    (RTG) signal leaked into the model at test time.

    The status quo eval pipeline feeds REALIZED RTG (cumulative future reward)
    into the DT at inference. This is information-theoretically equivalent to
    giving the model a summary of future returns before it predicts the action.

CONDITIONS:
    A. REALIZED-RTG (status quo): feed batch["rtg"] unchanged (leaked).
    B. FIXED-G: replace ALL rtg values in eval sequences with a single CONSTANT
       desired-return prompt = 90th percentile of training-set per-trajectory
       initial RTG. This removes future info while keeping a "aim high" signal.
    C. RANDOM-TIMING: ignore the model entirely; generate random actions with
       per-symbol trade frequency matched to condition A. Isolates the cash-
       timing Sharpe artifact from variable-sizing portfolios.

VERDICT CRITERIA:
    - "LEAK-DOMINATED" if A >> B ≈ C
    - "PARTIAL-SKILL" if C < B < A
    - "SKILL-CONFIRMED" if B ≈ A and both >> C

SYMBOLS: [SPY, XLF, XLK, IEF, GLD, USO] (6 representative assets)
SEEDS: [0, 1, 7, 42] (4 seeds, L4 default)
WF: 5-fold, L4 defaults for window/context_length/commission

GPU: CUDA_VISIBLE_DEVICES=2 (RTX 4090, shared with co-resident L6 sweep)

NON-DESTRUCTIVE: imports utilities read-only, does not modify any existing script.

Usage:
    python -u ablation_rtg_leak.py
    python -u ablation_rtg_leak.py --symbols SPY QQQ --seeds 0 42
    python -u ablation_rtg_leak.py --smoke
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

import numpy as np
import pandas as pd
import torch

SCRIPTS_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS_DIR))

from panier_loader import load_panier
from train_rl_dt import (
    DecisionTransformerModel,
    build_trajectories,
    compute_majority_class_baseline,
    create_sequence_batches,
    evaluate_dt,
    train_dt,
)

sys.path.insert(0, str(SCRIPTS_DIR.parent / "shared"))
from features import FeatureEngineer

try:
    from walk_forward import WalkForwardSplitter
except ImportError:
    WalkForwardSplitter = None

RESULTS_DIR = SCRIPTS_DIR / "results" / "ablation_rtg_leak"


# ---------------------------------------------------------------------------
# Re-use L4 helpers (imported from sweep_l4_decision_transformer where needed)
# ---------------------------------------------------------------------------

def compute_sharpe(returns: np.ndarray, annual_factor: int = 252) -> float:
    """Annualized Sharpe ratio from daily returns."""
    if len(returns) < 10:
        return 0.0
    mean = np.mean(returns)
    std = np.std(returns)
    if std < 1e-10:
        return 0.0
    return float(mean / std * np.sqrt(annual_factor))


def simulate_dt_portfolio(
    prices: np.ndarray,
    actions: np.ndarray,
    commission_bps: float = 5.0,
) -> np.ndarray:
    """Simulate portfolio returns from DT action predictions.

    Actions: 0=hold, 1=buy (long), 2=sell (flat).
    """
    n = len(actions)
    commission = commission_bps / 10000.0
    position = 0.0
    portfolio_returns = np.zeros(n, dtype=np.float64)

    for i in range(1, n):
        price_ret = (prices[i] - prices[i - 1]) / (prices[i - 1] + 1e-8)

        if actions[i] == 1:
            target_pos = 1.0
        elif actions[i] == 2:
            target_pos = 0.0  # flat
        else:
            target_pos = position

        trade_cost = abs(target_pos - position) * commission
        portfolio_returns[i] = position * price_ret - trade_cost
        position = target_pos

    return portfolio_returns


# ---------------------------------------------------------------------------
# Core ablation logic
# ---------------------------------------------------------------------------

def compute_train_rtg_p90(
    train_prices: np.ndarray,
    train_features_norm: np.ndarray,
    window: int = 20,
    context_length: int = 20,
    commission_bps: float = 5.0,
) -> float:
    """Compute the 90th percentile of per-trajectory initial RTG from training data.

    'Initial RTG' = RTG at the first timestep of each trajectory segment,
    which is the cumulative future reward from that point to end of the price
    series. The 90th percentile represents a 'high but not extreme' desired
    return prompt for condition B.

    Returns:
        float: the 90th percentile value.
    """
    trajs = build_trajectories(
        train_prices, train_features_norm,
        window=window, context_length=context_length,
        commission=commission_bps / 10000.0,
    )
    rtg_vals = trajs["rtg"].flatten()
    # The first `context_length` entries are the initial RTGs for segments
    # starting at positions [start_idx, start_idx + context_length).
    # But actually build_trajectories returns one entry per timestep from
    # start_idx to n-context_length. The 'initial RTG' for the first
    # segment of length context_length is rtg[0].
    # For the 90th percentile of 'per-trajectory initial RTG', we sample
    # every context_length-th entry (non-overlapping segments).
    n = len(rtg_vals)
    n_segments = n // context_length
    if n_segments == 0:
        return float(np.percentile(rtg_vals, 90))

    initial_rtgs = []
    for i in range(n_segments):
        idx = i * context_length
        if idx < n:
            initial_rtgs.append(rtg_vals[idx])

    return float(np.percentile(initial_rtgs, 90))


def run_condition_a(
    model: DecisionTransformerModel,
    test_trajs: dict,
    test_prices: np.ndarray,
    context_length: int = 20,
    window: int = 20,
    commission_bps: float = 5.0,
    device: str = "cpu",
) -> dict:
    """Condition A: REALIZED-RTG (status quo, leaked).

    Runs the exact same eval as L4 sweep lines 238-293.
    """
    model.eval()
    with torch.no_grad():
        batches = create_sequence_batches(
            test_trajs, context_length=context_length, batch_size=64, shuffle=False,
        )
        all_preds = []
        for batch in batches:
            states = batch["states"].to(device)
            actions = batch["actions"].to(device)
            rtg = batch["rtg"].to(device)  # REALIZED RTG (leaked)
            mask = batch["attention_mask"].to(device)
            logits = model(states, actions, rtg, attention_mask=mask)
            preds = logits.argmax(dim=-1)[:, -1].cpu().numpy()
            all_preds.extend(preds.tolist())

    n_preds = len(all_preds)
    if n_preds < 10:
        return {"error": "too few predictions"}

    test_prices_subset = test_prices[window:window + n_preds]
    if len(test_prices_subset) < n_preds:
        n_preds = len(test_prices_subset)
        all_preds = all_preds[:n_preds]
    test_prices_subset = test_prices_subset[:n_preds]

    dt_rets = simulate_dt_portfolio(
        test_prices_subset, np.array(all_preds, dtype=np.int64),
        commission_bps=commission_bps,
    )
    bh_rets = np.diff(test_prices_subset) / (test_prices_subset[:-1] + 1e-8)
    bh_rets = np.concatenate([[0.0], bh_rets])

    min_len = min(len(dt_rets), len(bh_rets))
    sharpe_dt = compute_sharpe(dt_rets[:min_len])
    sharpe_bh = compute_sharpe(bh_rets[:min_len])

    # Direction accuracy
    actual_dir = (np.diff(test_prices_subset[:min_len]) > 0).astype(int)
    pred_arr = np.array(all_preds[:len(actual_dir)])
    if len(pred_arr) >= len(actual_dir):
        pred_arr = pred_arr[:len(actual_dir)]
        correct = (pred_arr == 1) == (actual_dir == 1)
        auc = float(correct.mean()) if len(correct) > 0 else 0.5
    else:
        auc = 0.5

    n_trades = int(np.sum(np.diff(all_preds[:min_len]) != 0))

    return {
        "sharpe_dt": round(sharpe_dt, 4),
        "sharpe_bh": round(sharpe_bh, 4),
        "delta_sharpe": round(sharpe_dt - sharpe_bh, 4),
        "auc": round(auc, 4),
        "n_trades": n_trades,
        "n_preds": n_preds,
    }


def run_condition_b(
    model: DecisionTransformerModel,
    test_trajs: dict,
    test_prices: np.ndarray,
    fixed_g: float,
    context_length: int = 20,
    window: int = 20,
    commission_bps: float = 5.0,
    device: str = "cpu",
) -> dict:
    """Condition B: FIXED-G (constant desired return prompt).

    Replaces ALL rtg values in eval sequences with a single constant
    `fixed_g`. This removes the realized-future signal while keeping
    a plausible 'aim high' conditioning.

    Implementation note:
        - create_sequence_batches returns batch["rtg"] of shape [B, T, 1]
        - We clone the batch and replace ALL rtg entries with fixed_g.
        - The model processes the interleaved [rtg_0, state_0, action_0, ...]
          sequence. By replacing rtg at all positions, every 'return cue'
          the model sees is identical = no future information.
        - The prediction at [:, -1] (last timestep) depends on the full
          context, so even the last-position RTG is constant.
    """
    model.eval()
    with torch.no_grad():
        batches = create_sequence_batches(
            test_trajs, context_length=context_length, batch_size=64, shuffle=False,
        )
        all_preds = []
        for batch in batches:
            states = batch["states"].to(device)
            actions = batch["actions"].to(device)
            # Replace RTG with constant
            rtg = torch.full_like(batch["rtg"], fixed_g).to(device)
            mask = batch["attention_mask"].to(device)
            logits = model(states, actions, rtg, attention_mask=mask)
            preds = logits.argmax(dim=-1)[:, -1].cpu().numpy()
            all_preds.extend(preds.tolist())

    n_preds = len(all_preds)
    if n_preds < 10:
        return {"error": "too few predictions"}

    test_prices_subset = test_prices[window:window + n_preds]
    if len(test_prices_subset) < n_preds:
        n_preds = len(test_prices_subset)
        all_preds = all_preds[:n_preds]
    test_prices_subset = test_prices_subset[:n_preds]

    dt_rets = simulate_dt_portfolio(
        test_prices_subset, np.array(all_preds, dtype=np.int64),
        commission_bps=commission_bps,
    )
    bh_rets = np.diff(test_prices_subset) / (test_prices_subset[:-1] + 1e-8)
    bh_rets = np.concatenate([[0.0], bh_rets])

    min_len = min(len(dt_rets), len(bh_rets))
    sharpe_dt = compute_sharpe(dt_rets[:min_len])
    sharpe_bh = compute_sharpe(bh_rets[:min_len])

    # Direction accuracy
    actual_dir = (np.diff(test_prices_subset[:min_len]) > 0).astype(int)
    pred_arr = np.array(all_preds[:len(actual_dir)])
    if len(pred_arr) >= len(actual_dir):
        pred_arr = pred_arr[:len(actual_dir)]
        correct = (pred_arr == 1) == (actual_dir == 1)
        auc = float(correct.mean()) if len(correct) > 0 else 0.5
    else:
        auc = 0.5

    n_trades = int(np.sum(np.diff(all_preds[:min_len]) != 0))

    return {
        "sharpe_dt": round(sharpe_dt, 4),
        "sharpe_bh": round(sharpe_bh, 4),
        "delta_sharpe": round(sharpe_dt - sharpe_bh, 4),
        "auc": round(auc, 4),
        "n_trades": n_trades,
        "n_preds": n_preds,
        "fixed_g": round(fixed_g, 6),
    }


def run_condition_c(
    test_prices: np.ndarray,
    n_trades_target: int,
    n_preds: int,
    window: int = 20,
    commission_bps: float = 5.0,
    seed: int = 42,
) -> dict:
    """Condition C: RANDOM-TIMING baseline.

    Generate random actions with trade frequency matched to condition A.
    This isolates the cash-timing Sharpe artifact: a variable-sizing
    portfolio that periodically holds cash can beat buy-and-hold Sharpe
    even with ZERO directional skill (volatility reduction).

    Method:
        1. Compute target trade count from condition A (n_trades_target).
        2. Compute target trade probability = n_trades_target / n_preds.
        3. At each timestep, with that probability, randomly choose
           action 1 (buy) or 2 (flat). Otherwise hold current position.
        4. Run simulate_dt_portfolio with these random actions.
    """
    rng = np.random.RandomState(seed + 1000)  # offset seed to decorrelate

    # Compute trade probability
    if n_preds < 2 or n_trades_target < 1:
        trade_prob = 0.1  # fallback
    else:
        trade_prob = min(n_trades_target / n_preds, 0.8)

    # Generate random actions
    random_actions = np.zeros(n_preds, dtype=np.int64)
    current_pos = 0  # 0=flat, 1=long
    for i in range(1, n_preds):
        if rng.random() < trade_prob:
            # Randomly choose to go long or flat
            new_pos = rng.choice([0, 1])
            if new_pos == 1:
                random_actions[i] = 1  # buy
            else:
                random_actions[i] = 2  # flat (sell)
            current_pos = new_pos
        else:
            random_actions[i] = 0  # hold

    test_prices_subset = test_prices[window:window + n_preds]
    if len(test_prices_subset) < n_preds:
        n_preds = len(test_prices_subset)
        random_actions = random_actions[:n_preds]
    test_prices_subset = test_prices_subset[:n_preds]

    rand_rets = simulate_dt_portfolio(
        test_prices_subset, random_actions,
        commission_bps=commission_bps,
    )
    bh_rets = np.diff(test_prices_subset) / (test_prices_subset[:-1] + 1e-8)
    bh_rets = np.concatenate([[0.0], bh_rets])

    min_len = min(len(rand_rets), len(bh_rets))
    sharpe_rand = compute_sharpe(rand_rets[:min_len])
    sharpe_bh = compute_sharpe(bh_rets[:min_len])

    # Direction accuracy (random baseline)
    actual_dir = (np.diff(test_prices_subset[:min_len]) > 0).astype(int)
    pred_arr = random_actions[:len(actual_dir)]
    if len(pred_arr) >= len(actual_dir):
        pred_arr = pred_arr[:len(actual_dir)]
        correct = (pred_arr == 1) == (actual_dir == 1)
        auc = float(correct.mean()) if len(correct) > 0 else 0.5
    else:
        auc = 0.5

    n_trades_actual = int(np.sum(np.diff(random_actions[:min_len]) != 0))

    return {
        "sharpe_dt": round(sharpe_rand, 4),
        "sharpe_bh": round(sharpe_bh, 4),
        "delta_sharpe": round(sharpe_rand - sharpe_bh, 4),
        "auc": round(auc, 4),
        "n_trades": n_trades_actual,
        "n_preds": n_preds,
        "trade_prob": round(trade_prob, 4),
    }


def run_single_ablation(
    symbol: str,
    seed: int,
    raw: pd.DataFrame,
    n_splits: int = 5,
    d_model: int = 128,
    nhead: int = 4,
    num_layers: int = 3,
    context_length: int = 20,
    epochs_per_fold: int = 15,
    window: int = 20,
    lookback: int = 20,
    commission_bps: float = 5.0,
    device: str = "cpu",
) -> dict:
    """Run full 3-condition ablation for one (symbol, seed) combo.

    Walk-forward 5-fold. For each fold:
        1. Train DT on train set (standard, with realized RTG -- training is fine)
        2. Compute fixed_g from train set (90th pctile of initial RTG)
        3. Evaluate condition A (realized RTG) on test
        4. Evaluate condition B (fixed-G) on test
        5. Evaluate condition C (random timing) on test

    Aggregate across folds: mean dSharpe, std, AUC, trades.
    """
    np.random.seed(seed)
    torch.manual_seed(seed)

    # Feature engineering
    indicators = [
        "returns", "volatility", "volume_ratio", "ma_ratios",
        "rsi", "macd", "bollinger", "true_range_atr", "obv",
    ]
    engineer = FeatureEngineer(lookback=lookback, indicators=indicators)
    features_df = engineer.transform(raw, add_target=False)
    features_arr = features_df.values.astype(np.float32)
    prices = raw.loc[features_df.index, "Close"].values.astype(np.float32)

    n = len(prices)
    if n < 500:
        return {"error": f"insufficient data ({n} rows)"}

    if WalkForwardSplitter is None:
        return {"error": "WalkForwardSplitter not available"}

    splitter = WalkForwardSplitter(
        n_splits=n_splits,
        train_size=max(252, n // (n_splits + 1)),
        test_size=max(63, n // (n_splits * 3)),
        gap=24,
    )

    fold_results = {"A": [], "B": [], "C": []}
    fixed_g_values = []

    for fold_idx, (train_idx, test_idx) in enumerate(splitter.split(np.arange(n))):
        if len(test_idx) < context_length + window + 10:
            continue

        # Normalize features on train only
        train_feat = features_arr[train_idx]
        mean = train_feat.mean(axis=0)
        std = train_feat.std(axis=0)
        std = np.where(std < 1e-8, 1.0, std)

        train_features_norm = (features_arr[train_idx] - mean) / std
        test_features_norm = (features_arr[test_idx] - mean) / std

        train_prices = prices[train_idx]
        test_prices = prices[test_idx]

        # Build training trajectories
        train_trajs = build_trajectories(
            train_prices, train_features_norm,
            window=window, context_length=context_length,
            commission=commission_bps / 10000.0,
        )

        if len(train_trajs["states"]) <= context_length:
            continue

        state_dim = train_trajs["states"].shape[1]

        # Train DT (standard -- RTG leak in training is by design for DT)
        result = train_dt(
            train_trajs,
            state_dim=state_dim,
            d_model=d_model,
            nhead=nhead,
            num_layers=num_layers,
            context_length=context_length,
            epochs=epochs_per_fold,
            batch_size=32,
            lr=1e-4,
            device=device,
        )
        model = result["model"]

        # Compute fixed_g from training set
        fixed_g = compute_train_rtg_p90(
            train_prices, train_features_norm,
            window=window, context_length=context_length,
            commission_bps=commission_bps,
        )
        fixed_g_values.append(fixed_g)

        # Build test trajectories
        test_trajs = build_trajectories(
            test_prices, test_features_norm,
            window=window, context_length=context_length,
            commission=commission_bps / 10000.0,
        )

        if len(test_trajs["states"]) <= context_length:
            continue

        # Condition A: realized RTG (leaked)
        res_a = run_condition_a(
            model, test_trajs, test_prices,
            context_length=context_length, window=window,
            commission_bps=commission_bps, device=device,
        )
        if "error" not in res_a:
            fold_results["A"].append(res_a)

        # Condition B: fixed-G
        res_b = run_condition_b(
            model, test_trajs, test_prices,
            fixed_g=fixed_g,
            context_length=context_length, window=window,
            commission_bps=commission_bps, device=device,
        )
        if "error" not in res_b:
            fold_results["B"].append(res_b)

        # Condition C: random timing (needs trade count from A)
        n_trades_a = res_a.get("n_trades", 10)
        n_preds_a = res_a.get("n_preds", 100)
        res_c = run_condition_c(
            test_prices,
            n_trades_target=n_trades_a,
            n_preds=n_preds_a,
            window=window,
            commission_bps=commission_bps,
            seed=seed,
        )
        if "error" not in res_c:
            fold_results["C"].append(res_c)

    # Aggregate across folds
    agg = {}
    for cond in ["A", "B", "C"]:
        folds = fold_results[cond]
        if not folds:
            agg[cond] = {"error": "no valid folds"}
            continue

        deltas = [f["delta_sharpe"] for f in folds]
        aucs = [f["auc"] for f in folds]
        trades = [f["n_trades"] for f in folds]

        agg[cond] = {
            "mean_dSharpe": round(float(np.mean(deltas)), 4),
            "std_dSharpe": round(float(np.std(deltas)), 4),
            "t_stat": round(float(np.mean(deltas) / (np.std(deltas) + 1e-10)), 4),
            "mean_auc": round(float(np.mean(aucs)), 4),
            "mean_trades": int(np.mean(trades)),
            "n_folds": len(folds),
            "fold_deltas": [round(d, 4) for d in deltas],
        }

    agg["fixed_g_mean"] = round(float(np.mean(fixed_g_values)), 6) if fixed_g_values else None
    agg["fixed_g_values"] = [round(g, 6) for g in fixed_g_values]

    return agg


def main():
    parser = argparse.ArgumentParser(description="RTG leak ablation for Decision Transformer")
    parser.add_argument("--symbols", nargs="+",
                        default=["SPY", "XLF", "XLK", "IEF", "GLD", "USO"],
                        help="Symbols to test")
    parser.add_argument("--seeds", nargs="+", type=int, default=[0, 1, 7, 42],
                        help="Random seeds")
    parser.add_argument("--n-splits", type=int, default=5)
    parser.add_argument("--epochs-per-fold", type=int, default=15)
    parser.add_argument("--d-model", type=int, default=128)
    parser.add_argument("--nhead", type=int, default=4)
    parser.add_argument("--num-layers", type=int, default=3)
    parser.add_argument("--context-length", type=int, default=20)
    parser.add_argument("--window", type=int, default=20)
    parser.add_argument("--lookback", type=int, default=20)
    parser.add_argument("--commission-bps", type=float, default=5.0)
    parser.add_argument("--smoke", action="store_true",
                        help="Quick test: 2 symbols, 2 seeds, 2 epochs")
    parser.add_argument("--output", type=str, default=None)
    args = parser.parse_args()

    # Device
    device = "cuda" if torch.cuda.is_available() else "cpu"
    print(f"Device: {device} | torch {torch.__version__}")

    # Smoke test
    if args.smoke:
        args.symbols = args.symbols[:2]
        args.seeds = args.seeds[:2]
        args.epochs_per_fold = 2
        args.n_splits = 2
        print("SMOKE MODE: 2 symbols, 2 seeds, 2 epochs, 2 folds")

    symbols = args.symbols
    seeds = args.seeds
    n_combos = len(symbols) * len(seeds)
    print(f"Ablation: {len(symbols)} symbols x {len(seeds)} seeds = {n_combos} combos")
    print(f"  Conditions: A=realized-RTG (leaked), B=fixed-G, C=random-timing")
    print(f"  WF folds={args.n_splits}, epochs/fold={args.epochs_per_fold}, "
          f"commission={args.commission_bps}bps")

    # Load panier
    panier = load_panier(start="2015-01-01", auto_fetch=True)
    loaded_symbols = [s for s in symbols if s in panier]
    if len(loaded_symbols) < len(symbols):
        missing = [s for s in symbols if s not in panier]
        print(f"WARNING: {len(missing)} symbols not in panier: {missing}")
    symbols = loaded_symbols

    print(f"Loaded panier: {len(symbols)} symbols")

    # Run ablation
    t0 = time.time()
    combo_idx = 0
    all_results = {}

    for symbol in symbols:
        raw = panier[symbol]
        all_results[symbol] = {}

        for seed in seeds:
            combo_idx += 1
            print(f"\n[{combo_idx}/{n_combos}] {symbol} seed={seed}")
            print(f"  Running 3-condition ablation...", flush=True)

            try:
                result = run_single_ablation(
                    symbol=symbol,
                    seed=seed,
                    raw=raw,
                    n_splits=args.n_splits,
                    d_model=args.d_model,
                    nhead=args.nhead,
                    num_layers=args.num_layers,
                    context_length=args.context_length,
                    epochs_per_fold=args.epochs_per_fold,
                    window=args.window,
                    lookback=args.lookback,
                    commission_bps=args.commission_bps,
                    device=device,
                )
                all_results[symbol][seed] = result

                # Print per-combo summary
                for cond in ["A", "B", "C"]:
                    if cond in result and "error" not in result.get(cond, {}):
                        r = result[cond]
                        print(f"  Cond {cond}: dSharpe={r['mean_dSharpe']:+.4f} "
                              f"(std={r['std_dSharpe']:.4f}, t={r['t_stat']:.2f}) "
                              f"auc={r['mean_auc']:.4f} trades={r['mean_trades']}")
                    else:
                        print(f"  Cond {cond}: ERROR")
                if result.get("fixed_g_mean"):
                    print(f"  Fixed-G value: {result['fixed_g_mean']:.6f}")

            except Exception as e:
                print(f"  EXCEPTION: {e}")
                import traceback
                traceback.print_exc()
                all_results[symbol][seed] = {"error": str(e)}

    # ===================================================================
    # Aggregate results: symbol x condition -> cross-seed stats
    # ===================================================================
    print(f"\n{'='*80}")
    print("ABLATION RESULTS TABLE")
    print(f"{'='*80}")
    print(f"{'Symbol':<8} {'Cond':<6} {'Mean dS':>10} {'Std':>8} {'t-stat':>8} "
          f"{'Mean AUC':>10} {'Trades':>8}")
    print("-" * 68)

    # Per-symbol aggregation
    table = {}
    for symbol in symbols:
        table[symbol] = {}
        for cond in ["A", "B", "C"]:
            deltas = []
            aucs = []
            trades = []
            for seed in seeds:
                res = all_results.get(symbol, {}).get(seed, {})
                cond_data = res.get(cond, {})
                if "error" in cond_data:
                    continue
                deltas.append(cond_data["mean_dSharpe"])
                aucs.append(cond_data["mean_auc"])
                trades.append(cond_data["mean_trades"])

            if deltas:
                mean_d = float(np.mean(deltas))
                std_d = float(np.std(deltas))
                t_stat = mean_d / (std_d + 1e-10)
                mean_auc = float(np.mean(aucs))
                mean_trades = int(np.mean(trades))
                table[symbol][cond] = {
                    "mean_dSharpe": round(mean_d, 4),
                    "std_dSharpe": round(std_d, 4),
                    "t_stat": round(t_stat, 4),
                    "mean_auc": round(mean_auc, 4),
                    "mean_trades": mean_trades,
                    "n_seeds": len(deltas),
                }
                print(f"{symbol:<8} {cond:<6} {mean_d:>+10.4f} {std_d:>8.4f} "
                      f"{t_stat:>8.4f} {mean_auc:>10.4f} {mean_trades:>8d}")
            else:
                table[symbol][cond] = {"error": "no valid seeds"}
                print(f"{symbol:<8} {cond:<6} {'ERROR':>10}")

    # Per-condition aggregate (all symbols pooled)
    print("-" * 68)
    print(f"{'ALL':<8} ", end="")
    agg_table = {}
    for cond in ["A", "B", "C"]:
        all_deltas = []
        all_aucs = []
        all_trades = []
        for symbol in symbols:
            if cond in table.get(symbol, {}) and "error" not in table[symbol].get(cond, {}):
                all_deltas.append(table[symbol][cond]["mean_dSharpe"])
                all_aucs.append(table[symbol][cond]["mean_auc"])
                all_trades.append(table[symbol][cond]["mean_trades"])

        if all_deltas:
            mean_d = float(np.mean(all_deltas))
            std_d = float(np.std(all_deltas))
            t_stat = mean_d / (std_d + 1e-10)
            mean_auc = float(np.mean(all_aucs))
            mean_trades = int(np.mean(all_trades))
            agg_table[cond] = {
                "mean_dSharpe": round(mean_d, 4),
                "std_dSharpe": round(std_d, 4),
                "t_stat": round(t_stat, 4),
                "mean_auc": round(mean_auc, 4),
                "mean_trades": mean_trades,
                "n_symbols": len(all_deltas),
            }
            print(f"{cond:<6} {mean_d:>+10.4f} {std_d:>8.4f} "
                  f"{t_stat:>8.4f} {mean_auc:>10.4f} {mean_trades:>8d}", end="")
            if cond < "C":
                print(f"\n{'':>8} ", end="")
        else:
            agg_table[cond] = {"error": "no data"}
            print(f"{cond:<6} {'ERROR':>10}", end="")
            if cond < "C":
                print(f"\n{'':>8} ", end="")
    print()

    # ===================================================================
    # Verdict
    # ===================================================================
    print(f"\n{'='*80}")
    print("VERDICT ANALYSIS")
    print(f"{'='*80}")

    # Check conditions for verdict
    a_agg = agg_table.get("A", {})
    b_agg = agg_table.get("B", {})
    c_agg = agg_table.get("C", {})

    a_mean = a_agg.get("mean_dSharpe", 0)
    b_mean = b_agg.get("mean_dSharpe", 0)
    c_mean = c_agg.get("mean_dSharpe", 0)

    print(f"  A (leaked) mean dSharpe: {a_mean:+.4f}")
    print(f"  B (fixed-G) mean dSharpe: {b_mean:+.4f}")
    print(f"  C (random)  mean dSharpe: {c_mean:+.4f}")

    a_b_diff = abs(a_mean - b_mean)
    b_c_diff = abs(b_mean - c_mean)
    a_c_diff = abs(a_mean - c_mean)

    print(f"  |A - B| = {a_b_diff:.4f}")
    print(f"  |B - C| = {b_c_diff:.4f}")
    print(f"  |A - C| = {a_c_diff:.4f}")

    # Verdict logic:
    # LEAK-DOMINATED: A >> B ≈ C  (i.e. A-B large, B-C small)
    # PARTIAL-SKILL:  C < B < A   (B is between C and A)
    # SKILL-CONFIRMED: B ≈ A and both >> C

    threshold_ratio = 2.0  # B must be within 50% of the other to count as "≈"
    a_abs = abs(a_mean)
    c_abs = abs(c_mean) if abs(c_mean) > 0.001 else 0.001

    if a_abs > 0.001:
        # Normalize differences
        b_close_to_c = b_c_diff < a_abs * 0.3  # B is within 30% of A's range to C
        b_close_to_a = a_b_diff < a_abs * 0.3  # B is within 30% of A
        a_far_from_c = a_c_diff > a_abs * 0.5

        if b_close_to_c and a_far_from_c:
            verdict = "LEAK-DOMINATED"
            reason = (f"A >> B ≈ C: leaked-RTG (A={a_mean:+.4f}) far above "
                      f"fixed-G (B={b_mean:+.4f}) ≈ random (C={c_mean:+.4f}). "
                      f"|A-B|={a_b_diff:.4f} >> |B-C|={b_c_diff:.4f}")
        elif b_close_to_a and a_far_from_c:
            verdict = "SKILL-CONFIRMED"
            reason = (f"B ≈ A >> C: fixed-G (B={b_mean:+.4f}) ≈ leaked (A={a_mean:+.4f}) "
                      f"both >> random (C={c_mean:+.4f}). "
                      f"|A-B|={a_b_diff:.4f} << |A-C|={a_c_diff:.4f}")
        elif c_mean < b_mean < a_mean:
            verdict = "PARTIAL-SKILL"
            reason = (f"C < B < A: random (C={c_mean:+.4f}) < fixed-G (B={b_mean:+.4f}) "
                      f"< leaked (A={a_mean:+.4f}). Some skill, but RTG inflates.")
        else:
            verdict = "INCONCLUSIVE"
            reason = f"No clear pattern: A={a_mean:+.4f}, B={b_mean:+.4f}, C={c_mean:+.4f}"
    else:
        verdict = "INCONCLUSIVE"
        reason = f"All conditions near zero: A={a_mean:+.4f}, B={b_mean:+.4f}, C={c_mean:+.4f}"

    print(f"\n  VERDICT: {verdict}")
    print(f"  REASON:  {reason}")

    # Per-symbol verdict
    print(f"\n  Per-symbol verdicts:")
    for symbol in symbols:
        a_s = table.get(symbol, {}).get("A", {}).get("mean_dSharpe", 0)
        b_s = table.get(symbol, {}).get("B", {}).get("mean_dSharpe", 0)
        c_s = table.get(symbol, {}).get("C", {}).get("mean_dSharpe", 0)

        if a_s == 0 and b_s == 0:
            sym_verdict = "NO-DATA"
        elif abs(b_s - c_s) < abs(a_s) * 0.3 and abs(a_s) > 0.01:
            sym_verdict = "LEAK-DOMINATED"
        elif abs(a_s - b_s) < abs(a_s) * 0.3 and abs(a_s - c_s) > abs(a_s) * 0.5:
            sym_verdict = "SKILL-CONFIRMED"
        elif c_s < b_s < a_s:
            sym_verdict = "PARTIAL-SKILL"
        else:
            sym_verdict = "INCONCLUSIVE"

        print(f"    {symbol:<8} A={a_s:+.4f} B={b_s:+.4f} C={c_s:+.4f} -> {sym_verdict}")

    elapsed = time.time() - t0

    # Save results
    output = {
        "verdict": verdict,
        "reason": reason,
        "aggregate": agg_table,
        "per_symbol": table,
        "per_symbol_seed": all_results,
        "config": {
            "symbols": symbols,
            "seeds": seeds,
            "n_splits": args.n_splits,
            "epochs_per_fold": args.epochs_per_fold,
            "d_model": args.d_model,
            "context_length": args.context_length,
            "window": args.window,
            "commission_bps": args.commission_bps,
        },
        "elapsed_s": round(elapsed, 2),
        "device": device,
    }

    out_path = Path(args.output) if args.output else RESULTS_DIR / "results.json"
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(output, indent=2, default=str), encoding="utf-8")

    print(f"\nResults saved: {out_path}")
    print(f"Elapsed: {elapsed:.0f}s")


if __name__ == "__main__":
    main()
