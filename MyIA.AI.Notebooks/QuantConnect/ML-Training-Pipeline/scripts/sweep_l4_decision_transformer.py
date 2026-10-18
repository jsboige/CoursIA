"""
L4 Decision Transformer sweep for Ladder #1409.

Multi-asset, multi-seed walk-forward evaluation of Decision Transformer.
Reuses DecisionTransformerModel from train_rl_dt.py.

For each (symbol, seed) combo:
  1. Load panier data
  2. Feature engineering (returns, volatility, RSI, MACD, etc.)
  3. Walk-forward 5-fold
  4. For each fold: train DT, predict OOS actions, simulate portfolio
  5. Aggregate: mean OOS Sharpe, delta vs B&H

Multi-seed edge evaluation (G.2 compliance):
  - For each symbol: mean_delta and std_delta across seeds
  - sigma_edge = mean_delta / std_delta
  - If sigma_edge >= 2 and mean_delta > 0: signal detected
  - No FAANG/Mag7 (panier_loader.FORBIDDEN_SYMBOLS enforced)

Usage:
    # Full sweep (25 symbols, 4 seeds, 5-fold WF)
    python sweep_l4_decision_transformer.py

    # Subset
    python sweep_l4_decision_transformer.py --symbols SPY QQQ TLT GLD --seeds 0 1 7 42

    # Smoke test
    python sweep_l4_decision_transformer.py --smoke

References:
    - Chen et al. (2021): "Decision Transformer: RL via Sequence Modeling"
    - arXiv:2411.17900: "Decision Transformer for Algorithmic Trading"
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

from panier_loader import (
    FORBIDDEN_SYMBOLS,
    PANIER_GROUPS,
    get_panier_symbols,
    load_panier,
)
from train_rl_dt import (
    DecisionTransformerModel,
    build_trajectories,
    compute_majority_class_baseline,
    evaluate_dt,
    train_dt,
)
from validate_xrp_dt import CAUSAL_EVAL_PROTOCOL, train_rtg_per_step
from ablation_rtg_leak import (
    causal_condition_actions,
    causal_eval_returns,
    score_actions,
    simulate_dt_portfolio,
)

sys.path.insert(0, str(SCRIPTS_DIR.parent / "shared"))
from features import FeatureEngineer

try:
    from walk_forward import WalkForwardSplitter
except ImportError:
    WalkForwardSplitter = None

RESULTS_DIR = SCRIPTS_DIR / "results" / "l4_decision_transformer"


import strategy_metrics  # noqa: E402


def compute_sharpe(returns: np.ndarray, annual_factor: int = 252) -> float:
    """Annualized Sharpe (``strategy_metrics.sharpe``: ddof=1, risk-free 0).

    Returns 0.0 for fewer than 10 returns or a standard deviation below 1e-10.
    The formula used the population standard deviation (ddof=0) until #19016:
    the standard deviation grows by ``sqrt(n / (n - 1))``, so the value is
    multiplied by ``sqrt((n - 1) / n)`` -- pinned by the tranche-4 tests.
    """
    if len(returns) < 10 or float(np.std(returns, ddof=1)) < 1e-10:
        return 0.0
    return float(strategy_metrics.sharpe(returns, periods_per_year=annual_factor))


def run_single_combo(
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
    """Run walk-forward DT training for one (symbol, seed) combo.

    Evaluation protocol ``causal-v1`` (#21187): one DT decision per test
    return, computed on states up to the previous row, with the RTG schedule
    fixed from the training fold (mean teacher reward per step times the
    remaining steps). Positions are long/flat (sell = flat), each one applied
    to the return it drives; buy-and-hold is scored on the same returns.
    Until #21187 the sweep fed the realized test RTG, which sums future test
    rewards, and paired each window's last decision with a return about
    ``context_length`` rows earlier.

    Returns dict with:
        sharpe_dt: annualized Sharpe from DT-driven portfolio
        sharpe_bh: annualized Sharpe from buy-and-hold
        delta_sharpe: sharpe_dt - sharpe_bh
        mean_auc: direction accuracy of the buy label (not an AUC; the key
            name is kept for continuity)
        mean_hit_rate: accuracy of the held position's sign
        mean_exposure: share of returns held long
        n_folds: number of completed folds
        n_trades: total position changes across folds
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

    # Walk-forward split
    if WalkForwardSplitter is None:
        return {"error": "WalkForwardSplitter not available"}

    splitter = WalkForwardSplitter(
        n_splits=n_splits,
        train_size=max(252, n // (n_splits + 1)),
        test_size=max(63, n // (n_splits * 3)),
        gap=24,
    )

    fold_deltas = []
    fold_auc = []
    fold_hit = []
    fold_exposure = []
    fold_trades = []
    all_dt_rets = []
    all_bh_rets = []

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

        # Build trajectories
        train_trajs = build_trajectories(
            train_prices, train_features_norm,
            window=window, context_length=context_length,
            commission=commission_bps / 10000.0,
        )

        if len(train_trajs["states"]) <= context_length:
            continue

        state_dim = train_trajs["states"].shape[1]

        # Train DT
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

        # Evaluate on test set
        test_trajs = build_trajectories(
            test_prices, test_features_norm,
            window=window, context_length=context_length,
            commission=commission_bps / 10000.0,
        )

        if len(test_trajs["states"]) <= context_length:
            continue

        # Input RTG fixed from the training fold: the realized test RTG sums
        # future test rewards (#21187).
        rtg_step = train_rtg_per_step(train_trajs)
        eval_result = evaluate_dt(
            model, test_trajs,
            context_length=context_length,
            device=device,
            rtg_per_step=rtg_step,
        )

        # One decision per return k -> k+1, read on rows <= k-2.
        rtg_rows = rtg_step * (len(test_prices) - np.arange(len(test_prices)))
        actions = causal_condition_actions(
            model, test_prices, test_features_norm, rtg_rows,
            context_length=context_length, window=window, device=device,
        )
        if len(actions) < 10:
            continue
        returns = causal_eval_returns(test_prices, window, context_length)

        dt_rets = simulate_dt_portfolio(actions, returns, commission_bps=commission_bps)
        scores = score_actions(actions, returns, commission_bps=commission_bps)
        all_dt_rets.extend(dt_rets.tolist())
        all_bh_rets.extend(returns.tolist())

        fold_deltas.append(compute_sharpe(dt_rets) - compute_sharpe(returns))
        fold_auc.append(scores["auc"])
        fold_hit.append(scores["hit_rate"])
        fold_exposure.append(scores["exposure"])
        fold_trades.append(scores["n_trades"])

    if not fold_deltas:
        return {"error": "no valid folds completed"}

    # Aggregate across folds
    sharpe_dt = compute_sharpe(np.array(all_dt_rets))
    sharpe_bh = compute_sharpe(np.array(all_bh_rets))

    return {
        "sharpe_dt": round(sharpe_dt, 4),
        "sharpe_bh": round(sharpe_bh, 4),
        "delta_sharpe": round(sharpe_dt - sharpe_bh, 4),
        "mean_fold_delta": round(float(np.mean(fold_deltas)), 4),
        "std_fold_delta": round(float(np.std(fold_deltas)), 4),
        "mean_auc": round(float(np.mean(fold_auc)), 4),
        "mean_hit_rate": round(float(np.mean(fold_hit)), 4),
        "mean_exposure": round(float(np.mean(fold_exposure)), 4),
        "eval_protocol": CAUSAL_EVAL_PROTOCOL,
        "n_folds": len(fold_deltas),
        "n_trades": sum(fold_trades),
        "fold_deltas": [round(d, 4) for d in fold_deltas],
    }


def main():
    parser = argparse.ArgumentParser(description="L4 Decision Transformer sweep")
    parser.add_argument("--symbols", nargs="+", default=None,
                        help="Symbols to test (default: full panier)")
    parser.add_argument("--seeds", nargs="+", type=int, default=[0, 1, 7, 42],
                        help="Random seeds (default: 0 1 7 42)")
    parser.add_argument("--n-splits", type=int, default=5,
                        help="Walk-forward folds")
    parser.add_argument("--epochs-per-fold", type=int, default=15,
                        help="Training epochs per WF fold")
    parser.add_argument("--d-model", type=int, default=128)
    parser.add_argument("--nhead", type=int, default=4)
    parser.add_argument("--num-layers", type=int, default=3)
    parser.add_argument("--context-length", type=int, default=20)
    parser.add_argument("--window", type=int, default=20)
    parser.add_argument("--lookback", type=int, default=20)
    parser.add_argument("--commission-bps", type=float, default=5.0,
                        help="Transaction cost in basis points")
    parser.add_argument("--smoke", action="store_true",
                        help="Quick test: 2 symbols, 2 seeds, 2 epochs")
    parser.add_argument("--output", type=str, default=None,
                        help="Output path for results JSON")
    parser.add_argument("--no-auto-fetch", action="store_true",
                        help="Skip yfinance fallback for missing panier symbols "
                             "(default: auto-fetch on, see PR #1726)")
    args = parser.parse_args()

    # Device
    device = "cuda" if torch.cuda.is_available() else "cpu"
    print(f"Device: {device} | torch {torch.__version__}")

    # Symbols
    if args.symbols:
        symbols = args.symbols
    else:
        symbols = get_panier_symbols()
    symbols = [s for s in symbols if s not in FORBIDDEN_SYMBOLS]

    # Smoke test override
    if args.smoke:
        symbols = symbols[:2]
        args.seeds = args.seeds[:2]
        args.epochs_per_fold = 2
        args.n_splits = 2
        print("SMOKE MODE: 2 symbols, 2 seeds, 2 epochs, 2 folds")

    seeds = args.seeds
    n_combos = len(symbols) * len(seeds)
    print(f"Sweep: {len(symbols)} symbols x {len(seeds)} seeds = {n_combos} combos")
    print(f"  WF folds={args.n_splits}, epochs/fold={args.epochs_per_fold}, "
          f"commission={args.commission_bps}bps")

    # Load panier (auto_fetch missing CSVs via yfinance unless --no-auto-fetch)
    panier = load_panier(start="2015-01-01", auto_fetch=not args.no_auto_fetch)
    loaded_symbols = [s for s in symbols if s in panier]
    if len(loaded_symbols) < len(symbols):
        missing = [s for s in symbols if s not in panier]
        print(f"WARNING: {len(missing)} symbols not in panier: {missing}")
    symbols = loaded_symbols

    print(f"Loaded panier: {len(symbols)} symbols, "
          f"{len(next(iter(panier.values())))} days")

    # Run sweep
    t0 = time.time()
    edges = []
    combo_idx = 0

    # Collect results per symbol across seeds
    symbol_seed_results = {}

    for symbol in symbols:
        raw = panier[symbol]
        symbol_seed_results[symbol] = {}

        for seed in seeds:
            combo_idx += 1
            print(f"[{combo_idx}/{n_combos}] {symbol} seed={seed} ", end="", flush=True)

            try:
                result = run_single_combo(
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

                if "error" in result:
                    print(f"ERROR: {result['error']}")
                else:
                    d = result["delta_sharpe"]
                    s = result["sharpe_dt"]
                    auc = result["mean_auc"]
                    nf = result["n_folds"]
                    nt = result["n_trades"]
                    print(f"dSharpe={d:+.4f} dtSharpe={s:.4f} auc={auc:.4f} "
                          f"folds={nf} trades={nt}")
                    symbol_seed_results[symbol][seed] = result

            except Exception as e:
                print(f"EXCEPTION: {e}")
                symbol_seed_results[symbol][seed] = {"error": str(e)}

    # Multi-seed edge evaluation per symbol
    for symbol in symbols:
        seed_results = symbol_seed_results.get(symbol, {})
        deltas = [r["delta_sharpe"] for r in seed_results.values()
                  if "delta_sharpe" in r]

        if len(deltas) < 2:
            mean_d = deltas[0] if deltas else 0.0
            std_d = 0.0
            sigma = 0.0
        else:
            mean_d = float(np.mean(deltas))
            std_d = float(np.std(deltas))
            sigma = mean_d / std_d if std_d > 1e-10 else 0.0

        aucs = [r["mean_auc"] for r in seed_results.values()
                if "mean_auc" in r]

        edges.append({
            "symbol": symbol,
            "mean_delta": round(mean_d, 4),
            "std_delta": round(std_d, 4),
            "sigma_edge": round(sigma, 4),
            "is_signal": sigma >= 2.0 and mean_d > 0,
            "n_seeds": len(deltas),
            "mean_auc": round(float(np.mean(aucs)), 4) if aucs else 0.0,
            "seed_details": {
                str(s): {"delta_sharpe": r.get("delta_sharpe"),
                         "sharpe_dt": r.get("sharpe_dt"),
                         "n_folds": r.get("n_folds")}
                for s, r in seed_results.items()
                if "delta_sharpe" in r
            },
        })

    # Verdict
    n_signal = sum(1 for e in edges if e["is_signal"])
    median_auc = float(np.median([e["mean_auc"] for e in edges])) if edges else 0.0

    if n_signal > 0:
        verdict = "BEATS"
    else:
        verdict = "NO BEATS"

    elapsed = time.time() - t0

    output = {
        "verdict": verdict,
        "n_signal": n_signal,
        "n_cells": len(edges),
        "median_auc": round(median_auc, 4),
        "edges": edges,
        "n_combos": n_combos,
        "elapsed_s": round(elapsed, 2),
        "device": device,
        "smoke": args.smoke,
        "config": {
            "model": "DecisionTransformer",
            "d_model": args.d_model,
            "nhead": args.nhead,
            "num_layers": args.num_layers,
            "context_length": args.context_length,
            "window": args.window,
            "epochs_per_fold": args.epochs_per_fold,
            "n_splits": args.n_splits,
            "seeds": seeds,
            "commission_bps": args.commission_bps,
        },
    }

    # Save
    out_path = Path(args.output) if args.output else RESULTS_DIR / "results.json"
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(output, indent=2, default=str), encoding="utf-8")

    print(f"\n{'='*60}")
    print(f"L4 sweep: {n_combos} combos in {elapsed:.0f}s")
    print(f"VERDICT: {verdict} (signal cells {n_signal}/{len(edges)}, "
          f"median AUC {median_auc:.4f})")
    print(f"Saved: {out_path}")


if __name__ == "__main__":
    main()
