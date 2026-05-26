"""
L2 — Cross-sectional + dual momentum on anti-bias panier.

Two strategies on 25-symbol anti-bias panier (7 asset classes):

1. Cross-sectional momentum: rank assets by past return, long top quantile,
   short (or cash) bottom quantile. Monthly rebalancing.

2. Dual momentum (Antonacci): combine relative (cross-sectional) + absolute
   momentum filter. Long top quantile only if absolute momentum > 0,
   otherwise go to cash/bonds.

Walk-forward expanding 5-fold x 4 seeds, transaction costs, comparison vs
L1 TSMOM and equal-weight B&H.

Usage:
    python L2_dual_momentum.py
    python L2_dual_momentum.py --dry-run
    python L2_dual_momentum.py --seeds 0 1 7 42
"""

import argparse
import json
import sys
from pathlib import Path

import numpy as np
import pandas as pd

SCRIPTS_DIR = Path(__file__).resolve().parent
CHECKPOINTS_DIR = SCRIPTS_DIR.parent / "checkpoints" / "l2_dual_momentum"
L1_RESULTS = SCRIPTS_DIR.parent / "checkpoints" / "l1_tsmom" / "L1_tsmom_results.json"

sys.path.insert(0, str(SCRIPTS_DIR))

from panier_loader import (
    PANIER_GROUPS,
    load_panier_closes,
    get_panier_symbols,
)
from walk_forward import WalkForwardSplitter
from transaction_costs import TransactionCostModel
from baselines import sharpe_from_returns

ALL_SYMBOLS = get_panier_symbols()
CRYPTO_SYMBOLS = set(PANIER_GROUPS["crypto"])

EQUITY_COST = TransactionCostModel(
    commission_bps=1.0, bid_ask_spread_bps=2.0,
    market_impact_coeff=0.05, daily_volume=5_000_000, slippage_bps=2.0,
)
CRYPTO_COST = TransactionCostModel(
    commission_bps=2.0, bid_ask_spread_bps=3.0,
    market_impact_coeff=0.05, daily_volume=1_000_000, slippage_bps=5.0,
)

DEFAULT_SEEDS = [0, 1, 7, 42]
REBALANCE_FREQ = 21  # monthly rebalancing
LOOKBACKS = [63, 126, 252]  # 3/6/12 month momentum lookbacks
TOP_N = 5  # long top-5 assets


def run_cross_sectional(
    closes: pd.DataFrame,
    lookback: int,
    top_n: int,
    seeds: list[int],
    n_splits: int = 5,
    gap: int = 21,
) -> dict:
    """Cross-sectional momentum: rank by past return, long top-N."""
    symbols = [c for c in closes.columns if c in ALL_SYMBOLS]
    returns = closes[symbols].pct_change().shift(-1)
    mom = closes[symbols].pct_change(lookback)

    all_seed_results = []

    for seed in seeds:
        splitter = WalkForwardSplitter(n_splits=n_splits, gap=gap)
        ret_arr = returns.values
        mom_arr = mom.values

        fold_gross = []
        fold_net = []
        fold_trades = []
        current_positions = np.zeros(len(symbols))
        last_rebal = -REBALANCE_FREQ  # force first rebalance

        for train_idx, test_idx in splitter.split(ret_arr):
            if len(test_idx) == 0:
                continue

            for t in range(len(test_idx)):
                idx = test_idx[t]
                abs_pos_in_fold = t

                # Rebalance check (monthly)
                if abs_pos_in_fold - last_rebal >= REBALANCE_FREQ or abs_pos_in_fold == 0:
                    last_rebal = abs_pos_in_fold
                    mom_scores = mom_arr[idx]

                    # Rank by momentum, select top-N
                    valid = ~np.isnan(mom_scores)
                    ranked = np.full(len(symbols), -np.inf)
                    ranked[valid] = mom_scores[valid]
                    top_indices = np.argsort(ranked)[-top_n:]

                    new_positions = np.zeros(len(symbols))
                    for ti in top_indices:
                        if valid[ti]:
                            new_positions[ti] = 1.0 / top_n

                    trades = np.sum(new_positions != current_positions)
                    current_positions = new_positions
                else:
                    trades = 0

                # Portfolio return
                day_ret = ret_arr[idx]
                port_gross = np.nansum(current_positions * day_ret)

                # Transaction cost
                if trades > 0:
                    n_crypto = sum(1 for i, s in enumerate(symbols)
                                   if s in CRYPTO_SYMBOLS and current_positions[i] > 0)
                    n_equity = trades - n_crypto
                    cost = (n_equity * EQUITY_COST.cost_per_trade(100) +
                            n_crypto * CRYPTO_COST.cost_per_trade(100))
                    avg_cost = cost / max(trades, 1)
                    port_net = port_gross - avg_cost
                else:
                    port_net = port_gross

                if not np.isnan(port_gross):
                    fold_gross.append(port_gross)
                    fold_net.append(port_net)
                    fold_trades.append(trades)

        gross_arr = np.array(fold_gross)
        net_arr = np.array(fold_net)

        if len(gross_arr) > 10:
            gross_sharpe = sharpe_from_returns(pd.Series(gross_arr))
            net_sharpe = sharpe_from_returns(pd.Series(net_arr))
        else:
            gross_sharpe = 0.0
            net_sharpe = 0.0

        all_seed_results.append({
            "seed": seed,
            "gross_sharpe": round(float(gross_sharpe), 4),
            "net_sharpe": round(float(net_sharpe), 4),
            "total_trades": int(np.sum(fold_trades)),
            "n_oos": len(gross_arr),
        })

    return {
        "strategy": "cross_sectional",
        "lookback": lookback,
        "top_n": top_n,
        "n_symbols": len(symbols),
        "seeds": all_seed_results,
    }


def run_dual_momentum(
    closes: pd.DataFrame,
    lookback: int,
    top_n: int,
    cash_proxy: str = "SHY",
    seeds: list[int] = DEFAULT_SEEDS,
    n_splits: int = 5,
    gap: int = 21,
) -> dict:
    """Dual momentum (Antonacci): cross-sectional + absolute filter.

    Long top-N by relative momentum, BUT only if each asset's absolute
    momentum (past return) is positive. Otherwise allocate to cash proxy.
    """
    symbols = [c for c in closes.columns if c in ALL_SYMBOLS]
    returns = closes[symbols].pct_change().shift(-1)
    mom = closes[symbols].pct_change(lookback)

    # Cash proxy returns
    if cash_proxy in closes.columns:
        cash_ret = closes[cash_proxy].pct_change().shift(-1).values
    else:
        cash_ret = np.zeros(len(closes))

    all_seed_results = []

    for seed in seeds:
        splitter = WalkForwardSplitter(n_splits=n_splits, gap=gap)
        ret_arr = returns.values
        mom_arr = mom.values

        fold_gross = []
        fold_net = []
        fold_trades = []
        current_positions = np.zeros(len(symbols))
        cash_weight = 0.0
        last_rebal = -REBALANCE_FREQ

        for train_idx, test_idx in splitter.split(ret_arr):
            if len(test_idx) == 0:
                continue

            for t in range(len(test_idx)):
                idx = test_idx[t]
                abs_pos = t

                if abs_pos - last_rebal >= REBALANCE_FREQ or abs_pos == 0:
                    last_rebal = abs_pos
                    mom_scores = mom_arr[idx]

                    valid = ~np.isnan(mom_scores)
                    ranked = np.full(len(symbols), -np.inf)
                    ranked[valid] = mom_scores[valid]
                    top_indices = np.argsort(ranked)[-top_n:]

                    new_positions = np.zeros(len(symbols))
                    cash_alloc = 0.0

                    for ti in top_indices:
                        if valid[ti]:
                            if mom_scores[ti] > 0:
                                new_positions[ti] = 1.0 / top_n
                            else:
                                cash_alloc += 1.0 / top_n

                    trades = np.sum(new_positions != current_positions)
                    if cash_alloc != cash_weight:
                        trades += 1
                    current_positions = new_positions
                    cash_weight = cash_alloc
                else:
                    trades = 0

                # Portfolio return: asset positions + cash allocation
                day_ret = ret_arr[idx]
                port_gross = np.nansum(current_positions * day_ret)

                # Add cash return for cash allocation
                if idx < len(cash_ret):
                    port_gross += cash_weight * cash_ret[idx]

                if trades > 0:
                    n_crypto = sum(1 for i, s in enumerate(symbols)
                                   if s in CRYPTO_SYMBOLS and current_positions[i] > 0)
                    n_equity = max(trades - n_crypto, 0)
                    cost = (n_equity * EQUITY_COST.cost_per_trade(100) +
                            n_crypto * CRYPTO_COST.cost_per_trade(100))
                    avg_cost = cost / max(trades, 1)
                    port_net = port_gross - avg_cost
                else:
                    port_net = port_gross

                if not np.isnan(port_gross):
                    fold_gross.append(port_gross)
                    fold_net.append(port_net)
                    fold_trades.append(trades)

        gross_arr = np.array(fold_gross)
        net_arr = np.array(fold_net)

        if len(gross_arr) > 10:
            gross_sharpe = sharpe_from_returns(pd.Series(gross_arr))
            net_sharpe = sharpe_from_returns(pd.Series(net_arr))
        else:
            gross_sharpe = 0.0
            net_sharpe = 0.0

        all_seed_results.append({
            "seed": seed,
            "gross_sharpe": round(float(gross_sharpe), 4),
            "net_sharpe": round(float(net_sharpe), 4),
            "total_trades": int(np.sum(fold_trades)),
            "n_oos": len(gross_arr),
        })

    return {
        "strategy": "dual_momentum",
        "lookback": lookback,
        "top_n": top_n,
        "cash_proxy": cash_proxy,
        "n_symbols": len(symbols),
        "seeds": all_seed_results,
    }


def compute_verdict(results: dict, bh_sharpe: float) -> dict:
    """Compute verdict for a strategy vs B&H."""
    sharpes = [s["net_sharpe"] for s in results["seeds"]]
    mean_sr = float(np.mean(sharpes))
    std_sr = float(np.std(sharpes)) if len(sharpes) > 1 else 0.0

    delta = mean_sr - bh_sharpe
    delta_std = max(std_sr, 0.01)
    t_stat = delta / delta_std

    seeds_positive = sum(1 for s in sharpes if s > bh_sharpe + 0.10)

    if delta > 0.10 and t_stat >= 2.0 and seeds_positive >= max(len(sharpes) * 3 // 4, 1):
        verdict = "BEATS"
    elif delta <= 0:
        verdict = "NO BEATS"
    else:
        verdict = "INCONCLUSIVE"

    return {
        "verdict": verdict,
        "mean_net_sharpe": round(mean_sr, 4),
        "std_net_sharpe": round(std_sr, 4),
        "bh_sharpe": round(bh_sharpe, 4),
        "delta": round(delta, 4),
        "t_stat": round(t_stat, 4),
        "seeds_positive": seeds_positive,
        "n_seeds": len(sharpes),
    }


def run_buyhold_baseline(closes: pd.DataFrame, seeds: list[int],
                         n_splits: int = 5, gap: int = 21) -> dict:
    """Equal-weight B&H baseline (same as L1)."""
    symbols = [c for c in closes.columns if c in ALL_SYMBOLS]
    returns = closes[symbols].pct_change().shift(-1).dropna(how="all")

    all_results = []
    for seed in seeds:
        splitter = WalkForwardSplitter(n_splits=n_splits, gap=gap)
        ret_arr = returns.values
        fold_ret = []
        for _, test_idx in splitter.split(ret_arr):
            if len(test_idx) == 0:
                continue
            port = np.nanmean(ret_arr[test_idx], axis=1)
            valid = ~np.isnan(port)
            fold_ret.extend(port[valid].tolist())

        ret = np.array(fold_ret)
        sr = sharpe_from_returns(pd.Series(ret)) if len(ret) > 10 else 0.0
        all_results.append({"seed": seed, "sharpe": round(float(sr), 4), "n_oos": len(ret)})

    return {"model": "equal_weight_bh", "seeds": all_results}


def print_comparison_table(cs_results: list, dm_results: list,
                           bh_result: dict, l1_data: dict | None):
    """Print side-by-side comparison table."""
    bh_sr = float(np.mean([s["sharpe"] for s in bh_result["seeds"]]))

    print("\n" + "=" * 110)
    print("L2 CROSS-SECTIONAL + DUAL MOMENTUM — VERDICT TABLE")
    print("=" * 110)
    print(f"{'Strategy':20s} {'Lookback':>8s} {'GrossSR':>8s} {'NetSR':>8s} "
          f"{'BH_SR':>7s} {'Delta':>7s} {'Trades':>7s} {'Verdict':14s}")
    print("-" * 110)

    all_verdicts = {}

    for res in cs_results:
        lb = res["lookback"]
        mean_gross = float(np.mean([s["gross_sharpe"] for s in res["seeds"]]))
        mean_net = float(np.mean([s["net_sharpe"] for s in res["seeds"]]))
        mean_trades = float(np.mean([s["total_trades"] for s in res["seeds"]]))
        v = compute_verdict(res, bh_sr)
        key = f"CS_lb{lb}"
        all_verdicts[key] = v
        print(f"{'Cross-sectional':20s} {lb:>7d}d {mean_gross:>8.4f} {mean_net:>8.4f} "
              f"{bh_sr:>7.4f} {v['delta']:>+7.4f} {mean_trades:>7.0f} {v['verdict']:14s}")

    for res in dm_results:
        lb = res["lookback"]
        mean_gross = float(np.mean([s["gross_sharpe"] for s in res["seeds"]]))
        mean_net = float(np.mean([s["net_sharpe"] for s in res["seeds"]]))
        mean_trades = float(np.mean([s["total_trades"] for s in res["seeds"]]))
        v = compute_verdict(res, bh_sr)
        key = f"DM_lb{lb}"
        all_verdicts[key] = v
        print(f"{'Dual momentum':20s} {lb:>7d}d {mean_gross:>8.4f} {mean_net:>8.4f} "
              f"{bh_sr:>7.4f} {v['delta']:>+7.4f} {mean_trades:>7.0f} {v['verdict']:14s}")

    # L1 comparison
    if l1_data:
        print("\n  L1 TSMOM comparison:")
        for res in l1_data.get("tsmom_results", []):
            if res.get("stress"):
                continue
            lb = res["lookback"]
            mean_net = float(np.mean([s["net_sharpe"] for s in res["seeds"]]))
            print(f"    L1 TSMOM lb={lb}d: Net Sharpe={mean_net:.4f}")

    return all_verdicts


def main():
    parser = argparse.ArgumentParser(description="L2 cross-sectional + dual momentum")
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--seeds", nargs="+", type=int, default=DEFAULT_SEEDS)
    parser.add_argument("--lookbacks", nargs="+", type=int, default=LOOKBACKS)
    parser.add_argument("--top-n", type=int, default=TOP_N)
    parser.add_argument("--n-splits", type=int, default=5)
    parser.add_argument("--gap", type=int, default=21)
    args = parser.parse_args()

    print("L2 Cross-Sectional + Dual Momentum — Anti-Bias Panier")
    print(f"Lookbacks: {args.lookbacks}d | Top-N: {args.top_n} | Seeds: {args.seeds}")
    print(f"Rebalancing: every {REBALANCE_FREQ}d | WF: {args.n_splits} folds, gap={args.gap}d")

    if args.dry_run:
        dates = pd.bdate_range("2015-01-01", "2025-12-31")
        closes = pd.DataFrame(
            np.random.randn(len(dates), 8).cumsum(axis=0) + 100,
            index=dates, columns=["SPY", "TLT", "GLD", "BTC-USD", "EFA", "SHY", "XLF", "EEM"],
        )
    else:
        closes = load_panier_closes().dropna(how="all")
        forbidden = set(closes.columns) & {"AAPL", "MSFT", "GOOG", "AMZN", "NVDA", "TSLA", "META"}
        if forbidden:
            closes = closes.drop(columns=list(forbidden))
        print(f"  {len(closes.columns)} symbols, {len(closes)} rows "
              f"({closes.index.min().date()} -> {closes.index.max().date()})")

    # B&H baseline
    print("\nRunning B&H baseline...")
    bh_result = run_buyhold_baseline(closes, args.seeds, args.n_splits, args.gap)
    bh_sr = float(np.mean([s["sharpe"] for s in bh_result["seeds"]]))
    print(f"  B&H mean Sharpe: {bh_sr:.4f}")

    # Cross-sectional momentum
    cs_results = []
    for lb in args.lookbacks:
        print(f"\nCross-sectional momentum lookback={lb}d...")
        res = run_cross_sectional(closes, lb, args.top_n, args.seeds,
                                  args.n_splits, args.gap)
        cs_results.append(res)
        mean_net = float(np.mean([s["net_sharpe"] for s in res["seeds"]]))
        print(f"  Mean net Sharpe: {mean_net:.4f} (delta: {mean_net - bh_sr:+.4f})")

    # Dual momentum
    dm_results = []
    for lb in args.lookbacks:
        print(f"\nDual momentum lookback={lb}d...")
        res = run_dual_momentum(closes, lb, args.top_n, "SHY", args.seeds,
                                args.n_splits, args.gap)
        dm_results.append(res)
        mean_net = float(np.mean([s["net_sharpe"] for s in res["seeds"]]))
        print(f"  Mean net Sharpe: {mean_net:.4f} (delta: {mean_net - bh_sr:+.4f})")

    # Load L1 results for comparison
    l1_data = None
    if L1_RESULTS.exists():
        with open(L1_RESULTS) as f:
            l1_data = json.load(f)

    # Print comparison
    all_verdicts = print_comparison_table(cs_results, dm_results, bh_result, l1_data)

    # Save
    CHECKPOINTS_DIR.mkdir(parents=True, exist_ok=True)
    output = {
        "strategy": "L2_dual_momentum",
        "n_symbols": len(closes.columns),
        "symbols": list(closes.columns),
        "lookbacks": args.lookbacks,
        "top_n": args.top_n,
        "seeds": args.seeds,
        "n_splits": args.n_splits,
        "gap": args.gap,
        "rebalance_freq": REBALANCE_FREQ,
        "buyhold_baseline": bh_result,
        "cross_sectional_results": cs_results,
        "dual_momentum_results": dm_results,
        "verdicts": all_verdicts,
        "l1_comparison": {
            "l1_best_net_sharpe": max(
                float(np.mean([s["net_sharpe"] for s in r["seeds"]]))
                for r in (l1_data or {}).get("tsmom_results", [])
                if not r.get("stress")
            ) if l1_data else None,
        },
    }

    out_path = CHECKPOINTS_DIR / "L2_dual_momentum_results.json"
    out_path.write_text(json.dumps(output, indent=2, default=str), encoding="utf-8")
    print(f"\nResults saved: {out_path}")

    # Final verdicts
    print("\n" + "=" * 60)
    print("FINAL VERDICTS:")
    for key, v in all_verdicts.items():
        print(f"  {key}: {v['verdict']} (delta={v['delta']:+.4f})")
    print("=" * 60)


if __name__ == "__main__":
    main()
