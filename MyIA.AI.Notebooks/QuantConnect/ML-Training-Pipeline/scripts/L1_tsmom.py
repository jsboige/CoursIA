"""
L1 — Time-Series Momentum (TSMOM) baseline on anti-bias panier.

Moskowitz-Ooi-Pedersen (2012) style TSMOM: signal = sign(past return) for
lookbacks 1/3/6/12 months, vol-scaled positions, walk-forward expanding
validation with 5 folds x 4 seeds.

Compares TSMOM portfolio (equal-weight across assets) vs equal-weight
buy-and-hold benchmark. Transaction costs: 5bps equity, 10bps crypto,
50bps stress test.

Usage:
    python L1_tsmom.py
    python L1_tsmom.py --dry-run
    python L1_tsmom.py --seeds 0 1 7 42
    python L1_tsmom.py --lookbacks 21 63 126 252
"""

import argparse
import json
import sys
from pathlib import Path

import numpy as np
import pandas as pd

SCRIPTS_DIR = Path(__file__).resolve().parent
CHECKPOINTS_DIR = SCRIPTS_DIR.parent / "checkpoints" / "l1_tsmom"

sys.path.insert(0, str(SCRIPTS_DIR))

from panier_loader import (
    PANIER_GROUPS,
    load_panier_closes,
    get_panier_symbols,
)
from walk_forward import WalkForwardSplitter
from transaction_costs import TransactionCostModel, compare_gross_vs_net
from baselines import sharpe_from_returns

# All 26 symbols flat
ALL_SYMBOLS = get_panier_symbols()

# Cost models per asset class
EQUITY_COST = TransactionCostModel(
    commission_bps=1.0, bid_ask_spread_bps=2.0,
    market_impact_coeff=0.05, daily_volume=5_000_000, slippage_bps=2.0,
)
CRYPTO_COST = TransactionCostModel(
    commission_bps=2.0, bid_ask_spread_bps=3.0,
    market_impact_coeff=0.05, daily_volume=1_000_000, slippage_bps=5.0,
)
STRESS_COST = TransactionCostModel(
    commission_bps=5.0, bid_ask_spread_bps=10.0,
    market_impact_coeff=0.1, daily_volume=1_000_000, slippage_bps=35.0,
)

CRYPTO_SYMBOLS = set(PANIER_GROUPS["crypto"])

DEFAULT_LOOKBACKS = [21, 63, 126, 252]  # ~1/3/6/12 months
DEFAULT_SEEDS = [0, 1, 7, 42]
TARGET_VOL = 0.15  # annualized target volatility
VOL_LOOKBACK = 63  # vol estimation window


def get_cost_model(symbol: str, stress: bool = False) -> TransactionCostModel:
    if stress:
        return STRESS_COST
    if symbol in CRYPTO_SYMBOLS:
        return CRYPTO_COST
    return EQUITY_COST


def compute_tsmom_signal(closes: pd.Series, lookback: int) -> pd.Series:
    """TSMOM signal: +1 if past return > 0, -1 otherwise."""
    past_return = closes.pct_change(lookback)
    return np.sign(past_return)


def compute_vol_scale(closes: pd.Series, lookback: int = VOL_LOOKBACK,
                      target_vol: float = TARGET_VOL) -> pd.Series:
    """Volatility scaling factor to achieve target annualized vol."""
    daily_vol = closes.pct_change().rolling(lookback).std()
    annual_vol = daily_vol * np.sqrt(252)
    scale = target_vol / annual_vol.clip(lower=0.01)
    return scale.clip(0.1, 3.0)


def run_tsmom_single_lookback(
    closes: pd.DataFrame,
    lookback: int,
    seeds: list[int],
    n_splits: int = 5,
    gap: int = 21,
    stress: bool = False,
) -> dict:
    """Run TSMOM for a single lookback across all seeds and folds."""
    symbols = [c for c in closes.columns if c in ALL_SYMBOLS]
    if not symbols:
        return {"lookback": lookback, "error": "no valid symbols"}

    # Build TSMOM signals + vol scales for each asset
    signals = {}
    vol_scales = {}
    for sym in symbols:
        sig = compute_tsmom_signal(closes[sym], lookback)
        vs = compute_vol_scale(closes[sym])
        signals[sym] = sig
        vol_scales[sym] = vs

    signals_df = pd.DataFrame(signals)
    vol_df = pd.DataFrame(vol_scales)

    # Align returns
    returns = closes[symbols].pct_change().shift(-1)
    valid_idx = returns.dropna(how="all").index
    returns = returns.loc[valid_idx]
    signals_df = signals_df.loc[valid_idx]
    vol_df = vol_df.loc[valid_idx]

    all_seed_results = []

    for seed in seeds:
        rng = np.random.default_rng(seed)
        n_samples = len(returns)

        # Walk-forward expanding
        splitter = WalkForwardSplitter(n_splits=n_splits, gap=gap)

        # Use aligned numpy arrays
        ret_arr = returns.values
        sig_arr = signals_df.values
        vol_arr = vol_df.values

        fold_returns_gross = []
        fold_returns_net = []
        fold_trades = []

        for train_idx, test_idx in splitter.split(ret_arr):
            if len(test_idx) == 0:
                continue

            # TSMOM portfolio return: equal-weight of (signal * vol_scale * asset return)
            # Signal from last training observation applied to test period
            test_sig = sig_arr[test_idx]
            test_vol = vol_arr[test_idx]
            test_ret = ret_arr[test_idx]

            # Position = signal * vol_scale, then equal-weight
            positions = test_sig * test_vol
            n_assets = positions.shape[1]
            # Replace NaN with 0
            positions = np.nan_to_num(positions, nan=0.0)

            # Portfolio gross return per day
            port_gross = np.nansum(positions * test_ret, axis=1) / n_assets

            # Detect trades (position changes across all assets)
            pos_changes = np.abs(np.diff(positions, axis=0, prepend=np.zeros_like(positions[0:1])))
            trades_per_day = np.sum(pos_changes > 0, axis=1)

            # Apply transaction costs
            if stress:
                cost_per_trade = STRESS_COST.cost_per_trade(100)
            else:
                # Weighted average: crypto symbols get higher cost
                n_crypto = sum(1 for s in symbols if s in CRYPTO_SYMBOLS)
                n_equity = len(symbols) - n_crypto
                avg_cost = (n_equity * EQUITY_COST.cost_per_trade(100) +
                            n_crypto * CRYPTO_COST.cost_per_trade(100)) / len(symbols)
                cost_per_trade = avg_cost

            trade_costs = trades_per_day * 2 * cost_per_trade / n_assets
            port_net = port_gross - trade_costs

            # Remove NaN
            valid = ~(np.isnan(port_gross) | np.isnan(port_net))
            fold_returns_gross.extend(port_gross[valid].tolist())
            fold_returns_net.extend(port_net[valid].tolist())
            fold_trades.extend(trades_per_day[valid].tolist())

        gross_arr = np.array(fold_returns_gross)
        net_arr = np.array(fold_returns_net)

        if len(gross_arr) > 10:
            gross_sharpe = sharpe_from_returns(pd.Series(gross_arr))
            net_sharpe = sharpe_from_returns(pd.Series(net_arr))
            gross_cagr = float(np.prod(1 + gross_arr) ** (252 / max(len(gross_arr), 1)) - 1)
            net_cagr = float(np.prod(1 + net_arr) ** (252 / max(len(net_arr), 1)) - 1)
            total_trades = int(np.sum(fold_trades))
            trade_freq = total_trades / max(len(gross_arr), 1)
        else:
            gross_sharpe = 0.0
            net_sharpe = 0.0
            gross_cagr = 0.0
            net_cagr = 0.0
            total_trades = 0
            trade_freq = 0.0

        all_seed_results.append({
            "seed": seed,
            "gross_sharpe": round(float(gross_sharpe), 4),
            "net_sharpe": round(float(net_sharpe), 4),
            "gross_cagr": round(float(gross_cagr), 4),
            "net_cagr": round(float(net_cagr), 4),
            "total_trades": total_trades,
            "trade_freq": round(float(trade_freq), 4),
            "n_oos": len(gross_arr),
        })

    return {
        "lookback": lookback,
        "n_symbols": len(symbols),
        "symbols": symbols,
        "seeds": all_seed_results,
        "stress": stress,
    }


def run_buyhold_baseline(
    closes: pd.DataFrame,
    seeds: list[int],
    n_splits: int = 5,
    gap: int = 21,
    stress: bool = False,
) -> dict:
    """Equal-weight buy-and-hold baseline for comparison."""
    symbols = [c for c in closes.columns if c in ALL_SYMBOLS]
    returns = closes[symbols].pct_change().shift(-1).dropna(how="all")

    all_seed_results = []

    for seed in seeds:
        splitter = WalkForwardSplitter(n_splits=n_splits, gap=gap)
        ret_arr = returns.values
        n_assets = ret_arr.shape[1]

        fold_returns = []
        for train_idx, test_idx in splitter.split(ret_arr):
            if len(test_idx) == 0:
                continue
            # Equal-weight B&H: no trading signal, just hold
            port_ret = np.nanmean(ret_arr[test_idx], axis=1)
            valid = ~np.isnan(port_ret)
            fold_returns.extend(port_ret[valid].tolist())

        ret_arr_bh = np.array(fold_returns)
        if len(ret_arr_bh) > 10:
            bh_sharpe = sharpe_from_returns(pd.Series(ret_arr_bh))
            bh_cagr = float(np.prod(1 + ret_arr_bh) ** (252 / max(len(ret_arr_bh), 1)) - 1)
        else:
            bh_sharpe = 0.0
            bh_cagr = 0.0

        all_seed_results.append({
            "seed": seed,
            "sharpe": round(float(bh_sharpe), 4),
            "cagr": round(float(bh_cagr), 4),
            "n_oos": len(ret_arr_bh),
        })

    return {
        "model": "equal_weight_bh",
        "n_symbols": len(symbols),
        "seeds": all_seed_results,
    }


def compute_verdict(tsmom_results: dict, bh_results: dict) -> dict:
    """Compute BEATS / NO BEATS / INCONCLUSIVE verdict."""
    tsmom_sharpes = [s["net_sharpe"] for s in tsmom_results["seeds"]]
    bh_sharpes = [s["sharpe"] for s in bh_results["seeds"]]

    mean_tsmom = float(np.mean(tsmom_sharpes))
    std_tsmom = float(np.std(tsmom_sharpes)) if len(tsmom_sharpes) > 1 else 0.0
    mean_bh = float(np.mean(bh_sharpes))
    std_bh = float(np.std(bh_sharpes)) if len(bh_sharpes) > 1 else 0.0

    delta = mean_tsmom - mean_bh
    delta_std = float(np.sqrt(std_tsmom**2 + std_bh**2))
    t_stat = delta / delta_std if delta_std > 1e-10 else 0.0

    # Gate: Net Sharpe > B&H + 0.10, 4/4 seeds positive delta, edge >= 2 sigma
    seeds_positive = sum(1 for ts, bs in zip(tsmom_sharpes, bh_sharpes) if ts > bs + 0.10)
    n_seeds = len(tsmom_sharpes)

    if delta > 0.10 and t_stat >= 2.0 and seeds_positive >= max(n_seeds * 3 // 4, 1):
        verdict = "BEATS"
    elif delta <= 0:
        verdict = "NO BEATS"
    else:
        verdict = "INCONCLUSIVE"

    return {
        "verdict": verdict,
        "mean_tsmom_net_sharpe": round(mean_tsmom, 4),
        "std_tsmom_net_sharpe": round(std_tsmom, 4),
        "mean_bh_sharpe": round(mean_bh, 4),
        "std_bh_sharpe": round(std_bh, 4),
        "delta_sharpe": round(delta, 4),
        "t_stat": round(t_stat, 4),
        "seeds_positive_delta": seeds_positive,
        "n_seeds": n_seeds,
    }


def print_results_table(all_results: list[dict], bh_result: dict):
    """Print summary verdict table."""
    print("\n" + "=" * 100)
    print("L1 TSMOM BASELINE — VERDICT TABLE (anti-bias panier 26 symbols)")
    print("=" * 100)

    bh_sharpes = {s["seed"]: s["sharpe"] for s in bh_result["seeds"]}

    for res in all_results:
        lb = res["lookback"]
        tsmom_sharpes = {s["seed"]: s["net_sharpe"] for s in res["seeds"]}
        gross_sharpes = {s["seed"]: s["gross_sharpe"] for s in res["seeds"]}

        mean_tsmom = float(np.mean(list(tsmom_sharpes.values())))
        mean_gross = float(np.mean(list(gross_sharpes.values())))
        mean_bh = float(np.mean(list(bh_sharpes.values())))
        delta = mean_tsmom - mean_bh

        verdict_info = compute_verdict(res, bh_result)
        verdict = verdict_info["verdict"]

        stress_tag = " [STRESS]" if res.get("stress") else ""
        print(f"\n  Lookback {lb:>4d}d{stress_tag} ({res['n_symbols']} symbols)")
        print(f"    TSMOM net Sharpe:  {mean_tsmom:>7.4f} (gross: {mean_gross:.4f})")
        print(f"    B&H Sharpe:        {mean_bh:>7.4f}")
        print(f"    Delta:             {delta:>+7.4f}  t-stat: {verdict_info['t_stat']:.3f}")
        print(f"    Seeds positive:    {verdict_info['seeds_positive_delta']}/{verdict_info['n_seeds']}")
        print(f"    Verdict:           {verdict}")

        # Per-seed detail
        for s in res["seeds"]:
            bh_s = bh_sharpes.get(s["seed"], 0.0)
            print(f"      seed={s['seed']:>2d}: TSMOM_net={s['net_sharpe']:>7.4f} "
                  f"BH={bh_s:>7.4f} delta={s['net_sharpe']-bh_s:>+7.4f} "
                  f"trades={s['total_trades']:>5d}")


def main():
    parser = argparse.ArgumentParser(description="L1 TSMOM baseline on anti-bias panier")
    parser.add_argument("--dry-run", action="store_true",
                        help="Use synthetic data for testing")
    parser.add_argument("--seeds", nargs="+", type=int, default=DEFAULT_SEEDS)
    parser.add_argument("--lookbacks", nargs="+", type=int, default=DEFAULT_LOOKBACKS)
    parser.add_argument("--n-splits", type=int, default=5)
    parser.add_argument("--gap", type=int, default=21, help="WF gap (trading days)")
    parser.add_argument("--stress", action="store_true",
                        help="Run 50bps stress test alongside normal")
    args = parser.parse_args()

    print("L1 TSMOM Baseline — Anti-Bias Panier (26 symbols, 7 asset classes)")
    print(f"Lookbacks: {args.lookbacks} days")
    print(f"Seeds: {args.seeds} | WF folds: {args.n_splits} | Gap: {args.gap}d")
    print(f"Target vol: {TARGET_VOL:.0%} annualized | Vol lookback: {VOL_LOOKBACK}d")
    print(f"Tx costs: ~5bps equity, ~10bps crypto, ~50bps stress")

    # Load data
    if args.dry_run:
        print("\nDRY RUN: generating synthetic data...")
        dates = pd.bdate_range("2015-01-01", "2025-12-31")
        closes = pd.DataFrame(
            np.random.randn(len(dates), 5).cumsum(axis=0) + 100,
            index=dates,
            columns=["SPY", "TLT", "GLD", "BTC-USD", "EFA"],
        )
    else:
        print("\nLoading panier data...")
        closes = load_panier_closes()
        closes = closes.dropna(how="all")
        print(f"  Loaded {len(closes.columns)} symbols, {len(closes)} rows "
              f"({closes.index.min().date()} -> {closes.index.max().date()})")

        # Verify no FAANG
        forbidden = set(closes.columns) & {"AAPL", "MSFT", "GOOG", "AMZN", "NVDA", "TSLA", "META"}
        if forbidden:
            print(f"  WARNING: Forbidden symbols found: {forbidden}")
            closes = closes.drop(columns=list(forbidden))

    # Buy-and-hold baseline
    print("\nRunning equal-weight B&H baseline...")
    bh_result = run_buyhold_baseline(closes, args.seeds, args.n_splits, args.gap)
    bh_mean = float(np.mean([s["sharpe"] for s in bh_result["seeds"]]))
    print(f"  B&H mean Sharpe: {bh_mean:.4f}")

    # TSMOM for each lookback
    all_results = []
    for lb in args.lookbacks:
        print(f"\nRunning TSMOM lookback={lb}d...")
        res = run_tsmom_single_lookback(
            closes, lb, args.seeds, args.n_splits, args.gap, stress=False,
        )
        all_results.append(res)
        mean_net = float(np.mean([s["net_sharpe"] for s in res["seeds"]]))
        print(f"  Mean net Sharpe: {mean_net:.4f} (delta vs B&H: {mean_net - bh_mean:+.4f})")

    # Stress test with best lookback (if enabled)
    if args.stress:
        best_lb = max(all_results, key=lambda r: float(np.mean(
            [s["net_sharpe"] for s in r["seeds"]])))["lookback"]
        print(f"\nRunning STRESS test (50bps) on best lookback={best_lb}d...")
        stress_res = run_tsmom_single_lookback(
            closes, best_lb, args.seeds, args.n_splits, args.gap, stress=True,
        )
        all_results.append(stress_res)

    # Print verdict table
    print_results_table(all_results, bh_result)

    # Save results
    CHECKPOINTS_DIR.mkdir(parents=True, exist_ok=True)

    output = {
        "strategy": "L1_TSMOM",
        "panier_symbols": list(closes.columns),
        "n_symbols": len(closes.columns),
        "lookbacks": args.lookbacks,
        "seeds": args.seeds,
        "n_splits": args.n_splits,
        "gap": args.gap,
        "target_vol": TARGET_VOL,
        "vol_lookback": VOL_LOOKBACK,
        "buyhold_baseline": bh_result,
        "tsmom_results": all_results,
        "verdicts": {},
    }

    for res in all_results:
        lb = res["lookback"]
        stress_tag = "_stress" if res.get("stress") else ""
        key = f"lb{lb}{stress_tag}"
        output["verdicts"][key] = compute_verdict(res, bh_result)

    out_path = CHECKPOINTS_DIR / "L1_tsmom_results.json"
    out_path.write_text(json.dumps(output, indent=2, default=str), encoding="utf-8")
    print(f"\nResults saved: {out_path}")

    # Print final verdict summary
    print("\n" + "=" * 60)
    print("FINAL VERDICTS:")
    for key, v in output["verdicts"].items():
        print(f"  {key}: {v['verdict']} (delta={v['delta_sharpe']:+.4f}, "
              f"t={v['t_stat']:.3f}, seeds+={v['seeds_positive_delta']}/{v['n_seeds']})")
    print("=" * 60)


if __name__ == "__main__":
    main()
