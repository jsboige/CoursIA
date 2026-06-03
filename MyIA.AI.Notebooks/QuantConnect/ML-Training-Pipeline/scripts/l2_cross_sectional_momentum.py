"""L2 Cross-Sectional + Dual Momentum — Antonacci (2014) on 26-symbol panier.

Reference
---------
Antonacci, G. (2014): "Dual Momentum Investing"
and cross-sectional momentum (Jegadeesh & Titman 1993).

Two sub-strategies combined:
  A. Cross-sectional momentum: rank assets by 12M return, long top tercile,
     short bottom tercile, vol-scaled, rebalanced monthly.
  B. Dual momentum (absolute + relative): long ONLY IF (a) 12M abs return > 0
     AND (b) 12M return > T-bill proxy (SHY). Otherwise go to cash/defensive.

Walk-forward 5-fold expanding, 26 symbols x 2 sub-strategies x 4 seeds.
Gate: net Sharpe > equal-weight B&H + 0.10 after tx costs, edge >= 2 sigma cross-seed.

Output
------
- results/l2_dual_momentum/l2_dual_momentum_results.csv
- results/l2_dual_momentum/results.json

Env: system Python (numpy, pandas, scipy). No GPU needed.
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

import numpy as np
import pandas as pd
from scipy import stats

SCRIPT_DIR = Path(__file__).resolve().parent
DATA_DIR = SCRIPT_DIR.parent.parent / "datasets" / "panier"
RESULTS_DIR = SCRIPT_DIR / "results" / "l2_dual_momentum"

PANIER_CSV = DATA_DIR / "panier_close_all.csv"

ASSET_CLASSES = {
    "SPY": "eq", "RSP": "eq", "IWM": "eq",
    "XLF": "eq", "XLK": "eq", "XLV": "eq", "XLY": "eq",
    "XLP": "eq", "XLI": "eq", "XLU": "eq", "XLB": "eq",
    "XLRE": "eq", "XLC": "eq",
    "TLT": "bond", "IEF": "bond", "SHY": "bond",
    "GLD": "commodity", "USO": "commodity", "DBA": "commodity",
    "EFA": "eq_intl", "EEM": "eq_intl",
    "BTC-USD": "crypto", "ETH-USD": "crypto",
    "LTC-USD": "crypto", "XRP-USD": "crypto",
}

COST_BPS = {
    "eq": 5.0, "eq_intl": 10.0, "bond": 5.0,
    "commodity": 10.0, "crypto": 10.0,
}
STRESS_BPS = 50.0

SEEDS = [0, 1, 7, 42]
N_SPLITS = 5
TARGET_VOL = 0.10
ANNUALIZE_FACTOR = 252
LOOKBACK_MONTHS = 12  # Standard momentum lookback
REBALANCE_FREQ = 21  # Monthly rebalance


def load_panier() -> pd.DataFrame:
    """Load panier prices, forward-fill."""
    df = pd.read_csv(PANIER_CSV, parse_dates=["Date"], index_col="Date")
    df = df.sort_index().ffill()
    return df


def sharpe(returns: np.ndarray) -> float:
    if len(returns) < 2:
        return 0.0
    std = np.std(returns, ddof=1)
    if std == 0:
        return 0.0
    return float(np.mean(returns) / std * np.sqrt(ANNUALIZE_FACTOR))


def max_drawdown(returns: np.ndarray) -> float:
    cum = np.cumprod(1 + returns)
    peak = np.maximum.accumulate(cum)
    dd = (peak - cum) / peak
    return float(np.max(dd)) if len(dd) > 0 else 0.0


def compute_regimes(prices: pd.DataFrame) -> pd.Series:
    """4-regime classification via SPY 12M return and 6M vol."""
    spy = prices.get("SPY", prices.iloc[:, 0])
    ret_12m = spy.pct_change(252)
    vol_6m = spy.pct_change().rolling(126).std() * np.sqrt(252)
    vol_median = vol_6m.expanding(min_periods=126).median()

    regime = pd.Series("range", index=prices.index)
    regime[vol_6m > vol_median] = "volatile"
    regime[(vol_6m <= vol_median) & (ret_12m > 0.05)] = "bull"
    regime[(vol_6m <= vol_median) & (ret_12m < -0.05)] = "bear"
    return regime


def run_cross_sectional(prices: pd.DataFrame, seed: int) -> dict:
    """Cross-sectional momentum: long top tercile, short bottom tercile.

    Rebalanced monthly based on 12M cumulative return ranking.
    """
    rng = np.random.RandomState(seed)
    symbols = [s for s in ASSET_CLASSES if s in prices.columns]
    returns_all = prices[symbols].pct_change().dropna()

    lb_days = LOOKBACK_MONTHS * 21
    n = len(returns_all)
    regimes = compute_regimes(prices)

    port_returns = []
    n_trades = 0
    prev_positions = None

    for t in range(lb_days + 21, n, REBALANCE_FREQ):
        # Rank by 12M return
        cum_ret = returns_all.iloc[t - lb_days:t].sum()
        valid = cum_ret.dropna()
        if len(valid) < 6:
            continue

        # Tercile split
        sorted_syms = valid.sort_values()
        n_sym = len(sorted_syms)
        n_tercile = max(n_sym // 3, 1)

        bottom = sorted_syms.index[:n_tercile]
        top = sorted_syms.index[-n_tercile:]

        # Build position vector
        positions = pd.Series(0.0, index=symbols)
        for sym in top:
            asset_class = ASSET_CLASSES.get(sym, "eq")
            cost_bps = COST_BPS.get(asset_class, 5.0)
            # Long with vol-scaling
            ret_series = prices[sym].pct_change().dropna()
            vol = ret_series.iloc[max(0, t - 60):t].std() * np.sqrt(ANNUALIZE_FACTOR)
            scale = min(TARGET_VOL / max(vol, 0.01), 2.0)
            positions[sym] = scale / n_tercile

        for sym in bottom:
            ret_series = prices[sym].pct_change().dropna()
            vol = ret_series.iloc[max(0, t - 60):t].std() * np.sqrt(ANNUALIZE_FACTOR)
            scale = min(TARGET_VOL / max(vol, 0.01), 2.0)
            positions[sym] = -scale / n_tercile

        # Count trades
        if prev_positions is not None:
            n_trades += int((positions != prev_positions).sum())
        prev_positions = positions.copy()

        # Compute return for next period
        end_t = min(t + REBALANCE_FREQ, n)
        for day in range(t, end_t):
            day_ret = returns_all.iloc[day] * positions
            day_ret = day_ret.dropna()
            port_returns.append(day_ret.sum())

    if not port_returns:
        return {"strategy": "cross_sectional", "seed": seed, "error": "no_data"}

    port_arr = np.array(port_returns)

    # Apply rough tx costs (estimated per rebalance)
    if n_trades > 0:
        avg_cost = 7.5 / 10000  # Average cost across asset classes
        total_cost = n_trades * avg_cost / len(port_arr)
        port_arr = port_arr - total_cost

    # Seed bootstrap for variation
    if seed != 0:
        block_size = max(20, len(port_arr) // 50)
        n_blocks = len(port_arr) // block_size
        idx = rng.randint(0, len(port_arr) - block_size, size=n_blocks)
        boot_idx = np.concatenate([np.arange(i, i + block_size) for i in idx])[:len(port_arr)]
        port_arr = port_arr[boot_idx]

    # Walk-forward folds
    fold_sharpes = []
    fold_size = len(port_arr) // (N_SPLITS + 1)
    for f in range(N_SPLITS):
        s = fold_size * (f + 1)
        e = min(s + fold_size, len(port_arr))
        if e > s:
            fold_sharpes.append(sharpe(port_arr[s:e]))

    net_sr = sharpe(port_arr)

    # B&H benchmark (equal-weight, same period)
    bh_port = returns_all.iloc[lb_days + 21:lb_days + 21 + len(port_arr)]
    bh_arr = bh_port.mean(axis=1).values
    if len(bh_arr) > len(port_arr):
        bh_arr = bh_arr[:len(port_arr)]
    elif len(bh_arr) < len(port_arr):
        port_arr = port_arr[:len(bh_arr)]
    bh_sr = sharpe(bh_arr)

    return {
        "strategy": "cross_sectional",
        "seed": seed,
        "n_trades": n_trades,
        "net_sharpe": net_sr,
        "bh_sharpe": bh_sr,
        "delta_sharpe": net_sr - bh_sr,
        "fold_sharpes": fold_sharpes,
        "mean_fold_sharpe": float(np.mean(fold_sharpes)) if fold_sharpes else 0.0,
        "total_return": float(np.prod(1 + port_arr) - 1),
        "max_drawdown": float(max_drawdown(port_arr)),
    }


def run_dual_momentum(prices: pd.DataFrame, seed: int) -> dict:
    """Dual momentum (Antonacci): absolute + relative momentum filter.

    Go long asset ONLY IF:
      (a) 12M absolute return > 0 (positive trend)
      (b) 12M return > SHY return (beats risk-free proxy)
    Otherwise: allocate to SHY (cash/defensive).
    Among eligible assets, equal-weight with vol-scaling.
    """
    rng = np.random.RandomState(seed)
    symbols = [s for s in ASSET_CLASSES if s in prices.columns and s != "SHY"]
    returns_all = prices[symbols].pct_change().dropna()

    lb_days = LOOKBACK_MONTHS * 21
    shy_ret_12m = prices["SHY"].pct_change(lb_days) if "SHY" in prices.columns else pd.Series(0, index=prices.index)
    n = len(returns_all)
    regimes = compute_regimes(prices)

    port_returns = []
    n_trades = 0
    prev_eligible = None

    for t in range(lb_days + 21, n, REBALANCE_FREQ):
        cum_ret = returns_all.iloc[t - lb_days:t].sum()
        shy_cum = shy_ret_12m.iloc[t] if t < len(shy_ret_12m) else 0

        # Filter: abs > 0 AND > SHY
        eligible = cum_ret[(cum_ret > 0) & (cum_ret > shy_cum)].dropna()

        if len(eligible) == 0:
            # All to defensive (SHY)
            eligible_syms = []
        else:
            eligible_syms = eligible.index.tolist()

        # Count trades
        if prev_eligible is not None:
            entered = set(eligible_syms) - set(prev_eligible)
            exited = set(prev_eligible) - set(eligible_syms)
            n_trades += len(entered) + len(exited)
        prev_eligible = eligible_syms

        # Build positions
        end_t = min(t + REBALANCE_FREQ, n)
        for day in range(t, end_t):
            if not eligible_syms:
                # Defensive: earn SHY-like return (use actual SHY return)
                if "SHY" in prices.columns and day < n:
                    shy_daily = prices["SHY"].pct_change().iloc[day] if day < len(prices) else 0
                    port_returns.append(shy_daily if not np.isnan(shy_daily) else 0)
                else:
                    port_returns.append(0.0)
            else:
                n_eligible = len(eligible_syms)
                day_ret = 0.0
                for sym in eligible_syms:
                    if sym in returns_all.columns and day < len(returns_all):
                        ret = returns_all[sym].iloc[day]
                        # Simple vol-scale
                        vol = returns_all[sym].iloc[max(0, t - 60):t].std() * np.sqrt(ANNUALIZE_FACTOR)
                        scale = min(TARGET_VOL / max(vol, 0.01), 2.0)
                        day_ret += scale * ret / n_eligible
                port_returns.append(day_ret)

    if not port_returns:
        return {"strategy": "dual_momentum", "seed": seed, "error": "no_data"}

    port_arr = np.array(port_returns)

    # Apply tx costs
    if n_trades > 0:
        avg_cost = 7.5 / 10000
        total_cost = n_trades * avg_cost / len(port_arr)
        port_arr = port_arr - total_cost

    # Seed bootstrap
    if seed != 0:
        block_size = max(20, len(port_arr) // 50)
        n_blocks = len(port_arr) // block_size
        idx = rng.randint(0, len(port_arr) - block_size, size=n_blocks)
        boot_idx = np.concatenate([np.arange(i, i + block_size) for i in idx])[:len(port_arr)]
        port_arr = port_arr[boot_idx]

    # Walk-forward folds
    fold_sharpes = []
    fold_size = len(port_arr) // (N_SPLITS + 1)
    for f in range(N_SPLITS):
        s = fold_size * (f + 1)
        e = min(s + fold_size, len(port_arr))
        if e > s:
            fold_sharpes.append(sharpe(port_arr[s:e]))

    net_sr = sharpe(port_arr)

    # B&H benchmark
    bh_port = returns_all.iloc[lb_days + 21:lb_days + 21 + len(port_arr)]
    bh_arr = bh_port.mean(axis=1).values
    if len(bh_arr) > len(port_arr):
        bh_arr = bh_arr[:len(port_arr)]
    elif len(bh_arr) < len(port_arr):
        port_arr = port_arr[:len(bh_arr)]
    bh_sr = sharpe(bh_arr)

    return {
        "strategy": "dual_momentum",
        "seed": seed,
        "n_trades": n_trades,
        "net_sharpe": net_sr,
        "bh_sharpe": bh_sr,
        "delta_sharpe": net_sr - bh_sr,
        "fold_sharpes": fold_sharpes,
        "mean_fold_sharpe": float(np.mean(fold_sharpes)) if fold_sharpes else 0.0,
        "total_return": float(np.prod(1 + port_arr) - 1),
        "max_drawdown": float(max_drawdown(port_arr)),
    }


def run_all(dry_run: bool = False) -> None:
    """Run all L2 momentum configurations."""
    print("=" * 60)
    print("L2 Cross-Sectional + Dual Momentum")
    print("=" * 60)

    prices = load_panier()
    print(f"Loaded panier: {prices.shape[0]} days x {prices.shape[1]} symbols")
    print(f"Date range: {prices.index[0].date()} to {prices.index[-1].date()}")
    print()

    all_results = []
    strategies = [("cross_sectional", run_cross_sectional), ("dual_momentum", run_dual_momentum)]
    n_configs = len(strategies) * len(SEEDS)
    t0 = time.time()
    cfg_idx = 0

    for strat_name, strat_fn in strategies:
        for seed in SEEDS:
            cfg_idx += 1
            print(f"[{cfg_idx}/{n_configs}] {strat_name}, seed={seed}...", end=" ", flush=True)

            res = strat_fn(prices, seed)
            all_results.append(res)

            if "error" in res:
                print(f"SKIP ({res['error']})")
            else:
                print(f"Sharpe={res['net_sharpe']:.3f} (BH={res['bh_sharpe']:.3f}, "
                      f"delta={res['delta_sharpe']:+.3f})")

            if dry_run and cfg_idx >= 4:
                print("\n[DRY RUN] stopping after 4 configs")
                break
        if dry_run and cfg_idx >= 4:
            break

    elapsed = time.time() - t0
    print(f"\nCompleted in {elapsed:.1f}s")

    # Aggregate by strategy
    print("\n" + "=" * 60)
    print("AGGREGATE RESULTS BY STRATEGY")
    print("=" * 60)

    verdicts = {}
    for strat_name, _ in strategies:
        strat_results = [r for r in all_results if r.get("strategy") == strat_name and "error" not in r]
        if not strat_results:
            continue

        sharpes = [r["net_sharpe"] for r in strat_results]
        deltas = [r["delta_sharpe"] for r in strat_results]
        mean_bh = np.mean([r["bh_sharpe"] for r in strat_results])

        mean_sr = np.mean(sharpes)
        mean_delta = np.mean(deltas)
        std_delta = np.std(deltas, ddof=1) if len(deltas) > 1 else 0.0
        edge_sigma = mean_delta / std_delta if std_delta > 0 else 0.0

        passes_gate = (mean_sr > mean_bh + 0.10) and (edge_sigma >= 2.0)
        verdict = "BEATS" if passes_gate else "NO BEATS"
        if abs(edge_sigma) < 0.5:
            verdict = "INCONCLUSIVE"

        verdicts[strat_name] = verdict

        print(f"\n  {strat_name}:")
        print(f"    Net Sharpe: {mean_sr:.3f} (std={np.std(sharpes):.3f})")
        print(f"    BH Sharpe:  {mean_bh:.3f}")
        print(f"    Delta:      {mean_delta:+.3f} (edge={edge_sigma:.1f} sigma)")
        print(f"    Verdict:    {verdict}")

    # Save
    RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    df = pd.DataFrame(all_results)
    df.to_csv(RESULTS_DIR / "l2_dual_momentum_results.csv", index=False)

    summary = {
        "timestamp": pd.Timestamp.now().isoformat(),
        "elapsed_seconds": round(elapsed, 1),
        "n_symbols": len(ASSET_CLASSES),
        "lookback_months": LOOKBACK_MONTHS,
        "seeds": SEEDS,
        "verdicts": verdicts,
        "overall_verdict": "BEATS" if any(v == "BEATS" for v in verdicts.values()) else "NO BEATS",
        "results": all_results,
    }
    with open(RESULTS_DIR / "results.json", "w") as f:
        json.dump(summary, f, indent=2, default=str)

    print(f"\nCSV: {RESULTS_DIR / 'l2_dual_momentum_results.csv'}")
    print(f"JSON: {RESULTS_DIR / 'results.json'}")
    print(f"\nOVERALL VERDICT: {summary['overall_verdict']}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="L2 Cross-Sectional + Dual Momentum")
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()
    run_all(dry_run=args.dry_run)
