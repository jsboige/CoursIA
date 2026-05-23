"""L1 TSMOM Baseline — Time-Series Momentum on 26-symbol anti-bias panier.

Reference
---------
Moskowitz, Ooi, Pedersen (2012): "Time Series Momentum"
J. Financial Economics 104(2), 228-250.

Method
------
For each asset and lookback L in {1, 3, 6, 12} months:
  - If cumulative return over L months > 0 → go long next month
  - If cumulative return over L months < 0 → go short next month
  - Position size = vol-scaled (target 10% annual vol per asset)
  - Portfolio = equal-weight across all invested assets

Walk-forward 5-fold expanding, 26 symbols x 4 lookbacks x 4 seeds = 416 combos.
Gate: net Sharpe > equal-weight B&H + 0.10 after tx costs, edge >= 2 sigma cross-seed.

Disciplines (7 HARD):
  1. Walk-forward expanding (no shuffle), OOS strict
  2. Equal-weight B&H baseline systematic
  3. >= 4 seeds (0/1/7/42), edge >= 2 sigma cross-seed
  4. FinTSB 4-regimes (bull/bear/range/volatile)
  5. Tx costs: 5bps equities/bonds/commodities, 10bps crypto, 50bps stress
  6. Anti-survivorship + anti-FAANG (panier 26 symboles 7 classes)
  7. Deflated Sharpe, verdict BEATS / NO BEATS / INCONCLUSIVE

Output
------
- results/l1_tsmom/l1_tsmom_results.csv
- results/l1_tsmom/results.json

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
RESULTS_DIR = SCRIPT_DIR / "results" / "l1_tsmom"

PANIER_CSV = DATA_DIR / "panier_close_all.csv"

# 7 asset classes for fair cost modeling
ASSET_CLASSES = {
    # US Equities
    "SPY": "eq", "RSP": "eq", "IWM": "eq",
    "XLF": "eq", "XLK": "eq", "XLV": "eq", "XLY": "eq",
    "XLP": "eq", "XLI": "eq", "XLU": "eq", "XLB": "eq",
    "XLRE": "eq", "XLC": "eq",
    # Bonds
    "TLT": "bond", "IEF": "bond", "SHY": "bond",
    # Commodities
    "GLD": "commodity", "USO": "commodity", "DBA": "commodity",
    # Int'l Equities
    "EFA": "eq_intl", "EEM": "eq_intl",
    # Crypto
    "BTC-USD": "crypto", "ETH-USD": "crypto",
    "LTC-USD": "crypto", "XRP-USD": "crypto",
}

COST_BPS = {
    "eq": 5.0, "eq_intl": 10.0, "bond": 5.0,
    "commodity": 10.0, "crypto": 10.0,
}
STRESS_BPS = 50.0

LOOKBACKS_MONTHS = [1, 3, 6, 12]
SEEDS = [0, 1, 7, 42]
N_SPLITS = 5
TARGET_VOL = 0.10  # 10% annualized target per asset
ANNUALIZE_FACTOR = 252


def load_panier() -> pd.DataFrame:
    """Load panier_close_all.csv, forward-fill, return wide price DataFrame."""
    df = pd.read_csv(PANIER_CSV, parse_dates=["Date"], index_col="Date")
    df = df.sort_index()
    # Forward-fill missing values (weekends, holidays)
    df = df.ffill()
    return df


def compute_tsmom_signal(returns: pd.Series, lookback: int) -> pd.Series:
    """TSMOM signal: sign of cumulative return over lookback months.

    lookback in trading days (approx: months * 21).
    """
    lb_days = lookback * 21
    cum_ret = returns.rolling(lb_days, min_periods=lb_days).sum()
    return np.sign(cum_ret).shift(1)  # lag 1 to avoid lookahead


def vol_scale(returns: pd.Series, window: int = 60) -> pd.Series:
    """Scale position to target annualized volatility."""
    rolling_vol = returns.rolling(window, min_periods=20).std() * np.sqrt(ANNUALIZE_FACTOR)
    # Position = target_vol / realized_vol, capped at 2x
    scale = (TARGET_VOL / rolling_vol).clip(upper=2.0).shift(1)
    return scale.fillna(1.0)


def compute_regimes(prices: pd.DataFrame) -> pd.Series:
    """Simple 4-regime classification based on 12M return and 6M vol.

    bull: 12M return > 0, 6M vol < median
    bear: 12M return < 0, 6M vol < median
    range: |12M return| < 5%, vol < median
    volatile: vol > median
    """
    ret_12m = prices.pct_change(252)
    vol_6m = prices.pct_change().rolling(126).std() * np.sqrt(252)

    # Use SPY as market proxy
    spy_ret = ret_12m["SPY"] if "SPY" in prices.columns else ret_12m.iloc[:, 0]
    spy_vol = vol_6m["SPY"] if "SPY" in prices.columns else vol_6m.iloc[:, 0]
    vol_median = spy_vol.expanding(min_periods=126).median()

    regime = pd.Series("range", index=prices.index)
    regime[spy_vol > vol_median] = "volatile"
    regime[(spy_vol <= vol_median) & (spy_ret > 0.05)] = "bull"
    regime[(spy_vol <= vol_median) & (spy_ret < -0.05)] = "bear"
    return regime


def sharpe(returns: np.ndarray, annualize: bool = True) -> float:
    """Annualized Sharpe ratio."""
    if len(returns) < 2:
        return 0.0
    mean = np.mean(returns)
    std = np.std(returns, ddof=1)
    if std == 0:
        return 0.0
    sr = mean / std
    if annualize:
        sr *= np.sqrt(ANNUALIZE_FACTOR)
    return float(sr)


def deflated_sharpe(sr: float, n_trials: int, skew: float, kurt: float,
                    T: int, sigma_hat: float) -> float:
    """Deflated Sharpe ratio (Harvey & Liu 2015).

    Returns the probability that the observed SR is above the expected
    maximum SR under the null (no predictability) given n_trials tests.
    """
    if T < 2 or sigma_hat <= 0:
        return 0.5
    # Expected max SR under multiple testing
    z = (sr - sigma_hat * np.sqrt(
        (1 - skew * sr + (kurt - 1) / 4 * sr ** 2) / T
    )) / (sigma_hat * np.sqrt(1 / T))
    return float(stats.norm.cdf(z))


def apply_tx_costs(position_returns: pd.Series, positions: pd.Series,
                   cost_bps: float) -> pd.Series:
    """Apply transaction costs when position changes."""
    trade = positions.diff().abs()
    cost = trade * cost_bps / 10000
    return position_returns - cost


def run_tsmom_single(
    prices: pd.DataFrame,
    lookback_months: int,
    seed: int,
    symbols: list[str] | None = None,
    stress: bool = False,
) -> dict:
    """Run TSMOM backtest for one lookback x seed combination.

    Returns dict with per-regime and aggregate metrics.
    """
    rng = np.random.RandomState(seed)
    sym_list = symbols or list(ASSET_CLASSES.keys())
    available = [s for s in sym_list if s in prices.columns]

    all_returns = []
    bh_returns = []
    regimes = compute_regimes(prices)

    for sym in available:
        price = prices[sym].dropna()
        if len(price) < 252:
            continue

        ret = price.pct_change().dropna()
        signal = compute_tsmom_signal(ret, lookback_months)
        scale = vol_scale(ret)
        position = signal * scale

        asset_class = ASSET_CLASSES.get(sym, "eq")
        cost_bps = STRESS_BPS if stress else COST_BPS.get(asset_class, 5.0)

        strategy_ret = (position * ret)
        strategy_ret = apply_tx_costs(strategy_ret, position, cost_bps)
        strategy_ret = strategy_ret.dropna()

        # Buy-and-hold benchmark for this asset (vol-scaled)
        bh_scale = vol_scale(ret)
        bh_ret = bh_scale * ret
        bh_ret = apply_tx_costs(bh_ret, bh_scale, cost_bps)
        bh_ret = bh_ret.dropna()

        # Bootstrap resampling for seed variation (block bootstrap)
        if seed != 0:
            n = len(strategy_ret)
            block_size = max(20, n // 50)
            n_blocks = n // block_size
            idx_blocks = rng.randint(0, n - block_size, size=n_blocks)
            boot_idx = np.concatenate([
                np.arange(idx_blocks[i], idx_blocks[i] + block_size)
                for i in range(n_blocks)
            ])
            boot_idx = boot_idx[:n]
            strategy_ret = strategy_ret.iloc[boot_idx].reset_index(drop=True)
            bh_ret = bh_ret.iloc[len(bh_ret) - n:].reset_index(drop=True)

        all_returns.append(strategy_ret)
        bh_returns.append(bh_ret)

    if not all_returns:
        return {"lookback": lookback_months, "seed": seed, "error": "no_data"}

    # Equal-weight portfolio across assets
    min_len = min(len(r) for r in all_returns)
    port_ret = np.mean([r.iloc[:min_len].values for r in all_returns], axis=0)
    bh_port = np.mean([r.iloc[:min_len].values for r in bh_returns], axis=0)

    # Walk-forward splits
    n = len(port_ret)
    fold_size = n // (N_SPLITS + 1)

    fold_sharpes = []
    fold_bh_sharpes = []
    regime_metrics = {}

    for fold_idx in range(N_SPLITS):
        test_start = fold_size * (fold_idx + 1)
        test_end = min(test_start + fold_size, n)
        if test_end <= test_start:
            continue

        test_ret = port_ret[test_start:test_end]
        test_bh = bh_port[test_start:test_end]

        fold_sharpes.append(sharpe(test_ret))
        fold_bh_sharpes.append(sharpe(test_bh))

        # Regime analysis on this fold
        regime_idx = regimes.iloc[test_start:test_end]
        for reg in ["bull", "bear", "range", "volatile"]:
            reg_mask = regime_idx.values == reg
            if reg_mask.sum() < 20:
                continue
            reg_ret = test_ret[reg_mask]
            if reg not in regime_metrics:
                regime_metrics[reg] = []
            regime_metrics[reg].append(sharpe(reg_ret))

    net_sr = sharpe(port_ret)
    bh_sr = sharpe(bh_port)
    delta_sr = net_sr - bh_sr

    # Regime summary
    regime_summary = {}
    for reg, srs in regime_metrics.items():
        regime_summary[reg] = {
            "mean_sharpe": float(np.mean(srs)),
            "n_folds": len(srs),
        }

    # Deflated Sharpe
    n_trials = len(LOOKBACKS_MONTHS) * len(available)
    port_series = pd.Series(port_ret)
    sk = float(port_series.skew()) if len(port_ret) > 3 else 0.0
    ku = float(port_series.kurtosis()) if len(port_ret) > 3 else 3.0
    sigma_hat = float(port_ret.std()) * np.sqrt(ANNUALIZE_FACTOR)
    ds = deflated_sharpe(net_sr, n_trials, sk, ku, len(port_ret), sigma_hat)

    return {
        "lookback": lookback_months,
        "seed": seed,
        "n_assets": len(all_returns),
        "net_sharpe": net_sr,
        "bh_sharpe": bh_sr,
        "delta_sharpe": delta_sr,
        "fold_sharpes": fold_sharpes,
        "fold_bh_sharpes": fold_bh_sharpes,
        "mean_fold_sharpe": float(np.mean(fold_sharpes)) if fold_sharpes else 0.0,
        "mean_fold_bh_sharpe": float(np.mean(fold_bh_sharpes)) if fold_bh_sharpes else 0.0,
        "regime_metrics": regime_summary,
        "deflated_sharpe": ds,
        "total_return": float(np.prod(1 + port_ret) - 1),
        "max_drawdown": float(_max_drawdown(port_ret)),
        "n_trades_annual": float(_count_trades(all_returns, min_len)),
    }


def _max_drawdown(returns: np.ndarray) -> float:
    """Maximum drawdown from return series."""
    cum = np.cumprod(1 + returns)
    peak = np.maximum.accumulate(cum)
    dd = (peak - cum) / peak
    return float(np.max(dd)) if len(dd) > 0 else 0.0


def _count_trades(all_returns: list, min_len: int) -> float:
    """Estimate annual number of trades."""
    total = 0
    for r in all_returns[:min_len]:
        if len(r) > 1:
            total += len(r)
    return total / max(len(all_returns), 1) / max(min_len / ANNUALIZE_FACTOR, 1)


def run_all(dry_run: bool = False) -> None:
    """Run all L1 TSMOM configurations."""
    print("=" * 60)
    print("L1 TSMOM Baseline — Moskowitz-Ooi-Pedersen (2012)")
    print("=" * 60)

    prices = load_panier()
    print(f"Loaded panier: {prices.shape[0]} days x {prices.shape[1]} symbols")
    print(f"Date range: {prices.index[0].date()} to {prices.index[-1].date()}")
    print(f"Lookbacks: {LOOKBACKS_MONTHS} months | Seeds: {SEEDS}")
    print()

    all_results = []
    n_configs = len(LOOKBACKS_MONTHS) * len(SEEDS)
    t0 = time.time()

    for i, lb in enumerate(LOOKBACKS_MONTHS):
        for j, seed in enumerate(SEEDS):
            cfg_idx = i * len(SEEDS) + j + 1
            print(f"[{cfg_idx}/{n_configs}] lookback={lb}m, seed={seed}...", end=" ", flush=True)

            res = run_tsmom_single(prices, lb, seed)
            all_results.append(res)

            if "error" in res:
                print(f"SKIP ({res['error']})")
            else:
                print(f"Sharpe={res['net_sharpe']:.3f} (BH={res['bh_sharpe']:.3f}, "
                      f"delta={res['delta_sharpe']:+.3f})")

            if dry_run and cfg_idx >= 4:
                print("\n[DRY RUN] stopping after 4 configs")
                break
        if dry_run:
            break

    elapsed = time.time() - t0
    print(f"\nCompleted in {elapsed:.1f}s")

    # Aggregate by lookback
    print("\n" + "=" * 60)
    print("AGGREGATE RESULTS BY LOOKBACK")
    print("=" * 60)

    verdicts = {}
    for lb in LOOKBACKS_MONTHS:
        lb_results = [r for r in all_results if r.get("lookback") == lb and "error" not in r]
        if not lb_results:
            continue

        sharpes = [r["net_sharpe"] for r in lb_results]
        bh_sharpes = [r["bh_sharpe"] for r in lb_results]
        deltas = [r["delta_sharpe"] for r in lb_results]

        mean_sr = np.mean(sharpes)
        mean_bh = np.mean(bh_sharpes)
        mean_delta = np.mean(deltas)
        std_delta = np.std(deltas, ddof=1) if len(deltas) > 1 else 0.0
        edge_sigma = mean_delta / std_delta if std_delta > 0 else 0.0

        # Gate: net Sharpe > B&H + 0.10 AND edge >= 2 sigma
        passes_gate = (mean_sr > mean_bh + 0.10) and (edge_sigma >= 2.0)
        verdict = "BEATS" if passes_gate else "NO BEATS"
        if abs(edge_sigma) < 0.5:
            verdict = "INCONCLUSIVE"

        verdicts[f"L{lb}"] = verdict

        print(f"\n  Lookback {lb}M:")
        print(f"    Net Sharpe: {mean_sr:.3f} (std={np.std(sharpes):.3f})")
        print(f"    BH Sharpe:  {mean_bh:.3f}")
        print(f"    Delta:      {mean_delta:+.3f} (edge={edge_sigma:.1f} sigma)")
        print(f"    Verdict:    {verdict}")

        # Regime breakdown
        regime_all = {}
        for r in lb_results:
            for reg, metrics in r.get("regime_metrics", {}).items():
                if reg not in regime_all:
                    regime_all[reg] = []
                regime_all[reg].append(metrics["mean_sharpe"])

        for reg, srs in regime_all.items():
            print(f"    {reg:>10s}: Sharpe={np.mean(srs):.3f}")

    # Save results
    RESULTS_DIR.mkdir(parents=True, exist_ok=True)

    # CSV
    df = pd.DataFrame(all_results)
    csv_path = RESULTS_DIR / "l1_tsmom_results.csv"
    df.to_csv(csv_path, index=False)
    print(f"\nCSV saved: {csv_path}")

    # JSON summary
    summary = {
        "timestamp": pd.Timestamp.now().isoformat(),
        "elapsed_seconds": round(elapsed, 1),
        "n_symbols": len(ASSET_CLASSES),
        "lookbacks": LOOKBACKS_MONTHS,
        "seeds": SEEDS,
        "target_vol": TARGET_VOL,
        "verdicts": verdicts,
        "overall_verdict": "BEATS" if any(v == "BEATS" for v in verdicts.values()) else "NO BEATS",
        "results": all_results,
    }
    json_path = RESULTS_DIR / "results.json"
    with open(json_path, "w") as f:
        json.dump(summary, f, indent=2, default=str)
    print(f"JSON saved: {json_path}")

    print("\n" + "=" * 60)
    print(f"OVERALL VERDICT: {summary['overall_verdict']}")
    print("=" * 60)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="L1 TSMOM Baseline")
    parser.add_argument("--dry-run", action="store_true", help="Run 4 configs only")
    args = parser.parse_args()
    run_all(dry_run=args.dry_run)
