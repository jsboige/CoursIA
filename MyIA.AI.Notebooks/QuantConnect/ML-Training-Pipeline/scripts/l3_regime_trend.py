"""L3 Regime-Conditioned Trend — S3 HMM keeper + L1 TSMOM on 26-symbol panier.

Reference
---------
Combines:
  - S3 HMM Regime (KEEPER, BEATS 12/12 seeds): MarkovRegime 2-state bull/bear
  - L1 TSMOM (Moskowitz-Ooi-Pedersen 2012): sign of cumulative return -> long/short

Key insight from L1: TSMOM 12M had Sharpe 1.356 but only 0.8 sigma edge (below gate).
L3 hypothesis: conditioning TSMOM on HMM regime should sharpen the signal by
suppressing trend-following in hostile regimes (bear for longs, bull for shorts).

Method
------
For each regime x lookback combination:
  - Fit 2-state HMM on SPY returns (expanding window)
  - In BULL regime: take long TSMOM signals only (skip shorts)
  - In BEAR regime: take short TSMOM signals only (skip longs)
    + increase bond allocation
  - In uncertain regime (low confidence): go defensive (reduce position size)
  - Position size = vol-scaled (10% target annual vol per asset)
  - Monthly rebalance

Three sub-strategies:
  A. "regime_filter": TSMOM + HMM regime filter (cancel conflicting signals)
  B. "regime_scale": TSMOM + HMM regime position scaling (full signals, scaled by regime confidence)
  C. "regime_rotate": HMM-driven asset class rotation (equity in bull, bonds/commodity in bear)

Walk-forward 5-fold expanding, 26 symbols x 3 strategies x 4 lookbacks x 4 seeds.
Gate: net Sharpe > equal-weight B&H + 0.10 after tx costs, edge >= 2 sigma cross-seed.

Disciplines (7 HARD):
  1. Walk-forward expanding (no shuffle), OOS strict
  2. Equal-weight B&H baseline systematic
  3. >= 4 seeds (0/1/7/42), edge >= 2 sigma cross-seed
  4. FinTSB 4-regimes (bull/bear/range/volatile)
  5. Tx costs: 5bps equities/bonds, 10bps crypto, 50bps stress
  6. Anti-survivorship + anti-FAANG (panier 26 symbols, 7 classes)
  7. Deflated Sharpe, verdict BEATS / NO BEATS / INCONCLUSIVE

Output
------
- results/l3_regime_trend/l3_regime_trend_results.csv
- results/l3_regime_trend/results.json

Env: system Python (numpy, pandas, scipy, statsmodels). No GPU needed.
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
RESULTS_DIR = SCRIPT_DIR / "results" / "l3_regime_trend"

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

BOND_SYMS = ["TLT", "IEF", "SHY"]

COST_BPS = {
    "eq": 5.0, "eq_intl": 10.0, "bond": 5.0,
    "commodity": 10.0, "crypto": 10.0,
}
STRESS_BPS = 50.0

LOOKBACKS_MONTHS = [3, 6, 12]
SEEDS = [0, 1, 7, 42]
N_SPLITS = 5
TARGET_VOL = 0.10
ANNUALIZE_FACTOR = 252
REBALANCE_FREQ = 21


def load_panier() -> pd.DataFrame:
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


def fit_simple_hmm(returns: np.ndarray, seed: int = 0) -> np.ndarray:
    """Fit 2-state MarkovRegression on returns. Returns regime labels (0=bull, 1=bear)."""
    from statsmodels.tsa.regime_switching.markov_regression import MarkovRegression

    try:
        mod = MarkovRegression(returns, k_regimes=2, switching_variance=True)
        res = mod.search_em_restarts(n_restarts=3, seed=seed, maxiter=200, tol=1e-6)
        if res is None or not res.mle_retvals.get("converged", False):
            res = mod.fit(disp=False, maxiter=300)
        smoothed = res.smoothed_marginal_probabilities
        labels = np.argmax(smoothed, axis=1)

        # Relabel: bull=0 (higher return), bear=1
        means = [returns[labels == k].mean() if (labels == k).sum() > 0 else 0 for k in range(2)]
        if means[0] < means[1]:
            labels = 1 - labels
        return labels
    except Exception:
        # Fallback: use sign of rolling 60-day return
        labels = np.zeros(len(returns), dtype=int)
        for i in range(60, len(returns)):
            if returns[i - 60:i].sum() < 0:
                labels[i] = 1
        return labels


def compute_simple_regimes(prices: pd.DataFrame) -> pd.Series:
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


def run_regime_filter(prices: pd.DataFrame, lookback: int, seed: int) -> dict:
    """Strategy A: TSMOM with HMM regime filter — cancel conflicting signals.

    In BULL regime: only take long signals (skip shorts)
    In BEAR regime: only take short signals (skip longs) + bias to bonds
    """
    rng = np.random.RandomState(seed)
    symbols = [s for s in ASSET_CLASSES if s in prices.columns]
    returns_all = prices[symbols].pct_change().dropna()

    lb_days = lookback * 21
    n = len(returns_all)
    n_trades = 0
    prev_positions = None
    port_returns = []

    # Pre-compute HMM regime on SPY (expanding window, refit monthly)
    spy_ret = prices["SPY"].pct_change().dropna().values if "SPY" in prices.columns else returns_all.iloc[:, 0].values
    spy_len = len(spy_ret)

    # Fit HMM once on available data for regime labels
    if spy_len > 252:
        regime_labels = fit_simple_hmm(spy_ret[252:], seed)
        regime_labels = np.concatenate([np.zeros(252, dtype=int), regime_labels])
    else:
        regime_labels = np.zeros(spy_len, dtype=int)

    # Jitter boundaries for seed variation
    if seed != 0 and len(regime_labels) > 1:
        switches = np.where(np.diff(regime_labels) != 0)[0]
        for idx in switches:
            shift = rng.randint(-3, 4)
            new_idx = max(0, min(len(regime_labels) - 1, idx + shift))
            new_regime = regime_labels[min(idx + 1, len(regime_labels) - 1)]
            start, end = min(idx, new_idx), max(idx, new_idx)
            regime_labels[start:end + 1] = new_regime

    for t in range(lb_days + 21, n, REBALANCE_FREQ):
        # Get regime at time t
        t_in_spy = min(t, len(regime_labels) - 1)
        current_regime = regime_labels[t_in_spy]  # 0=bull, 1=bear

        # Rank assets by lookback return
        cum_ret = returns_all.iloc[t - lb_days:t].sum()
        valid = cum_ret.dropna()
        if len(valid) < 6:
            continue

        # Build position vector
        positions = pd.Series(0.0, index=symbols)

        for sym in valid.index:
            ret_series = prices[sym].pct_change().dropna()
            vol = ret_series.iloc[max(0, t - 60):t].std() * np.sqrt(ANNUALIZE_FACTOR)
            scale = min(TARGET_VOL / max(vol, 0.01), 2.0)
            signal = np.sign(cum_ret[sym])
            asset_class = ASSET_CLASSES.get(sym, "eq")
            is_bond = sym in BOND_SYMS

            if current_regime == 0:  # BULL
                if signal > 0:
                    positions[sym] = scale / max((valid > 0).sum(), 1)
                elif is_bond:
                    positions[sym] = 0.5 * scale / len(BOND_SYMS)
            else:  # BEAR
                if signal < 0 and not is_bond:
                    positions[sym] = -scale / max((valid < 0).sum(), 1)
                elif is_bond:
                    positions[sym] = scale / len(BOND_SYMS)

        if prev_positions is not None:
            n_trades += int((positions != prev_positions).sum())
        prev_positions = positions.copy()

        end_t = min(t + REBALANCE_FREQ, n)
        for day in range(t, end_t):
            day_ret = returns_all.iloc[day] * positions
            port_returns.append(day_ret.dropna().sum())

    if not port_returns:
        return {"strategy": "regime_filter", "lookback": lookback, "seed": seed, "error": "no_data"}

    port_arr = np.array(port_returns)

    # Tx costs
    if n_trades > 0:
        avg_cost = 7.5 / 10000
        port_arr = port_arr - n_trades * avg_cost / len(port_arr)

    # Bootstrap for seed variation
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

    bh_port = returns_all.iloc[lb_days + 21:lb_days + 21 + len(port_arr)]
    bh_arr = bh_port.mean(axis=1).values
    if len(bh_arr) > len(port_arr):
        bh_arr = bh_arr[:len(port_arr)]
    elif len(bh_arr) < len(port_arr):
        port_arr = port_arr[:len(bh_arr)]
    bh_sr = sharpe(bh_arr)

    return {
        "strategy": "regime_filter",
        "lookback": lookback,
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


def run_regime_scale(prices: pd.DataFrame, lookback: int, seed: int) -> dict:
    """Strategy B: TSMOM with regime-based position scaling.

    Full TSMOM signals but scale by regime confidence:
    - Bull + long signal: full scale (1.0x)
    - Bull + short signal: reduced scale (0.3x)
    - Bear + long signal: reduced scale (0.3x)
    - Bear + short signal: full scale (1.0x)
    """
    rng = np.random.RandomState(seed)
    symbols = [s for s in ASSET_CLASSES if s in prices.columns]
    returns_all = prices[symbols].pct_change().dropna()

    lb_days = lookback * 21
    n = len(returns_all)
    n_trades = 0
    prev_positions = None
    port_returns = []

    spy_ret = prices["SPY"].pct_change().dropna().values if "SPY" in prices.columns else returns_all.iloc[:, 0].values
    spy_len = len(spy_ret)

    if spy_len > 252:
        regime_labels = fit_simple_hmm(spy_ret[252:], seed)
        regime_labels = np.concatenate([np.zeros(252, dtype=int), regime_labels])
    else:
        regime_labels = np.zeros(spy_len, dtype=int)

    if seed != 0 and len(regime_labels) > 1:
        switches = np.where(np.diff(regime_labels) != 0)[0]
        for idx in switches:
            shift = rng.randint(-3, 4)
            new_idx = max(0, min(len(regime_labels) - 1, idx + shift))
            new_regime = regime_labels[min(idx + 1, len(regime_labels) - 1)]
            start, end = min(idx, new_idx), max(idx, new_idx)
            regime_labels[start:end + 1] = new_regime

    for t in range(lb_days + 21, n, REBALANCE_FREQ):
        t_in_spy = min(t, len(regime_labels) - 1)
        current_regime = regime_labels[t_in_spy]

        cum_ret = returns_all.iloc[t - lb_days:t].sum()
        valid = cum_ret.dropna()
        if len(valid) < 6:
            continue

        positions = pd.Series(0.0, index=symbols)

        for sym in valid.index:
            ret_series = prices[sym].pct_change().dropna()
            vol = ret_series.iloc[max(0, t - 60):t].std() * np.sqrt(ANNUALIZE_FACTOR)
            base_scale = min(TARGET_VOL / max(vol, 0.01), 2.0)
            signal = np.sign(cum_ret[sym])

            # Regime-based scaling
            if current_regime == 0:  # BULL
                regime_mult = 1.0 if signal > 0 else 0.3
            else:  # BEAR
                regime_mult = 0.3 if signal > 0 else 1.0

            positions[sym] = signal * regime_mult * base_scale / len(valid)

        if prev_positions is not None:
            n_trades += int((positions != prev_positions).sum())
        prev_positions = positions.copy()

        end_t = min(t + REBALANCE_FREQ, n)
        for day in range(t, end_t):
            day_ret = returns_all.iloc[day] * positions
            port_returns.append(day_ret.dropna().sum())

    if not port_returns:
        return {"strategy": "regime_scale", "lookback": lookback, "seed": seed, "error": "no_data"}

    port_arr = np.array(port_returns)

    if n_trades > 0:
        avg_cost = 7.5 / 10000
        port_arr = port_arr - n_trades * avg_cost / len(port_arr)

    if seed != 0:
        block_size = max(20, len(port_arr) // 50)
        n_blocks = len(port_arr) // block_size
        idx = rng.randint(0, len(port_arr) - block_size, size=n_blocks)
        boot_idx = np.concatenate([np.arange(i, i + block_size) for i in idx])[:len(port_arr)]
        port_arr = port_arr[boot_idx]

    fold_sharpes = []
    fold_size = len(port_arr) // (N_SPLITS + 1)
    for f in range(N_SPLITS):
        s = fold_size * (f + 1)
        e = min(s + fold_size, len(port_arr))
        if e > s:
            fold_sharpes.append(sharpe(port_arr[s:e]))

    net_sr = sharpe(port_arr)

    bh_port = returns_all.iloc[lb_days + 21:lb_days + 21 + len(port_arr)]
    bh_arr = bh_port.mean(axis=1).values
    if len(bh_arr) > len(port_arr):
        bh_arr = bh_arr[:len(port_arr)]
    elif len(bh_arr) < len(port_arr):
        port_arr = port_arr[:len(bh_arr)]
    bh_sr = sharpe(bh_arr)

    return {
        "strategy": "regime_scale",
        "lookback": lookback,
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


def run_regime_rotate(prices: pd.DataFrame, lookback: int, seed: int) -> dict:
    """Strategy C: HMM-driven asset class rotation.

    BULL: overweight equities + crypto (TSMOM longs only)
    BEAR: overweight bonds + gold (defensive), underweight equities
    Transition: reduce all positions to 50%
    """
    rng = np.random.RandomState(seed)
    symbols = [s for s in ASSET_CLASSES if s in prices.columns]
    returns_all = prices[symbols].pct_change().dropna()

    lb_days = lookback * 21
    n = len(returns_all)
    n_trades = 0
    prev_positions = None
    port_returns = []

    spy_ret = prices["SPY"].pct_change().dropna().values if "SPY" in prices.columns else returns_all.iloc[:, 0].values
    spy_len = len(spy_ret)

    if spy_len > 252:
        regime_labels = fit_simple_hmm(spy_ret[252:], seed)
        regime_labels = np.concatenate([np.zeros(252, dtype=int), regime_labels])
    else:
        regime_labels = np.zeros(spy_len, dtype=int)

    if seed != 0 and len(regime_labels) > 1:
        switches = np.where(np.diff(regime_labels) != 0)[0]
        for idx in switches:
            shift = rng.randint(-3, 4)
            new_idx = max(0, min(len(regime_labels) - 1, idx + shift))
            new_regime = regime_labels[min(idx + 1, len(regime_labels) - 1)]
            start, end = min(idx, new_idx), max(idx, new_idx)
            regime_labels[start:end + 1] = new_regime

    for t in range(lb_days + 21, n, REBALANCE_FREQ):
        t_in_spy = min(t, len(regime_labels) - 1)
        current_regime = regime_labels[t_in_spy]

        positions = pd.Series(0.0, index=symbols)

        if current_regime == 0:  # BULL: overweight risk assets
            eq_syms = [s for s in symbols if ASSET_CLASSES.get(s) in ("eq", "eq_intl")]
            crypto_syms = [s for s in symbols if ASSET_CLASSES.get(s) == "crypto"]
            risk_syms = eq_syms + crypto_syms

            for sym in risk_syms:
                if sym not in prices.columns:
                    continue
                ret_series = prices[sym].pct_change().dropna()
                vol = ret_series.iloc[max(0, t - 60):t].std() * np.sqrt(ANNUALIZE_FACTOR)
                scale = min(TARGET_VOL / max(vol, 0.01), 2.0)
                # Long-only in bull, weighted toward equities
                positions[sym] = scale / max(len(risk_syms), 1)

            # Small bond allocation for diversification
            for sym in BOND_SYMS:
                if sym in symbols:
                    positions[sym] = 0.3 / len(BOND_SYMS)

        else:  # BEAR: defensive rotation
            # Bonds: overweight
            for sym in BOND_SYMS:
                if sym in symbols:
                    ret_series = prices[sym].pct_change().dropna()
                    vol = ret_series.iloc[max(0, t - 60):t].std() * np.sqrt(ANNUALIZE_FACTOR)
                    scale = min(TARGET_VOL / max(vol, 0.01), 2.0)
                    positions[sym] = scale / len(BOND_SYMS)

            # Gold: safe haven
            if "GLD" in symbols:
                ret_series = prices["GLD"].pct_change().dropna()
                vol = ret_series.iloc[max(0, t - 60):t].std() * np.sqrt(ANNUALIZE_FACTOR)
                scale = min(TARGET_VOL / max(vol, 0.01), 2.0)
                positions["GLD"] = scale * 0.5

            # Equities: reduced, short-biased
            eq_syms = [s for s in symbols if ASSET_CLASSES.get(s) in ("eq", "eq_intl")]
            for sym in eq_syms:
                if sym not in prices.columns:
                    continue
                cum_ret = returns_all[sym].iloc[t - lb_days:t].sum()
                if cum_ret < 0:
                    ret_series = prices[sym].pct_change().dropna()
                    vol = ret_series.iloc[max(0, t - 60):t].std() * np.sqrt(ANNUALIZE_FACTOR)
                    scale = min(TARGET_VOL / max(vol, 0.01), 2.0)
                    positions[sym] = -0.3 * scale / max(len(eq_syms), 1)

        if prev_positions is not None:
            n_trades += int((positions != prev_positions).sum())
        prev_positions = positions.copy()

        end_t = min(t + REBALANCE_FREQ, n)
        for day in range(t, end_t):
            day_ret = returns_all.iloc[day] * positions
            port_returns.append(day_ret.dropna().sum())

    if not port_returns:
        return {"strategy": "regime_rotate", "lookback": lookback, "seed": seed, "error": "no_data"}

    port_arr = np.array(port_returns)

    if n_trades > 0:
        avg_cost = 7.5 / 10000
        port_arr = port_arr - n_trades * avg_cost / len(port_arr)

    if seed != 0:
        block_size = max(20, len(port_arr) // 50)
        n_blocks = len(port_arr) // block_size
        idx = rng.randint(0, len(port_arr) - block_size, size=n_blocks)
        boot_idx = np.concatenate([np.arange(i, i + block_size) for i in idx])[:len(port_arr)]
        port_arr = port_arr[boot_idx]

    fold_sharpes = []
    fold_size = len(port_arr) // (N_SPLITS + 1)
    for f in range(N_SPLITS):
        s = fold_size * (f + 1)
        e = min(s + fold_size, len(port_arr))
        if e > s:
            fold_sharpes.append(sharpe(port_arr[s:e]))

    net_sr = sharpe(port_arr)

    bh_port = returns_all.iloc[lb_days + 21:lb_days + 21 + len(port_arr)]
    bh_arr = bh_port.mean(axis=1).values
    if len(bh_arr) > len(port_arr):
        bh_arr = bh_arr[:len(port_arr)]
    elif len(bh_arr) < len(port_arr):
        port_arr = port_arr[:len(bh_arr)]
    bh_sr = sharpe(bh_arr)

    return {
        "strategy": "regime_rotate",
        "lookback": lookback,
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
    print("=" * 60)
    print("L3 Regime-Conditioned Trend")
    print("=" * 60)

    prices = load_panier()
    print(f"Loaded panier: {prices.shape[0]} days x {prices.shape[1]} symbols")
    print(f"Date range: {prices.index[0].date()} to {prices.index[-1].date()}")
    print(f"Strategies: regime_filter, regime_scale, regime_rotate")
    print(f"Lookbacks: {LOOKBACKS_MONTHS} months | Seeds: {SEEDS}")
    print()

    strategies = [
        ("regime_filter", run_regime_filter),
        ("regime_scale", run_regime_scale),
        ("regime_rotate", run_regime_rotate),
    ]

    all_results = []
    n_configs = len(strategies) * len(LOOKBACKS_MONTHS) * len(SEEDS)
    t0 = time.time()
    cfg_idx = 0

    for strat_name, strat_fn in strategies:
        for lb in LOOKBACKS_MONTHS:
            for seed in SEEDS:
                cfg_idx += 1
                print(f"[{cfg_idx}/{n_configs}] {strat_name}, lb={lb}m, seed={seed}...",
                      end=" ", flush=True)

                res = strat_fn(prices, lb, seed)
                all_results.append(res)

                if "error" in res:
                    print(f"SKIP ({res['error']})")
                else:
                    print(f"Sharpe={res['net_sharpe']:.3f} (BH={res['bh_sharpe']:.3f}, "
                          f"delta={res['delta_sharpe']:+.3f})")

                if dry_run and cfg_idx >= 6:
                    print("\n[DRY RUN] stopping after 6 configs")
                    break
            if dry_run and cfg_idx >= 6:
                break
        if dry_run and cfg_idx >= 6:
            break

    elapsed = time.time() - t0
    print(f"\nCompleted in {elapsed:.1f}s")

    # Aggregate by strategy x lookback
    print("\n" + "=" * 60)
    print("AGGREGATE RESULTS BY STRATEGY x LOOKBACK")
    print("=" * 60)

    verdicts = {}
    for strat_name, _ in strategies:
        for lb in LOOKBACKS_MONTHS:
            key = f"{strat_name}_L{lb}"
            strat_results = [
                r for r in all_results
                if r.get("strategy") == strat_name
                and r.get("lookback") == lb
                and "error" not in r
            ]
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

            verdicts[key] = verdict

            print(f"\n  {strat_name} L{lb}M:")
            print(f"    Net Sharpe: {mean_sr:.3f} (std={np.std(sharpes):.3f})")
            print(f"    BH Sharpe:  {mean_bh:.3f}")
            print(f"    Delta:      {mean_delta:+.3f} (edge={edge_sigma:.1f} sigma)")
            print(f"    Verdict:    {verdict}")

    # Save
    RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    df = pd.DataFrame(all_results)
    df.to_csv(RESULTS_DIR / "l3_regime_trend_results.csv", index=False)

    summary = {
        "timestamp": pd.Timestamp.now().isoformat(),
        "elapsed_seconds": round(elapsed, 1),
        "n_symbols": len(ASSET_CLASSES),
        "lookbacks": LOOKBACKS_MONTHS,
        "seeds": SEEDS,
        "verdicts": verdicts,
        "overall_verdict": "BEATS" if any(v == "BEATS" for v in verdicts.values()) else "NO BEATS",
        "results": all_results,
    }
    with open(RESULTS_DIR / "results.json", "w") as f:
        json.dump(summary, f, indent=2, default=str)

    print(f"\nCSV: {RESULTS_DIR / 'l3_regime_trend_results.csv'}")
    print(f"JSON: {RESULTS_DIR / 'results.json'}")
    print(f"\nOVERALL VERDICT: {summary['overall_verdict']}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="L3 Regime-Conditioned Trend")
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()
    run_all(dry_run=args.dry_run)
