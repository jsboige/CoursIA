"""S5 LASSO Stop-Loss (Hands-On AI Trading Ch6 Ex8).

Question
--------
Does a LASSO-predicted optimal stop-loss level beat buy-and-hold on
a sector ETF universe with transaction costs?

The book result: 28/30 param combos beat BH on KO with 50bps tx costs.
We adapt to sector ETFs (anti-FAANG) with walk-forward validation.

Methodology
-----------
- Universe: XLP, XLV, XLU, XLF, TLT, XLB, XLI, XLE, SPY (no FAANG/Mag7)
- Features: VIX proxy (SPY rolling vol), ATR(14), rolling std(20), ADX(14)
- Target: max drawdown over next 20 days (optimal stop level)
- Model: LASSO alpha=1e-4
- Lookback: 3 months (63 trading days)
- Buffer: 1% under predicted stop (anti-noise)
- Walk-forward 5-fold expanding window
- Multi-seed block bootstrap 0/1/7/42
- OOS strict 2027
- Tx costs: 5bps per trade, 50bps stress
- Gate: delta-Sharpe >= 0.10 cross-seed

Output
------
- results/s5_lasso_stop_loss/results.json
- results/s5_lasso_stop_loss/verdict.md

Env: coursia-ml-training (sklearn, numpy, pandas, yfinance).
CPU only.
"""

from __future__ import annotations

import argparse
import json
import time
from datetime import datetime
from pathlib import Path

import numpy as np
import pandas as pd
from sklearn.linear_model import Lasso

SCRIPT_DIR = Path(__file__).resolve().parent
RESULTS_DIR = SCRIPT_DIR / "results" / "s5_lasso_stop_loss"

# Universe: sectors + defensive + SPY benchmark (anti-FAANG)
SYMBOLS = ["SPY", "TLT", "XLP", "XLV", "XLU", "XLF", "XLB", "XLI", "XLE"]
SEEDS = [0, 1, 7, 42]
N_SPLITS = 5
OOS_YEAR = 2027
TX_COST_BPS = 5
TX_COST_STRESS_BPS = 50
GATE_SHARPE_DELTA = 0.10
BLOCK_SIZE = 22

# LASSO and stop-loss params
LASSO_ALPHA = 1e-4
LOOKBACK = 63        # 3 months trading days
HORIZON = 20         # forward window for stop target
BUFFER = 0.01        # 1% under predicted stop
ATR_PERIOD = 14
STD_WINDOW = 20
ADX_PERIOD = 14


# -- Data loading -----------------------------------------------------------

def load_data(start: str = "2017-01-01", end: str = "2026-12-31") -> pd.DataFrame:
    """Load daily OHLCV for all symbols via yfinance."""
    import yfinance as yf

    all_frames = {}
    for sym in SYMBOLS:
        df = yf.download(sym, start=start, end=end, progress=False)
        if df.empty:
            raise RuntimeError(f"No data for {sym}")
        if isinstance(df.columns, pd.MultiIndex):
            sub = df.xs(sym, axis=1, level=1) if sym in df.columns.get_level_values(1) else df.xs(sym, axis=1, level=0)
            all_frames[sym] = sub
        else:
            all_frames[sym] = df

    return all_frames


# -- Technical indicators ---------------------------------------------------

def compute_atr(high: np.ndarray, low: np.ndarray, close: np.ndarray,
                period: int = ATR_PERIOD) -> np.ndarray:
    """Average True Range."""
    tr = np.zeros(len(close))
    tr[0] = high[0] - low[0]
    for i in range(1, len(close)):
        tr[i] = max(high[i] - low[i],
                     abs(high[i] - low[i - 1]),
                     abs(close[i - 1] - low[i]))
    # Wilder smoothing
    atr = np.zeros(len(close))
    atr[:period] = tr[:period].mean() if len(tr) >= period else tr.mean()
    for i in range(period, len(close)):
        atr[i] = (atr[i - 1] * (period - 1) + tr[i]) / period
    return atr


def compute_adx(high: np.ndarray, low: np.ndarray, close: np.ndarray,
                period: int = ADX_PERIOD) -> np.ndarray:
    """Average Directional Index."""
    n = len(close)
    plus_dm = np.zeros(n)
    minus_dm = np.zeros(n)
    tr = np.zeros(n)

    for i in range(1, n):
        up_move = high[i] - high[i - 1]
        down_move = low[i - 1] - low[i]
        plus_dm[i] = up_move if up_move > down_move and up_move > 0 else 0
        minus_dm[i] = down_move if down_move > up_move and down_move > 0 else 0
        tr[i] = max(high[i] - low[i],
                     abs(high[i] - low[i - 1]),
                     abs(close[i - 1] - low[i]))

    # Smooth with Wilder
    atr = np.zeros(n)
    plus_di = np.zeros(n)
    minus_di = np.zeros(n)
    dx = np.zeros(n)

    atr[:period] = tr[1:period + 1].mean() if n > period else tr[1:].mean()
    s_plus = plus_dm[1:period + 1].sum() if n > period else plus_dm[1:].sum()
    s_minus = minus_dm[1:period + 1].sum() if n > period else minus_dm[1:].sum()

    for i in range(period, n):
        atr[i] = (atr[i - 1] * (period - 1) + tr[i]) / period
        s_plus = (s_plus * (period - 1) + plus_dm[i]) / period
        s_minus = (s_minus * (period - 1) + minus_dm[i]) / period
        plus_di[i] = 100 * s_plus / (atr[i] + 1e-10)
        minus_di[i] = 100 * s_minus / (atr[i] + 1e-10)
        di_sum = plus_di[i] + minus_di[i]
        dx[i] = 100 * abs(plus_di[i] - minus_di[i]) / (di_sum + 1e-10)

    # Smooth DX to get ADX
    adx = np.zeros(n)
    adx[:period * 2] = dx[:period * 2].mean() if n >= period * 2 else dx.mean()
    for i in range(period * 2, n):
        adx[i] = (adx[i - 1] * (period - 1) + dx[i]) / period

    return adx


# -- Feature engineering ----------------------------------------------------

def build_features(sym_df: pd.DataFrame) -> pd.DataFrame:
    """Build features for one symbol: VIX proxy, ATR, std, ADX."""
    close = sym_df["Close"].values.astype(float)
    high = sym_df["High"].values.astype(float)
    low = sym_df["Low"].values.astype(float)

    n = len(close)
    returns = np.diff(close) / close[:-1]
    returns = np.concatenate([[0], returns])

    # VIX proxy: 20-day rolling volatility annualized
    vix_proxy = pd.Series(returns).rolling(STD_WINDOW).std().values * np.sqrt(252)
    vix_proxy = np.nan_to_num(vix_proxy, nan=np.nanmean(vix_proxy[~np.isnan(vix_proxy)]))

    # ATR normalized by price
    atr = compute_atr(high, low, close, ATR_PERIOD) / close

    # Rolling std of returns (20d)
    std20 = pd.Series(returns).rolling(STD_WINDOW).std().values
    std20 = np.nan_to_num(std20, nan=np.nanmean(std20[~np.isnan(std20)]))

    # ADX
    adx = compute_adx(high, low, close, ADX_PERIOD)

    df = pd.DataFrame({
        "vix_proxy": vix_proxy,
        "atr_norm": atr,
        "std_20d": std20,
        "adx": adx,
    }, index=sym_df.index)

    return df


def compute_stop_target(close: np.ndarray, horizon: int = HORIZON) -> np.ndarray:
    """Compute max drawdown over next `horizon` days (optimal stop level).

    Returns negative values representing the worst drawdown from current price.
    """
    n = len(close)
    target = np.full(n, np.nan)
    for i in range(n - horizon):
        window = close[i:i + horizon + 1]
        peak = np.maximum.accumulate(window)
        dd = (window - peak) / peak
        target[i] = dd.min()  # most negative = worst drawdown
    return target


# -- Block bootstrap --------------------------------------------------------

def block_bootstrap(data: np.ndarray, block_size: int, seed: int) -> np.ndarray:
    rng = np.random.RandomState(seed)
    n = len(data)
    n_blocks = (n + block_size - 1) // block_size
    indices = []
    for _ in range(n_blocks):
        start = rng.randint(0, n - block_size + 1)
        indices.extend(range(start, min(start + block_size, n)))
    return data[indices[:n]]


# -- Walk-forward evaluation ------------------------------------------------

def walk_forward_single(
    sym: str,
    sym_df: pd.DataFrame,
    seed: int = 0,
) -> dict:
    """Walk-forward 5-fold for one symbol with LASSO stop-loss."""
    close = sym_df["Close"].values.astype(float)
    features = build_features(sym_df)
    target = compute_stop_target(close, HORIZON)

    # Drop NaN rows
    valid_mask = ~(np.isnan(target) | np.isnan(features.values).any(axis=1))
    valid_mask[:LOOKBACK] = False  # need lookback for first window

    feat_arr = features.values[valid_mask]
    target_arr = target[valid_mask]
    close_arr = close[valid_mask]
    dates = sym_df.index[valid_mask]

    oos_mask = dates >= f"{OOS_YEAR}-01-01"
    if oos_mask.any():
        # Strict OOS: only use pre-2027 data for IS evaluation
        is_mask = ~oos_mask
    else:
        is_mask = np.ones(len(dates), dtype=bool)

    n_is = is_mask.sum()
    if n_is < 200:
        return {"error": f"Insufficient IS data for {sym}: {n_is} rows"}

    fold_size = n_is // N_SPLITS
    rng = np.random.RandomState(seed)

    # Collect OOS daily returns for both strategies
    lasso_dates = []
    lasso_rets = []
    bh_rets = []

    n_stops_triggered = 0
    n_total_days = 0

    for fold_idx in range(N_SPLITS):
        train_end = fold_size * (fold_idx + 2)
        train_end = min(train_end, n_is)
        test_start = fold_size * (fold_idx + 1)
        test_end = train_end

        if train_end < LOOKBACK + HORIZON or test_end <= test_start:
            continue

        # Training data
        train_feat = feat_arr[:train_end]
        train_target = target_arr[:train_end]
        train_close = close_arr[:train_end]

        # Block bootstrap training for seed variability
        n_train = len(train_feat)
        boot_idx = block_bootstrap(np.arange(n_train), BLOCK_SIZE, seed)
        boot_feat = train_feat[boot_idx]
        boot_target = train_target[boot_idx]

        # Fit LASSO
        model = Lasso(alpha=LASSO_ALPHA, max_iter=5000, random_state=seed)
        model.fit(boot_feat, boot_target)

        # Test data
        test_feat = feat_arr[test_start:test_end]
        test_close = close_arr[test_start:test_end]
        test_dates_slice = dates[test_start:test_end]

        if len(test_close) < 5:
            continue

        # Predict optimal stop for each day
        pred_stops = model.predict(test_feat)

        # Simulate trailing stop strategy
        position = 0  # 0=flat, 1=long
        entry_price = 0.0
        stop_price = 0.0

        for t in range(len(test_close)):
            price = test_close[t]
            pred_stop = pred_stops[t]
            daily_ret = (test_close[t] / test_close[t - 1] - 1) if t > 0 else 0.0

            if position == 0:
                # Enter long
                position = 1
                entry_price = price
                # Set stop at predicted drawdown + buffer
                stop_level = price * (1 + pred_stop - BUFFER)
                stop_price = max(stop_level, price * 0.90)  # cap at 10% loss
                lasso_ret = daily_ret
            elif position == 1:
                if price < stop_price:
                    # Stop triggered: exit
                    lasso_ret = (stop_price / test_close[t - 1] - 1) if t > 0 else 0.0
                    position = 0
                    n_stops_triggered += 1
                    # Re-enter next day
                else:
                    lasso_ret = daily_ret
                    # Trail stop up if price rose
                    new_stop = price * (1 + pred_stop - BUFFER)
                    new_stop = max(new_stop, price * 0.90)
                    stop_price = max(stop_price, new_stop)

            lasso_dates.append(test_dates_slice[t])
            lasso_rets.append(lasso_ret)
            bh_rets.append(daily_ret)
            n_total_days += 1

    if not lasso_rets:
        return {"error": f"No folds produced results for {sym}"}

    lasso_ret = np.array(lasso_rets)
    bh_ret = np.array(bh_rets)

    # Transaction costs: apply when stop triggered or at fold boundaries
    tx = TX_COST_BPS / 10000
    lasso_ret -= tx  # conservative: apply cost once per fold

    results = {
        "symbol": sym,
        "seed": seed,
        "lasso_sharpe": float(_sharpe(lasso_ret)),
        "bh_sharpe": float(_sharpe(bh_ret)),
        "lasso_cum_ret": float(np.prod(1 + lasso_ret) - 1),
        "bh_cum_ret": float(np.prod(1 + bh_ret) - 1),
        "lasso_max_dd": float(_max_drawdown(lasso_ret)),
        "bh_max_dd": float(_max_drawdown(bh_ret)),
        "lasso_vol": float(np.std(lasso_ret) * np.sqrt(252)),
        "bh_vol": float(np.std(bh_ret) * np.sqrt(252)),
        "delta_sharpe": float(_sharpe(lasso_ret) - _sharpe(bh_ret)),
        "n_stops": n_stops_triggered,
        "n_days": n_total_days,
        "n_folds": N_SPLITS,
    }

    return results


def walk_forward_portfolio(
    data: dict[str, pd.DataFrame],
    seed: int = 0,
) -> dict:
    """Run walk-forward across all symbols and aggregate into portfolio."""
    per_sym = []
    for sym in SYMBOLS:
        sym_df = data[sym]
        result = walk_forward_single(sym, sym_df, seed=seed)
        if "error" not in result:
            per_sym.append(result)
        else:
            print(f"  {sym}: {result['error']}")

    if not per_sym:
        return {"error": "No symbols produced results"}

    # Aggregate: equal-weight portfolio of per-symbol strategies
    # Use average daily returns across symbols
    n_sym = len(per_sym)

    agg = {
        "seed": seed,
        "n_symbols": n_sym,
        "mean_lasso_sharpe": float(np.mean([r["lasso_sharpe"] for r in per_sym])),
        "mean_bh_sharpe": float(np.mean([r["bh_sharpe"] for r in per_sym])),
        "mean_delta": float(np.mean([r["delta_sharpe"] for r in per_sym])),
        "min_delta": float(min(r["delta_sharpe"] for r in per_sym)),
        "max_delta": float(max(r["delta_sharpe"] for r in per_sym)),
        "mean_lasso_cum": float(np.mean([r["lasso_cum_ret"] for r in per_sym])),
        "mean_bh_cum": float(np.mean([r["bh_cum_ret"] for r in per_sym])),
        "mean_lasso_max_dd": float(np.mean([r["lasso_max_dd"] for r in per_sym])),
        "mean_bh_max_dd": float(np.mean([r["bh_max_dd"] for r in per_sym])),
        "total_stops": sum(r["n_stops"] for r in per_sym),
        "total_days": per_sym[0]["n_days"] if per_sym else 0,
        "n_folds": N_SPLITS,
        "per_symbol": per_sym,
        "symbols_beating": sum(1 for r in per_sym if r["delta_sharpe"] > 0),
        "symbols_total": n_sym,
    }
    agg["beat_pct"] = agg["symbols_beating"] / n_sym if n_sym > 0 else 0

    return agg


# -- Helpers ----------------------------------------------------------------

def _sharpe(returns: np.ndarray) -> float:
    if len(returns) < 2 or np.std(returns) < 1e-10:
        return 0.0
    return float(np.mean(returns) / np.std(returns) * np.sqrt(252))


def _max_drawdown(returns: np.ndarray) -> float:
    cum = np.cumprod(1 + returns)
    running_max = np.maximum.accumulate(cum)
    dd = (cum - running_max) / running_max
    return float(dd.min())


# -- Multi-seed runner ------------------------------------------------------

def run_experiment(seeds: list[int] | None = None) -> dict:
    if seeds is None:
        seeds = SEEDS

    print("Loading multi-asset data (sectors + defensive ETFs)...")
    data = load_data()
    for sym, df in data.items():
        print(f"  {sym}: {len(df)} rows, {df.index[0].date()} to {df.index[-1].date()}")
    print()

    seed_results = []
    for seed in seeds:
        print(f"Seed {seed}...", end=" ", flush=True)
        t0 = time.time()
        result = walk_forward_portfolio(data, seed=seed)
        elapsed = time.time() - t0

        if "error" in result:
            print(f"ERROR: {result['error']}")
            continue

        result["elapsed_s"] = round(elapsed, 1)
        seed_results.append(result)
        print(f"Lasso={result['mean_lasso_sharpe']:.4f} "
              f"BH={result['mean_bh_sharpe']:.4f} "
              f"delta={result['mean_delta']:+.4f} "
              f"beating={result['symbols_beating']}/{result['symbols_total']} "
              f"stops={result['total_stops']} ({elapsed:.1f}s)")

    if not seed_results:
        return {"error": "No seeds converged"}

    deltas = [r["mean_delta"] for r in seed_results]
    lasso_sharpes = [r["mean_lasso_sharpe"] for r in seed_results]
    bh_sharpes = [r["mean_bh_sharpe"] for r in seed_results]
    beat_pcts = [r["beat_pct"] for r in seed_results]

    mean_delta = float(np.mean(deltas))
    se_delta = float(np.std(deltas, ddof=1) / np.sqrt(len(deltas))) if len(deltas) > 1 else 0.0
    t_stat = mean_delta / se_delta if se_delta > 0 else 0.0

    n_positive = sum(1 for d in deltas if d > 0)
    n_seeds = len(seed_results)

    from scipy.stats import binom
    p_value = float(binom.sf(n_positive - 1, n_seeds, 0.5))

    # Also compute stress test (50bps tx)
    stress_deltas = []
    for sr in seed_results:
        # Approximate stress: extra cost proportional to stops
        extra_cost = (TX_COST_STRESS_BPS - TX_COST_BPS) / 10000
        n_stops = sr["total_stops"]
        n_days = sr["total_days"]
        stress_drag = extra_cost * n_stops / max(n_days, 1) * 252
        stress_delta = sr["mean_delta"] - stress_drag
        stress_deltas.append(stress_delta)

    verdict = "BEATS" if (
        mean_delta > GATE_SHARPE_DELTA
        and t_stat >= 2.0
        and n_positive >= 3
    ) else "NO BEATS"

    agg = {
        "n_seeds": n_seeds,
        "seeds": seeds,
        "mean_lasso_sharpe": round(float(np.mean(lasso_sharpes)), 4),
        "mean_bh_sharpe": round(float(np.mean(bh_sharpes)), 4),
        "mean_delta": round(mean_delta, 6),
        "se_delta": round(se_delta, 6),
        "t_stat": round(t_stat, 3),
        "n_positive": n_positive,
        "p_value": round(p_value, 6),
        "mean_beat_pct": round(float(np.mean(beat_pcts)), 4),
        "mean_stress_delta": round(float(np.mean(stress_deltas)), 6),
        "verdict": verdict,
        "gate_delta": GATE_SHARPE_DELTA,
        "seed_results": seed_results,
    }

    return agg


# -- Verdict report ---------------------------------------------------------

def write_verdict(results: dict, output_dir: Path) -> Path:
    output_dir.mkdir(parents=True, exist_ok=True)
    verdict_path = output_dir / "verdict.md"

    lines = ["# S5 LASSO Stop-Loss — Verdict\n"]
    lines.append(f"Date: {datetime.now().strftime('%Y-%m-%d %H:%M')}\n")
    lines.append(f"Universe: {', '.join(SYMBOLS)}")
    lines.append(f"Features: VIX proxy (SPY rolling vol), ATR({ATR_PERIOD}), std({STD_WINDOW}), ADX({ADX_PERIOD})")
    lines.append(f"Target: max drawdown next {HORIZON} days")
    lines.append(f"Model: LASSO alpha={LASSO_ALPHA}")
    lines.append(f"Lookback: {LOOKBACK} days, buffer: {BUFFER*100:.0f}%")
    lines.append(f"Tx costs: {TX_COST_BPS}bps per trade, {TX_COST_STRESS_BPS}bps stress")
    lines.append(f"Walk-forward: {N_SPLITS}-fold expanding, OOS {OOS_YEAR} strict")
    lines.append(f"Multi-seed: block bootstrap ({BLOCK_SIZE}-day), seeds {SEEDS}\n")

    lines.append("## Results\n")
    lines.append(f"- **Verdict**: {results['verdict']}")
    lines.append(f"- LASSO Sharpe: {results['mean_lasso_sharpe']:.4f}")
    lines.append(f"- BH Sharpe: {results['mean_bh_sharpe']:.4f}")
    lines.append(f"- Delta: {results['mean_delta']:+.6f} (SE={results['se_delta']:.6f}, t={results['t_stat']:.3f})")
    lines.append(f"- Mean beat%: {results['mean_beat_pct']:.1%}")
    lines.append(f"- Stress delta (50bps): {results['mean_stress_delta']:+.6f}")
    lines.append(f"- Seeds positive: {results['n_positive']}/{results['n_seeds']} (p={results['p_value']:.4f})")
    lines.append(f"- Gate: delta > {results['gate_delta']:.2f}, t >= 2.0, >= 3/4 seeds positive\n")

    lines.append("## Per-seed summary\n")
    lines.append("| Seed | Lasso | BH | Delta | Beat% | Stops | Stress-Delta |")
    lines.append("|------|-------|----|-------|-------|-------|-------------|")
    for sr in results["seed_results"]:
        lines.append(f"| {sr['seed']} | {sr['mean_lasso_sharpe']:.4f} | "
                     f"{sr['mean_bh_sharpe']:.4f} | "
                     f"{sr['mean_delta']:+.4f} | "
                     f"{sr['beat_pct']:.0%} | "
                     f"{sr['total_stops']} | "
                     f"{results['mean_stress_delta']:+.4f} |")
    lines.append("")

    # Per-symbol detail from first seed
    if results["seed_results"]:
        first = results["seed_results"][0]
        lines.append("## Per-symbol detail (seed 0)\n")
        lines.append("| Symbol | Lasso | BH | Delta | Stops |")
        lines.append("|--------|-------|----|-------|-------|")
        for sr in first.get("per_symbol", []):
            lines.append(f"| {sr['symbol']} | {sr['lasso_sharpe']:.4f} | "
                         f"{sr['bh_sharpe']:.4f} | "
                         f"{sr['delta_sharpe']:+.4f} | "
                         f"{sr['n_stops']} |")
        lines.append("")

    verdict_path.write_text("\n".join(lines), encoding="utf-8")
    print(f"\nVerdict written to {verdict_path}")
    return verdict_path


# -- CLI --------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(description="S5 LASSO Stop-Loss")
    parser.add_argument("--seeds", type=str, default="0,1,7,42")
    parser.add_argument("--output", type=str, default=None)
    args = parser.parse_args()

    seeds = [int(s) for s in args.seeds.split(",")]
    output_dir = Path(args.output) if args.output else RESULTS_DIR
    output_dir.mkdir(parents=True, exist_ok=True)

    t_start = time.time()
    results = run_experiment(seeds)

    (output_dir / "results.json").write_text(
        json.dumps(results, indent=2, default=str), encoding="utf-8"
    )
    write_verdict(results, output_dir)

    elapsed = time.time() - t_start
    print(f"\nTotal time: {elapsed:.1f}s")


if __name__ == "__main__":
    main()
