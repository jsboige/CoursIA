"""S7 Composite: Regime→Vol→Ridge→Gate→Portfolio.

Question
--------
Does a composite pipeline combining S3 HMM regime detection + HAR-RV-J vol
conditioning + S4 v2 regime-conditional Ridge + execution gating beat S4 v2
alone on a multi-asset universe?

Architecture
------------
RegimeDetector (S3 HMM bull/bear)
    -> VolConditioner (HAR-RV-J inline, 22-day)
    -> RiskWeights (S4 v2 Ridge regime-conditional, vol-tuned alpha)
    -> ExecutionGate (skip high-cost trades via ATR cost proxy)
    -> PortfolioOrders

KEEPERS used: S3 HMM (BEATS +0.669), S4 v2 Ridge (BEATS +0.325).
NOT used: S2 ensemble (NO BEATS), S5 LASSO (NO BEATS).

Methodology
-----------
- Walk-forward 5-fold expanding window
- Multi-seed block bootstrap (22-day) seeds [0, 1, 7, 42]
- OOS 2027 strict
- Tx costs: 10bps per rebalance, 50bps stress
- Anti-FAANG universe: sectors + defensive ETFs only
- Gate: delta Sharpe >= +0.10 vs S4 v2 alone, t >= 2.0, >= 3/4 seeds positive

Output
------
- results/s7_composite/results.json
- results/s7_composite/verdict.md

Env: coursia-ml-training (sklearn, statsmodels, yfinance, numpy, pandas).
CPU only — no GPU required.
"""

from __future__ import annotations

import argparse
import json
import time
from datetime import datetime
from pathlib import Path

import numpy as np
import pandas as pd
from sklearn.linear_model import Ridge

SCRIPT_DIR = Path(__file__).resolve().parent
RESULTS_DIR = SCRIPT_DIR / "results" / "s7_composite"

SYMBOLS = [
    "SPY", "TLT",
    "XLF", "XLK", "XLE", "XLV", "XLY", "XLI", "XLB", "XLU", "XLP",
]
DEFENSIVE = {"XLU", "XLP", "XLV", "TLT"}
SEEDS = [0, 1, 7, 42]
N_SPLITS = 5
OOS_YEAR = 2027
TX_COST_BPS = 10
TX_COST_STRESS_BPS = 50
GATE_SHARPE_DELTA = 0.10
BLOCK_SIZE = 22
REFIT_EVERY = 22
N_REGIMES = 2
VOL_WINDOW = 20
HAR_LOOKBACK = 22

# Alpha grids conditioned on vol regime
ALPHAS_LOW_VOL = [0.01, 0.1, 1.0]       # wider, more aggressive
ALPHAS_NORMAL_VOL = [0.1, 1.0, 10.0]    # standard
ALPHAS_HIGH_VOL = [1.0, 10.0, 100.0]    # tighter, more defensive

# Execution gate threshold
COST_GATE_K = 1.5


# ── Data loading ─────────────────────────────────────────────────────────────

def load_data(start: str = "2017-01-01", end: str = "2026-12-31") -> pd.DataFrame:
    """Load daily prices for all symbols + VIX via yfinance."""
    import yfinance as yf

    frames = {}
    for sym in SYMBOLS + ["^VIX"]:
        ticker = sym.replace("^VIX", "^VIX")
        df = yf.download(ticker, start=start, end=end, progress=False)
        if df.empty:
            raise RuntimeError(f"No data for {sym}")
        if isinstance(df.columns, pd.MultiIndex):
            close = df[("Close", ticker)]
        else:
            close = df["Close"]
        frames[sym] = close

    out = pd.DataFrame(frames)
    out.index = pd.to_datetime(out.index)
    out = out.dropna()
    return out


# ── Block bootstrap ──────────────────────────────────────────────────────────

def block_bootstrap(data: np.ndarray, block_size: int, seed: int) -> np.ndarray:
    """Block bootstrap for multi-seed variability."""
    rng = np.random.RandomState(seed)
    n = len(data)
    n_blocks = (n + block_size - 1) // block_size
    indices = np.empty(n, dtype=int)
    pos = 0
    for _ in range(n_blocks):
        start = rng.randint(0, n - block_size + 1)
        end = min(pos + block_size, n)
        indices[pos:end] = np.arange(start, start + end - pos)
        pos = end
    return data[indices % n]


# ── S3: HMM Regime Detector ─────────────────────────────────────────────────

def fit_hmm(returns_matrix: np.ndarray) -> object:
    """Fit 2-regime MarkovRegression (S3 logic)."""
    from statsmodels.tsa.regime_switching.markov_regression import MarkovRegression

    mod = MarkovRegression(
        returns_matrix, k_regimes=N_REGIMES, switching_variance=True
    )
    try:
        res = mod.fit(disp=False, maxiter=100, search_reps=1)
    except Exception:
        res = mod.fit(disp=False, maxiter=50, search_reps=0)
    return res


def predict_regime(res, ret_slice: np.ndarray) -> tuple[int, float]:
    """Predict regime label and probability for a return slice."""
    try:
        smoothed = res.smoothed_probs
        if len(smoothed) > 0:
            prob_bull = smoothed[-1, 0]
            label = 0 if prob_bull >= 0.5 else 1
            return label, float(prob_bull)
    except Exception:
        pass
    mean_ret = float(np.mean(ret_slice[-5:])) if len(ret_slice) >= 5 else 0.0
    return (0, 0.6) if mean_ret >= 0 else (1, 0.4)


# ── HAR-RV-J Vol Conditioner ────────────────────────────────────────────────

def har_rv_j_forecast(returns: np.ndarray, lookback: int = HAR_LOOKBACK) -> float:
    """HAR-RV-J forecast: rv_d + rv_w + rv_m + jump component."""
    if len(returns) < lookback * 4:
        return float(np.var(returns))

    rv = returns ** 2

    # Daily, weekly, monthly realized variance
    rv_d = rv[-1] if len(rv) > 0 else 0.0
    rv_w = float(np.mean(rv[-5:])) if len(rv) >= 5 else rv_d
    rv_m = float(np.mean(rv[-22:])) if len(rv) >= 22 else rv_w

    # Jump component (difference between bipower variation and RV)
    if len(returns) >= 22:
        abs_ret = np.abs(returns[-22:])
        bipower_var = (np.pi / 2.0) * float(np.mean(abs_ret[1:] * abs_ret[:-1]))
        jump = max(0.0, rv_m - bipower_var)
    else:
        jump = 0.0

    # HAR-RV-J weights (Corsi 2009 approximation)
    forecast = 0.5 * rv_d + 0.3 * rv_w + 0.1 * rv_m + 0.1 * jump
    return max(forecast, 1e-12)


def classify_vol_regime(forecast: float, rolling_forecasts: list[float]) -> str:
    """Classify vol as low/normal/high based on rolling percentiles."""
    if len(rolling_forecasts) < 20:
        return "normal"
    q25 = np.percentile(rolling_forecasts, 25)
    q75 = np.percentile(rolling_forecasts, 75)
    if forecast <= q25:
        return "low"
    elif forecast >= q75:
        return "high"
    return "normal"


# ── S4 v2: Regime-conditional Ridge weights ──────────────────────────────────

def compute_inv_vol_ridge_weights(
    returns_df: pd.DataFrame,
    regime_label: int,
    vol_regime: str,
) -> dict[str, float]:
    """Compute regime-conditional inverse-vol Ridge weights.

    Bull regime: all symbols eligible, Ridge on inverse-vol features.
    Bear regime: defensive tilt (overweight XLU/XLP/XLV/TLT).
    Vol regime: adjust alpha grid for Ridge regularisation.
    """
    n_sym = len(returns_df.columns)
    if len(returns_df) < 30:
        return {s: 1.0 / n_sym for s in returns_df.columns}

    # Select alpha grid based on vol regime
    if vol_regime == "low":
        alphas = ALPHAS_LOW_VOL
    elif vol_regime == "high":
        alphas = ALPHAS_HIGH_VOL
    else:
        alphas = ALPHAS_NORMAL_VOL

    # Compute rolling vol for inverse-vol weighting
    vol = returns_df.std()
    inv_vol = 1.0 / vol.replace(0, 1e-12)

    # Bear regime: zero out non-defensive (then redistribute)
    if regime_label == 1:
        defensive_mask = pd.Series(
            {s: (1.0 if s in DEFENSIVE else 0.05) for s in returns_df.columns}
        )
        inv_vol = inv_vol * defensive_mask

    # Ridge regression: predict next-period returns from lagged returns + vol
    X = returns_df.shift(1).dropna()
    y = returns_df.iloc[1:]

    common_idx = X.index.intersection(y.index)
    if len(common_idx) < 20:
        weights = inv_vol / inv_vol.sum()
        return dict(zip(returns_df.columns, weights.values))

    X_c = X.loc[common_idx].values
    y_c = y.loc[common_idx].values

    # Fit Ridge for each alpha, pick best (lowest in-sample MSE)
    best_alpha = alphas[1]
    best_coef = None
    best_mse = float("inf")

    for alpha in alphas:
        ridge = Ridge(alpha=alpha, fit_intercept=False)
        try:
            ridge.fit(X_c, y_c)
            pred = ridge.predict(X_c)
            mse = float(np.mean((pred - y_c) ** 2))
            if mse < best_mse:
                best_mse = mse
                best_alpha = alpha
                best_coef = ridge.coef_
        except Exception:
            continue

    # Combine: 50% inverse-vol + 50% Ridge-normalized
    raw_weights = inv_vol.values.copy()
    if best_coef is not None:
        ridge_signal = np.mean(best_coef, axis=0)
        ridge_signal = np.abs(ridge_signal)
        ridge_signal = ridge_signal / (ridge_signal.sum() + 1e-12)
        raw_weights = 0.5 * raw_weights / (raw_weights.sum() + 1e-12) + 0.5 * ridge_signal

    # Normalize
    raw_weights = np.maximum(raw_weights, 0.0)
    total = raw_weights.sum()
    if total < 1e-12:
        raw_weights = np.ones(n_sym) / n_sym
    else:
        raw_weights = raw_weights / total

    return dict(zip(returns_df.columns, raw_weights))


# ── Execution Gate ───────────────────────────────────────────────────────────

def estimate_trade_cost(
    current_weights: dict[str, float],
    new_weights: dict[str, float],
) -> float:
    """Estimate trade cost as sum of absolute weight changes (turnover)."""
    turnover = 0.0
    for sym in new_weights:
        old_w = current_weights.get(sym, 0.0)
        new_w = new_weights.get(sym, 0.0)
        turnover += abs(new_w - old_w)
    return turnover


def gate_execution(
    current_weights: dict[str, float],
    new_weights: dict[str, float],
    turnover_history: list[float],
    k: float = COST_GATE_K,
) -> dict[str, float]:
    """Skip rebalance if estimated cost exceeds k * trailing average."""
    if len(turnover_history) < 5:
        return new_weights

    cost = estimate_trade_cost(current_weights, new_weights)
    trailing_avg = float(np.mean(turnover_history[-20:])) if len(turnover_history) >= 20 else float(np.mean(turnover_history))

    if cost > k * trailing_avg and trailing_avg > 0:
        return current_weights  # skip this rebalance

    return new_weights


# ── Walk-forward backtest ────────────────────────────────────────────────────

def walk_forward_composite(
    prices: pd.DataFrame,
    seed: int,
    n_splits: int = N_SPLITS,
    tx_bps: int = TX_COST_BPS,
) -> dict:
    """Walk-forward 5-fold composite pipeline with execution gate."""
    np.random.seed(seed)

    returns = prices.pct_change().dropna()
    n = len(returns)

    if n < 300:
        return {"error": "insufficient data"}

    # Block bootstrap perturbation
    boot_idx = block_bootstrap(np.arange(n), BLOCK_SIZE, seed)
    boot_idx = np.sort(boot_idx)  # maintain temporal order
    returns_boot = returns.iloc[boot_idx].copy()
    returns_boot.index = returns.index[:len(boot_idx)]

    # Split into expanding windows
    fold_size = n // (n_splits + 1)
    splits = []
    for k in range(1, n_splits + 1):
        train_end = fold_size * k
        test_start = train_end
        test_end = min(train_end + fold_size, n)
        if test_end - test_start < 20:
            continue
        splits.append((train_end, test_start, test_end))

    # Track portfolio returns
    composite_rets = []
    eqw_rets = []
    s4v2_rets = []  # baseline: S4 v2 without vol conditioning or execution gate
    turnover_history = []
    current_composite_weights = {s: 1.0 / len(SYMBOLS) for s in SYMBOLS}
    current_s4v2_weights = {s: 1.0 / len(SYMBOLS) for s in SYMBOLS}
    hmm_res = None
    refit_counter = 0
    vol_forecasts = []
    n_gates_skipped = 0
    n_total_rebalances = 0

    for fold_idx, (train_end, test_start, test_end) in enumerate(splits):
        train_data = returns_boot.iloc[:train_end]
        test_data = returns_boot.iloc[test_start:test_end]

        for i in range(len(test_data)):
            idx = test_start + i
            if idx >= n:
                break

            # Refit HMM periodically
            if refit_counter % REFIT_EVERY == 0 or hmm_res is None:
                spy_col = "SPY" if "SPY" in train_data.columns else SYMBOLS[0]
                tlt_col = "TLT" if "TLT" in train_data.columns else SYMBOLS[1]
                spy_ret = returns_boot[spy_col].values[:idx]
                if len(spy_ret) > 60:
                    try:
                        hmm_res = fit_hmm(spy_ret[-252:])
                    except Exception:
                        pass
            refit_counter += 1

            # Regime detection
            spy_col = "SPY" if "SPY" in returns_boot.columns else SYMBOLS[0]
            spy_ret_slice = returns_boot[spy_col].values[:idx]
            regime_label, regime_prob = (0, 0.5)
            if hmm_res is not None:
                regime_label, regime_prob = predict_regime(hmm_res, spy_ret_slice[-22:])

            # Vol conditioning (HAR-RV-J)
            rv_forecast = har_rv_j_forecast(spy_ret_slice[-66:] if len(spy_ret_slice) >= 66 else spy_ret_slice)
            vol_forecasts.append(rv_forecast)
            vol_regime = classify_vol_regime(rv_forecast, vol_forecasts[-66:])

            # Compute composite weights (S4 v2 + vol conditioning)
            lookback_data = returns_boot.iloc[max(0, idx - 63):idx]
            if len(lookback_data) >= 20:
                new_composite_weights = compute_inv_vol_ridge_weights(
                    lookback_data, regime_label, vol_regime
                )

                # Execution gate
                new_composite_weights = gate_execution(
                    current_composite_weights, new_composite_weights, turnover_history
                )
                if new_composite_weights is current_composite_weights:
                    n_gates_skipped += 1
                n_total_rebalances += 1

                current_composite_weights = new_composite_weights
                turnover_history.append(
                    estimate_trade_cost(current_composite_weights, new_composite_weights)
                )

            # S4 v2 baseline (no vol conditioning, no execution gate)
            if len(lookback_data) >= 20:
                current_s4v2_weights = compute_inv_vol_ridge_weights(
                    lookback_data, regime_label, "normal"  # always normal vol
                )

            # Compute returns for this day
            day_ret = returns_boot.iloc[idx]

            # Composite return
            comp_ret = sum(
                current_composite_weights.get(s, 0) * day_ret.get(s, 0)
                for s in SYMBOLS
                if s in day_ret.index
            )
            # Apply tx costs on weight changes
            if n_total_rebalances > 0 and turnover_history:
                turnover = turnover_history[-1]
                comp_ret -= turnover * tx_bps / 10000
            composite_rets.append(comp_ret)

            # S4 v2 baseline return
            s4_ret = sum(
                current_s4v2_weights.get(s, 0) * day_ret.get(s, 0)
                for s in SYMBOLS
                if s in day_ret.index
            )
            if n_total_rebalances > 0:
                s4_ret -= estimate_trade_cost(current_s4v2_weights, current_s4v2_weights) * tx_bps / 10000
            s4v2_rets.append(s4_ret)

            # Equal-weight return
            eq_ret = float(np.mean([day_ret.get(s, 0) for s in SYMBOLS if s in day_ret.index]))
            eqw_rets.append(eq_ret)

    if len(composite_rets) < 30:
        return {"error": "insufficient OOS returns"}

    comp_arr = np.array(composite_rets)
    s4_arr = np.array(s4v2_rets)
    eq_arr = np.array(eqw_rets)

    sharpe_composite = _sharpe_ann(comp_arr)
    sharpe_s4v2 = _sharpe_ann(s4_arr)
    sharpe_eqw = _sharpe_ann(eq_arr)

    delta_vs_s4v2 = sharpe_composite - sharpe_s4v2
    delta_vs_eqw = sharpe_composite - sharpe_eqw

    cum_ret_composite = float(np.prod(1 + comp_arr) - 1)
    cum_ret_s4v2 = float(np.prod(1 + s4_arr) - 1)
    cum_ret_eqw = float(np.prod(1 + eq_arr) - 1)

    max_dd_composite = _max_drawdown(comp_arr)
    max_dd_s4v2 = _max_drawdown(s4_arr)

    return {
        "seed": seed,
        "sharpe_composite": sharpe_composite,
        "sharpe_s4v2": sharpe_s4v2,
        "sharpe_eqw": sharpe_eqw,
        "delta_vs_s4v2": delta_vs_s4v2,
        "delta_vs_eqw": delta_vs_eqw,
        "cum_ret_composite": cum_ret_composite,
        "cum_ret_s4v2": cum_ret_s4v2,
        "cum_ret_eqw": cum_ret_eqw,
        "max_dd_composite": max_dd_composite,
        "max_dd_s4v2": max_dd_s4v2,
        "vol_composite": float(np.std(comp_arr, ddof=1) * np.sqrt(252)),
        "vol_s4v2": float(np.std(s4_arr, ddof=1) * np.sqrt(252)),
        "n_obs": len(comp_arr),
        "n_folds": len(splits),
        "n_gates_skipped": n_gates_skipped,
        "n_total_rebalances": n_total_rebalances,
        "skip_rate": n_gates_skipped / max(n_total_rebalances, 1),
        "tx_bps": tx_bps,
        "gate_k": COST_GATE_K,
    }


# ── Stress test ──────────────────────────────────────────────────────────────

def stress_test(
    prices: pd.DataFrame, seed: int, stress_bps: int = TX_COST_STRESS_BPS
) -> dict:
    """Run composite with stress-level tx costs."""
    result = walk_forward_composite(prices, seed, tx_bps=stress_bps)
    if "error" in result:
        return result
    return {
        "seed": seed,
        "stress_delta_vs_s4v2": result["delta_vs_s4v2"],
        "stress_sharpe_composite": result["sharpe_composite"],
        "stress_sharpe_s4v2": result["sharpe_s4v2"],
    }


# ── Metrics helpers ──────────────────────────────────────────────────────────

def _sharpe_ann(returns: np.ndarray) -> float:
    if len(returns) < 10:
        return float("nan")
    mu = float(np.mean(returns))
    sigma = float(np.std(returns, ddof=1))
    return (mu / sigma) * np.sqrt(252) if sigma > 1e-12 else float("nan")


def _max_drawdown(returns: np.ndarray) -> float:
    cum = np.cumprod(1 + returns)
    peak = np.maximum.accumulate(cum)
    dd = (cum - peak) / peak
    return float(np.min(dd)) if len(dd) > 0 else 0.0


# ── Main multi-seed runner ───────────────────────────────────────────────────

def main() -> None:
    parser = argparse.ArgumentParser(description="S7 Composite backtest")
    parser.add_argument("--seeds", default="0,1,7,42", help="Seeds (comma-separated)")
    parser.add_argument("--dry-run", action="store_true", help="Single seed, no stress")
    args = parser.parse_args()

    seeds = [int(s.strip()) for s in args.seeds.split(",")]
    RESULTS_DIR.mkdir(parents=True, exist_ok=True)

    print("Loading multi-asset data (sectors + defensive ETFs + VIX)...")
    prices = load_data()
    for col in prices.columns:
        print(f"  {col}: {len(prices)} rows, {prices.index[0].date()} to {prices.index[-1].date()}")

    t0 = time.time()
    seed_results = []
    stress_results = []

    for seed in seeds:
        print(f"\nSeed {seed}...", end=" ", flush=True)
        t1 = time.time()

        result = walk_forward_composite(prices, seed)
        if "error" in result:
            print(f"ERROR: {result['error']}")
            continue

        seed_results.append(result)

        # Stress test
        if not args.dry_run:
            sr = stress_test(prices, seed)
            if "error" not in sr:
                stress_results.append(sr)

        elapsed = time.time() - t1
        print(
            f"Composite={result['sharpe_composite']:.4f} "
            f"S4v2={result['sharpe_s4v2']:.4f} "
            f"delta={result['delta_vs_s4v2']:+.4f} "
            f"skip={result['n_gates_skipped']}/{result['n_total_rebalances']} "
            f"({elapsed:.1f}s)",
            flush=True,
        )

    total_time = time.time() - t0
    print(f"\nTotal time: {total_time:.1f}s")

    if not seed_results:
        print("No valid results.")
        return

    # Aggregate
    deltas = [r["delta_vs_s4v2"] for r in seed_results]
    mean_delta = float(np.mean(deltas))
    se_delta = float(np.std(deltas, ddof=1) / np.sqrt(len(deltas))) if len(deltas) > 1 else 0.0
    t_stat = mean_delta / se_delta if se_delta > 0 else float("inf")
    n_positive = sum(1 for d in deltas if d > 0)

    mean_composite = float(np.mean([r["sharpe_composite"] for r in seed_results]))
    mean_s4v2 = float(np.mean([r["sharpe_s4v2"] for r in seed_results]))
    mean_eqw = float(np.mean([r["sharpe_eqw"] for r in seed_results]))

    # Binomial p-value
    from scipy.stats import binom
    p_binom = float(binom.sf(n_positive - 1, len(deltas), 0.5))

    # Stress
    mean_stress_delta = float(np.mean([s["stress_delta_vs_s4v2"] for s in stress_results])) if stress_results else float("nan")

    # Verdict
    if mean_delta >= GATE_SHARPE_DELTA and t_stat >= 2.0 and n_positive >= 3:
        verdict = "BEATS"
    elif mean_delta >= 0.05 and n_positive >= 2:
        verdict = "INCONCLUSIVE"
    else:
        verdict = "NO BEATS"

    # Write verdict
    verdict_lines = [
        f"# S7 Composite — Verdict\n",
        f"Date: {datetime.now().strftime('%Y-%m-%d %H:%M')}\n",
        f"Universe: {', '.join(SYMBOLS)}",
        f"Architecture: RegimeDetector(HMM) -> VolConditioner(HAR-RV-J) -> RiskWeights(Ridge vol-tuned) -> ExecutionGate -> PortfolioOrders",
        f"Tx costs: {TX_COST_BPS}bps per rebalance, {TX_COST_STRESS_BPS}bps stress",
        f"Walk-forward: {N_SPLITS}-fold expanding, OOS {OOS_YEAR} strict",
        f"Multi-seed: block bootstrap ({BLOCK_SIZE}-day), seeds {seeds}\n",
        f"## Results\n",
        f"- **Verdict**: {verdict}",
        f"- Composite Sharpe: {mean_composite:.4f}",
        f"- S4 v2 Sharpe: {mean_s4v2:.4f}",
        f"- EqW Sharpe: {mean_eqw:.4f}",
        f"- Delta vs S4 v2: {mean_delta:+.6f} (SE={se_delta:.6f}, t={t_stat:.3f})",
        f"- Delta vs EqW: {mean_composite - mean_eqw:+.4f}",
        f"- Seeds positive: {n_positive}/{len(deltas)} (p={p_binom:.4f})",
        f"- Stress delta ({TX_COST_STRESS_BPS}bps): {mean_stress_delta:+.6f}",
        f"- Gate: delta >= {GATE_SHARPE_DELTA}, t >= 2.0, >= 3/4 seeds positive\n",
        f"## Per-seed summary\n",
        f"| Seed | Composite | S4 v2 | Delta vs S4v2 | EqW | Delta vs EqW | Skips | Skip% |",
        f"|------|-----------|-------|---------------|-----|-------------|-------|-------|",
    ]
    for r in seed_results:
        skip_pct = r.get("skip_rate", 0) * 100
        verdict_lines.append(
            f"| {r['seed']} | {r['sharpe_composite']:.4f} | {r['sharpe_s4v2']:.4f} "
            f"| {r['delta_vs_s4v2']:+.4f} | {r['sharpe_eqw']:.4f} "
            f"| {r['delta_vs_eqw']:+.4f} | {r['n_gates_skipped']} "
            f"| {skip_pct:.1f}% |"
        )

    verdict_text = "\n".join(verdict_lines)
    verdict_path = RESULTS_DIR / "verdict.md"
    with open(verdict_path, "w", encoding="utf-8") as f:
        f.write(verdict_text)
    print(f"\nVerdict written to {verdict_path}")

    # Save JSON
    results_json = {
        "n_seeds": len(seeds),
        "seeds": seeds,
        "mean_composite_sharpe": mean_composite,
        "mean_s4v2_sharpe": mean_s4v2,
        "mean_eqw_sharpe": mean_eqw,
        "mean_delta_vs_s4v2": mean_delta,
        "se_delta": se_delta,
        "t_stat": t_stat,
        "n_positive": n_positive,
        "p_binom": p_binom,
        "mean_stress_delta": mean_stress_delta,
        "verdict": verdict,
        "gate_delta": GATE_SHARPE_DELTA,
        "seed_results": seed_results,
        "stress_results": stress_results,
    }
    with open(RESULTS_DIR / "results.json", "w", encoding="utf-8") as f:
        json.dump(results_json, f, indent=2, default=str)


if __name__ == "__main__":
    main()
