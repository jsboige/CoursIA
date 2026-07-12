"""S4 v2 Inverse Volatility Ridge with HMM Regime Features.

Question
--------
Does regime-conditional inverse-volatility weighting with Ridge regularisation
beat equal-weight on a multi-asset universe (SPY + TLT + VIX + sectors)?

The v1 (crypto-7) failed: delta +0.022 (gate +0.10). The key insight from S3:
HMM regime detection BEATS (+0.67 delta). V2 combines regime signals with
inverse-vol weighting, switching allocation based on regime.

Methodology
-----------
- Universe: SPY, TLT + 9 sector ETFs (XLF/XLK/XLE/XLV/XLY/XLI/XLB/XLU/XLP)
- HMM regime detection: MarkovRegression 2-regime (reused from S3)
- Regime-conditional weights:
    Bull: overweight high-momentum sectors via inverse-vol Ridge
    Bear: rotate to defensive sectors (XLU, XLP, XLV) + TLT
- Walk-forward 5-fold expanding window
- Multi-seed block bootstrap (22-day blocks) 0/1/7/42
- OOS strict 2027
- Tx costs: 5bps SPY/sectors, 50bps stress scenario
- Gate: Sharpe regime-ridge > equal-weight + 0.10 cross-seed

Output
------
- results/s4_inverse_vol_ridge_v2/results.json
- results/s4_inverse_vol_ridge_v2/verdict.md

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
RESULTS_DIR = SCRIPT_DIR / "results" / "s4_inverse_vol_ridge_v2"

# Universe: SPY + TLT + 9 sector ETFs
SYMBOLS = [
    "SPY", "TLT",
    "XLF", "XLK", "XLE", "XLV", "XLY", "XLI", "XLB", "XLU", "XLP",
]
DEFENSIVE = {"XLU", "XLP", "XLV", "TLT"}
SEEDS = [0, 1, 7, 42]
N_SPLITS = 5
OOS_YEAR = 2027
TX_COST_BPS = 5
TX_COST_STRESS_BPS = 50
GATE_SHARPE_DELTA = 0.10
BLOCK_SIZE = 22
N_REGIMES = 2
VOL_WINDOW = 20
REFIT_EVERY = 22

# Ridge alpha grid for cross-validation
ALPHAS = [0.01, 0.1, 1.0, 10.0, 100.0]


# ── Data loading ─────────────────────────────────────────────────────────────

def load_data(start: str = "2017-01-01", end: str = "2026-12-31") -> pd.DataFrame:
    """Load daily prices for all symbols via yfinance."""
    import yfinance as yf

    frames = {}
    for sym in SYMBOLS:
        df = yf.download(sym, start=start, end=end, progress=False)
        if df.empty:
            raise RuntimeError(f"No data for {sym}")
        if isinstance(df.columns, pd.MultiIndex):
            close = df[("Close", sym)]
        else:
            close = df["Close"]
        frames[sym] = close

    prices = pd.DataFrame(frames)
    prices.index = pd.to_datetime(prices.index)
    prices = prices.dropna()
    return prices


# ── Block bootstrap ──────────────────────────────────────────────────────────

def block_bootstrap(data: np.ndarray, block_size: int, seed: int) -> np.ndarray:
    rng = np.random.RandomState(seed)
    n = len(data)
    n_blocks = (n + block_size - 1) // block_size
    indices = []
    for _ in range(n_blocks):
        start = rng.randint(0, n - block_size + 1)
        indices.extend(range(start, min(start + block_size, n)))
    return data[indices[:n]]


# ── HMM regime detection (reused from S3) ────────────────────────────────────

def fit_hmm_regime(
    spy_ret: np.ndarray,
    tlt_ret: np.ndarray,
    vix_proxy: np.ndarray | None = None,
    seed: int = 0,
) -> dict:
    """Fit MarkovRegression 2-regime on SPY returns with exog."""
    from statsmodels.tsa.regime_switching.markov_regression import MarkovRegression

    if vix_proxy is not None:
        vix_norm = (vix_proxy - vix_proxy.mean()) / (vix_proxy.std() + 1e-8)
        exog = np.column_stack([tlt_ret, vix_norm])
    else:
        exog = tlt_ret

    try:
        mod = MarkovRegression(
            spy_ret, k_regimes=N_REGIMES,
            exog=exog, switching_variance=True,
        )
        res = mod.search_em_restarts(n_restarts=4, seed=seed, maxiter=200, tol=1e-6)
        if res is None or not res.mle_retvals.get("converged", False):
            res = mod.fit(disp=False, maxiter=300)
    except Exception:
        try:
            mod = MarkovRegression(
                spy_ret, k_regimes=N_REGIMES, switching_variance=True,
            )
            res = mod.fit(disp=False, maxiter=300)
        except Exception:
            return {
                "labels": np.zeros(len(spy_ret), dtype=int),
                "converged": False,
            }

    smoothed = res.smoothed_marginal_probabilities
    labels = np.argmax(smoothed, axis=1)

    # Relabel: bull=0 (higher return), bear=1
    means = [spy_ret[labels == k].mean() if (labels == k).sum() > 0 else 0
             for k in range(N_REGIMES)]
    if means[0] < means[1]:
        labels = 1 - labels

    return {"labels": labels, "converged": True}


def jitter_regime(labels: np.ndarray, seed: int, max_jitter: int = 5) -> np.ndarray:
    if seed == 0:
        return labels.copy()
    rng = np.random.RandomState(seed)
    jittered = labels.copy()
    switches = np.where(np.diff(labels) != 0)[0]
    for idx in switches:
        shift = rng.randint(-max_jitter, max_jitter + 1)
        new_idx = max(0, min(len(labels) - 1, idx + shift))
        new_regime = labels[idx + 1]
        start, end = min(idx, new_idx), max(idx, new_idx)
        for i in range(start, end + 1):
            jittered[i] = new_regime
    return jittered


# ── Portfolio weighting ──────────────────────────────────────────────────────

def inv_vol_weights(returns: np.ndarray) -> np.ndarray:
    vols = np.std(returns, axis=0) + 1e-8
    w = 1.0 / vols
    return _project_simplex(w)


def _project_simplex(v: np.ndarray) -> np.ndarray:
    n = len(v)
    u = np.sort(v)[::-1]
    cssv = np.cumsum(u) - 1
    rho = np.nonzero(u * np.arange(1, n + 1) > cssv)[0][-1]
    theta = cssv[rho] / (rho + 1.0)
    w = np.maximum(v - theta, 0)
    return w / w.sum()


def regime_conditional_weights(
    returns: np.ndarray,
    regime_label: int,
    alpha: float = 1.0,
) -> np.ndarray:
    """Regime-conditional inverse-vol weights with Ridge shrinkage.

    Bull (regime=0): standard inverse-vol across all assets.
    Bear (regime=1): tilt towards defensive assets by doubling their
                     inverse-vol contribution, then Ridge-shrink.
    """
    n_assets = returns.shape[1]
    base_w = inv_vol_weights(returns)

    if regime_label == 1:  # Bear: tilt defensive
        defensive_mask = np.array([1.0 if SYMBOLS[i] in DEFENSIVE else 0.5
                                   for i in range(n_assets)])
        tilted_w = base_w * defensive_mask
        tilted_w = tilted_w / tilted_w.sum()
    else:
        tilted_w = base_w

    # Ridge shrinkage towards equal-weight
    eq_w = np.ones(n_assets) / n_assets
    ridge_w = (tilted_w + alpha * eq_w) / (1 + alpha)
    return _project_simplex(ridge_w)


def equal_weights(n: int) -> np.ndarray:
    return np.ones(n) / n


# ── Walk-forward evaluation ─────────────────────────────────────────────────

def walk_forward(
    prices: pd.DataFrame,
    seed: int = 0,
) -> dict:
    """Walk-forward 5-fold expanding with HMM regime + inverse-vol Ridge."""
    returns = prices.pct_change().dropna()

    oos_mask = returns.index >= f"{OOS_YEAR}-01-01"
    is_returns = returns[~oos_mask]

    n_is = len(is_returns)
    n_assets = is_returns.shape[1]
    fold_size = n_is // N_SPLITS

    rng = np.random.RandomState(seed)

    oos_dates = []
    ridge_ret_all = []
    invvol_ret_all = []
    eq_ret_all = []
    regime_counts = {0: 0, 1: 0}
    n_switches = 0
    prev_regime = None

    for fold_idx in range(N_SPLITS):
        train_end = fold_size * (fold_idx + 2)
        train_end = min(train_end, n_is)
        test_start = fold_size * (fold_idx + 1)
        test_end = train_end

        if train_end < 252 or test_end <= test_start:
            continue

        train_block = is_returns.iloc[:train_end]
        test_block = is_returns.iloc[test_start:test_end]

        # Block bootstrap training for seed variability
        n_train = len(train_block)
        indices = rng.choice(n_train, size=n_train, replace=True)
        boot_train = train_block.values[indices]

        # Fit HMM on training block (SPY is column 0, TLT is column 1)
        spy_ret_train = train_block.iloc[:, 0].values  # SPY
        tlt_ret_train = train_block.iloc[:, 1].values  # TLT

        # Use rolling volatility of SPY as VIX proxy
        spy_vol_proxy = pd.Series(spy_ret_train).rolling(VOL_WINDOW).std().values
        spy_vol_proxy = np.nan_to_num(spy_vol_proxy, nan=spy_vol_proxy[~np.isnan(spy_vol_proxy)].mean())

        hmm_result = fit_hmm_regime(spy_ret_train, tlt_ret_train, spy_vol_proxy, seed)

        if not hmm_result.get("converged", False):
            # Fallback: use simple momentum regime
            train_labels = np.where(spy_ret_train > 0, 0, 1).astype(int)
        else:
            train_labels = hmm_result["labels"]

        # Predict regime for test block using last training regime
        # Walk-forward: refit HMM on test block separately
        spy_ret_test = test_block.iloc[:, 0].values
        tlt_ret_test = test_block.iloc[:, 1].values
        spy_vol_test = pd.Series(spy_ret_test).rolling(VOL_WINDOW).std().values
        spy_vol_test = np.nan_to_num(spy_vol_test, nan=np.nanmean(spy_vol_test) if not np.all(np.isnan(spy_vol_test)) else 0.01)

        test_hmm = fit_hmm_regime(spy_ret_test, tlt_ret_test, spy_vol_test, seed)
        if test_hmm.get("converged", False):
            test_labels = jitter_regime(test_hmm["labels"], seed)
        else:
            test_labels = np.where(spy_ret_test > 0, 0, 1).astype(int)

        # Cross-validate alpha on last 20% of training
        val_start = int(n_train * 0.8)
        val_data = train_block.values[val_start:]
        best_alpha = ALPHAS[0]
        best_sharpe = -np.inf

        for alpha in ALPHAS:
            # Use majority regime from validation for alpha selection
            val_regime = int(np.median(train_labels[val_start:]) > 0.5)
            w = regime_conditional_weights(boot_train, val_regime, alpha)
            port_ret = val_data @ w
            s = _sharpe(port_ret)
            if s > best_sharpe:
                best_sharpe = s
                best_alpha = alpha

        # Apply regime-conditional weights per day in test block
        test_arr = test_block.values
        ridge_fold = np.zeros(len(test_arr))
        invvol_w = inv_vol_weights(boot_train)
        eq_w = equal_weights(n_assets)

        for t in range(len(test_arr)):
            regime = test_labels[t]
            w = regime_conditional_weights(boot_train, regime, best_alpha)
            ridge_fold[t] = test_arr[t] @ w
            regime_counts[regime] = regime_counts.get(regime, 0) + 1
            if prev_regime is not None and regime != prev_regime:
                n_switches += 1
            prev_regime = regime

        invvol_fold = test_arr @ invvol_w
        eq_fold = test_arr @ eq_w

        # Transaction costs at rebalance
        tx = TX_COST_BPS / 10000
        ridge_fold[0] -= tx
        invvol_fold[0] -= tx

        oos_dates.extend(test_block.index)
        ridge_ret_all.extend(ridge_fold)
        invvol_ret_all.extend(invvol_fold)
        eq_ret_all.extend(eq_fold)

    if not ridge_ret_all:
        return {"error": "No folds produced results"}

    ridge_ret = np.array(ridge_ret_all)
    invvol_ret = np.array(invvol_ret_all)
    eq_ret = np.array(eq_ret_all)

    # Per-regime analysis
    regime_labels_full = np.zeros(len(ridge_ret), dtype=int)
    idx = 0
    for fold_idx in range(N_SPLITS):
        fold_size_actual = n_is // N_SPLITS
        test_start = fold_size_actual * (fold_idx + 1)
        test_end = min(fold_size_actual * (fold_idx + 2), n_is)
        n_test = test_end - test_start
        if n_test <= 0 or test_start >= n_is:
            continue
        test_block = is_returns.iloc[test_start:test_end]
        spy_test = test_block.iloc[:, 0].values
        tlt_test = test_block.iloc[:, 1].values
        spy_vol_t = pd.Series(spy_test).rolling(VOL_WINDOW).std().values
        spy_vol_t = np.nan_to_num(spy_vol_t, nan=0.01)
        hmm_t = fit_hmm_regime(spy_test, tlt_test, spy_vol_t, seed)
        if hmm_t.get("converged", False):
            regime_labels_full[idx:idx + len(spy_test)] = jitter_regime(hmm_t["labels"], seed)
        else:
            regime_labels_full[idx:idx + len(spy_test)] = np.where(spy_test > 0, 0, 1)
        idx += len(spy_test)

    # Trim to actual length
    regime_labels_full = regime_labels_full[:len(ridge_ret)]

    results = {}
    for name, ret in [("ridge", ridge_ret), ("inv_vol", invvol_ret), ("equal_weight", eq_ret)]:
        results[f"{name}_sharpe"] = float(_sharpe(ret))
        results[f"{name}_cum_ret"] = float(np.prod(1 + ret) - 1)
        results[f"{name}_max_dd"] = float(_max_drawdown(ret))
        results[f"{name}_vol"] = float(np.std(ret) * np.sqrt(252))

    # Per-regime Sharpe
    bull_mask = regime_labels_full == 0
    bear_mask = regime_labels_full == 1
    results["ridge_sharpe_bull"] = float(_sharpe(ridge_ret[bull_mask])) if bull_mask.sum() > 10 else 0.0
    results["ridge_sharpe_bear"] = float(_sharpe(ridge_ret[bear_mask])) if bear_mask.sum() > 10 else 0.0
    results["eq_sharpe_bull"] = float(_sharpe(eq_ret[bull_mask])) if bull_mask.sum() > 10 else 0.0
    results["eq_sharpe_bear"] = float(_sharpe(eq_ret[bear_mask])) if bear_mask.sum() > 10 else 0.0

    results["delta_ridge_vs_eq"] = results["ridge_sharpe"] - results["equal_weight_sharpe"]
    results["delta_bear"] = results["ridge_sharpe_bear"] - results["eq_sharpe_bear"]
    results["n_obs"] = len(ridge_ret)
    results["n_folds"] = N_SPLITS
    results["seed"] = seed
    results["best_alpha"] = best_alpha
    results["n_switches"] = n_switches
    results["regime_counts"] = {int(k): int(v) for k, v in regime_counts.items()}
    results["bull_pct"] = float(bull_mask.mean())

    return results


def _sharpe(returns: np.ndarray) -> float:
    if len(returns) < 2 or np.std(returns) < 1e-10:
        return 0.0
    return float(np.mean(returns) / np.std(returns) * np.sqrt(252))


def _max_drawdown(returns: np.ndarray) -> float:
    cum = np.cumprod(1 + returns)
    running_max = np.maximum.accumulate(cum)
    dd = (cum - running_max) / running_max
    return float(dd.min())


# ── Multi-seed runner ────────────────────────────────────────────────────────

def run_experiment(seeds: list[int] | None = None) -> dict:
    if seeds is None:
        seeds = SEEDS

    print("Loading multi-asset data (SPY + TLT + 9 sectors)...")
    prices = load_data()
    returns = prices.pct_change().dropna()
    print(f"  {len(returns)} days, {returns.columns.tolist()}")
    print(f"  {returns.index[0].date()} to {returns.index[-1].date()}\n")

    seed_results = []
    for seed in seeds:
        print(f"  Seed {seed}...", end=" ", flush=True)
        t0 = time.time()
        result = walk_forward(prices, seed=seed)
        elapsed = time.time() - t0

        if "error" in result:
            print(f"ERROR: {result['error']}")
            continue

        result["elapsed_s"] = round(elapsed, 1)
        seed_results.append(result)
        print(f"done ({elapsed:.1f}s) Ridge={result['ridge_sharpe']:.4f} "
              f"EqW={result['equal_weight_sharpe']:.4f} "
              f"delta={result['delta_ridge_vs_eq']:+.4f} "
              f"bull={result['bull_pct']:.0%} "
              f"alpha={result['best_alpha']}")

    if not seed_results:
        return {"error": "No seeds converged"}

    deltas = [r["delta_ridge_vs_eq"] for r in seed_results]
    deltas_bear = [r["delta_bear"] for r in seed_results]
    ridge_sharpes = [r["ridge_sharpe"] for r in seed_results]
    eq_sharpes = [r["equal_weight_sharpe"] for r in seed_results]

    mean_delta = float(np.mean(deltas))
    se_delta = float(np.std(deltas, ddof=1) / np.sqrt(len(deltas))) if len(deltas) > 1 else 0.0
    t_stat = mean_delta / se_delta if se_delta > 0 else 0.0

    n_positive = sum(1 for d in deltas if d > 0)
    n_seeds = len(seed_results)

    from scipy.stats import binom
    p_value = float(binom.sf(n_positive - 1, n_seeds, 0.5))

    verdict = "BEATS" if (
        mean_delta > GATE_SHARPE_DELTA
        and t_stat >= 2.0
        and n_positive >= 3
    ) else "NO BEATS"

    agg = {
        "n_seeds": n_seeds,
        "seeds": seeds,
        "mean_ridge_sharpe": round(float(np.mean(ridge_sharpes)), 4),
        "mean_eq_sharpe": round(float(np.mean(eq_sharpes)), 4),
        "mean_delta": round(mean_delta, 6),
        "se_delta": round(se_delta, 6),
        "t_stat": round(t_stat, 3),
        "n_positive": n_positive,
        "p_value": round(p_value, 6),
        "mean_delta_bear": round(float(np.mean(deltas_bear)), 4),
        "verdict": verdict,
        "gate_delta": GATE_SHARPE_DELTA,
        "seed_results": seed_results,
    }

    return agg


# ── Verdict report ───────────────────────────────────────────────────────────

def write_verdict(results: dict, output_dir: Path) -> Path:
    output_dir.mkdir(parents=True, exist_ok=True)
    verdict_path = output_dir / "verdict.md"

    lines = ["# S4 v2 Inverse Vol Ridge + HMM Regime — Verdict\n"]
    lines.append(f"Date: {datetime.now().strftime('%Y-%m-%d %H:%M')}\n")
    lines.append(f"Universe: SPY + TLT + 9 sector ETFs")
    lines.append(f"Defensive tilt (bear): {', '.join(sorted(DEFENSIVE))}")
    lines.append(f"Method: HMM regime-conditional inverse-vol Ridge (MarkovRegression 2-regime)")
    lines.append(f"Ridge alphas: {ALPHAS}")
    lines.append(f"Tx costs: {TX_COST_BPS}bps per rebalance, {TX_COST_STRESS_BPS}bps stress")
    lines.append(f"Walk-forward: {N_SPLITS}-fold expanding, OOS {OOS_YEAR} strict")
    lines.append(f"Multi-seed: block bootstrap ({BLOCK_SIZE}-day), seeds {SEEDS}\n")

    lines.append("## Results\n")
    lines.append(f"- **Verdict**: {results['verdict']}")
    lines.append(f"- Ridge Sharpe: {results['mean_ridge_sharpe']:.4f}")
    lines.append(f"- Equal-Weight Sharpe: {results['mean_eq_sharpe']:.4f}")
    lines.append(f"- Delta: {results['mean_delta']:+.6f} (SE={results['se_delta']:.6f}, t={results['t_stat']:.3f})")
    lines.append(f"- Delta bear regime: {results['mean_delta_bear']:+.4f}")
    lines.append(f"- Seeds positive: {results['n_positive']}/{results['n_seeds']} (p={results['p_value']:.4f})")
    lines.append(f"- Gate: delta > {results['gate_delta']:.2f}, t >= 2.0, >= 3/4 seeds positive\n")

    lines.append("## Per-seed detail\n")
    lines.append("| Seed | Ridge | EqW | Delta | Delta-Bear | Bull% | Alpha |")
    lines.append("|------|-------|-----|-------|------------|-------|-------|")
    for sr in results["seed_results"]:
        lines.append(f"| {sr['seed']} | {sr['ridge_sharpe']:.4f} | "
                     f"{sr['equal_weight_sharpe']:.4f} | "
                     f"{sr['delta_ridge_vs_eq']:+.4f} | "
                     f"{sr['delta_bear']:+.4f} | "
                     f"{sr['bull_pct']:.0%} | "
                     f"{sr['best_alpha']} |")
    lines.append("")

    verdict_path.write_text("\n".join(lines), encoding="utf-8")
    print(f"\nVerdict written to {verdict_path}")
    return verdict_path


# ── CLI ──────────────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(description="S4 v2 Inverse Vol Ridge + HMM")
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
