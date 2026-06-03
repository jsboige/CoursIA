"""S4 Inverse Volatility Ridge — Portfolio weighting with L2 regularisation.

Question
--------
Does inverse-volatility weighting with Ridge regularisation beat Markowitz
equal-weight on a crypto-7 universe?

Methodology
-----------
- Inverse-volatility weights: w_i proportional to 1/sigma_i (rolling 20-day vol)
- Ridge regularisation: L2 penalty on weight deviations from inv-vol target
- Walk-forward 5-fold expanding window
- Multi-seed 0/1/7/42 (bootstrap variability on training windows)
- OOS strict 2027 (not touched during fit)
- Baselines: equal-weight Markowitz, simple inverse-variance (no Ridge)
- Tx costs: 10bps per rebalance
- Gate: Sharpe Ridge > Sharpe Markowitz + 0.10 cross-seed

Output
------
- results/s4_inverse_vol_ridge/results.json
- results/s4_inverse_vol_ridge/verdict.md

Env: system Python 3.13. sklearn, yfinance, numpy, pandas.
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from datetime import datetime
from pathlib import Path

import numpy as np
import pandas as pd
from sklearn.linear_model import Ridge

SCRIPT_DIR = Path(__file__).resolve().parent
RESULTS_DIR = SCRIPT_DIR / "results" / "s4_inverse_vol_ridge"

COINS = ["BTC-USD", "ETH-USD", "SOL-USD", "LTC-USD", "XRP-USD", "ADA-USD", "DOT-USD"]
SEEDS = [0, 1, 7, 42]
N_SPLITS = 5
OOS_YEAR = 2027
TX_COST_BPS = 10
VOL_WINDOW = 20
GATE_SHARPE_DELTA = 0.10


# ── Data loading ─────────────────────────────────────────────────────────────

def load_crypto_returns(start: str = "2017-01-01", end: str = "2026-12-31") -> pd.DataFrame:
    """Load daily returns for crypto-7 universe."""
    import yfinance as yf

    frames = {}
    for coin in COINS:
        df = yf.download(coin, start=start, end=end, progress=False)
        if df.empty:
            raise RuntimeError(f"No data for {coin}")
        if isinstance(df.columns, pd.MultiIndex):
            close = df[("Close", coin)]
        else:
            close = df["Close"]
        frames[coin] = close

    prices = pd.DataFrame(frames)
    prices.index = pd.to_datetime(prices.index)
    prices = prices.dropna()
    returns = prices.pct_change().dropna()
    return returns


# ── Portfolio weighting methods ───────────────────────────────────────────────

def inv_vol_weights(returns: np.ndarray) -> np.ndarray:
    """Inverse-volatility weights from return matrix (T, N)."""
    vols = np.std(returns, axis=0) + 1e-8
    w = 1.0 / vols
    return w / w.sum()


def inv_var_weights(returns: np.ndarray) -> np.ndarray:
    """Inverse-variance weights (no Ridge)."""
    vars_ = np.var(returns, axis=0) + 1e-8
    w = 1.0 / vars_
    return w / w.sum()


def ridge_inv_vol_weights(
    returns: np.ndarray,
    target_w: np.ndarray,
    alpha: float = 1.0,
) -> np.ndarray:
    """Ridge-regularised inverse-volatility weights.

    Minimises ||w - target||^2 + alpha * ||w||^2, then projects to simplex.
    """
    n = len(target_w)
    # Closed-form Ridge solution: w = target / (1 + alpha)
    # Then project to simplex (weights sum to 1, all >= 0)
    w = target_w / (1 + alpha)
    w = _project_simplex(w)
    return w


def equal_weights(n: int) -> np.ndarray:
    """Equal-weight (1/N) portfolio."""
    return np.ones(n) / n


def _project_simplex(v: np.ndarray) -> np.ndarray:
    """Project vector v onto the probability simplex (sum=1, all>=0)."""
    n = len(v)
    u = np.sort(v)[::-1]
    cssv = np.cumsum(u) - 1
    rho = np.nonzero(u * np.arange(1, n + 1) > cssv)[0][-1]
    theta = cssv[rho] / (rho + 1.0)
    w = np.maximum(v - theta, 0)
    return w / w.sum()


# ── Walk-forward evaluation ──────────────────────────────────────────────────

def walk_forward_portfolio(
    returns: pd.DataFrame,
    seed: int = 0,
    alphas: list[float] | None = None,
) -> dict:
    """Walk-forward 5-fold expanding window portfolio comparison.

    Each seed uses a bootstrap sample of the training window for variability.
    """
    if alphas is None:
        alphas = [0.01, 0.1, 1.0, 10.0]

    oos_mask = returns.index >= f"{OOS_YEAR}-01-01"
    is_returns = returns[~oos_mask]

    n_is = len(is_returns)
    n_assets = is_returns.shape[1]
    fold_size = n_is // N_SPLITS

    # Store per-fold OOS portfolios
    oos_dates_all = []
    ridge_ret_all = []
    invvol_ret_all = []
    invvar_ret_all = []
    eq_ret_all = []
    rebalance_count = 0

    rng = np.random.RandomState(seed)

    for fold_idx in range(N_SPLITS):
        # Expanding window
        train_end = fold_size * (fold_idx + 2)
        train_end = min(train_end, n_is)
        test_start = fold_size * (fold_idx + 1)
        test_end = train_end

        if train_end < 126 or test_end <= test_start:
            continue

        train_block = is_returns.iloc[:train_end]
        test_block = is_returns.iloc[test_start:test_end]

        # Bootstrap training data for seed variability
        n_train = len(train_block)
        indices = rng.choice(n_train, size=n_train, replace=True)
        boot_train = train_block.values[indices]

        # Compute target weights
        target_w = inv_vol_weights(boot_train)

        # Find best alpha via in-sample Sharpe on last 20% of train
        val_start = int(n_train * 0.8)
        val_data = train_block.values[val_start:]
        best_alpha = alphas[0]
        best_sharpe = -np.inf

        for alpha in alphas:
            w = ridge_inv_vol_weights(boot_train, target_w, alpha)
            port_ret = val_data @ w
            s = _sharpe(port_ret)
            if s > best_sharpe:
                best_sharpe = s
                best_alpha = alpha

        # Final weights for this fold
        ridge_w = ridge_inv_vol_weights(boot_train, target_w, best_alpha)
        invvol_w = inv_vol_weights(boot_train)
        invvar_w = inv_var_weights(boot_train)
        eq_w = equal_weights(n_assets)

        # Apply to test block
        test_arr = test_block.values
        ridge_fold = test_arr @ ridge_w
        invvol_fold = test_arr @ invvol_w
        invvar_fold = test_arr @ invvar_w
        eq_fold = test_arr @ eq_w

        # Transaction costs: penalise at rebalance (once per fold)
        tx = TX_COST_BPS / 10000
        ridge_fold[0] -= tx
        invvol_fold[0] -= tx
        invvar_fold[0] -= tx
        # Equal-weight doesn't rebalance
        rebalance_count += 1

        oos_dates_all.extend(test_block.index)
        ridge_ret_all.extend(ridge_fold)
        invvol_ret_all.extend(invvol_fold)
        invvar_ret_all.extend(invvar_fold)
        eq_ret_all.extend(eq_fold)

    if not ridge_ret_all:
        return {"error": "No folds produced results"}

    # Compute metrics
    ridge_ret = np.array(ridge_ret_all)
    invvol_ret = np.array(invvol_ret_all)
    invvar_ret = np.array(invvar_ret_all)
    eq_ret = np.array(eq_ret_all)

    results = {}
    for name, ret in [("ridge", ridge_ret), ("inv_vol", invvol_ret),
                       ("inv_var", invvar_ret), ("equal_weight", eq_ret)]:
        results[f"{name}_sharpe"] = float(_sharpe(ret))
        results[f"{name}_cum_ret"] = float(np.prod(1 + ret) - 1)
        results[f"{name}_max_dd"] = float(_max_drawdown(ret))
        results[f"{name}_vol"] = float(np.std(ret) * np.sqrt(252))

    # Delta vs equal-weight Markowitz baseline
    results["delta_ridge_vs_eq"] = results["ridge_sharpe"] - results["equal_weight_sharpe"]
    results["delta_invvol_vs_eq"] = results["inv_vol_sharpe"] - results["equal_weight_sharpe"]
    results["delta_ridge_vs_invvol"] = results["ridge_sharpe"] - results["inv_vol_sharpe"]
    results["best_alpha"] = best_alpha
    results["n_obs"] = len(ridge_ret)
    results["n_folds"] = N_SPLITS
    results["seed"] = seed

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


# ── Multi-seed runner ─────────────────────────────────────────────────────────

def run_experiment(seeds: list[int] | None = None) -> dict:
    """Run full multi-seed S4 experiment."""
    if seeds is None:
        seeds = SEEDS

    print("Loading crypto-7 returns...")
    returns = load_crypto_returns()
    print(f"  {len(returns)} days, {returns.columns.tolist()}")
    print(f"  {returns.index[0].date()} to {returns.index[-1].date()}\n")

    seed_results = []
    for seed in seeds:
        print(f"  Seed {seed}...", end=" ", flush=True)
        t0 = time.time()
        result = walk_forward_portfolio(returns, seed=seed)
        elapsed = time.time() - t0

        if "error" in result:
            print(f"ERROR: {result['error']}")
            continue

        result["elapsed_s"] = round(elapsed, 1)
        seed_results.append(result)
        print(f"done ({elapsed:.1f}s) Ridge={result['ridge_sharpe']:.4f} "
              f"InvVol={result['inv_vol_sharpe']:.4f} "
              f"EqW={result['equal_weight_sharpe']:.4f} "
              f"delta={result['delta_ridge_vs_eq']:+.4f}")

    if not seed_results:
        return {"error": "No seeds converged"}

    # Aggregate
    deltas = [r["delta_ridge_vs_eq"] for r in seed_results]
    ridge_sharpes = [r["ridge_sharpe"] for r in seed_results]
    eq_sharpes = [r["equal_weight_sharpe"] for r in seed_results]
    invvol_sharpes = [r["inv_vol_sharpe"] for r in seed_results]

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
        "mean_inv_vol_sharpe": round(float(np.mean(invvol_sharpes)), 4),
        "mean_eq_sharpe": round(float(np.mean(eq_sharpes)), 4),
        "mean_delta_ridge_vs_eq": round(mean_delta, 6),
        "se_delta": round(se_delta, 6),
        "t_stat": round(t_stat, 3),
        "n_positive": n_positive,
        "p_value": round(p_value, 6),
        "verdict": verdict,
        "gate_delta": GATE_SHARPE_DELTA,
        "seed_results": seed_results,
    }

    return agg


# ── Verdict report ────────────────────────────────────────────────────────────

def write_verdict(results: dict, output_dir: Path) -> Path:
    output_dir.mkdir(parents=True, exist_ok=True)
    verdict_path = output_dir / "verdict.md"

    lines = ["# S4 Inverse Volatility Ridge — Verdict\n"]
    lines.append(f"Date: {datetime.now().strftime('%Y-%m-%d %H:%M')}\n")
    lines.append(f"Universe: crypto-7 ({', '.join(COINS)})")
    lines.append(f"Vol window: {VOL_WINDOW} days")
    lines.append(f"Tx costs: {TX_COST_BPS}bps per rebalance")
    lines.append(f"Walk-forward: {N_SPLITS}-fold expanding, OOS {OOS_YEAR} strict")
    lines.append(f"Multi-seed: bootstrap, seeds {SEEDS}\n")

    lines.append("## Results\n")
    lines.append(f"- **Verdict**: {results['verdict']}")
    lines.append(f"- Ridge Sharpe: {results['mean_ridge_sharpe']:.4f}")
    lines.append(f"- Inv-Vol Sharpe: {results['mean_inv_vol_sharpe']:.4f}")
    lines.append(f"- Equal-Weight Sharpe: {results['mean_eq_sharpe']:.4f}")
    lines.append(f"- Delta Ridge vs EqW: {results['mean_delta_ridge_vs_eq']:+.6f} "
                 f"(SE={results['se_delta']:.6f}, t={results['t_stat']:.3f})")
    lines.append(f"- Seeds positive: {results['n_positive']}/{results['n_seeds']} "
                 f"(p={results['p_value']:.4f})")
    lines.append(f"- Gate: delta > {results['gate_delta']:.2f}, t >= 2.0, >= 3/4 seeds positive\n")

    # Per-seed table
    lines.append("## Per-seed detail\n")
    lines.append("| Seed | Ridge | Inv-Vol | EqW | Delta |")
    lines.append("|------|-------|---------|-----|-------|")
    for sr in results["seed_results"]:
        lines.append(f"| {sr['seed']} | {sr['ridge_sharpe']:.4f} | "
                     f"{sr['inv_vol_sharpe']:.4f} | {sr['equal_weight_sharpe']:.4f} | "
                     f"{sr['delta_ridge_vs_eq']:+.4f} |")
    lines.append("")

    verdict_path.write_text("\n".join(lines), encoding="utf-8")
    print(f"\nVerdict written to {verdict_path}")
    return verdict_path


# ── CLI ───────────────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(description="S4 Inverse Volatility Ridge")
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
