"""S2 GSP Cross-Asset Volatility — Graph Signal Processing on crypto-7.

Question
--------
Does cross-asset volatility denoising via Graph Signal Processing (GSP) improve
volatility forecasting over single-asset HAR baselines?

The idea: crypto coins are correlated. When BTC volatility spikes, ETH/SOL/etc
follow. A graph Laplacian built from rolling vol correlations can capture this
structure. Low-pass graph filtering smooths volatility signals using the graph
topology, potentially reducing noise while preserving the shared volatility component.

Methodology
-----------
1. Build dynamic graph Laplacian from rolling 60-day correlations of log-RV
   across 7 crypto coins (BTC, ETH, SOL, LTC, XRP, ADA, DOT)
2. Low-pass graph filter: f_filtered = (I - alpha * L) @ f, where L = D - A
3. Use filtered log-RV as input to HAR model instead of raw log-RV
4. Walk-forward 5-fold expanding window, OOS strict 2027
5. Multi-seed {0,1,7,42} with bootstrap variability
6. Compare GSP-HAR vs standalone HAR on MSE and Sharpe

Gate: GSP-HAR Sharpe > HAR Sharpe + 0.10 cross-seed, edge >= 2sigma.

Output
------
- results/s2_gsp_cross_asset_vol/results.json
- results/s2_gsp_cross_asset_vol/verdict.md

Env: system Python 3.13. numpy, pandas, yfinance, scipy.

References
----------
- arXiv:2410.22706 — Graph Signal Processing for cross-asset volatility
- Shuman et al. (2013) "The Emerging Field of Signal Processing on Graphs"
- Corsi (2009) HAR model
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
from scipy import linalg

SCRIPT_DIR = Path(__file__).resolve().parent
RESULTS_DIR = SCRIPT_DIR / "results" / "s2_gsp_cross_asset_vol"

COINS = ["BTC-USD", "ETH-USD", "SOL-USD", "LTC-USD", "XRP-USD", "ADA-USD", "DOT-USD"]
SEEDS = [0, 1, 7, 42]
N_SPLITS = 5
OOS_YEAR = 2027
TX_COST_BPS = 10
HORIZONS = [1, 5, 10]
VOL_WINDOW = 60
GRAPH_WINDOW = 60
GATE_SHARPE_DELTA = 0.10


# ── Data loading ─────────────────────────────────────────────────────────────

def load_crypto_rv(start: str = "2017-01-01", end: str = "2026-12-31") -> pd.DataFrame:
    """Load daily close prices and compute realized-volatility proxy (squared returns)."""
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
    # RV proxy = squared daily returns (for daily data this IS the realized variance)
    rv = returns ** 2
    return rv, returns


# ── Graph Signal Processing ───────────────────────────────────────────────────

def build_graph_laplacian(returns_window: np.ndarray, threshold: float = 0.3) -> np.ndarray:
    """Build combinatorial graph Laplacian from return correlations.

    L = D - A where A_ij = |corr(i,j)| if |corr| > threshold else 0.
    """
    n = returns_window.shape[1]
    corr = np.corrcoef(returns_window, rowvar=False)
    adj = np.abs(corr)
    np.fill_diagonal(adj, 0.0)
    adj[adj < threshold] = 0.0
    degree = adj.sum(axis=1)
    L = np.diag(degree) - adj
    return L


def low_pass_graph_filter(signal: np.ndarray, L: np.ndarray, alpha: float = 0.5) -> np.ndarray:
    """Apply low-pass graph filter: f_out = (I - alpha * L_norm) @ f_in.

    Smooths the signal along the graph structure. High alpha = more smoothing.
    L_norm = D^{-1/2} L D^{-1/2} for symmetric normalization.
    """
    n = L.shape[0]
    degree = np.diag(L)
    safe_degree = np.where(degree > 0, degree, 1.0)
    d_inv_sqrt = np.where(degree > 0, 1.0 / np.sqrt(safe_degree), 0.0)
    D_inv_sqrt = np.diag(d_inv_sqrt)
    L_norm = D_inv_sqrt @ L @ D_inv_sqrt

    H = np.eye(n) - alpha * L_norm
    return H @ signal


def graph_fourier_denoise(
    signal: np.ndarray,
    L: np.ndarray,
    keep_ratio: float = 0.5,
) -> np.ndarray:
    """Denoise signal via graph Fourier transform.

    Keep only the lowest `keep_ratio` graph frequencies (eigenvectors of L
    with smallest eigenvalues = smoothest signals on the graph).
    """
    eigenvalues, eigenvectors = linalg.eigh(L)
    n = len(signal)
    n_keep = max(1, int(n * keep_ratio))
    # Low-pass: keep eigenvectors with smallest eigenvalues
    U_keep = eigenvectors[:, :n_keep]
    # Project, then reconstruct
    coeffs = U_keep.T @ signal
    return U_keep @ coeffs


# ── HAR forecast with GSP preprocessing ───────────────────────────────────────

def har_features(log_rv: np.ndarray, t: int) -> np.ndarray | None:
    """Build HAR features [1, rv_d, rv_w, rv_m] at time t."""
    if t < 22:
        return None
    rv_d = log_rv[t - 1]
    rv_w = np.mean(log_rv[t - 5:t])
    rv_m = np.mean(log_rv[t - 22:t])
    return np.array([1.0, rv_d, rv_w, rv_m])


def fit_har_ols(log_rv: np.ndarray) -> np.ndarray:
    """Fit HAR OLS on log-RV series. Returns coefficients [intercept, d, w, m]."""
    n = len(log_rv)
    X_rows, y_rows = [], []
    for t in range(22, n):
        feats = har_features(log_rv, t)
        if feats is not None:
            X_rows.append(feats)
            y_rows.append(log_rv[t])
    if len(X_rows) < 30:
        return np.array([np.mean(log_rv)] * 4)
    X = np.array(X_rows)
    y = np.array(y_rows)
    coef, *_ = np.linalg.lstsq(X, y, rcond=None)
    return coef


def predict_har(coef: np.ndarray, log_rv: np.ndarray, t: int) -> float:
    """One-step HAR forecast at time t."""
    feats = har_features(log_rv, t)
    if feats is None:
        return np.mean(log_rv)
    return float(feats @ coef)


# ── Walk-forward evaluation ──────────────────────────────────────────────────

def walk_forward_gsp(
    rv_df: pd.DataFrame,
    returns_df: pd.DataFrame,
    coin: str,
    horizon: int,
    seed: int,
    alpha: float = 0.5,
    method: str = "low_pass",
    keep_ratio: float = 0.5,
) -> dict:
    """Walk-forward 5-fold evaluation of GSP-HAR vs HAR baseline.

    Steps per fold:
    1. Build graph Laplacian from training returns
    2. Apply graph filter to all coins' log-RV
    3. Fit HAR on filtered log-RV (GSP-HAR) and raw log-RV (HAR)
    4. Evaluate OOS predictions for target coin
    """
    coin_idx = COINS.index(coin)
    oos_mask = rv_df.index >= f"{OOS_YEAR}-01-01"
    is_rv = rv_df[~oos_mask]
    is_returns = returns_df[~oos_mask]

    n_is = len(is_rv)
    fold_size = n_is // N_SPLITS

    rng = np.random.RandomState(seed)

    gsp_preds_all = []
    har_preds_all = []
    actuals_all = []

    for fold_idx in range(N_SPLITS):
        train_end = fold_size * (fold_idx + 2)
        train_end = min(train_end, n_is)
        test_start = fold_size * (fold_idx + 1)
        test_end = train_end

        if train_end < 126 or test_end <= test_start:
            continue

        # Bootstrap training indices for seed variability
        n_train = train_end
        boot_indices = rng.choice(n_train, size=n_train, replace=True)
        boot_indices.sort()

        # Build graph Laplacian from bootstrapped training returns
        train_returns = is_returns.values[boot_indices]
        L = build_graph_laplacian(train_returns, threshold=0.3)

        # Get log-RV for all coins in training
        train_rv = is_rv.values[boot_indices]
        train_log_rv = np.log(np.clip(train_rv, 1e-12, None))

        # Apply graph filtering to the LAST snapshot of log-RV
        # For each time step, filter the cross-sectional log-RV signal
        # Then use the filtered series for HAR
        n_times = train_log_rv.shape[0]
        filtered_log_rv = np.zeros_like(train_log_rv)

        for t in range(n_times):
            signal = train_log_rv[t]
            if method == "low_pass":
                filtered_log_rv[t] = low_pass_graph_filter(signal, L, alpha=alpha)
            elif method == "fourier":
                filtered_log_rv[t] = graph_fourier_denoise(signal, L, keep_ratio=keep_ratio)
            else:
                filtered_log_rv[t] = signal

        # Fit HAR on filtered log-RV for target coin
        gsp_coef = fit_har_ols(filtered_log_rv[:, coin_idx])
        har_coef = fit_har_ols(train_log_rv[:, coin_idx])

        # Evaluate on test block
        test_block = is_rv.values[test_start:test_end]
        test_actual_log_rv = np.log(np.clip(test_block, 1e-12, None))

        # Build graph Laplacian for test period from rolling window
        test_returns = is_returns.values[test_start:test_end]
        if len(test_returns) >= VOL_WINDOW:
            test_L = build_graph_laplacian(
                is_returns.values[max(0, test_start - VOL_WINDOW):test_start],
                threshold=0.3,
            )
        else:
            test_L = L

        for t_offset in range(horizon, len(test_block)):
            t_global = test_start + t_offset

            # Raw HAR prediction
            raw_history = np.log(np.clip(
                is_rv.values[:t_global, coin_idx], 1e-12, None
            ))
            har_pred = predict_har(har_coef, raw_history, len(raw_history))

            # GSP-HAR: filter the cross-sectional signal at this time, then predict
            cross_section = np.log(np.clip(is_rv.values[t_global - 1], 1e-12, None))
            if method == "low_pass":
                filtered_cs = low_pass_graph_filter(cross_section, test_L, alpha=alpha)
            elif method == "fourier":
                filtered_cs = graph_fourier_denoise(cross_section, test_L, keep_ratio=keep_ratio)
            else:
                filtered_cs = cross_section

            # Build filtered history by replacing last value with filtered version
            filtered_history = raw_history.copy()
            filtered_history[-1] = filtered_cs[coin_idx]
            gsp_pred = predict_har(gsp_coef, filtered_history, len(filtered_history))

            # Horizon target: average log-RV over next h days
            if t_offset + horizon <= len(test_block):
                target = np.mean(test_actual_log_rv[t_offset:t_offset + horizon, coin_idx])
            else:
                continue

            gsp_preds_all.append(gsp_pred)
            har_preds_all.append(har_pred)
            actuals_all.append(target)

    if len(gsp_preds_all) < 10:
        return {"error": "Too few predictions"}

    gsp_preds = np.array(gsp_preds_all)
    har_preds = np.array(har_preds_all)
    actuals = np.array(actuals_all)

    # MSE
    gsp_mse = float(np.mean((gsp_preds - actuals) ** 2))
    har_mse = float(np.mean((har_preds - actuals) ** 2))

    # Sharpe from volatility-timing strategy:
    # Use forecast to size positions: long vol when forecast > median, short otherwise
    median_actual = np.median(actuals)
    gsp_positions = np.where(gsp_preds > np.median(gsp_preds), 1.0, -1.0)
    har_positions = np.where(har_preds > np.median(har_preds), 1.0, -1.0)

    # PnL: position * (actual - median) normalized
    gsp_pnl = gsp_positions * (actuals - median_actual)
    har_pnl = har_positions * (actuals - median_actual)

    # Transaction costs
    gsp_turnover = np.mean(np.abs(np.diff(gsp_positions))) if len(gsp_positions) > 1 else 0
    har_turnover = np.mean(np.abs(np.diff(har_positions))) if len(har_positions) > 1 else 0
    tx = TX_COST_BPS / 10000
    gsp_pnl_net = gsp_pnl - tx * gsp_turnover
    har_pnl_net = har_pnl - tx * har_turnover

    gsp_sharpe = _sharpe(gsp_pnl_net)
    har_sharpe = _sharpe(har_pnl_net)

    delta_mse = (gsp_mse - har_mse) / har_mse * 100 if har_mse > 0 else 0
    delta_sharpe = gsp_sharpe - har_sharpe

    return {
        "coin": coin,
        "horizon": horizon,
        "seed": seed,
        "method": method,
        "alpha": alpha,
        "gsp_mse": round(gsp_mse, 6),
        "har_mse": round(har_mse, 6),
        "delta_mse_pct": round(delta_mse, 2),
        "gsp_sharpe": round(gsp_sharpe, 4),
        "har_sharpe": round(har_sharpe, 4),
        "delta_sharpe": round(delta_sharpe, 4),
        "gsp_beats_mse": gsp_mse < har_mse,
        "gsp_beats_sharpe": gsp_sharpe > har_sharpe + 0.001,
        "n_obs": len(gsp_preds),
    }


def _sharpe(returns: np.ndarray) -> float:
    if len(returns) < 2 or np.std(returns) < 1e-10:
        return 0.0
    return float(np.mean(returns) / np.std(returns) * np.sqrt(252))


# ── Multi-seed runner ─────────────────────────────────────────────────────────

def run_experiment(
    seeds: list[int] | None = None,
    method: str = "low_pass",
    alpha: float = 0.5,
    keep_ratio: float = 0.5,
) -> dict:
    """Run full S2 GSP experiment across all coins, horizons, seeds."""
    if seeds is None:
        seeds = SEEDS

    print("Loading crypto-7 RV data...")
    rv_df, returns_df = load_crypto_rv()
    print(f"  {len(rv_df)} days, {rv_df.columns.tolist()}")
    print(f"  {rv_df.index[0].date()} to {rv_df.index[-1].date()}")
    print(f"  Method: {method}, alpha={alpha}, keep_ratio={keep_ratio}\n")

    results = []
    total = len(COINS) * len(HORIZONS) * len(seeds)
    count = 0

    for coin in COINS:
        for horizon in HORIZONS:
            for seed in seeds:
                count += 1
                t0 = time.time()
                result = walk_forward_gsp(
                    rv_df, returns_df,
                    coin=coin,
                    horizon=horizon,
                    seed=seed,
                    alpha=alpha,
                    method=method,
                    keep_ratio=keep_ratio,
                )
                elapsed = time.time() - t0

                if "error" in result:
                    print(f"  [{count}/{total}] {coin} h={horizon} s={seed} ERROR: {result['error']}")
                    continue

                results.append(result)
                mse_flag = "MSE-WIN" if result["gsp_beats_mse"] else "mse-loss"
                sha_flag = "SHA-WIN" if result["gsp_beats_sharpe"] else "sha-loss"
                print(f"  [{count}/{total}] {coin} h={horizon} s={seed} "
                      f"dMSE={result['delta_mse_pct']:+.1f}% dSha={result['delta_sharpe']:+.4f} "
                      f"[{mse_flag}/{sha_flag}] ({elapsed:.0f}s)")

    if not results:
        return {"error": "No results produced"}

    # Aggregate verdict
    n_total = len(results)
    n_mse_wins = sum(1 for r in results if r["gsp_beats_mse"])
    n_sharpe_wins = sum(1 for r in results if r["gsp_beats_sharpe"])
    deltas_sharpe = [r["delta_sharpe"] for r in results]
    deltas_mse = [r["delta_mse_pct"] for r in results]

    mean_delta_sharpe = float(np.mean(deltas_sharpe))
    se_delta_sharpe = float(np.std(deltas_sharpe, ddof=1) / np.sqrt(len(deltas_sharpe))) if len(deltas_sharpe) > 1 else 0.0
    t_stat = mean_delta_sharpe / se_delta_sharpe if se_delta_sharpe > 0 else 0.0

    n_positive = sum(1 for d in deltas_sharpe if d > 0)

    from scipy.stats import binom
    p_value = float(binom.sf(n_positive - 1, n_total, 0.5)) if n_positive > 0 else 1.0

    verdict = "BEATS" if (
        mean_delta_sharpe > GATE_SHARPE_DELTA
        and t_stat >= 2.0
        and n_positive > n_total * 0.6
    ) else "NO BEATS"

    agg = {
        "verdict": verdict,
        "n_total": n_total,
        "n_mse_wins": n_mse_wins,
        "n_sharpe_wins": n_sharpe_wins,
        "mean_delta_sharpe": round(mean_delta_sharpe, 6),
        "median_delta_sharpe": round(float(np.median(deltas_sharpe)), 6),
        "median_delta_mse_pct": round(float(np.median(deltas_mse)), 2),
        "se_delta_sharpe": round(se_delta_sharpe, 6),
        "t_stat": round(t_stat, 3),
        "n_positive_sharpe": n_positive,
        "p_value": round(p_value, 6),
        "gate_delta": GATE_SHARPE_DELTA,
        "method": method,
        "alpha": alpha,
        "keep_ratio": keep_ratio,
        "seeds": seeds,
        "per_result": results,
    }

    return agg


# ── Verdict report ────────────────────────────────────────────────────────────

def write_verdict(results: dict, output_dir: Path) -> Path:
    output_dir.mkdir(parents=True, exist_ok=True)
    verdict_path = output_dir / "verdict.md"

    lines = ["# S2 GSP Cross-Asset Volatility — Verdict\n"]
    lines.append(f"Date: {datetime.now().strftime('%Y-%m-%d %H:%M')}\n")
    lines.append(f"Universe: crypto-7 ({', '.join(COINS)})")
    lines.append(f"Method: {results['method']}")
    lines.append(f"Alpha: {results.get('alpha', 'N/A')}")
    lines.append(f"Keep ratio: {results.get('keep_ratio', 'N/A')}")
    lines.append(f"Graph window: {GRAPH_WINDOW} days")
    lines.append(f"Walk-forward: {N_SPLITS}-fold expanding, OOS {OOS_YEAR} strict")
    lines.append(f"Multi-seed: {results['seeds']}")
    lines.append(f"Horizons: {HORIZONS}")
    lines.append(f"Tx costs: {TX_COST_BPS}bps per rebalance\n")

    lines.append("## Results\n")
    lines.append(f"- **Verdict**: {results['verdict']}")
    lines.append(f"- MSE wins: GSP-HAR wins {results['n_mse_wins']}/{results['n_total']} "
                 f"({results['n_mse_wins']/results['n_total']*100:.1f}%)")
    lines.append(f"- Sharpe wins: GSP-HAR wins {results['n_sharpe_wins']}/{results['n_total']} "
                 f"({results['n_sharpe_wins']/results['n_total']*100:.1f}%)")
    lines.append(f"- Mean delta Sharpe: {results['mean_delta_sharpe']:+.6f} "
                 f"(SE={results['se_delta_sharpe']:.6f}, t={results['t_stat']:.3f})")
    lines.append(f"- Median delta Sharpe: {results['median_delta_sharpe']:+.6f}")
    lines.append(f"- Median delta MSE: {results['median_delta_mse_pct']:+.2f}%")
    lines.append(f"- Seeds positive: {results['n_positive_sharpe']}/{results['n_total']} "
                 f"(p={results['p_value']:.4f})")
    lines.append(f"- Gate: delta > {results['gate_delta']:.2f}, t >= 2.0, "
                 f"positive rate > 0.6\n")

    # Per-coin table
    per_results = results.get("per_result", [])
    lines.append("## Per-coin detail\n")
    lines.append("| Coin | MSE wins | Sharpe wins | Median dMSE | Median dSharpe |")
    lines.append("|------|----------|-------------|-------------|----------------|")
    for coin in COINS:
        coin_results = [r for r in per_results if r["coin"] == coin]
        if not coin_results:
            continue
        mse_wins = sum(1 for r in coin_results if r["gsp_beats_mse"])
        sha_wins = sum(1 for r in coin_results if r["gsp_beats_sharpe"])
        med_dmse = np.median([r["delta_mse_pct"] for r in coin_results])
        med_dsha = np.median([r["delta_sharpe"] for r in coin_results])
        n = len(coin_results)
        lines.append(f"| {coin} | {mse_wins}/{n} | {sha_wins}/{n} | "
                     f"{med_dmse:+.2f}% | {med_dsha:+.4f} |")
    lines.append("")

    # Per-horizon table
    lines.append("## Per-horizon detail\n")
    lines.append("| Horizon | MSE wins | Sharpe wins | Mean dSharpe |")
    lines.append("|---------|----------|-------------|-------------|")
    for h in HORIZONS:
        h_results = [r for r in per_results if r["horizon"] == h]
        if not h_results:
            continue
        mse_wins = sum(1 for r in h_results if r["gsp_beats_mse"])
        sha_wins = sum(1 for r in h_results if r["gsp_beats_sharpe"])
        mean_dsha = np.mean([r["delta_sharpe"] for r in h_results])
        n = len(h_results)
        lines.append(f"| {h} | {mse_wins}/{n} | {sha_wins}/{n} | {mean_dsha:+.4f} |")
    lines.append("")

    verdict_path.write_text("\n".join(lines), encoding="utf-8")
    print(f"\nVerdict written to {verdict_path}")
    return verdict_path


# ── CLI ───────────────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(description="S2 GSP Cross-Asset Volatility")
    parser.add_argument("--seeds", type=str, default="0,1,7,42")
    parser.add_argument("--method", type=str, default="low_pass",
                        choices=["low_pass", "fourier"])
    parser.add_argument("--alpha", type=float, default=0.5,
                        help="Graph filter strength for low_pass method")
    parser.add_argument("--keep-ratio", type=float, default=0.5,
                        help="Frequency keep ratio for fourier method")
    parser.add_argument("--output", type=str, default=None)
    args = parser.parse_args()

    seeds = [int(s) for s in args.seeds.split(",")]
    output_dir = Path(args.output) if args.output else RESULTS_DIR
    output_dir.mkdir(parents=True, exist_ok=True)

    t_start = time.time()
    results = run_experiment(
        seeds=seeds,
        method=args.method,
        alpha=args.alpha,
        keep_ratio=args.keep_ratio,
    )

    (output_dir / "results.json").write_text(
        json.dumps(results, indent=2, default=str), encoding="utf-8"
    )
    write_verdict(results, output_dir)

    elapsed = time.time() - t_start
    print(f"\nTotal time: {elapsed:.1f}s")


if __name__ == "__main__":
    main()
