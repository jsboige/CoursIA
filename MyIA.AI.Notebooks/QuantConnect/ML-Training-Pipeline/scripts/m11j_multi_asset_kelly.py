"""M11j Multi-Asset Kelly — portfolio Kelly on M11i winners (BTC/XRP/ADA/DOT).

Question
--------
M11i per-coin attribution identified 4 consistent winners: BTC, XRP, ADA, DOT.
Does a portfolio-level Kelly criterion using the correlation matrix of these
4 assets beat single-asset BTC Kelly?

Multi-asset Kelly formula (Brushin 2011):
    f* = Sigma^{-1} * mu
where mu = vector of expected excess returns, Sigma = covariance matrix of returns.

Capped per-asset at 0.5, global cap at 1.0 (sum of all weights).
Walk-forward rolling 60d window for mu and Sigma estimation.
HAR forecast provides sigma^2 estimate for each asset.

Output
------
- results/m11j_multi_asset_kelly/results.json
- results/m11j_multi_asset_kelly/m11j_results.csv

Env: system Python 3.13 (no conda). Reuses har_model, m11g infra.
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

import numpy as np
import pandas as pd

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

from har_model import walk_forward_har  # noqa: E402
from intraday_loader import hourly_log_returns, load_yf_intraday  # noqa: E402
from m11c_sharpe_test import ledoit_wolf_sharpe_diff_se  # noqa: E402
from m11g_fee_aware_kelly import (  # noqa: E402
    _binomial_pvalue_one_sided,
    _net_at_fee,
)
from realized_variance import daily_realized_variance  # noqa: E402

# M11i winners only
WINNERS = ["BTC-USD", "XRP-USD", "ADA-USD", "DOT-USD"]
HORIZONS = [1, 5, 10]
SEEDS = [0, 1, 7, 42]
KELLY_CAP_GLOBAL = 1.0
KELLY_CAP_PER_ASSET = 0.5
MU_WINDOW = 60
N_SPLITS = 5
REFIT_EVERY = 22
RESULTS_DIR = SCRIPT_DIR / "results" / "m11j_multi_asset_kelly"


def _load_one_coin(coin: str) -> pd.Series:
    # All coins via yfinance for consistent date range (2024-05 to 2026-05)
    return hourly_log_returns(load_yf_intraday(coin))


def _sharpe_ann(returns: np.ndarray) -> float:
    if len(returns) < 10:
        return float("nan")
    mu = float(np.mean(returns))
    sigma = float(np.std(returns, ddof=1))
    return (mu / sigma) * np.sqrt(365) if sigma > 1e-12 else float("nan")


def _max_drawdown(returns: np.ndarray) -> float:
    if len(returns) < 10:
        return float("nan")
    cum = np.cumprod(1 + returns)
    peak = np.maximum.accumulate(cum)
    dd = (cum - peak) / peak
    return float(np.min(dd))


def _prepare_coin_data(
    coin: str, horizon: int,
) -> tuple[pd.Series, pd.Series, pd.Series] | None:
    """Load coin data, run HAR walk-forward, return (daily_rets, forecasts, rv)."""
    hourly_rets = _load_one_coin(coin)
    if len(hourly_rets) < 1000:
        return None
    rv = daily_realized_variance(hourly_rets)
    if len(rv) < 300:
        return None
    try:
        har_out = walk_forward_har(
            rv, horizon=horizon, n_splits=N_SPLITS, refit_every=REFIT_EVERY
        )
    except (ValueError, Exception):
        return None

    har_fc = har_out["forecasts"]
    daily_rets = hourly_rets.groupby(hourly_rets.index.normalize()).sum().rename("r_daily")
    daily_rets.index = pd.DatetimeIndex(daily_rets.index).normalize()
    daily_rets = daily_rets.reindex(har_fc.index).dropna()
    har_fc = har_fc.reindex(daily_rets.index)
    if len(daily_rets) < 100:
        return None
    return daily_rets, har_fc, rv


def evaluate_one_combo(
    horizon: int,
    seed: int,
    fee_bps: float = 50,
) -> dict | None:
    """Run multi-asset Kelly vs single-asset BTC vs equal-weight for one combo."""
    np.random.seed(seed)

    # Load all 4 winners
    coin_data: dict[str, tuple[pd.Series, pd.Series]] = {}
    for coin in WINNERS:
        result = _prepare_coin_data(coin, horizon)
        if result is None:
            return None
        daily_rets, har_fc, _ = result
        coin_data[coin] = (daily_rets, har_fc)

    # Align all coins to common dates
    all_dates = None
    for coin in WINNERS:
        dates = coin_data[coin][0].index
        all_dates = dates if all_dates is None else all_dates.intersection(dates)
    if len(all_dates) < MU_WINDOW + 60:
        return None

    n_assets = len(WINNERS)
    n_days = len(all_dates)

    # Build return and forecast matrices (n_days x n_assets)
    ret_matrix = np.zeros((n_days, n_assets))
    fc_matrix = np.zeros((n_days, n_assets))
    for j, coin in enumerate(WINNERS):
        daily_rets, har_fc = coin_data[coin]
        ret_matrix[:, j] = daily_rets.reindex(all_dates).fillna(0).values
        fc_matrix[:, j] = har_fc.reindex(all_dates).fillna(0).values

    # Walk-forward multi-asset Kelly
    weights_multi = np.zeros((n_days, n_assets))
    weights_single = np.zeros((n_days, n_assets))
    weights_equal = np.zeros((n_days, n_assets))

    for t in range(MU_WINDOW, n_days):
        # Rolling window
        window_rets = ret_matrix[t - MU_WINDOW : t, :]
        mu_vec = np.mean(window_rets, axis=0)
        Sigma = np.cov(window_rets, rowvar=False)

        # Regularize Sigma (add small ridge for numerical stability)
        Sigma_reg = Sigma + 1e-8 * np.eye(n_assets)

        try:
            Sigma_inv = np.linalg.inv(Sigma_reg)
        except np.linalg.LinAlgError:
            # Fallback: equal weight
            weights_multi[t, :] = 1.0 / n_assets
            weights_single[t, 0] = 1.0  # BTC only
            weights_equal[t, :] = 1.0 / n_assets
            continue

        # Multi-asset Kelly: f* = Sigma^{-1} * mu
        f_star = Sigma_inv @ mu_vec

        # Clip per-asset
        f_star = np.clip(f_star, 0.0, KELLY_CAP_PER_ASSET)

        # Scale to global cap
        total_weight = np.sum(f_star)
        if total_weight > KELLY_CAP_GLOBAL:
            f_star = f_star * (KELLY_CAP_GLOBAL / total_weight)

        weights_multi[t, :] = f_star

        # Single-asset BTC Kelly (using HAR forecast)
        r_btc = ret_matrix[t - MU_WINDOW : t, 0]
        mu_btc = np.mean(r_btc)
        sigma2_btc = np.exp(fc_matrix[t, 0])
        f_btc = mu_btc / max(sigma2_btc, 1e-12)
        f_btc = np.clip(f_btc, 0.0, KELLY_CAP_GLOBAL)
        weights_single[t, 0] = f_btc

        # Equal weight
        weights_equal[t, :] = 1.0 / n_assets

    # Portfolio returns
    rets_aligned = ret_matrix[MU_WINDOW:, :]
    w_multi = weights_multi[MU_WINDOW:, :]
    w_single = weights_single[MU_WINDOW:, :]
    w_equal = weights_equal[MU_WINDOW:, :]

    # Portfolio PnL (sum of weighted individual returns)
    pnl_multi = np.sum(w_multi * rets_aligned, axis=1)
    pnl_single = np.sum(w_single * rets_aligned, axis=1)
    pnl_equal = np.sum(w_equal * rets_aligned, axis=1)

    # Buy-hold BTC
    pnl_bh = rets_aligned[:, 0]

    # Fee drag
    turnover_multi = np.sum(np.abs(np.diff(w_multi, axis=0, prepend=w_multi[0:1])), axis=1)
    turnover_single = np.sum(np.abs(np.diff(w_single, axis=0, prepend=w_single[0:1])), axis=1)
    turnover_equal = np.sum(np.abs(np.diff(w_equal, axis=0, prepend=w_equal[0:1])), axis=1)

    fee_mult = fee_bps / 10000.0
    net_multi = pnl_multi - fee_mult * turnover_multi
    net_single = pnl_single - fee_mult * turnover_single
    net_equal = pnl_equal - fee_mult * turnover_equal

    # Sharpe ratios
    sharpe_multi = _sharpe_ann(net_multi)
    sharpe_single = _sharpe_ann(net_single)
    sharpe_equal = _sharpe_ann(net_equal)
    sharpe_bh = _sharpe_ann(pnl_bh)

    # Max drawdown
    dd_multi = _max_drawdown(net_multi)
    dd_single = _max_drawdown(net_single)

    # LW2008 paired Sharpe-diff: multi vs single-asset BTC
    _, _, _, se_ms = ledoit_wolf_sharpe_diff_se(net_multi, net_single)
    delta_ms = sharpe_multi - sharpe_single
    t_ms = delta_ms / se_ms if isinstance(se_ms, float) and se_ms > 1e-12 else float("nan")

    # LW2008: multi vs equal-weight
    _, _, _, se_me = ledoit_wolf_sharpe_diff_se(net_multi, net_equal)
    delta_me = sharpe_multi - sharpe_equal
    t_me = delta_me / se_me if isinstance(se_me, float) and se_me > 1e-12 else float("nan")

    # Per-asset weights stats
    avg_weights = np.mean(w_multi, axis=0)
    avg_turnover = float(np.mean(turnover_multi))

    return {
        "horizon": horizon,
        "seed": seed,
        "fee_bps": fee_bps,
        "n_days": n_days - MU_WINDOW,
        "sharpe_multi": sharpe_multi,
        "sharpe_single_btc": sharpe_single,
        "sharpe_equal": sharpe_equal,
        "sharpe_bh": sharpe_bh,
        "delta_multi_vs_single": delta_ms,
        "delta_multi_vs_equal": delta_me,
        "lw_se_multi_vs_single": se_ms,
        "t_stat_multi_vs_single": t_ms,
        "lw_se_multi_vs_equal": se_me,
        "t_stat_multi_vs_equal": t_me,
        "dd_multi": dd_multi,
        "dd_single_btc": dd_single,
        "avg_turnover_daily": avg_turnover,
        "avg_weight_btc": float(avg_weights[0]),
        "avg_weight_xrp": float(avg_weights[1]),
        "avg_weight_ada": float(avg_weights[2]),
        "avg_weight_dot": float(avg_weights[3]),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="M11j Multi-Asset Kelly sweep")
    parser.add_argument("--dry-run", action="store_true", help="Run h=1 seed=0 fee=50 only")
    parser.add_argument(
        "--fee-bps-grid", type=float, nargs="+", default=[10.0, 50.0, 100.0],
    )
    args = parser.parse_args()

    RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    t0 = time.time()

    combos: list[dict] = []
    fee_grid = [50.0] if args.dry_run else args.fee_bps_grid
    total = len(HORIZONS) * len(SEEDS) * len(fee_grid)
    done = 0

    if args.dry_run:
        print("[DRY RUN] h=1 seed=0 fee=50 only")
        row = evaluate_one_combo(1, 0, 50.0)
        if row:
            combos.append(row)
            print(json.dumps(row, indent=2))
        return

    for h in HORIZONS:
        for seed in SEEDS:
            for fee in fee_grid:
                done += 1
                print(f"\n[{done}/{total}] h={h} seed={seed} fee={fee:.0f}bps", flush=True)
                row = evaluate_one_combo(h, seed, fee)
                if row is not None:
                    combos.append(row)
                else:
                    print(f"  SKIPPED (insufficient data)", flush=True)

    elapsed = time.time() - t0
    print(f"\n{'='*60}")
    print(f"M11j Multi-Asset Kelly sweep: {len(combos)}/{total} combos in {elapsed:.0f}s")

    # Aggregate sign-test: multi vs single-asset BTC
    n_combos = len(combos)
    n_multi_beats_single = sum(1 for r in combos if r["delta_multi_vs_single"] > 0)
    n_multi_beats_equal = sum(1 for r in combos if r["delta_multi_vs_equal"] > 0)
    median_delta_single = float(
        np.median([r["delta_multi_vs_single"] for r in combos])
    ) if combos else float("nan")
    median_delta_equal = float(
        np.median([r["delta_multi_vs_equal"] for r in combos])
    ) if combos else float("nan")
    p_sign_single = _binomial_pvalue_one_sided(n_multi_beats_single, n_combos)
    p_sign_equal = _binomial_pvalue_one_sided(n_multi_beats_equal, n_combos)

    print(f"\nMulti vs Single-Asset BTC:")
    print(f"  Beats: {n_multi_beats_single}/{n_combos} ({n_multi_beats_single/max(n_combos,1)*100:.1f}%)")
    print(f"  p-sign = {p_sign_single:.4f}")
    print(f"  median delta-Sharpe = {median_delta_single:+.4f}")

    print(f"\nMulti vs Equal-Weight:")
    print(f"  Beats: {n_multi_beats_equal}/{n_combos} ({n_multi_beats_equal/max(n_combos,1)*100:.1f}%)")
    print(f"  p-sign = {p_sign_equal:.4f}")
    print(f"  median delta-Sharpe = {median_delta_equal:+.4f}")

    # Fee sweep breakdown
    print(f"\nPer-fee breakdown:")
    for fee in fee_grid:
        fee_rows = [r for r in combos if r["fee_bps"] == fee]
        if not fee_rows:
            continue
        n_beats = sum(1 for r in fee_rows if r["delta_multi_vs_single"] > 0)
        med = float(np.median([r["delta_multi_vs_single"] for r in fee_rows]))
        p = _binomial_pvalue_one_sided(n_beats, len(fee_rows))
        print(f"  {fee:.0f}bps: beats={n_beats}/{len(fee_rows)} p={p:.4f} med_delta={med:+.4f}")

    # Verdict
    if p_sign_single < 0.05 and n_multi_beats_single / max(n_combos, 1) >= 0.60:
        verdict = "BEATS"
    elif p_sign_single < 0.10 and n_multi_beats_single / max(n_combos, 1) >= 0.55:
        verdict = "INCONCLUSIVE"
    else:
        verdict = "NO BEATS"

    print(f"\nVERDICT: {verdict} (p={p_sign_single:.4f})")

    # Save
    results = {
        "model": "M11j_Multi_Asset_Kelly",
        "assets": WINNERS,
        "kelly_cap_global": KELLY_CAP_GLOBAL,
        "kelly_cap_per_asset": KELLY_CAP_PER_ASSET,
        "mu_window": MU_WINDOW,
        "n_combos": n_combos,
        "n_multi_beats_single": n_multi_beats_single,
        "win_rate_vs_single": n_multi_beats_single / max(n_combos, 1),
        "p_sign_vs_single": p_sign_single,
        "median_delta_vs_single": median_delta_single,
        "p_sign_vs_equal": p_sign_equal,
        "median_delta_vs_equal": median_delta_equal,
        "verdict": verdict,
        "elapsed_s": elapsed,
        "combos": combos,
    }

    with open(RESULTS_DIR / "results.json", "w") as f:
        json.dump(results, f, indent=2, default=str)

    if combos:
        df = pd.DataFrame(combos)
        df.to_csv(RESULTS_DIR / "m11j_results.csv", index=False)
        print(f"\nSaved: {RESULTS_DIR / 'results.json'}")
        print(f"Saved: {RESULTS_DIR / 'm11j_results.csv'}")


if __name__ == "__main__":
    main()
