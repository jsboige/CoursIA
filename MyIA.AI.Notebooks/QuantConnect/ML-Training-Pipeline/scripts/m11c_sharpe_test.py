"""M11c Diebold-Mariano-equivalent significance test on M11 Sharpe deltas.

Converts the per-combo "kelly_har_muXXX BEATS buy_hold by Δ Sharpe" claims of
M11a (h=1/5/10) and M11b (h=15/20) into statistically defensible
"BEATS at p<0.05" claims per CLAUDE.md G.2 (multi-seed + significance).

Primary test : **Ledoit-Wolf 2008** closed-form paired Sharpe-difference SE.

  Ledoit & Wolf (2008) "Robust performance hypothesis testing with the Sharpe
  ratio", Journal of Empirical Finance 15(5).

  For two paired daily return streams r_a (active) and r_b (baseline) of length
  T, the Sharpe ratio difference \\hat S_a - \\hat S_b is asymptotically normal
  with variance
      V = (1/T) * grad' * Omega * grad
  where Omega is the HAC long-run covariance of theta_t =
  (r_a, r_a^2 - mu_a^2, r_b, r_b^2 - mu_b^2) and the gradient comes from
  delta-method on (mu, sigma) -> mu/sigma. We use the centred form (r - mu,
  (r-mu)^2 - sigma^2) and a Newey-West HAC with q = floor(T^(1/4)) lags
  (standard auto rule, matches Ledoit-Wolf paper Section 3.2).

Bootstrap sanity-check : stationary bootstrap of paired returns, B=1000,
block-length 5 (typical for daily crypto, ~weekly autocorr scale). Done on
the strongest 3-5 combos only — fast even at B=1000.

Inputs
------
- `results/m11a_har_kelly_simulation/results.json` (existing, 21 combos × 8 strats)
- `results/m11b_har_kelly_long_horizons/results.json` (existing, 14 × 8)

We re-derive the per-period net returns by replaying the simulation locally
(deterministic OLS HAR + Kelly logic from `simulate_har_kelly.py`), so the
shared script is NOT modified.

Outputs
-------
- `results/m11c_dm_test/dm_results.json`
- `results/m11c_dm_test/dm_results.csv`
- stdout summary

Usage
-----
    python -u scripts/m11c_sharpe_test.py \\
        --strategies kelly_har_mu60 kelly_har_mu250 \\
        --bootstrap-top 5

Env : `coursia-ml-training` (numpy 2.x, pandas 3.x, scipy 1.17). No extra deps.
"""

from __future__ import annotations

import argparse
import csv
import json
import sys
import time
from pathlib import Path

import numpy as np
import pandas as pd

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

# Re-use the M11a/M11b machinery
from garch_rolling_baseline import naive_constant_baseline  # noqa: E402
from har_model import walk_forward_har  # noqa: E402
from intraday_loader import (  # noqa: E402
    hourly_log_returns,
    load_binance_eth,
    load_bitstamp_btc,
    load_yf_intraday,
)
from realized_variance import daily_realized_variance  # noqa: E402


# ---------------------------------------------------------------------------
# Ledoit-Wolf 2008 paired Sharpe difference SE
# ---------------------------------------------------------------------------

def _hac_cov(z: np.ndarray, q: int) -> np.ndarray:
    """Newey-West HAC covariance matrix of a (T, k) zero-mean series z.

    Bartlett kernel, truncation lag q. Returns a (k, k) symmetric PSD matrix.
    """
    t, k = z.shape
    z = z - z.mean(axis=0, keepdims=True)
    gamma0 = (z.T @ z) / t
    omega = gamma0.copy()
    for h in range(1, q + 1):
        w = 1.0 - h / (q + 1.0)
        gh = (z[h:].T @ z[:-h]) / t
        omega += w * (gh + gh.T)
    return omega


def ledoit_wolf_sharpe_diff_se(
    r_a: np.ndarray, r_b: np.ndarray, q: int | None = None
) -> tuple[float, float, float, float]:
    """Ledoit-Wolf 2008 paired Sharpe-difference asymptotic SE.

    Parameters
    ----------
    r_a, r_b : (T,) ndarrays — paired daily net returns (same index).
    q : HAC truncation lag. None -> floor(T^(1/4)).

    Returns
    -------
    (sharpe_a, sharpe_b, sharpe_diff, se_diff)  — sharpes are daily (not annual).

    Notes
    -----
    Daily Sharpe = mu/sigma. To get annualised Sharpe, multiply by sqrt(252).
    The SE on the *daily* Sharpe difference scales the same way, so the
    *t-statistic* sharpe_diff/se_diff is invariant to the annualisation
    factor — which is what we use for p-values.
    """
    r_a = np.asarray(r_a, dtype=float).ravel()
    r_b = np.asarray(r_b, dtype=float).ravel()
    if len(r_a) != len(r_b):
        raise ValueError(f"paired returns must have same length: {len(r_a)} vs {len(r_b)}")
    t = len(r_a)
    if t < 30:
        return (float("nan"),) * 4

    mu_a, mu_b = float(r_a.mean()), float(r_b.mean())
    sig2_a = float(np.var(r_a, ddof=0))
    sig2_b = float(np.var(r_b, ddof=0))
    sig_a, sig_b = float(np.sqrt(sig2_a)), float(np.sqrt(sig2_b))

    if sig_a < 1e-12 or sig_b < 1e-12:
        return (float("nan"),) * 4

    sharpe_a = mu_a / sig_a
    sharpe_b = mu_b / sig_b

    # Centred moments: u_t = r_t - mu, v_t = (r_t-mu)^2 - sigma^2 (4 series stacked)
    ua = r_a - mu_a
    va = ua * ua - sig2_a
    ub = r_b - mu_b
    vb = ub * ub - sig2_b
    z = np.column_stack([ua, va, ub, vb])  # (T, 4)

    if q is None:
        q = max(1, int(np.floor(t ** 0.25)))
    omega = _hac_cov(z, q)

    # Delta-method gradient of (mu_a/sig_a - mu_b/sig_b) wrt (mu_a, sig2_a, mu_b, sig2_b)
    # d(mu/sig)/dmu       = 1/sig
    # d(mu/sig)/dsig2     = -mu / (2 * sig^3)
    grad = np.array([
        1.0 / sig_a,
        -mu_a / (2.0 * sig_a ** 3),
        -1.0 / sig_b,
        mu_b / (2.0 * sig_b ** 3),
    ])
    var_diff = float(grad @ omega @ grad) / t
    se_diff = float(np.sqrt(max(var_diff, 0.0)))
    return sharpe_a, sharpe_b, sharpe_a - sharpe_b, se_diff


# ---------------------------------------------------------------------------
# Stationary bootstrap of paired Sharpe difference (Politis & Romano 1994)
# ---------------------------------------------------------------------------

def stationary_bootstrap_sharpe_diff(
    r_a: np.ndarray, r_b: np.ndarray, n_boot: int = 1000, mean_block: float = 5.0,
    rng_seed: int = 0,
) -> tuple[float, float, np.ndarray]:
    """One-sided p-value for H0: Sharpe(a) <= Sharpe(b).

    Stationary bootstrap with random geometric block length, mean = `mean_block`
    days (~1 trading week for daily series).

    Returns
    -------
    p_one_sided : Pr( Sharpe_a_boot - Sharpe_b_boot <= 0 ) under the empirical
        joint distribution (re-centred). Small = strong evidence Sharpe_a >
        Sharpe_b.
    sharpe_diff_obs : observed daily Sharpe diff.
    boot_diffs : (n_boot,) array of bootstrapped differences, NON-recentred —
        useful for percentile CI plotting.
    """
    r_a = np.asarray(r_a, dtype=float).ravel()
    r_b = np.asarray(r_b, dtype=float).ravel()
    t = len(r_a)
    p_geom = 1.0 / mean_block
    rng = np.random.default_rng(rng_seed)

    mu_a, mu_b = r_a.mean(), r_b.mean()
    sig_a, sig_b = r_a.std(ddof=0), r_b.std(ddof=0)
    if sig_a < 1e-12 or sig_b < 1e-12:
        return float("nan"), float("nan"), np.zeros(n_boot)
    obs = mu_a / sig_a - mu_b / sig_b

    diffs = np.empty(n_boot)
    for b in range(n_boot):
        idx = np.empty(t, dtype=np.int64)
        i = rng.integers(0, t)
        for k in range(t):
            idx[k] = i
            if rng.random() < p_geom:
                i = int(rng.integers(0, t))
            else:
                i = (i + 1) % t
        ra_b = r_a[idx]
        rb_b = r_b[idx]
        sa = ra_b.mean() / max(ra_b.std(ddof=0), 1e-12)
        sb = rb_b.mean() / max(rb_b.std(ddof=0), 1e-12)
        diffs[b] = sa - sb

    # For one-sided p-value of "active beats baseline", re-centre under H0
    # (Sharpe_a = Sharpe_b) by subtracting the observed diff
    centred = diffs - obs
    p_one_sided = float(np.mean(centred >= obs))
    return p_one_sided, float(obs), diffs


# ---------------------------------------------------------------------------
# Re-derive per-period net returns (verbatim from simulate_har_kelly.py)
# ---------------------------------------------------------------------------

def _equity_curve_sharpe(returns: np.ndarray) -> float:
    if len(returns) < 20:
        return float("nan")
    mu = float(np.mean(returns))
    sd = float(np.std(returns, ddof=1))
    if sd < 1e-12:
        return 0.0
    return (mu * 252.0) / (sd * np.sqrt(252.0))


def _kelly_net_returns(
    daily_returns: pd.Series,
    forecast_log_rv: pd.Series,
    mu_window: int,
    kelly_cap: float,
    fee_bps: float,
) -> pd.Series:
    """Replicates `_kelly_strategy` in simulate_har_kelly.py, returns the
    per-period `net` series indexed by trading day (no aggregation)."""
    aligned = pd.concat(
        [daily_returns.rename("r"), forecast_log_rv.rename("logrv")], axis=1
    ).dropna()
    if len(aligned) < mu_window + 30:
        return pd.Series(dtype=float)
    mu_hat = aligned["r"].rolling(mu_window).mean().shift(1)
    sigma2_daily = np.exp(aligned["logrv"].values)
    f_kelly = mu_hat.values / np.clip(sigma2_daily, 1e-12, None)
    f_kelly = np.nan_to_num(f_kelly, nan=0.0, posinf=kelly_cap, neginf=0.0)
    f_kelly = np.clip(f_kelly, 0.0, kelly_cap)
    r = aligned["r"].values
    pnl = f_kelly * r
    turnover = np.abs(np.diff(f_kelly, prepend=f_kelly[0]))
    fee_drag = (fee_bps / 10000.0) * turnover
    net = pnl - fee_drag
    return pd.Series(net, index=aligned.index, name="net")


def _buy_hold_net_returns(daily_returns: pd.Series) -> pd.Series:
    return daily_returns.dropna().astype(float).rename("net")


def _load_one_coin(coin: str) -> pd.Series:
    """Lazy hourly-returns loader matching `_load_panel` in simulate_har_kelly."""
    if coin == "BTC-USD":
        return hourly_log_returns(load_bitstamp_btc())
    if coin == "ETH-USD":
        return hourly_log_returns(load_binance_eth())
    return hourly_log_returns(load_yf_intraday(coin))


def derive_paired_returns(
    coin: str,
    horizon: int,
    mu_window: int,
    kelly_cap: float,
    fee_bps: float,
    n_splits: int,
    refit_every: int,
) -> tuple[pd.Series, pd.Series] | None:
    """Returns (r_buy_hold, r_kelly_har_mu{mu_window}) aligned on common index.

    None if HAR cannot be fit (insufficient data).
    """
    hourly_rets = _load_one_coin(coin)
    rv = daily_realized_variance(hourly_rets)
    if len(rv) < 300:
        return None
    har_out = walk_forward_har(rv, horizon=horizon, n_splits=n_splits, refit_every=refit_every)
    har_forecasts = har_out["forecasts"]
    daily_close_rets = (
        hourly_rets.groupby(hourly_rets.index.normalize()).sum().rename("r_daily")
    )
    daily_close_rets.index = pd.DatetimeIndex(daily_close_rets.index).normalize()
    daily_close_rets = daily_close_rets.reindex(har_forecasts.index).dropna()
    har_forecasts = har_forecasts.reindex(daily_close_rets.index)

    r_kelly = _kelly_net_returns(
        daily_close_rets, har_forecasts, mu_window, kelly_cap, fee_bps
    )
    if r_kelly.empty:
        return None
    r_bh = _buy_hold_net_returns(daily_close_rets).reindex(r_kelly.index).dropna()
    r_kelly = r_kelly.reindex(r_bh.index).dropna()
    return r_bh, r_kelly


# ---------------------------------------------------------------------------
# Main pipeline
# ---------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--strategies", type=str, nargs="+",
        default=["kelly_har_mu60", "kelly_har_mu250"],
        help="Active strategies to test vs buy_hold (extracts mu window from name)",
    )
    parser.add_argument("--horizons", type=int, nargs="+",
                        default=[1, 5, 10, 15, 20])
    parser.add_argument(
        "--coins", type=str, nargs="+",
        default=["BTC-USD", "ETH-USD", "SOL-USD", "LTC-USD", "XRP-USD", "ADA-USD", "DOT-USD"],
    )
    parser.add_argument("--target-vol", type=float, default=0.15)
    parser.add_argument("--kelly-cap", type=float, default=1.0)
    parser.add_argument("--fee-bps", type=float, default=10.0)
    parser.add_argument("--n-splits", type=int, default=5)
    parser.add_argument("--refit-every", type=int, default=22)
    parser.add_argument("--bootstrap-top", type=int, default=5,
                        help="Number of strongest combos to bootstrap-check")
    parser.add_argument("--n-boot", type=int, default=1000)
    parser.add_argument("--block-mean", type=float, default=5.0)
    parser.add_argument("--out-dir", type=str,
                        default="MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/results/m11c_dm_test")
    args = parser.parse_args()

    t0 = time.time()
    print(f"[setup] strategies={args.strategies}  horizons={args.horizons}  coins={args.coins}", flush=True)
    print(f"[setup] LW2008 HAC q=floor(T^0.25), Bootstrap stationary B={args.n_boot} mean_block={args.block_mean}", flush=True)

    # Parse mu_windows from strategy names
    def mu_from(strat: str) -> int:
        if not strat.startswith("kelly_har_mu"):
            raise ValueError(f"Unsupported strategy {strat} (only kelly_har_muXXX supported in M11c)")
        return int(strat.removeprefix("kelly_har_mu"))

    mu_windows = {s: mu_from(s) for s in args.strategies}

    rows: list[dict] = []
    cached_kelly: dict[tuple[str, int, int], pd.Series] = {}
    cached_bh: dict[tuple[str, int], pd.Series] = {}

    for coin in args.coins:
        for h in args.horizons:
            for strategy in args.strategies:
                mu_w = mu_windows[strategy]
                key_k = (coin, h, mu_w)
                key_b = (coin, h)
                try:
                    if key_k not in cached_kelly:
                        pair = derive_paired_returns(
                            coin=coin, horizon=h, mu_window=mu_w,
                            kelly_cap=args.kelly_cap, fee_bps=args.fee_bps,
                            n_splits=args.n_splits, refit_every=args.refit_every,
                        )
                        if pair is None:
                            print(f"[skip] {coin} h={h} {strategy}: data insufficient", flush=True)
                            cached_kelly[key_k] = pd.Series(dtype=float)
                            continue
                        r_bh, r_k = pair
                        cached_kelly[key_k] = r_k
                        cached_bh[key_b] = r_bh
                    r_kelly = cached_kelly[key_k]
                    r_bh = cached_bh.get(key_b)
                    if r_kelly.empty or r_bh is None or r_bh.empty:
                        continue
                    common = r_bh.index.intersection(r_kelly.index)
                    r_bh_c = r_bh.reindex(common).values
                    r_k_c = r_kelly.reindex(common).values

                    sa, sb, diff_daily, se_daily = ledoit_wolf_sharpe_diff_se(r_k_c, r_bh_c)
                    if not np.isfinite(se_daily) or se_daily == 0.0:
                        t_stat = float("nan")
                        p_one = float("nan")
                    else:
                        t_stat = diff_daily / se_daily
                        # one-sided H1: Sharpe_active > Sharpe_baseline ; normal approx
                        # p = 1 - Phi(t)
                        from scipy.stats import norm
                        p_one = float(1.0 - norm.cdf(t_stat))

                    sharpe_diff_ann = (sa - sb) * np.sqrt(252.0)
                    row = {
                        "coin": coin,
                        "horizon": h,
                        "strategy": strategy,
                        "vs": "buy_hold",
                        "n_periods": int(len(common)),
                        "sharpe_active_ann": round(sa * np.sqrt(252.0), 4),
                        "sharpe_baseline_ann": round(sb * np.sqrt(252.0), 4),
                        "sharpe_diff_ann": round(sharpe_diff_ann, 4),
                        "se_daily_LW2008": float(se_daily) if np.isfinite(se_daily) else None,
                        "t_stat": float(t_stat) if np.isfinite(t_stat) else None,
                        "p_value_one_sided": float(p_one) if np.isfinite(p_one) else None,
                        "BEATS_p005": bool(np.isfinite(p_one) and p_one < 0.05),
                        "BEATS_p001": bool(np.isfinite(p_one) and p_one < 0.01),
                        "BEATS_delta_sharpe": bool(sharpe_diff_ann > 0),
                    }
                    rows.append(row)
                    flag = "***" if row["BEATS_p001"] else ("**" if row["BEATS_p005"] else (
                        "+" if row["BEATS_delta_sharpe"] else ""))
                    print(
                        f"  {coin:<8s} h={h:<2d} {strategy:<20s} "
                        f"Δ Sharpe_ann={sharpe_diff_ann:+.3f}  t={t_stat:+.3f}  "
                        f"p={p_one:.4f}  {flag}",
                        flush=True,
                    )
                except Exception as exc:
                    print(f"[ERROR] {coin} h={h} {strategy}: {type(exc).__name__}: {exc}", flush=True)
                    rows.append({
                        "coin": coin, "horizon": h, "strategy": strategy,
                        "vs": "buy_hold", "error": f"{type(exc).__name__}: {exc}",
                    })

    # Bootstrap sanity check on top-K combos by t-stat
    valid = [r for r in rows if r.get("t_stat") is not None]
    top = sorted(valid, key=lambda r: r["t_stat"], reverse=True)[: args.bootstrap_top]
    print(f"\n=== Bootstrap stationary B={args.n_boot} on top-{len(top)} combos ===", flush=True)
    boot_rows: list[dict] = []
    for r in top:
        key_k = (r["coin"], r["horizon"], mu_windows[r["strategy"]])
        key_b = (r["coin"], r["horizon"])
        r_k = cached_kelly.get(key_k)
        r_bh = cached_bh.get(key_b)
        if r_k is None or r_bh is None or r_k.empty or r_bh.empty:
            continue
        common = r_bh.index.intersection(r_k.index)
        r_bh_c = r_bh.reindex(common).values
        r_k_c = r_k.reindex(common).values
        p_boot, diff_obs, _ = stationary_bootstrap_sharpe_diff(
            r_k_c, r_bh_c, n_boot=args.n_boot, mean_block=args.block_mean,
            rng_seed=42,
        )
        boot_rows.append({
            "coin": r["coin"], "horizon": r["horizon"], "strategy": r["strategy"],
            "p_LW2008": r["p_value_one_sided"],
            "p_bootstrap": float(p_boot) if np.isfinite(p_boot) else None,
            "diff_daily_obs": float(diff_obs),
        })
        print(
            f"  {r['coin']:<8s} h={r['horizon']:<2d} {r['strategy']:<20s} "
            f"p_LW={r['p_value_one_sided']:.4f}  p_boot={p_boot:.4f}",
            flush=True,
        )

    # Aggregate
    print("\n=== Aggregate BEATS counts ===", flush=True)
    for strategy in args.strategies:
        valid_s = [r for r in rows if r.get("strategy") == strategy and r.get("p_value_one_sided") is not None]
        n = len(valid_s)
        b005 = sum(1 for r in valid_s if r["BEATS_p005"])
        b001 = sum(1 for r in valid_s if r["BEATS_p001"])
        b_delta = sum(1 for r in valid_s if r["BEATS_delta_sharpe"])
        print(f"  {strategy:<20s} BEATS Δ>0: {b_delta}/{n}  BEATS p<0.05: {b005}/{n}  BEATS p<0.01: {b001}/{n}", flush=True)

    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    json_path = out_dir / "dm_results.json"
    csv_path = out_dir / "dm_results.csv"

    json_payload = {
        "rows": rows,
        "bootstrap_rows": boot_rows,
        "elapsed_s": time.time() - t0,
        "config": {
            "strategies": args.strategies,
            "horizons": args.horizons,
            "coins": args.coins,
            "target_vol": args.target_vol,
            "kelly_cap": args.kelly_cap,
            "fee_bps": args.fee_bps,
            "n_splits": args.n_splits,
            "refit_every": args.refit_every,
            "bootstrap": {
                "n_boot": args.n_boot,
                "mean_block": args.block_mean,
                "top": args.bootstrap_top,
            },
            "test": "Ledoit-Wolf 2008 closed-form paired Sharpe SE + stationary bootstrap cross-check",
        },
    }
    json_path.write_text(json.dumps(json_payload, indent=2))

    # CSV — flatten rows only (skip error rows in CSV but keep in JSON)
    csv_cols = [
        "coin", "horizon", "strategy", "vs", "n_periods",
        "sharpe_active_ann", "sharpe_baseline_ann", "sharpe_diff_ann",
        "se_daily_LW2008", "t_stat", "p_value_one_sided",
        "BEATS_p005", "BEATS_p001", "BEATS_delta_sharpe",
    ]
    with open(csv_path, "w", newline="") as fh:
        wr = csv.DictWriter(fh, fieldnames=csv_cols)
        wr.writeheader()
        for r in rows:
            if "error" in r:
                continue
            wr.writerow({k: r.get(k) for k in csv_cols})

    print(f"\n[done] {time.time() - t0:.1f}s — wrote {json_path} and {csv_path}", flush=True)


if __name__ == "__main__":
    main()
