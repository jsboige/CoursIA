"""M11e Ensemble strategy: kelly_har_mu60 + kelly_naive30_mu120 + vol_target_har.

Builds a simple equal-weight ensemble of the three top M11a/b active strategies
and tests whether averaging adds value over the single best component
(`kelly_har_mu60`).

Components (rationale from M11a verdict memo backlog):
- `kelly_har_mu60`     — dominant single, 27/35 raw BEATS combined (M11a + M11b)
- `kelly_naive30_mu120`— BTC-dominator at long horizons, uses naive-30d sigma
- `vol_target_har`     — median-low-vol option, ~50% combined raw BEATS, lower DD

Aggregation rule
----------------
For each daily timestamp t, the ensemble position weight is the **arithmetic
mean** of the three component daily weights at t. Net daily return is then

    r_ens_t = w_ens_t * r_t - fee_bps/1e4 * |w_ens_t - w_ens_{t-1}|

This is NOT the same as averaging the three components' net daily returns,
because the latter pays three independent fee streams whereas a real-world
implementation would only pay the ensemble turnover. We compute both for
diagnostic purposes (`r_ens_naive` = avg-of-net, `r_ens` = real-world combined
weight). The headline test uses `r_ens` (combined-weight version).

Tests
-----
Per-combo paired Ledoit-Wolf 2008 Sharpe-diff p-values vs two baselines:
  1. vs `buy_hold`    — does ensemble beat passive ?
  2. vs `kelly_har_mu60` — does ensemble add anything over the single winner ?

Plus sign-tests on the count of positive Δ Sharpe across the 35-combo panel.

Reuses
------
- `simulate_har_kelly.py` for HAR walk-forward + Kelly component weights
- `m11c_sharpe_test.py` for the LW2008 paired SE machinery

Output
------
- `results/m11e_ensemble/results.json`
- `results/m11e_ensemble/results.csv`
- stdout summary

Usage
-----
    python -u scripts/m11e_ensemble.py \\
        --horizons 1 5 10 15 20 \\
        --fee-bps 10

Env : `coursia-ml-training` (numpy 2, pandas 3, scipy 1.17). No extra deps.
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

from garch_rolling_baseline import naive_constant_baseline  # noqa: E402
from har_model import walk_forward_har  # noqa: E402
from intraday_loader import (  # noqa: E402
    hourly_log_returns,
    load_binance_eth,
    load_bitstamp_btc,
    load_yf_intraday,
)
from m11c_sharpe_test import ledoit_wolf_sharpe_diff_se  # noqa: E402
from realized_variance import daily_realized_variance  # noqa: E402


# ---------------------------------------------------------------------------
# Component weight helpers (same logic as simulate_har_kelly.py but returning
# the per-day weight series instead of equity-curve summaries).
# ---------------------------------------------------------------------------

def _kelly_weights(
    daily_returns: pd.Series,
    forecast_log_rv: pd.Series,
    mu_window: int,
    kelly_cap: float,
) -> pd.Series:
    """Long-only fractional Kelly per-day weight series."""
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
    return pd.Series(f_kelly, index=aligned.index, name="w_kelly")


def _vol_target_weights(
    daily_returns: pd.Series,
    forecast_log_rv: pd.Series,
    target_vol: float,
    max_leverage: float = 4.0,
) -> pd.Series:
    aligned = pd.concat(
        [daily_returns.rename("r"), forecast_log_rv.rename("logrv")], axis=1
    ).dropna()
    if len(aligned) < 30:
        return pd.Series(dtype=float)
    forecast_var_daily = np.exp(aligned["logrv"].values)
    forecast_vol_daily = np.sqrt(np.clip(forecast_var_daily, 1e-12, None))
    forecast_vol_annual = forecast_vol_daily * np.sqrt(252.0)
    weights = target_vol / np.clip(forecast_vol_annual, 0.01, None)
    weights = np.clip(weights, 0.0, max_leverage)
    return pd.Series(weights, index=aligned.index, name="w_vt")


def _apply_fees(weights: np.ndarray, r: np.ndarray, fee_bps: float) -> np.ndarray:
    pnl = weights * r
    turnover = np.abs(np.diff(weights, prepend=weights[0]))
    fee_drag = (fee_bps / 10000.0) * turnover
    return pnl - fee_drag


def _summary(net: np.ndarray) -> dict:
    n = len(net)
    if n < 20:
        return {"sharpe_ann": float("nan"), "ann_return": float("nan"),
                "ann_vol": float("nan"), "max_drawdown": float("nan"),
                "n_periods": int(n)}
    mu = float(np.mean(net))
    sd = float(np.std(net, ddof=1))
    eq = np.cumprod(1.0 + net)
    peaks = np.maximum.accumulate(eq)
    dd = (eq - peaks) / peaks
    return {
        "sharpe_ann": round((mu * 252.0) / (sd * np.sqrt(252.0)), 4) if sd > 1e-10 else 0.0,
        "ann_return": round(mu * 252.0, 6),
        "ann_vol": round(sd * np.sqrt(252.0), 6),
        "max_drawdown": round(float(dd.min()), 6),
        "n_periods": int(n),
    }


# ---------------------------------------------------------------------------
# Build ensemble for one (coin, horizon)
# ---------------------------------------------------------------------------

def _load_one_coin(coin: str) -> pd.Series:
    if coin == "BTC-USD":
        return hourly_log_returns(load_bitstamp_btc())
    if coin == "ETH-USD":
        return hourly_log_returns(load_binance_eth())
    return hourly_log_returns(load_yf_intraday(coin))


def evaluate_one(
    coin: str,
    horizon: int,
    fee_bps: float,
    kelly_cap: float,
    target_vol: float,
    n_splits: int,
    refit_every: int,
    train_size: int,
) -> dict | None:
    """Build ensemble + components and return all per-day net return series,
    plus LW2008 p-values vs buy_hold and vs kelly_har_mu60."""
    hourly_rets = _load_one_coin(coin)
    rv = daily_realized_variance(hourly_rets)
    if len(rv) < 300:
        print(f"[skip] {coin} h={horizon}: RV<300", flush=True)
        return None

    print(f"\n[{coin} h={horizon}] RV days={len(rv)}", flush=True)

    har_out = walk_forward_har(rv, horizon=horizon, n_splits=n_splits, refit_every=refit_every)
    har_forecasts = har_out["forecasts"]
    daily_close_rets = (
        hourly_rets.groupby(hourly_rets.index.normalize()).sum().rename("r_daily")
    )
    daily_close_rets.index = pd.DatetimeIndex(daily_close_rets.index).normalize()
    daily_close_rets = daily_close_rets.reindex(har_forecasts.index).dropna()
    har_forecasts = har_forecasts.reindex(daily_close_rets.index)

    try:
        naive = naive_constant_baseline(
            rv, horizon=horizon, train_size=train_size, refit_every=refit_every
        )
        naive_log = np.log(naive.clip(lower=1e-12))
        naive_log = naive_log.reindex(daily_close_rets.index).dropna()
    except Exception as exc:
        print(f"  naive baseline FAILED: {exc}", flush=True)
        naive_log = None

    if naive_log is None or len(naive_log) < 30:
        print(f"[skip] {coin} h={horizon}: naive baseline unavailable", flush=True)
        return None

    # --- Component weight series ----------------------------------------------
    w_k60 = _kelly_weights(daily_close_rets, har_forecasts, 60, kelly_cap)
    w_kn120 = _kelly_weights(daily_close_rets, naive_log, 120, kelly_cap)
    w_vt = _vol_target_weights(daily_close_rets, har_forecasts, target_vol)

    if w_k60.empty or w_kn120.empty or w_vt.empty:
        print(f"[skip] {coin} h={horizon}: one component empty", flush=True)
        return None

    common = w_k60.index.intersection(w_kn120.index).intersection(w_vt.index)
    common = daily_close_rets.index.intersection(common)
    if len(common) < 100:
        print(f"[skip] {coin} h={horizon}: common index<100", flush=True)
        return None

    r = daily_close_rets.reindex(common).values
    wk60 = w_k60.reindex(common).values
    wkn = w_kn120.reindex(common).values
    wvt = w_vt.reindex(common).values

    # --- Ensemble weight (real-world: combined weight then 1 fee stream) ------
    w_ens = (wk60 + wkn + wvt) / 3.0

    # --- Per-strategy net daily returns ---------------------------------------
    net_bh = r.copy()
    net_k60 = _apply_fees(wk60, r, fee_bps)
    net_kn120 = _apply_fees(wkn, r, fee_bps)
    net_vt = _apply_fees(wvt, r, fee_bps)
    net_ens = _apply_fees(w_ens, r, fee_bps)
    # Naive avg-of-net (pays 3 fee streams ; diagnostic only) ------------------
    net_avg = (net_k60 + net_kn120 + net_vt) / 3.0

    # --- LW2008 p-values vs each baseline -------------------------------------
    sa_ens, sb_bh, diff_ens_bh, se_ens_bh = ledoit_wolf_sharpe_diff_se(net_ens, net_bh)
    sa_ens2, sb_k60, diff_ens_k60, se_ens_k60 = ledoit_wolf_sharpe_diff_se(net_ens, net_k60)
    sa_k60_bh, _, diff_k60_bh, se_k60_bh = ledoit_wolf_sharpe_diff_se(net_k60, net_bh)

    from scipy.stats import norm

    def _pval(diff: float, se: float) -> float:
        if not np.isfinite(se) or se <= 0:
            return float("nan")
        return float(1.0 - norm.cdf(diff / se))

    p_ens_bh = _pval(diff_ens_bh, se_ens_bh)
    p_ens_k60 = _pval(diff_ens_k60, se_ens_k60)
    p_k60_bh = _pval(diff_k60_bh, se_k60_bh)

    sharpe_diff_ens_bh_ann = (sa_ens - sb_bh) * np.sqrt(252.0)
    sharpe_diff_ens_k60_ann = (sa_ens2 - sb_k60) * np.sqrt(252.0)
    sharpe_diff_k60_bh_ann = (sa_k60_bh - sb_bh) * np.sqrt(252.0)

    # --- Summaries ------------------------------------------------------------
    sm_bh = _summary(net_bh)
    sm_k60 = _summary(net_k60)
    sm_kn = _summary(net_kn120)
    sm_vt = _summary(net_vt)
    sm_ens = _summary(net_ens)
    sm_avg = _summary(net_avg)

    return {
        "coin": coin,
        "horizon": horizon,
        "n_periods": int(len(r)),
        # Sharpe summaries
        "sharpe_buy_hold": sm_bh["sharpe_ann"],
        "sharpe_kelly_har_mu60": sm_k60["sharpe_ann"],
        "sharpe_kelly_naive30_mu120": sm_kn["sharpe_ann"],
        "sharpe_vol_target_har": sm_vt["sharpe_ann"],
        "sharpe_ensemble": sm_ens["sharpe_ann"],
        "sharpe_avg_of_nets": sm_avg["sharpe_ann"],
        "max_dd_ensemble": sm_ens["max_drawdown"],
        "max_dd_kelly_har_mu60": sm_k60["max_drawdown"],
        # Δ Sharpe (annualised)
        "delta_sharpe_ens_vs_bh": round(sharpe_diff_ens_bh_ann, 4),
        "delta_sharpe_ens_vs_k60": round(sharpe_diff_ens_k60_ann, 4),
        "delta_sharpe_k60_vs_bh": round(sharpe_diff_k60_bh_ann, 4),
        # LW2008 p-values
        "p_ens_vs_bh": float(p_ens_bh) if np.isfinite(p_ens_bh) else None,
        "p_ens_vs_k60": float(p_ens_k60) if np.isfinite(p_ens_k60) else None,
        "p_k60_vs_bh": float(p_k60_bh) if np.isfinite(p_k60_bh) else None,
        "BEATS_ens_vs_bh_p005": bool(np.isfinite(p_ens_bh) and p_ens_bh < 0.05),
        "BEATS_ens_vs_k60_p005": bool(np.isfinite(p_ens_k60) and p_ens_k60 < 0.05),
        "BEATS_ens_vs_bh_delta": bool(sharpe_diff_ens_bh_ann > 0),
        "BEATS_ens_vs_k60_delta": bool(sharpe_diff_ens_k60_ann > 0),
    }


# ---------------------------------------------------------------------------
# Sign-test helper (binomial against null=0.5)
# ---------------------------------------------------------------------------

def _binomial_pvalue_one_sided(k: int, n: int, p_null: float = 0.5) -> float:
    """One-sided binomial p-value for H1: success rate > p_null."""
    if n <= 0:
        return float("nan")
    from scipy.stats import binomtest
    return float(binomtest(k, n, p=p_null, alternative="greater").pvalue)


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--coins", type=str, nargs="+",
        default=["BTC-USD", "ETH-USD", "SOL-USD", "LTC-USD", "XRP-USD", "ADA-USD", "DOT-USD"],
    )
    parser.add_argument("--horizons", type=int, nargs="+", default=[1, 5, 10, 15, 20])
    parser.add_argument("--fee-bps", type=float, default=10.0)
    parser.add_argument("--kelly-cap", type=float, default=1.0)
    parser.add_argument("--target-vol", type=float, default=0.15)
    parser.add_argument("--n-splits", type=int, default=5)
    parser.add_argument("--refit-every", type=int, default=22)
    parser.add_argument("--train-size", type=int, default=250)
    parser.add_argument(
        "--out-dir", type=str,
        default="MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/results/m11e_ensemble",
    )
    args = parser.parse_args()

    t0 = time.time()
    print(f"[setup] coins={args.coins}  horizons={args.horizons}  fee_bps={args.fee_bps}", flush=True)
    print("[setup] components = kelly_har_mu60 + kelly_naive30_mu120 + vol_target_har (equal-weight avg)", flush=True)

    rows: list[dict] = []
    for coin in args.coins:
        for h in args.horizons:
            try:
                res = evaluate_one(
                    coin=coin, horizon=h,
                    fee_bps=args.fee_bps, kelly_cap=args.kelly_cap, target_vol=args.target_vol,
                    n_splits=args.n_splits, refit_every=args.refit_every,
                    train_size=args.train_size,
                )
                if res is not None:
                    rows.append(res)
                    print(
                        f"  Δ Sharpe ens-vs-BH={res['delta_sharpe_ens_vs_bh']:+.3f}  "
                        f"p={res['p_ens_vs_bh']:.4f}  | "
                        f"Δ Sharpe ens-vs-K60={res['delta_sharpe_ens_vs_k60']:+.3f}  "
                        f"p={res['p_ens_vs_k60']:.4f}",
                        flush=True,
                    )
            except Exception as exc:
                print(f"[ERROR] {coin} h={h}: {type(exc).__name__}: {exc}", flush=True)
                rows.append({"coin": coin, "horizon": h, "error": f"{type(exc).__name__}: {exc}"})

    # --- Aggregate sign-tests ---------------------------------------------------
    print("\n=== M11e Aggregate Verdict ===", flush=True)
    valid = [r for r in rows if r.get("p_ens_vs_bh") is not None]
    n = len(valid)

    if n > 0:
        b_ens_bh_delta = sum(1 for r in valid if r["BEATS_ens_vs_bh_delta"])
        b_ens_bh_005 = sum(1 for r in valid if r["BEATS_ens_vs_bh_p005"])
        b_ens_k60_delta = sum(1 for r in valid if r["BEATS_ens_vs_k60_delta"])
        b_ens_k60_005 = sum(1 for r in valid if r["BEATS_ens_vs_k60_p005"])

        p_signtest_ens_bh = _binomial_pvalue_one_sided(b_ens_bh_delta, n)
        p_signtest_ens_k60 = _binomial_pvalue_one_sided(b_ens_k60_delta, n)

        print(f"  Combos tested: {n}/{len(args.coins) * len(args.horizons)}")
        print(f"  ENSEMBLE vs buy_hold      Δ Sharpe>0 : {b_ens_bh_delta}/{n} (sign-test p={p_signtest_ens_bh:.4f})")
        print(f"  ENSEMBLE vs buy_hold      p<0.05    : {b_ens_bh_005}/{n}")
        print(f"  ENSEMBLE vs kelly_har_mu60 Δ Sharpe>0: {b_ens_k60_delta}/{n} (sign-test p={p_signtest_ens_k60:.4f})")
        print(f"  ENSEMBLE vs kelly_har_mu60 p<0.05    : {b_ens_k60_005}/{n}")

        median_delta_ens_bh = float(np.median([r["delta_sharpe_ens_vs_bh"] for r in valid]))
        median_delta_ens_k60 = float(np.median([r["delta_sharpe_ens_vs_k60"] for r in valid]))
        print(f"  Median Δ Sharpe ens-vs-BH : {median_delta_ens_bh:+.4f}")
        print(f"  Median Δ Sharpe ens-vs-K60: {median_delta_ens_k60:+.4f}")

        # Verdict label — gated on sign-test significance (G.2 honest reporting)
        if p_signtest_ens_k60 < 0.05 and b_ens_k60_delta > n / 2:
            verdict = f"HELPS vs kelly_har_mu60 (sign-test p={p_signtest_ens_k60:.3f})"
        elif p_signtest_ens_k60 < 0.05 and b_ens_k60_delta < n / 2:
            verdict = f"HURTS vs kelly_har_mu60 (sign-test p={p_signtest_ens_k60:.3f})"
        else:
            verdict = (f"DILUTION / NOT SIGNIFICANT vs kelly_har_mu60 "
                       f"(sign-test p={p_signtest_ens_k60:.3f}, {b_ens_k60_delta}/{n} Δ>0)")
        print(f"\n  VERDICT: {verdict}", flush=True)

        agg = {
            "n_combos": n,
            "ens_vs_bh_count_delta": b_ens_bh_delta,
            "ens_vs_bh_count_p005": b_ens_bh_005,
            "ens_vs_bh_signtest_p": p_signtest_ens_bh,
            "ens_vs_k60_count_delta": b_ens_k60_delta,
            "ens_vs_k60_count_p005": b_ens_k60_005,
            "ens_vs_k60_signtest_p": p_signtest_ens_k60,
            "median_delta_ens_vs_bh": median_delta_ens_bh,
            "median_delta_ens_vs_k60": median_delta_ens_k60,
            "verdict": verdict,
        }
    else:
        agg = {"n_combos": 0, "verdict": "NO_DATA"}

    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / "results.json").write_text(json.dumps({
        "rows": rows,
        "aggregate": agg,
        "config": {
            "coins": args.coins,
            "horizons": args.horizons,
            "fee_bps": args.fee_bps,
            "kelly_cap": args.kelly_cap,
            "target_vol": args.target_vol,
            "n_splits": args.n_splits,
            "refit_every": args.refit_every,
            "train_size": args.train_size,
            "components": ["kelly_har_mu60", "kelly_naive30_mu120", "vol_target_har"],
            "aggregation": "equal-weight arithmetic mean of daily component weights",
            "test": "Ledoit-Wolf 2008 paired Sharpe-diff (one-sided, normal asymp)",
        },
        "elapsed_s": time.time() - t0,
    }, indent=2))

    cols = [
        "coin", "horizon", "n_periods",
        "sharpe_buy_hold", "sharpe_kelly_har_mu60", "sharpe_ensemble",
        "delta_sharpe_ens_vs_bh", "delta_sharpe_ens_vs_k60",
        "p_ens_vs_bh", "p_ens_vs_k60",
        "BEATS_ens_vs_bh_p005", "BEATS_ens_vs_k60_p005",
        "BEATS_ens_vs_bh_delta", "BEATS_ens_vs_k60_delta",
    ]
    with open(out_dir / "results.csv", "w", newline="") as fh:
        wr = csv.DictWriter(fh, fieldnames=cols)
        wr.writeheader()
        for r in rows:
            if "error" in r:
                continue
            wr.writerow({k: r.get(k) for k in cols})

    print(f"\n[done] {time.time() - t0:.1f}s — wrote {out_dir}/results.{{json,csv}}", flush=True)


if __name__ == "__main__":
    main()
