"""M11i Max-DD analysis — does cap=3.0 survive on Calmar basis?

Question
--------
M11h found that kelly_cap=3.0 pushes break-even from ~50bps to ~100bps on
Sharpe alone (p=0.088). But cap=3.0 = up to 3x leverage, which may double
or triple drawdowns. This script computes max-DD per combo and Calmar ratio
(sharpe_ann / |max_dd|) to check whether the edge survives risk-adjustment.

Sweep
-----
Same as M11h: kelly_cap in {1.0, 2.0, 3.0} x threshold in {0.00, 0.05, 0.10}
x fee_bps in {10, 50, 100} x 7 coins x 5 horizons = 945 rows.

Each row now also contains: max_dd_pct, sharpe_net_ann, calmar_ratio.

Verdict
-------
Sign-test cap=3.0 vs cap=1.0 on Calmar at fee=100bps.
If >=60% of combos have Calmar(cap=3.0) > Calmar(cap=1.0) with p<0.10:
  REAL POSITIVE. Otherwise: NULL conditional (edge on Sharpe but not Calmar).

Also reports per-cap aggregate Calmar grid for documentation.

Env: coursia-ml-training. Imports building blocks from m11g_fee_aware_kelly.
"""

from __future__ import annotations

import argparse
import csv
import json
import sys
import time
from pathlib import Path

import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

from m11g_fee_aware_kelly import (  # noqa: E402
    _apply_threshold_band,
    _binomial_pvalue_one_sided,
    _kelly_weights_and_returns,
    _load_one_coin,
    _net_at_fee,
    ledoit_wolf_sharpe_diff_se,
    walk_forward_har,
    daily_realized_variance,
)
import pandas as pd


def _max_drawdown_pct(net_returns: np.ndarray) -> float:
    """Max drawdown in percentage terms from log-return series."""
    cum = np.cumsum(net_returns)
    peak = np.maximum.accumulate(cum)
    dd_log = cum - peak
    min_dd = float(np.min(dd_log))
    return 1.0 - np.exp(min_dd)


def evaluate_combo_with_dd(
    coin: str, horizon: int, mu_window: int, kelly_cap: float,
    fee_bps_grid: list[float], threshold_grid: list[float],
    n_splits: int, refit_every: int,
) -> list[dict]:
    hourly_rets = _load_one_coin(coin)
    rv = daily_realized_variance(hourly_rets)
    if len(rv) < 300:
        return [{"coin": coin, "horizon": horizon, "kelly_cap": kelly_cap,
                 "skipped": "rv<300"}]

    har_out = walk_forward_har(rv, horizon=horizon, n_splits=n_splits,
                               refit_every=refit_every)
    har_forecasts = har_out["forecasts"]
    daily_close_rets = (
        hourly_rets.groupby(hourly_rets.index.normalize()).sum()
        .rename("r_daily")
    )
    daily_close_rets.index = pd.DatetimeIndex(daily_close_rets.index).normalize()
    daily_close_rets = daily_close_rets.reindex(har_forecasts.index).dropna()
    har_forecasts = har_forecasts.reindex(daily_close_rets.index)

    pair = _kelly_weights_and_returns(
        daily_close_rets, har_forecasts, mu_window, kelly_cap
    )
    if pair is None:
        return [{"coin": coin, "horizon": horizon, "kelly_cap": kelly_cap,
                 "skipped": "insufficient"}]

    base_weights, r = pair
    t = len(r)
    if t < 50:
        return [{"coin": coin, "horizon": horizon, "kelly_cap": kelly_cap,
                 "skipped": "T<50"}]

    bh = r.copy()
    rows = []
    for thr in threshold_grid:
        weights_thr = _apply_threshold_band(base_weights, thr)
        for fee in fee_bps_grid:
            net_kelly = _net_at_fee(weights_thr, r, fee)
            sa, sb, diff_daily, se_daily = ledoit_wolf_sharpe_diff_se(net_kelly, bh)
            if not np.isfinite(se_daily) or se_daily <= 0:
                t_stat = float("nan")
                p_one = float("nan")
            else:
                t_stat = diff_daily / se_daily
                from scipy.stats import norm
                p_one = float(1.0 - norm.cdf(t_stat))

            sharpe_active_ann = sa * np.sqrt(252.0)
            sharpe_diff_ann = (sa - sb) * np.sqrt(252.0)
            max_dd = _max_drawdown_pct(net_kelly)
            max_dd_bh = _max_drawdown_pct(bh)
            calmar = sharpe_active_ann / max_dd if max_dd > 1e-8 else float("nan")

            rows.append({
                "kelly_cap": kelly_cap,
                "coin": coin,
                "horizon": horizon,
                "threshold": thr,
                "fee_bps": fee,
                "n_periods": int(t),
                "sharpe_active_ann": round(sharpe_active_ann, 4),
                "sharpe_baseline_ann": round(sb * np.sqrt(252.0), 4),
                "delta_sharpe_ann": round(sharpe_diff_ann, 4),
                "max_dd_active": round(max_dd, 6),
                "max_dd_buyhold": round(max_dd_bh, 6),
                "dd_ratio": round(max_dd / max_dd_bh, 4) if max_dd_bh > 1e-8 else None,
                "calmar_ratio": round(calmar, 4) if np.isfinite(calmar) else None,
                "t_stat": float(t_stat) if np.isfinite(t_stat) else None,
                "p_value_one_sided": float(p_one) if np.isfinite(p_one) else None,
                "BEATS_delta_sharpe": bool(sharpe_diff_ann > 0),
            })
    return rows


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--coins", type=str, nargs="+",
        default=["BTC-USD", "ETH-USD", "SOL-USD", "LTC-USD",
                 "XRP-USD", "ADA-USD", "DOT-USD"],
    )
    parser.add_argument("--horizons", type=int, nargs="+", default=[1, 5, 10, 15, 20])
    parser.add_argument("--mu-window", type=int, default=60)
    parser.add_argument("--kelly-caps", type=float, nargs="+", default=[1.0, 2.0, 3.0])
    parser.add_argument("--fee-bps-grid", type=float, nargs="+",
                        default=[10.0, 50.0, 100.0])
    parser.add_argument("--threshold-grid", type=float, nargs="+",
                        default=[0.00, 0.05, 0.10])
    parser.add_argument("--n-splits", type=int, default=5)
    parser.add_argument("--refit-every", type=int, default=22)
    parser.add_argument(
        "--out-dir", type=str,
        default="MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/"
                "results/m11i_max_dd",
    )
    args = parser.parse_args()

    t0 = time.time()
    print(
        f"[M11i setup] caps={args.kelly_caps} fees={args.fee_bps_grid} "
        f"thresholds={args.threshold_grid} coins={len(args.coins)} "
        f"horizons={len(args.horizons)}",
        flush=True,
    )

    all_rows: list[dict] = []
    total = len(args.kelly_caps) * len(args.coins) * len(args.horizons)
    done = 0
    for cap in args.kelly_caps:
        print(f"\n=== kelly_cap = {cap} ===", flush=True)
        for coin in args.coins:
            for h in args.horizons:
                done += 1
                try:
                    rows = evaluate_combo_with_dd(
                        coin=coin, horizon=h, mu_window=args.mu_window,
                        kelly_cap=cap, fee_bps_grid=args.fee_bps_grid,
                        threshold_grid=args.threshold_grid,
                        n_splits=args.n_splits, refit_every=args.refit_every,
                    )
                    all_rows.extend(rows)
                    tag = "OK" if not rows[0].get("skipped") else rows[0]["skipped"]
                    print(f"  [{done}/{total}] cap={cap} {coin} h={h} {tag}",
                          flush=True)
                except Exception as exc:
                    print(f"  [ERROR] cap={cap} {coin} h={h}: {exc}", flush=True)
                    all_rows.append({
                        "kelly_cap": cap, "coin": coin, "horizon": h,
                        "error": f"{type(exc).__name__}: {exc}",
                    })

    # --- Aggregate: per-cap max-DD distribution ----------------------------
    print("\n=== M11i Max-DD distribution by cap ===", flush=True)
    for cap in args.kelly_caps:
        sel = [r for r in all_rows if r.get("kelly_cap") == cap
               and r.get("max_dd_active") is not None
               and r.get("fee_bps") == 50.0 and r.get("threshold") == 0.0]
        if sel:
            dds = [r["max_dd_active"] for r in sel]
            print(f"  cap={cap} fee=50bps thr=0.00: "
                  f"median_dd={np.median(dds):.3f} "
                  f"mean_dd={np.mean(dds):.3f} "
                  f"max_dd={np.max(dds):.3f} "
                  f"n={len(dds)}",
                  flush=True)

    # --- Aggregate: Calmar grid (cap x threshold x fee) --------------------
    print("\n=== M11i Calmar grid (cap x threshold x fee) ===", flush=True)
    grid_rows = []
    for cap in args.kelly_caps:
        print(f"\n--- kelly_cap = {cap} ---", flush=True)
        header = "  thr/fee  " + "  ".join(
            f"{f:>10.0f}bps" for f in args.fee_bps_grid)
        print(header, flush=True)
        for thr in args.threshold_grid:
            line_parts = [f"  {thr:>6.3f}  "]
            for fee in args.fee_bps_grid:
                sel = [r for r in all_rows
                       if r.get("kelly_cap") == cap
                       and r.get("threshold") == thr
                       and r.get("fee_bps") == fee
                       and r.get("calmar_ratio") is not None]
                n = len(sel)
                med_calmar = float(np.median(
                    [r["calmar_ratio"] for r in sel])) if sel else float("nan")
                med_dd = float(np.median(
                    [r["max_dd_active"] for r in sel])) if sel else float("nan")
                line_parts.append(
                    f"  calmar={med_calmar:>+.2f} dd={med_dd:.3f} n={n}")
                grid_rows.append({
                    "kelly_cap": cap, "threshold": thr, "fee_bps": fee,
                    "n_combos": n,
                    "median_calmar": med_calmar,
                    "median_max_dd": med_dd,
                })
            print("  ".join(line_parts), flush=True)

    # --- Core verdict: Calmar sign-test cap=3.0 vs cap=1.0 at 100bps -------
    print("\n=== M11i CORE VERDICT: Calmar cap=3.0 vs cap=1.0 ===", flush=True)
    verdict_rows = []
    for fee in [50.0, 100.0]:
        for thr in args.threshold_grid:
            pairs_cap1 = {(r["coin"], r["horizon"]): r
                         for r in all_rows
                         if r.get("kelly_cap") == 1.0
                         and r.get("threshold") == thr
                         and r.get("fee_bps") == fee
                         and r.get("calmar_ratio") is not None}
            pairs_cap3 = {(r["coin"], r["horizon"]): r
                         for r in all_rows
                         if r.get("kelly_cap") == 3.0
                         and r.get("threshold") == thr
                         and r.get("fee_bps") == fee
                         and r.get("calmar_ratio") is not None}

            common = set(pairs_cap1.keys()) & set(pairs_cap3.keys())
            n_pairs = len(common)
            count_cap3_better = sum(
                1 for k in common
                if pairs_cap3[k]["calmar_ratio"] > pairs_cap1[k]["calmar_ratio"]
            )
            p_calmar = _binomial_pvalue_one_sided(count_cap3_better, n_pairs)

            # Also compare max-DD
            count_dd_worse = sum(
                1 for k in common
                if pairs_cap3[k]["max_dd_active"] > pairs_cap1[k]["max_dd_active"]
            )
            p_dd = _binomial_pvalue_one_sided(count_dd_worse, n_pairs)

            med_calmar1 = float(np.median(
                [pairs_cap1[k]["calmar_ratio"] for k in common])) if common else float("nan")
            med_calmar3 = float(np.median(
                [pairs_cap3[k]["calmar_ratio"] for k in common])) if common else float("nan")
            med_dd1 = float(np.median(
                [pairs_cap1[k]["max_dd_active"] for k in common])) if common else float("nan")
            med_dd3 = float(np.median(
                [pairs_cap3[k]["max_dd_active"] for k in common])) if common else float("nan")

            verdict_rows.append({
                "fee_bps": fee, "threshold": thr,
                "n_pairs": n_pairs,
                "count_cap3_calmar_better": count_cap3_better,
                "p_calmar_sign_test": p_calmar,
                "count_cap3_dd_worse": count_dd_worse,
                "p_dd_worse_sign_test": p_dd,
                "med_calmar_cap1": med_calmar1,
                "med_calmar_cap3": med_calmar3,
                "med_dd_cap1": med_dd1,
                "med_dd_cap3": med_dd3,
            })
            print(
                f"  fee={fee:.0f}bps thr={thr:.3f}: "
                f"Calmar cap3>cap1 = {count_cap3_better}/{n_pairs} p={p_calmar:.3f} | "
                f"DD cap3>cap1 = {count_dd_worse}/{n_pairs} p={p_dd:.3f} | "
                f"med_calmar {med_calmar1:+.2f} -> {med_calmar3:+.2f} | "
                f"med_dd {med_dd1:.3f} -> {med_dd3:.3f}",
                flush=True,
            )

    # --- Final verdict statement -------------------------------------------
    print("\n=== M11i FINAL VERDICT ===", flush=True)
    escalate_calmar = [v for v in verdict_rows
                       if v["fee_bps"] == 100.0
                       and v["n_pairs"] >= 20
                       and v["count_cap3_calmar_better"] / v["n_pairs"] >= 0.60
                       and v["p_calmar_sign_test"] < 0.10]
    if escalate_calmar:
        print("REAL POSITIVE: cap=3.0 beats cap=1.0 on Calmar at fee=100bps:",
              flush=True)
        for v in escalate_calmar:
            print(f"  thr={v['threshold']:.3f}: "
                  f"{v['count_cap3_calmar_better']}/{v['n_pairs']} p={v['p_calmar_sign_test']:.3f} "
                  f"med_calmar {v['med_calmar_cap1']:+.2f}->{v['med_calmar_cap3']:+.2f} "
                  f"med_dd {v['med_dd_cap1']:.3f}->{v['med_dd_cap3']:.3f}",
                  flush=True)
    else:
        print("NULL CONDITIONAL: cap=3.0 edge on Sharpe does NOT survive "
              "Calmar risk-adjustment at fee=100bps.", flush=True)

    # Check DD penalty specifically
    dd_penalty = [v for v in verdict_rows
                  if v["fee_bps"] == 100.0
                  and v["count_cap3_dd_worse"] / max(v["n_pairs"], 1) >= 0.60
                  and v["p_dd_worse_sign_test"] < 0.10]
    if dd_penalty:
        print("DD PENALTY CONFIRMED: cap=3.0 significantly increases max-DD:",
              flush=True)
        for v in dd_penalty:
            print(f"  thr={v['threshold']:.3f}: "
                  f"{v['count_cap3_dd_worse']}/{v['n_pairs']} p={v['p_dd_worse_sign_test']:.3f} "
                  f"med_dd {v['med_dd_cap1']:.3f}->{v['med_dd_cap3']:.3f}",
                  flush=True)

    # --- Persist -----------------------------------------------------------
    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    json_path = out_dir / "results.json"
    with open(json_path, "w", encoding="utf-8") as f:
        json.dump(
            {
                "experiment": "M11i_MAX_DD_ANALYSIS",
                "args": vars(args),
                "wallclock_s": round(time.time() - t0, 1),
                "per_combo": all_rows,
                "calmar_grid": grid_rows,
                "verdict": verdict_rows,
            },
            f, indent=2, default=str,
        )

    csv_path = out_dir / "m11i_max_dd_grid.csv"
    if all_rows:
        keys = sorted({k for r in all_rows for k in r.keys()})
        with open(csv_path, "w", newline="", encoding="utf-8") as f:
            w = csv.DictWriter(f, fieldnames=keys)
            w.writeheader()
            for r in all_rows:
                w.writerow(r)

    print(f"\n[done] wallclock={time.time() - t0:.1f}s  out={out_dir}", flush=True)


if __name__ == "__main__":
    main()
