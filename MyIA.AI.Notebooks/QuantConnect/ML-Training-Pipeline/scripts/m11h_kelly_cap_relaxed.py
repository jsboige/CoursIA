"""M11h Kelly-cap relaxed sweep — does relaxing the Kelly cap recover edge under fees?

Question
--------
M11g (no-trade band) ended NULL: thresholds did not push break-even past 100bps.
M11g pistes ouvertes mention `Kelly non-cape ou cap relaxe produirait plus de variation
intermediaire dans les weights` — relaxing the cap may help OR may amplify drawdowns.

This script extends M11g by sweeping kelly_cap in {1.0, 2.0, 3.0} on top of the
existing (threshold, fee, coin, horizon) grid.

Sweep
-----
- kelly_cap  in {1.0, 2.0, 3.0}                   (3 levels, 1.0 = M11g baseline)
- threshold  in {0.00, 0.05, 0.10}                (3 levels — focused, not 5)
- fee_bps    in {10, 50, 100}                     (3 levels — break-even region)
- 7 coins x 5 horizons x 3 caps x 3 thresholds x 3 fees = 945 rows

Verdict
-------
Per-cap aggregate sign-test vs buy-hold at fee=50bps and fee=100bps. If any cap level
delivers >= 60% Δ>0 with sign-test p < 0.10, escalate to ai-01 review.

Env: coursia-ml-training. Imports m11g.evaluate_coin_horizon for the per-coin loop.
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

from m11g_fee_aware_kelly import evaluate_coin_horizon, _binomial_pvalue_one_sided  # noqa: E402


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--coins", type=str, nargs="+",
        default=["BTC-USD", "ETH-USD", "SOL-USD", "LTC-USD", "XRP-USD", "ADA-USD", "DOT-USD"],
    )
    parser.add_argument("--horizons", type=int, nargs="+", default=[1, 5, 10, 15, 20])
    parser.add_argument("--mu-window", type=int, default=60)
    parser.add_argument("--kelly-caps", type=float, nargs="+", default=[1.0, 2.0, 3.0])
    parser.add_argument("--fee-bps-grid", type=float, nargs="+", default=[10.0, 50.0, 100.0])
    parser.add_argument("--threshold-grid", type=float, nargs="+", default=[0.00, 0.05, 0.10])
    parser.add_argument("--n-splits", type=int, default=5)
    parser.add_argument("--refit-every", type=int, default=22)
    parser.add_argument(
        "--out-dir", type=str,
        default="MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/results/m11h_kelly_cap_relaxed",
    )
    args = parser.parse_args()

    t0 = time.time()
    print(
        f"[setup] mu_window={args.mu_window}  kelly_caps={args.kelly_caps}  "
        f"fee_grid={args.fee_bps_grid}  threshold_grid={args.threshold_grid}  "
        f"coins={len(args.coins)} horizons={len(args.horizons)}",
        flush=True,
    )

    all_rows: list[dict] = []
    for cap in args.kelly_caps:
        print(f"\n=== kelly_cap = {cap} ===", flush=True)
        for coin in args.coins:
            for h in args.horizons:
                try:
                    rows = evaluate_coin_horizon(
                        coin=coin, horizon=h, mu_window=args.mu_window,
                        kelly_cap=cap, fee_bps_grid=args.fee_bps_grid,
                        threshold_grid=args.threshold_grid,
                        n_splits=args.n_splits, refit_every=args.refit_every,
                    )
                    for r in rows:
                        r["kelly_cap"] = cap
                    all_rows.extend(rows)
                except Exception as exc:
                    print(f"[ERROR] cap={cap} {coin} h={h}: {type(exc).__name__}: {exc}", flush=True)
                    all_rows.append({
                        "kelly_cap": cap, "coin": coin, "horizon": h,
                        "error": f"{type(exc).__name__}: {exc}",
                    })

    # --- Aggregate (kelly_cap, threshold, fee) sign-test grid -------------
    print("\n=== M11h Kelly-cap relaxed: sign-test (cap x threshold x fee) ===", flush=True)
    grid_rows = []
    for cap in args.kelly_caps:
        print(f"\n--- kelly_cap = {cap} ---", flush=True)
        header = "  thr/fee  " + "  ".join(f"{f:>10.0f}bps" for f in args.fee_bps_grid)
        print(header, flush=True)
        for thr in args.threshold_grid:
            line_parts = [f"  {thr:>6.3f}  "]
            for fee in args.fee_bps_grid:
                sel = [r for r in all_rows
                       if r.get("kelly_cap") == cap and r.get("threshold") == thr
                       and r.get("fee_bps") == fee
                       and r.get("p_value_one_sided") is not None]
                n = len(sel)
                b_delta = sum(1 for r in sel if r["BEATS_delta_sharpe"])
                med = float(np.median([r["delta_sharpe_ann"] for r in sel])) if sel else float("nan")
                p_st = _binomial_pvalue_one_sided(b_delta, n)
                line_parts.append(f"  Δ>0={b_delta:>2d}/{n} p={p_st:.3f} med={med:+.3f}")
                grid_rows.append({
                    "kelly_cap": cap, "threshold": thr, "fee_bps": fee,
                    "n_combos": n, "count_delta_positive": b_delta,
                    "median_delta_sharpe": med, "signtest_p_value": p_st,
                })
            print("  ".join(line_parts), flush=True)

    # --- Persist ----------------------------------------------------------
    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    json_path = out_dir / "results.json"
    with open(json_path, "w", encoding="utf-8") as f:
        json.dump(
            {
                "experiment": "M11h_KELLY_CAP_RELAXED_SWEEP",
                "args": vars(args),
                "wallclock_s": round(time.time() - t0, 1),
                "per_combo": all_rows,
                "grid": grid_rows,
            },
            f, indent=2, default=str,
        )

    csv_path = out_dir / "results.csv"
    if all_rows:
        keys = sorted({k for r in all_rows for k in r.keys()})
        with open(csv_path, "w", newline="", encoding="utf-8") as f:
            w = csv.DictWriter(f, fieldnames=keys)
            w.writeheader()
            for r in all_rows:
                w.writerow(r)

    # --- Final verdict ----------------------------------------------------
    print("\n=== M11h FINAL VERDICT ===", flush=True)
    escalate = []
    for g in grid_rows:
        if g["fee_bps"] in (50.0, 100.0) and g["n_combos"] >= 20:
            ratio = g["count_delta_positive"] / g["n_combos"]
            if ratio >= 0.60 and g["signtest_p_value"] < 0.10:
                escalate.append(g)
    if escalate:
        print(f"ESCALATE: {len(escalate)} cells with >=60% Δ>0 and p<0.10 at fee>=50bps:", flush=True)
        for g in escalate:
            print(f"  cap={g['kelly_cap']} thr={g['threshold']} fee={g['fee_bps']}bps "
                  f"-> {g['count_delta_positive']}/{g['n_combos']} p={g['signtest_p_value']:.3f}", flush=True)
    else:
        print("NULL: no cap level recovers fee-robust edge. M11h confirms M11g/M11f tail loss.", flush=True)

    print(f"\n[done] wallclock={time.time() - t0:.1f}s  out={out_dir}", flush=True)


if __name__ == "__main__":
    main()
