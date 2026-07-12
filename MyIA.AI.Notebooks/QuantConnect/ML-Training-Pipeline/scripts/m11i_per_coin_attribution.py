"""M11i Per-coin attribution — is edge concentrated or distributed?

Question
--------
M11h/M11i found edge at cap=3.0 on aggregate 35-combo sign-test. But is this
edge carried by 1-2 coins (concentrated) or spread across all 7 (distributed)?

This script reads M11i results (or re-computes if missing) and decomposes:
- Per-coin win rate (delta_sharpe > 0) across horizons
- Per-coin median delta Sharpe at fee=100bps
- Per-coin Calmar at fee=100bps
- Implications for M_NEXT_VOL roadmap

Output
------
- results/m11i_per_coin/m11i_per_coin_attribution.csv
- docs/M11i_PER_COIN_NOTES.md (printed to stdout for capture)

Env: coursia-ml-training. Reads results from m11i_max_dd if available.
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

M11I_RESULTS = SCRIPT_DIR.parent / "results" / "m11i_max_dd" / "results.json"
M11H_RESULTS = SCRIPT_DIR.parent / "results" / "m11h_kelly_cap_relaxed" / "results.json"


def _binomial_pvalue_one_sided(k: int, n: int, p_null: float = 0.5) -> float:
    if n <= 0:
        return float("nan")
    from scipy.stats import binomtest
    return float(binomtest(k, n, p=p_null, alternative="greater").pvalue)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--coins", type=str, nargs="+",
        default=["BTC-USD", "ETH-USD", "SOL-USD", "LTC-USD",
                 "XRP-USD", "ADA-USD", "DOT-USD"],
    )
    parser.add_argument("--horizons", type=int, nargs="+",
                        default=[1, 5, 10, 15, 20])
    parser.add_argument("--kelly-caps", type=float, nargs="+",
                        default=[1.0, 2.0, 3.0])
    parser.add_argument("--fee-bps-focus", type=float, default=100.0,
                        help="Fee level for primary attribution")
    parser.add_argument(
        "--out-dir", type=str,
        default="MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/"
                "results/m11i_per_coin",
    )
    args = parser.parse_args()

    t0 = time.time()

    # Try loading M11i results first, then M11h
    rows = None
    for path in [M11I_RESULTS, M11H_RESULTS]:
        if path.exists():
            print(f"[load] Reading {path.name} ({path.stat().st_size / 1024:.0f} KB)",
                  flush=True)
            with open(path, encoding="utf-8") as f:
                data = json.load(f)
            rows = data.get("per_combo", [])
            if rows:
                print(f"[load] {len(rows)} per-combo rows loaded", flush=True)
                break

    if not rows:
        print("[ERROR] No M11i or M11h results found. Run m11i_max_dd_analysis.py first.",
              flush=True)
        sys.exit(1)

    fee_focus = args.fee_bps_focus
    print(f"\n=== M11i Per-Coin Attribution (fee={fee_focus:.0f}bps) ===", flush=True)

    # --- Per-coin, per-cap attribution ------------------------------------
    coin_rows = []
    for cap in args.kelly_caps:
        print(f"\n--- kelly_cap = {cap} ---", flush=True)
        for coin in args.coins:
            sel = [r for r in rows
                   if r.get("kelly_cap") == cap
                   and r.get("coin") == coin
                   and r.get("fee_bps") == fee_focus
                   and r.get("delta_sharpe_ann") is not None
                   and not r.get("skipped")
                   and not r.get("error")]
            n = len(sel)
            if n == 0:
                print(f"  {coin}: no data", flush=True)
                continue

            win_count = sum(1 for r in sel if r["delta_sharpe_ann"] > 0)
            med_sharpe = float(np.median([r["delta_sharpe_ann"] for r in sel]))
            med_sharpe_active = float(np.median(
                [r.get("sharpe_active_ann", 0) for r in sel]))

            # Per-horizon breakdown
            per_h = {}
            for h in args.horizons:
                h_sel = [r for r in sel if r.get("horizon") == h]
                if h_sel:
                    h_win = sum(1 for r in h_sel if r["delta_sharpe_ann"] > 0)
                    h_med = float(np.median(
                        [r["delta_sharpe_ann"] for r in h_sel]))
                    per_h[h] = {"win": h_win, "total": len(h_sel),
                                "med_delta": h_med}

            # Calmar if available (from M11i)
            calmars = [r["calmar_ratio"] for r in sel
                       if r.get("calmar_ratio") is not None]
            med_calmar = float(np.median(calmars)) if calmars else None

            # Max-DD if available
            dds = [r["max_dd_active"] for r in sel
                   if r.get("max_dd_active") is not None]
            med_dd = float(np.median(dds)) if dds else None

            p_coin = _binomial_pvalue_one_sided(win_count, n)

            h_str = "  ".join(
                f"h{h}={'Y' if per_h.get(h, {}).get('win', 0) > 0 else 'N'}"
                for h in args.horizons
            )
            print(
                f"  {coin:>8s}: win={win_count}/{n} ({win_count/n:.0%}) "
                f"p={p_coin:.3f} med_delta={med_sharpe:+.3f} "
                f"med_calmar={med_calmar:+.2f} med_dd={med_dd:.3f} "
                f"| {h_str}",
                flush=True,
            )

            coin_rows.append({
                "kelly_cap": cap, "coin": coin, "fee_bps": fee_focus,
                "n_horizons": n, "win_count": win_count, "win_rate": win_count / n,
                "p_value": p_coin,
                "median_delta_sharpe": med_sharpe,
                "median_sharpe_active": med_sharpe_active,
                "median_calmar": med_calmar,
                "median_max_dd": med_dd,
                **{f"h{h}_win": per_h.get(h, {}).get("win", None)
                   for h in args.horizons},
                **{f"h{h}_med_delta": per_h.get(h, {}).get("med_delta", None)
                   for h in args.horizons},
            })

    # --- Aggregate: concentration metrics ----------------------------------
    print("\n=== M11i Concentration Analysis ===", flush=True)
    for cap in args.kelly_caps:
        cap_rows = [r for r in coin_rows if r["kelly_cap"] == cap]
        if not cap_rows:
            continue
        winners = [r for r in cap_rows if r["win_rate"] > 0.50]
        total_wins = sum(r["win_count"] for r in cap_rows)
        winner_wins = sum(r["win_count"] for r in winners)
        top_coin = max(cap_rows, key=lambda r: r["win_count"])

        concentration = winner_wins / total_wins if total_wins > 0 else 0
        print(
            f"  cap={cap}: {len(winners)}/{len(cap_rows)} coins >50% win | "
            f"top={top_coin['coin']} ({top_coin['win_count']}/{top_coin['n_horizons']}) | "
            f"winner_concentration={concentration:.0%}",
            flush=True,
        )

        # Implications
        if len(winners) <= 2:
            print(f"  -> CONCENTRATED: edge in {len(winners)} coin(s). "
                  "Strategy viable only for specific assets.", flush=True)
        elif len(winners) >= 5:
            print(f"  -> DISTRIBUTED: edge in {len(winners)}/7 coins. "
                  "Robust cross-asset signal.", flush=True)
        else:
            print(f"  -> MODERATE: edge in {len(winners)}/7 coins. "
                  "Partial concentration.", flush=True)

    # --- Cross-cap comparison per coin -------------------------------------
    print("\n=== M11i Cross-Cap Delta (cap=3.0 minus cap=1.0) per coin ===",
          flush=True)
    cap1_map = {r["coin"]: r for r in coin_rows if r["kelly_cap"] == 1.0}
    cap3_map = {r["coin"]: r for r in coin_rows if r["kelly_cap"] == 3.0}
    for coin in args.coins:
        c1 = cap1_map.get(coin)
        c3 = cap3_map.get(coin)
        if c1 and c3:
            delta_wr = c3["win_rate"] - c1["win_rate"]
            delta_sharpe = c3["median_delta_sharpe"] - c1["median_delta_sharpe"]
            dd_mult = (c3["median_max_dd"] / c1["median_max_dd"]
                       if c1.get("median_max_dd") and c3.get("median_max_dd")
                       and c1["median_max_dd"] > 0 else None)
            calmar_delta = ((c3["median_calmar"] - c1["median_calmar"])
                            if c3.get("median_calmar") is not None
                            and c1.get("median_calmar") is not None else None)
            print(
                f"  {coin:>8s}: delta_wr={delta_wr:+.0%} "
                f"delta_sharpe={delta_sharpe:+.3f} "
                f"dd_mult={dd_mult:.2f}x "
                f"calmar_delta={calmar_delta:+.2f}",
                flush=True,
            )

    # --- Persist -----------------------------------------------------------
    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    csv_path = out_dir / "m11i_per_coin_attribution.csv"
    if coin_rows:
        keys = sorted({k for r in coin_rows for k in r.keys()})
        with open(csv_path, "w", newline="", encoding="utf-8") as f:
            w = csv.DictWriter(f, fieldnames=keys)
            w.writeheader()
            for r in coin_rows:
                w.writerow(r)

    # Save JSON too for easy consumption
    json_path = out_dir / "results.json"
    with open(json_path, "w", encoding="utf-8") as f:
        json.dump({
            "experiment": "M11i_PER_COIN_ATTRIBUTION",
            "args": vars(args),
            "wallclock_s": round(time.time() - t0, 1),
            "per_coin": coin_rows,
        }, f, indent=2, default=str)

    print(f"\n[done] wallclock={time.time() - t0:.1f}s  out={out_dir}", flush=True)


if __name__ == "__main__":
    main()
