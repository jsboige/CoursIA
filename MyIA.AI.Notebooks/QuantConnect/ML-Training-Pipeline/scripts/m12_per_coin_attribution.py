"""M12 Per-Coin Attribution — decompose HAR-RV-J verdict by coin.

Reads m12_har_rv_j results.json and produces per-coin breakdown.
Pattern follows m11i_per_coin_attribution.py.

Output:
- results/m12_har_rv_j/m12_per_coin_attribution.csv
- results/m12_har_rv_j/m12_per_coin_results.json
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np
import pandas as pd

SCRIPT_DIR = Path(__file__).resolve().parent
RESULTS_DIR = SCRIPT_DIR / "results" / "m12_har_rv_j"
COINS = ["BTC-USD", "ETH-USD", "SOL-USD", "LTC-USD", "XRP-USD", "ADA-USD", "DOT-USD"]


def main() -> None:
    results_file = RESULTS_DIR / "results.json"
    if not results_file.exists():
        print(f"ERROR: {results_file} not found. Run m12_har_rv_j.py first.")
        sys.exit(1)

    with open(results_file) as f:
        data = json.load(f)

    combos = data["combos"]
    df = pd.DataFrame(combos)
    print(f"Loaded {len(df)} combos from M12 results")

    per_coin_rows = []
    per_horizon_rows = []

    for coin in COINS:
        coin_df = df[df["coin"] == coin]
        if len(coin_df) == 0:
            continue
        deltas = coin_df["delta_sharpe_hrj_vs_har"].values
        mses = coin_df["mse_reduction_pct"].values
        n_beats = int(np.sum(deltas > 0))
        n_total = len(deltas)
        win_rate = n_beats / n_total if n_total > 0 else float("nan")

        from m11g_fee_aware_kelly import _binomial_pvalue_one_sided
        p_val = _binomial_pvalue_one_sided(n_beats, n_total)

        row = {
            "coin": coin,
            "n_combos": n_total,
            "n_hrj_beats_har": n_beats,
            "win_rate": win_rate,
            "p_value": p_val,
            "median_delta_sharpe": float(np.median(deltas)),
            "mean_delta_sharpe": float(np.mean(deltas)),
            "median_mse_reduction_pct": float(np.median(mses)),
            "median_sharpe_har": float(np.median(coin_df["sharpe_har"].values)),
            "median_sharpe_hrj": float(np.median(coin_df["sharpe_hrj"].values)),
            "median_sharpe_bh": float(np.median(coin_df["sharpe_bh"].values)),
        }
        per_coin_rows.append(row)

        # Per-horizon breakdown
        for h in sorted(coin_df["horizon"].unique()):
            h_df = coin_df[coin_df["horizon"] == h]
            h_deltas = h_df["delta_sharpe_hrj_vs_har"].values
            h_mses = h_df["mse_reduction_pct"].values
            h_beats = int(np.sum(h_deltas > 0))
            h_total = len(h_deltas)
            h_row = {
                "coin": coin,
                "horizon": h,
                "n_combos": h_total,
                "n_hrj_beats_har": h_beats,
                "win_rate": h_beats / h_total if h_total > 0 else float("nan"),
                "median_delta_sharpe": float(np.median(h_deltas)),
                "median_mse_reduction_pct": float(np.median(h_mses)),
            }
            per_horizon_rows.append(h_row)

    per_coin_df = pd.DataFrame(per_coin_rows)
    per_horizon_df = pd.DataFrame(per_horizon_rows)

    # Print summary
    print(f"\n{'='*70}")
    print("M12 HAR-RV-J Per-Coin Attribution")
    print(f"{'='*70}")
    print(f"\n{'Coin':<10} {'Beats':>7} {'Win%':>6} {'p-val':>8} {'Med ΔSharpe':>12} {'Med MSE%':>10}")
    print("-" * 60)
    for _, r in per_coin_df.iterrows():
        print(
            f"{r['coin']:<10} "
            f"{r['n_hrj_beats_har']:>3}/{r['n_combos']:<3} "
            f"{r['win_rate']*100:>5.1f}% "
            f"{r['p_value']:>8.4f} "
            f"{r['median_delta_sharpe']:>+12.4f} "
            f"{r['median_mse_reduction_pct']:>+9.1f}%"
        )

    # Per-horizon
    print(f"\nPer-Horizon Detail:")
    print(f"{'Coin':<10} {'h':>3} {'Beats':>7} {'Win%':>6} {'Med ΔSharpe':>12} {'Med MSE%':>10}")
    print("-" * 55)
    for _, r in per_horizon_df.iterrows():
        print(
            f"{r['coin']:<10} "
            f"{r['horizon']:>3} "
            f"{r['n_hrj_beats_har']:>3}/{r['n_combos']:<3} "
            f"{r['win_rate']*100:>5.1f}% "
            f"{r['median_delta_sharpe']:>+12.4f} "
            f"{r['median_mse_reduction_pct']:>+9.1f}%"
        )

    # Edge concentration
    winners = per_coin_df[per_coin_df["win_rate"] > 0.5]
    n_winners = len(winners)
    print(f"\nEdge concentration: {n_winners}/{len(COINS)} coins have win_rate > 50%")

    # Save
    per_coin_df.to_csv(RESULTS_DIR / "m12_per_coin_attribution.csv", index=False)
    out = {
        "model": "HAR-RV-J",
        "overall_verdict": data.get("verdict", "UNKNOWN"),
        "overall_p_sign": data.get("p_sign", float("nan")),
        "n_winners": n_winners,
        "n_coins": len(COINS),
        "per_coin": per_coin_rows,
        "per_horizon": per_horizon_rows,
    }
    with open(RESULTS_DIR / "m12_per_coin_results.json", "w") as f:
        json.dump(out, f, indent=2, default=str)

    print(f"\nSaved: {RESULTS_DIR / 'm12_per_coin_attribution.csv'}")
    print(f"Saved: {RESULTS_DIR / 'm12_per_coin_results.json'}")


if __name__ == "__main__":
    main()
