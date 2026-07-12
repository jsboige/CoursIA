"""M12-HF decisive comparison: MINUTE vs HOURLY HAR-RV-J on the SAME period.

The scientific question of M12-HF (#4132) is NOT "does adding jumps help at minute
frequency" (that is HAR-RV-J vs HAR-Classic, answered within `m12_hf_har_rv_j.py`),
but "does MINUTE sampling (1440 obs/day) beat HOURLY sampling (24 obs/day) for
HAR-RV-J volatility forecasting?" — i.e. is the realized-variance / bipower /
jump ESTIMATOR tighter at higher frequency?

This script runs HAR-RV-J on the SAME coin (BTC) over the SAME window (2018-01 ->
2024-02, the common coverage of both owned sources) at BOTH frequencies, then
compares the Kelly-strategy annualized Sharpe:

    delta = Sharpe(HAR-RV-J @ minute) - Sharpe(HAR-RV-J @ hourly)

plus a sign-test across the 12 combos (3 horizons x 4 seeds). This is the
"baseline (a) M12-horaire" decisive comparison of M12_HF_PROPOSAL.md §6.

0 QCC: both sources are owned (BTC Bitstamp tick -> minute resample; BTC Bitstamp
hourly CSV). CPU-only.

Output:
    results/m12_hf/compare_minute_vs_hourly.csv
    results/m12_hf/compare_minute_vs_hourly.json
"""

from __future__ import annotations

import json
import sys
import time
from pathlib import Path

import numpy as np
import pandas as pd

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

from har_model import walk_forward_har  # noqa: E402
from intraday_loader import hourly_log_returns, load_bitstamp_btc  # noqa: E402
from m11g_fee_aware_kelly import (  # noqa: E402
    _binomial_pvalue_one_sided,
    _kelly_weights_and_returns,
    _net_at_fee,
)
from m11c_sharpe_test import ledoit_wolf_sharpe_diff_se  # noqa: E402
from realized_variance import daily_realized_variance  # noqa: E402
from m12_har_rv_j import daily_jump_component, walk_forward_har_rv_j  # noqa: E402
from m12_hf_har_rv_j import (  # noqa: E402
    KELLY_CAP,
    MU_WINDOW,
    FEE_BPS,
    N_SPLITS,
    REFIT_EVERY,
    _load_one_coin_minute,
)

COIN = "BTC-USD"
HORIZONS = [1, 5, 10]
SEEDS = [0, 1, 7, 42]
RESULTS_DIR = SCRIPT_DIR / "results" / "m12_hf"
START = pd.Timestamp("2018-01-01")


def _sharpe_ann(returns: np.ndarray) -> float:
    if len(returns) < 10:
        return float("nan")
    mu = float(np.mean(returns))
    sigma = float(np.std(returns, ddof=1))
    return (mu / sigma) * np.sqrt(365) if sigma > 1e-12 else float("nan")


def _rv_jumps_and_daily(intraday_rets: pd.Series):
    """Shared pipeline: intraday returns -> (rv, jumps, daily_rets)."""
    rv = daily_realized_variance(intraday_rets)
    jumps = daily_jump_component(intraday_rets)
    common_idx = rv.index.intersection(jumps.index)
    rv = rv.loc[common_idx]
    jumps = jumps.loc[common_idx]
    daily_rets = intraday_rets.groupby(intraday_rets.index.normalize()).sum().rename("r_daily")
    daily_rets.index = pd.DatetimeIndex(daily_rets.index).normalize()
    return rv, jumps, daily_rets


def har_rv_j_sharpe(rv, jumps, daily_rets, horizon):
    """Run HAR-RV-J walk-forward + Kelly, return (sharpe_hrj_net, n_obs, mse)."""
    try:
        har_out = walk_forward_har(rv, horizon=horizon, n_splits=N_SPLITS, refit_every=REFIT_EVERY)
    except (ValueError, Exception):
        return None
    try:
        hrj_out = walk_forward_har_rv_j(
            rv, jumps, horizon=horizon, n_splits=N_SPLITS, refit_every=REFIT_EVERY
        )
    except (ValueError, Exception):
        return None
    hrj_fc = hrj_out["forecasts"]
    hrj_fc = hrj_fc.reindex(daily_rets.index)
    pair = _kelly_weights_and_returns(daily_rets, hrj_fc, MU_WINDOW, KELLY_CAP)
    if pair is None:
        return None
    w, r = pair
    if len(r) < 50:
        return None
    net = _net_at_fee(w, r, FEE_BPS)
    sharpe = _sharpe_ann(net)
    target = hrj_out["targets"].reindex(daily_rets.index).dropna()
    pred = hrj_fc.reindex(target.index)
    mse = float(np.mean((pred - target) ** 2)) if len(pred.dropna()) else float("nan")
    return {"sharpe": sharpe, "n_obs": len(r), "mse": mse}


def main() -> None:
    RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    cache = RESULTS_DIR / "_cache"
    t0 = time.time()

    print("Loading MINUTE returns (BTC, owned tick resample)...")
    minute_rets = _load_one_coin_minute(COIN, cache=cache)
    print(f"  {len(minute_rets):,} minute returns, {minute_rets.index.min()} -> {minute_rets.index.max()}")

    print("Loading HOURLY returns (BTC, Bitstamp CSV)...")
    hourly_rets = hourly_log_returns(load_bitstamp_btc())
    hourly_rets = hourly_rets[hourly_rets.index >= START]
    # Align to the minute coverage end (2024-02-11).
    hourly_rets = hourly_rets[hourly_rets.index <= minute_rets.index.max()]
    print(f"  {len(hourly_rets):,} hourly returns (>= {START:%Y-%m-%d}), "
          f"{hourly_rets.index.min()} -> {hourly_rets.index.max()}")

    rv_min, j_min, d_min = _rv_jumps_and_daily(minute_rets)
    rv_hr, j_hr, d_hr = _rv_jumps_and_daily(hourly_rets)
    print(f"  MINUTE: {len(rv_min):,} days | HOURLY: {len(rv_hr):,} days")

    combos = []
    total = len(HORIZONS) * len(SEEDS)
    done = 0
    for h in HORIZONS:
        for seed in SEEDS:
            done += 1
            np.random.seed(seed)
            m = har_rv_j_sharpe(rv_min, j_min, d_min, h)
            hr = har_rv_j_sharpe(rv_hr, j_hr, d_hr, h)
            if m is None or hr is None:
                print(f"  [{done}/{total}] h={h} seed={seed}: SKIPPED")
                continue
            delta = m["sharpe"] - hr["sharpe"]
            # Ledoit-Wolf paired SE between the two return streams
            # (reconstruct net streams for the SE — approximate via the Sharpe-diff SE
            #  on the two Kelly net return arrays is ideal; here we reuse the LW helper
            #  on the daily-return vs Kelly-residual proxy is complex, so we report
            #  the per-combo delta and the cross-combo sign-test as the headline.)
            row = {
                "coin": COIN,
                "horizon": h,
                "seed": seed,
                "sharpe_minute": m["sharpe"],
                "sharpe_hourly": hr["sharpe"],
                "delta_minute_minus_hourly": delta,
                "mse_minute": m["mse"],
                "mse_hourly": hr["mse"],
                "mse_reduction_pct": (m["mse"] - hr["mse"]) / hr["mse"] * 100 if hr["mse"] > 0 else float("nan"),
                "n_obs_minute": m["n_obs"],
                "n_obs_hourly": hr["n_obs"],
            }
            combos.append(row)
            print(f"  [{done}/{total}] h={h} seed={seed}: "
                  f"minute={m['sharpe']:+.4f} hourly={hr['sharpe']:+.4f} "
                  f"delta={delta:+.4f} (mse {row['mse_reduction_pct']:+.1f}%)")

    elapsed = time.time() - t0
    n = len(combos)
    n_beats = sum(1 for r in combos if r["delta_minute_minus_hourly"] > 0)
    median_delta = float(np.median([r["delta_minute_minus_hourly"] for r in combos])) if combos else float("nan")
    p_sign = _binomial_pvalue_one_sided(n_beats, n)

    print(f"\n{'='*60}")
    print(f"M12-HF decisive comparison: MINUTE vs HOURLY HAR-RV-J ({COIN}, 2018-2024)")
    print(f"  minute beats hourly: {n_beats}/{n} ({n_beats/max(n,1)*100:.1f}%)")
    print(f"  p-value (one-sided sign-test) = {p_sign:.4f}")
    print(f"  median delta-Sharpe (minute - hourly) = {median_delta:+.6f}")
    print(f"  elapsed {elapsed:.0f}s")

    # Per-horizon breakdown
    print(f"\nPer-horizon median delta-Sharpe (minute - hourly):")
    for h in HORIZONS:
        ds = [r["delta_minute_minus_hourly"] for r in combos if r["horizon"] == h]
        if ds:
            print(f"  h={h}: median {np.median(ds):+.6f}  (n={len(ds)})")

    # Verdict (BTC-only scope: the proposal's >=4/7 threshold does not apply to a
    # single-coin run; we report the sign-test verdict for the 12 combos instead).
    if p_sign < 0.05 and n_beats / max(n, 1) >= 0.60:
        verdict = "BEATS (minute > hourly, BTC)"
    elif p_sign < 0.10 and n_beats / max(n, 1) >= 0.55:
        verdict = "INCONCLUSIVE (minute > hourly, BTC)"
    else:
        verdict = "NO BEATS (minute <= hourly, BTC)"
    print(f"\nVERDICT: {verdict}")

    out = {
        "comparison": "M12-HF minute vs hourly HAR-RV-J (decisive)",
        "coin": COIN,
        "window": [str(minute_rets.index.min()), str(minute_rets.index.max())],
        "n_minute_returns": len(minute_rets),
        "n_hourly_returns": len(hourly_rets),
        "n_days_minute": len(rv_min),
        "n_days_hourly": len(rv_hr),
        "sample_freq_minute": "1min",
        "n_combos": n,
        "n_minute_beats_hourly": n_beats,
        "win_rate": n_beats / max(n, 1),
        "p_sign": p_sign,
        "median_delta_sharpe": median_delta,
        "verdict": verdict,
        "note": ("BTC-only 0-QCC execution. The proposal's >=4/7-coin threshold does "
                 "not apply; the sign-test verdict on 12 combos (3 horizons x 4 seeds) "
                 "is the headline. Extension to ETH/SOL/ADA/DOT is gated by this verdict."),
        "elapsed_s": elapsed,
        "combos": combos,
    }
    with open(RESULTS_DIR / "compare_minute_vs_hourly.json", "w") as f:
        json.dump(out, f, indent=2, default=str)
    if combos:
        pd.DataFrame(combos).to_csv(RESULTS_DIR / "compare_minute_vs_hourly.csv", index=False)
    print(f"\nSaved: {RESULTS_DIR / 'compare_minute_vs_hourly.json'}")
    print(f"Saved: {RESULTS_DIR / 'compare_minute_vs_hourly.csv'}")


if __name__ == "__main__":
    main()
