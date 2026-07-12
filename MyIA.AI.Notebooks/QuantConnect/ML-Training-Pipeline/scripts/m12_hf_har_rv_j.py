"""M12-HF HAR-RV-J — minute-frequency fork of M12 (high-frequency RV).

M12-HF (#4132): does MINUTE intraday sampling (1440 obs/day) improve HAR-RV-J
volatility forecasting vs M12-horaire (24 obs/day)?

This is a minimal fork of `m12_har_rv_j.py`. The estimators
(`daily_realized_variance`, `daily_bipower_variation`, `daily_jump_component`)
and the Kelly/walk-forward harness (`m11g_fee_aware_kelly`, `m11c_sharpe_test`,
`har_model`, `realized_variance`) are REUSED unchanged — they are
resolution-agnostic. The ONLY change vs M12-horaire is the data source:
`_load_one_coin_minute` (BTC owned tick -> resample 1-min, 0 QCC) replaces
`_load_one_coin` (hourly).

Scope (this fork, 0-QCC first execution): BTC-USD only — the most liquid coin,
where the minute-RV hypothesis is most testable. The owned Bitstamp tick covers
2011-2024, so the post-2018 decisive segment (bear-2022 + recovery-2023) is
reached with 0 QCC. Extension to ETH/SOL/ADA/DOT is subordinated to the BTC
verdict (would justify a targeted `lean data download` purchase then).

Baseline comparison:
    (a) M12-horaire  (the decisive comparison — same coin, hourly sampling)
    (b) HAR Classic  (no jump component)

Output:
    results/m12_hf/m12_hf_har_rv_j_results.csv
    results/m12_hf/results.json

Env: system Python 3.13 (no conda). CPU-only (OLS + pandas).
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
from m11g_fee_aware_kelly import (  # noqa: E402
    _binomial_pvalue_one_sided,
    _kelly_weights_and_returns,
    _net_at_fee,
)
from m11c_sharpe_test import ledoit_wolf_sharpe_diff_se  # noqa: E402
from realized_variance import (  # noqa: E402
    daily_realized_variance,
)
from minute_loader import load_btc_minute_returns  # noqa: E402
# Reuse the shared jump decomposition + HAR-RV-J model (identical to M12-horaire).
from m12_har_rv_j import (  # noqa: E402
    daily_jump_component,
    walk_forward_har_rv_j,
)

# 0-QCC first execution scope: BTC only (owned tick -> minute resample).
COINS = ["BTC-USD"]
HORIZONS = [1, 5, 10]
SEEDS = [0, 1, 7, 42]
SAMPLE_FREQ = "1min"  # near-optimal for liquid BTC; "5min" = defensive option
KELLY_CAP = 1.0
MU_WINDOW = 60
FEE_BPS = 50
N_SPLITS = 5
REFIT_EVERY = 22
RESULTS_DIR = SCRIPT_DIR / "results" / "m12_hf"


def _load_one_coin_minute(coin: str, cache: Path | None = None) -> pd.Series:
    """Minute log-returns for the coin from owned tick data (0 QCC).

    Currently BTC-only (the 0-QCC owned-tick path). Other coins would require a
    `lean data download` purchase (gated by the BTC verdict first).
    """
    if coin != "BTC-USD":
        raise NotImplementedError(
            f"Minute data for {coin} is not owned (0-QCC path). Only BTC-USD has "
            f"owned tick coverage (Bitstamp 2011-2024). Extending to other coins "
            f"requires a gated `lean data download` purchase (see M12_HF_PROPOSAL.md §4.5)."
        )
    return load_btc_minute_returns(sample_freq=SAMPLE_FREQ, tmp_cache=cache)


def _sharpe_ann(returns: np.ndarray) -> float:
    if len(returns) < 10:
        return float("nan")
    mu = float(np.mean(returns))
    sigma = float(np.std(returns, ddof=1))
    return (mu / sigma) * np.sqrt(365) if sigma > 1e-12 else float("nan")


def evaluate_one_combo(
    coin: str,
    horizon: int,
    seed: int,
    cache: Path | None = None,
) -> dict | None:
    """Run HAR-RV-J (minute) vs HAR Classic (minute) for one combo.

    The decisive comparison is M12-HF-minute vs M12-horaire (handled by the
    caller merging results.json from both runs); within this function both
    models use the SAME minute data, so HAR-RV-J vs HAR-Classic here isolates
    the jump-component contribution at minute frequency.
    """
    np.random.seed(seed)
    minute_rets = _load_one_coin_minute(coin, cache=cache)
    if len(minute_rets) < 1000:
        return None

    rv = daily_realized_variance(minute_rets)
    jumps = daily_jump_component(minute_rets)
    if len(rv) < 300 or len(jumps) < 300:
        return None

    common_idx = rv.index.intersection(jumps.index)
    rv = rv.loc[common_idx]
    jumps = jumps.loc[common_idx]

    # HAR Classic baseline (minute)
    try:
        har_out = walk_forward_har(rv, horizon=horizon, n_splits=N_SPLITS, refit_every=REFIT_EVERY)
    except (ValueError, Exception):
        return None

    # HAR-RV-J (minute)
    try:
        hrj_out = walk_forward_har_rv_j(
            rv, jumps, horizon=horizon, n_splits=N_SPLITS, refit_every=REFIT_EVERY
        )
    except (ValueError, Exception):
        return None

    har_fc = har_out["forecasts"]
    hrj_fc = hrj_out["forecasts"]
    common_fc_idx = har_fc.index.intersection(hrj_fc.index)
    if len(common_fc_idx) < 30:
        return None
    har_fc = har_fc.loc[common_fc_idx]
    hrj_fc = hrj_fc.loc[common_fc_idx]

    # Daily close returns (sum of intraday minute log returns per day)
    daily_rets = minute_rets.groupby(minute_rets.index.normalize()).sum().rename("r_daily")
    daily_rets.index = pd.DatetimeIndex(daily_rets.index).normalize()
    daily_rets = daily_rets.reindex(common_fc_idx).dropna()
    if len(daily_rets) < 30:
        return None
    har_fc = har_fc.reindex(daily_rets.index)
    hrj_fc = hrj_fc.reindex(daily_rets.index)

    har_pair = _kelly_weights_and_returns(daily_rets, har_fc, MU_WINDOW, KELLY_CAP)
    hrj_pair = _kelly_weights_and_returns(daily_rets, hrj_fc, MU_WINDOW, KELLY_CAP)
    if har_pair is None or hrj_pair is None:
        return None
    har_w, r = har_pair
    hrj_w, _ = hrj_pair
    if len(r) < 50:
        return None

    har_net = _net_at_fee(har_w, r, FEE_BPS)
    hrj_net = _net_at_fee(hrj_w, r, FEE_BPS)
    bh_net = r.copy()

    sharpe_har = _sharpe_ann(har_net)
    sharpe_hrj = _sharpe_ann(hrj_net)
    sharpe_bh = _sharpe_ann(bh_net)
    delta_sharpe_hrj_vs_har = sharpe_hrj - sharpe_har

    _, _, _, se = ledoit_wolf_sharpe_diff_se(hrj_net, har_net)
    t_stat = delta_sharpe_hrj_vs_har / se if isinstance(se, float) and se > 1e-12 else float("nan")

    target = har_out["targets"].reindex(common_fc_idx).dropna()
    har_pred_aligned = har_fc.reindex(target.index)
    hrj_pred_aligned = hrj_fc.reindex(target.index)
    mse_har = float(np.mean((har_pred_aligned - target) ** 2))
    mse_hrj = float(np.mean((hrj_pred_aligned - target) ** 2))
    mse_reduction_pct = (mse_hrj - mse_har) / mse_har * 100 if mse_har > 0 else float("nan")

    return {
        "coin": coin,
        "horizon": horizon,
        "seed": seed,
        "sample_freq": SAMPLE_FREQ,
        "sharpe_har": sharpe_har,
        "sharpe_hrj": sharpe_hrj,
        "sharpe_bh": sharpe_bh,
        "delta_sharpe_hrj_vs_har": delta_sharpe_hrj_vs_har,
        "lw_se": se,
        "t_stat": t_stat,
        "mse_har": mse_har,
        "mse_hrj": mse_hrj,
        "mse_reduction_pct": mse_reduction_pct,
        "n_obs": len(r),
        "hrj_preds": len(hrj_fc),
        "har_preds": len(har_fc),
        "n_minute_obs": len(minute_rets),
        "n_days": len(rv),
    }


def _csv_int_list(value: str) -> list[int]:
    return [int(s.strip()) for s in value.split(",") if s.strip()]


def main() -> None:
    parser = argparse.ArgumentParser(description="M12-HF HAR-RV-J minute sweep (BTC, 0 QCC)")
    parser.add_argument("--dry-run", action="store_true", help="Run BTC h=1 seed=0 only")
    parser.add_argument("--horizons", type=_csv_int_list, default=None)
    parser.add_argument("--seeds", type=_csv_int_list, default=None)
    parser.add_argument("--output", type=Path, default=None)
    args = parser.parse_args()

    horizons = args.horizons if args.horizons is not None else HORIZONS
    seeds = args.seeds if args.seeds is not None else SEEDS
    results_dir = args.output if args.output is not None else RESULTS_DIR
    results_dir.mkdir(parents=True, exist_ok=True)
    cache = results_dir / "_cache"

    t0 = time.time()
    combos: list[dict] = []

    if args.dry_run:
        print("[DRY RUN] BTC-USD h=1 seed=0 only (minute)")
        row = evaluate_one_combo("BTC-USD", 1, 0, cache=cache)
        if row:
            combos.append(row)
            print(json.dumps(row, indent=2, default=str))
        return

    total = len(COINS) * len(horizons) * len(seeds)
    done = 0
    for coin in COINS:
        for h in horizons:
            for seed in seeds:
                done += 1
                print(f"\n[{done}/{total}] {coin} h={h} seed={seed} (minute)", flush=True)
                row = evaluate_one_combo(coin, h, seed, cache=cache)
                if row is not None:
                    combos.append(row)
                else:
                    print("  SKIPPED (insufficient data)", flush=True)

    elapsed = time.time() - t0
    print(f"\n{'='*60}")
    print(f"M12-HF HAR-RV-J minute sweep: {len(combos)}/{total} combos in {elapsed:.0f}s")

    n_combos = len(combos)
    n_hrj_beats_har = sum(1 for r in combos if r["delta_sharpe_hrj_vs_har"] > 0)
    median_delta = (
        float(np.median([r["delta_sharpe_hrj_vs_har"] for r in combos])) if combos else float("nan")
    )
    p_sign = _binomial_pvalue_one_sided(n_hrj_beats_har, n_combos)

    print(f"\nSign-test (HRJ vs HAR, both minute): {n_hrj_beats_har}/{n_combos} "
          f"({n_hrj_beats_har/max(n_combos,1)*100:.1f}%)")
    print(f"  p-value = {p_sign:.4f}")
    print(f"  median delta-Sharpe (HRJ-HAR @minute) = {median_delta:+.6f}")
    print(f"\nNOTE: the DECISIVE comparison is M12-HF-minute vs M12-horaire.")
    print(f"      Cross-reference results/m12_har_rv_j/ for the hourly baseline.")

    if p_sign < 0.05 and n_hrj_beats_har / max(n_combos, 1) >= 0.60:
        verdict = "BEATS (HRJ vs HAR @minute)"
    elif p_sign < 0.10 and n_hrj_beats_har / max(n_combos, 1) >= 0.55:
        verdict = "INCONCLUSIVE (HRJ vs HAR @minute)"
    else:
        verdict = "NO BEATS (HRJ vs HAR @minute)"
    print(f"\nVERDICT (within-minute): {verdict}")

    results = {
        "model": "HAR-RV-J @ minute (M12-HF)",
        "reference": "Andersen, Bollerslev, Diebold (2007) + minute sampling",
        "sample_freq": SAMPLE_FREQ,
        "coins": COINS,
        "kelly_cap": KELLY_CAP,
        "fee_bps": FEE_BPS,
        "mu_window": MU_WINDOW,
        "n_splits": N_SPLITS,
        "refit_every": REFIT_EVERY,
        "n_combos": n_combos,
        "n_hrj_beats_har": n_hrj_beats_har,
        "win_rate": n_hrj_beats_har / max(n_combos, 1),
        "p_sign": p_sign,
        "median_delta_sharpe_hrj_vs_har": median_delta,
        "verdict_within_minute": verdict,
        "note": "Decisive comparison M12-HF-minute vs M12-horaire requires merging with results/m12_har_rv_j/.",
        "elapsed_s": elapsed,
        "combos": combos,
    }

    with open(results_dir / "results.json", "w") as f:
        json.dump(results, f, indent=2, default=str)
    if combos:
        pd.DataFrame(combos).to_csv(results_dir / "m12_hf_har_rv_j_results.csv", index=False)
    print(f"\nSaved: {results_dir / 'results.json'}")
    print(f"Saved: {results_dir / 'm12_hf_har_rv_j_results.csv'}")


if __name__ == "__main__":
    main()
