"""M10 Realized GARCH walk-forward training pipeline.

Walk-forward expanding window evaluation of Realized GARCH (Hansen 2012)
against HAR classic baseline. Multi-seed (0,1,7,42), multi-coin, multi-horizon.

Produces per-combo verdicts (BEATS_p005 / BEATS_p010 / BEATEN_p005 / INCONCLUSIVE)
with DM test and direction-aware classification.

Usage:
    python train_realized_garch.py
    python train_realized_garch.py --coins BTC-USD ETH-USD --horizons 1 5 10
    python train_realized_garch.py --seeds 0 1 --dry-run
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

from realized_garch import (
    RealizedGARCHParams,
    fit_realized_garch,
    realized_garch_log_forecast_at,
)
from realized_variance import daily_realized_variance, realized_variance_to_log
from har_model import HARModel, walk_forward_har
from intraday_loader import hourly_log_returns, load_bitstamp_btc, load_binance_eth, load_yf_intraday
from diebold_mariano import diebold_mariano_test

SEEDS = [0, 1, 7, 42]
HORIZONS = [1, 5, 10]
COINS = ["ADA-USD", "BTC-USD", "DOT-USD", "ETH-USD", "LTC-USD", "SOL-USD", "XRP-USD"]
TRAIN_SIZE = 250
REFIT_EVERY = 22
RESULTS_DIR = SCRIPT_DIR.parent / "results"


def load_coin_hourly(coin: str, skip_remote: bool = False) -> pd.Series | None:
    """Load hourly log returns for a coin."""
    try:
        if coin == "BTC-USD":
            ds = load_bitstamp_btc()
            return hourly_log_returns(ds)
        elif coin == "ETH-USD":
            ds = load_binance_eth()
            return hourly_log_returns(ds)
        elif not skip_remote:
            ds = load_yf_intraday(coin)
            return hourly_log_returns(ds)
    except Exception as exc:
        print(f"  [WARN] {coin} load failed: {exc}")
    return None


def classify_combo(dm_stat: float, p_value: float) -> str:
    """Direction-aware DM verdict classification."""
    if np.isnan(p_value) or np.isnan(dm_stat):
        return "INCONCLUSIVE"
    if p_value < 0.05:
        if dm_stat < 0:
            return "BEATS_p005"
        else:
            return "BEATEN_p005"
    if p_value < 0.10:
        if dm_stat < 0:
            return "BEATS_p010"
        else:
            return "BEATEN_p010"
    return "INCONCLUSIVE"


def walk_forward_realized_garch(
    returns: np.ndarray,
    rv: np.ndarray,
    dates: pd.DatetimeIndex,
    horizon: int = 1,
    train_size: int = 250,
    refit_every: int = 22,
    seed: int = 0,
) -> dict:
    """Walk-forward expanding window Realized GARCH evaluation.

    The forecast at origin ``i`` uses information through day ``i-1`` and
    predicts the mean log-RV over ``[i, i+horizon)`` — the *same* target
    definition as :func:`walk_forward_har`. Errors are returned as a
    date-indexed Series so the caller can align them with the HAR errors
    on the common forecast dates before running the Diebold-Mariano test.

    The previous version shifted the target by a spurious ``gap`` of 10
    days (``log_rv[i+gap:i+gap+horizon]``) while the GARCH forecast itself
    was an ``horizon``-step forecast — the forecast and the target were
    mismatched, and the bare numpy errors were later truncated by
    *position* against the HAR 5-fold errors, so the DM test compared
    different dates entirely. Both issues are fixed here.
    """
    np.random.seed(seed)
    n = len(returns)
    if n < train_size + horizon + 30:
        return {"error": f"insufficient data: {n} < {train_size + horizon + 30}"}

    log_rv = np.log(np.clip(rv, 1e-12, None))

    preds: list[float] = []
    truths: list[float] = []
    pred_dates: list[pd.Timestamp] = []

    params = None
    h_cache = None
    last_refit_idx = -1

    for i in range(train_size, n - horizon):
        if (i - last_refit_idx) >= refit_every or params is None:
            r_train = returns[:i]
            rv_train = rv[:i]
            try:
                params = fit_realized_garch(r_train, rv_train)
            except Exception as exc:
                if len(preds) == 0:
                    return {"error": f"MLE fit failed at i={i}: {exc}"}
                break
            h_t = params.omega / (1.0 - params.alpha - params.beta + 1e-12)
            for t in range(1, i):
                h_t = params.omega + params.alpha * r_train[t - 1] ** 2 + params.beta * h_t
                h_t = max(h_t, 1e-12)
            h_cache = h_t
            last_refit_idx = i
        else:
            h_cache = params.omega + params.alpha * returns[i - 1] ** 2 + params.beta * h_cache
            h_cache = max(h_cache, 1e-12)

        log_pred = realized_garch_log_forecast_at(params, h_cache, horizon=horizon)
        target_window = log_rv[i: i + horizon]
        if len(target_window) < horizon:
            continue
        target = float(target_window.mean())

        preds.append(log_pred)
        truths.append(target)
        pred_dates.append(dates[i])

    if len(preds) < 20:
        return {"error": f"too few predictions: {len(preds)}"}

    preds_arr = np.array(preds)
    truths_arr = np.array(truths)
    mse = float(np.mean((preds_arr - truths_arr) ** 2))
    idx = pd.DatetimeIndex(pred_dates)

    return {
        "n_preds": len(preds),
        "mse_logrv": mse,
        "errors": pd.Series(truths_arr - preds_arr, index=idx, name="rg_error"),
        "forecasts": pd.Series(preds_arr, index=idx, name="rg_logrv_pred"),
        "targets": pd.Series(truths_arr, index=idx, name="logrv_target"),
    }


def run_one_combo(
    coin: str,
    horizon: int,
    seed: int,
    hourly_rets: pd.Series,
) -> dict:
    """Run one coin × horizon × seed combo."""
    rv = daily_realized_variance(hourly_rets)
    if len(rv) < 400:
        return {"coin": coin, "horizon": horizon, "seed": seed, "error": f"rv days={len(rv)} < 400"}

    daily_rets = hourly_rets.groupby(hourly_rets.index.normalize()).sum()
    daily_rets.index = pd.DatetimeIndex(daily_rets.index).normalize()
    common = daily_rets.index.intersection(rv.index)
    common_dates = pd.DatetimeIndex(common)
    daily_rets_v = daily_rets.loc[common].values.astype(float)
    rv_vals = rv.loc[common].values.astype(float)
    rv_common = rv.loc[common]

    rg_result = walk_forward_realized_garch(
        daily_rets_v, rv_vals, common_dates,
        horizon=horizon,
        train_size=TRAIN_SIZE,
        refit_every=REFIT_EVERY,
        seed=seed,
    )

    if "error" in rg_result:
        return {"coin": coin, "horizon": horizon, "seed": seed, "error": rg_result["error"]}

    # HAR baseline on the *same* daily-RV series (restricted to the common
    # dates) so both models consume identical data — only the walk-forward
    # windowing differs (RG expanding-from-train_size vs HAR 5-fold).
    har_out = walk_forward_har(rv_common, horizon=horizon, n_splits=5, refit_every=REFIT_EVERY)
    har_err = (har_out["forecasts"] - har_out["targets"]).dropna()
    har_err.name = "har_error"
    rg_err = rg_result["errors"]

    # Align both error series on their common forecast dates — the DM test
    # is only valid when the two models are scored on identical (date,
    # target) pairs. Position-based truncation (the previous [:min_len])
    # silently compared errors from different calendar dates.
    aligned = pd.concat([rg_err, har_err], axis=1, sort=True).dropna()
    if len(aligned) < 20:
        return {
            "coin": coin, "horizon": horizon, "seed": seed,
            "rg_mse": rg_result["mse_logrv"],
            "har_mse": har_out["aggregate_mse_logrv"],
            "error": f"date-aligned overlap too short: {len(aligned)}",
        }

    rg_err_aligned = aligned["rg_error"].to_numpy()
    har_err_aligned = aligned["har_error"].to_numpy()

    rg_mse = float(np.mean(rg_err_aligned ** 2))
    har_mse = float(np.mean(har_err_aligned ** 2))
    mse_red_pct = (har_mse - rg_mse) / har_mse * 100.0 if har_mse > 0 else 0.0

    dm = diebold_mariano_test(rg_err_aligned, har_err_aligned, h=horizon)
    verdict = classify_combo(dm["dm_stat"], dm["p_value"])

    return {
        "coin": coin,
        "horizon": horizon,
        "seed": seed,
        "n_preds": rg_result["n_preds"],
        "n_aligned": int(len(aligned)),
        "rg_mse": rg_mse,
        "har_mse": har_mse,
        "mse_red_pct": round(mse_red_pct, 2),
        "dm_stat": round(dm["dm_stat"], 4),
        "dm_pvalue": round(dm["p_value"], 6),
        "verdict": verdict,
    }


def run_all(
    coins: list[str],
    horizons: list[int],
    seeds: list[int],
    skip_remote: bool = False,
    dry_run: bool = False,
) -> list[dict]:
    """Run all combos and return results."""
    results: list[dict] = []
    hourly_cache: dict[str, pd.Series] = {}

    total = len(coins) * len(horizons) * len(seeds)
    done = 0

    for coin in coins:
        if coin not in hourly_cache:
            print(f"\n[load] {coin} ...")
            hourly_cache[coin] = load_coin_hourly(coin, skip_remote)
        rets = hourly_cache[coin]
        if rets is None:
            print(f"  [SKIP] {coin}: no data")
            for h in horizons:
                for s in seeds:
                    results.append({"coin": coin, "horizon": h, "seed": s, "error": "no data"})
                    done += 1
            continue

        for h in horizons:
            for s in seeds:
                done += 1
                print(f"[{done}/{total}] {coin} h={h} seed={s} ... ", end="", flush=True)
                if dry_run:
                    print("DRY-RUN")
                    results.append({"coin": coin, "horizon": h, "seed": s, "verdict": "DRY-RUN"})
                    continue
                try:
                    row = run_one_combo(coin, h, s, rets)
                    if "error" in row and "verdict" not in row:
                        print(f"ERROR: {row['error']}")
                    else:
                        print(f"{row.get('verdict', 'ERROR')} mse_red={row.get('mse_red_pct', 'N/A')}%")
                    results.append(row)
                except Exception as exc:
                    print(f"EXCEPTION: {exc}")
                    results.append({"coin": coin, "horizon": h, "seed": s, "error": str(exc)})

    return results


def summarize_results(results: list[dict]) -> dict:
    """Aggregate per-coin-horizon verdicts with sign-test."""
    from collections import defaultdict
    from scipy import stats as sp_stats

    combo_verdicts: dict[tuple, list[str]] = defaultdict(list)
    combo_details: dict[tuple, dict] = {}

    for r in results:
        if "error" in r and "verdict" not in r:
            continue
        key = (r["coin"], r["horizon"])
        v = r.get("verdict", "INCONCLUSIVE")
        combo_verdicts[key].append(v)

    rows = []
    total_beats = 0
    total_beaten = 0
    total_inconclusive = 0
    total_combos = 0

    for (coin, h), verdicts in sorted(combo_verdicts.items()):
        n_beats = sum(1 for v in verdicts if v.startswith("BEATS"))
        n_beaten = sum(1 for v in verdicts if v.startswith("BEATEN"))
        n_seeds = len(verdicts)

        beats_count = n_beats
        sign_p = float(sp_stats.binomtest(beats_count, n_seeds, 0.5).pvalue) if n_seeds > 0 else 1.0

        if beats_count >= n_seeds * 0.75 and sign_p < 0.10:
            combo_verdict = f"BEATS_p{int(round(sign_p * 100)):03d}" if sign_p < 0.05 else "BEATS_p010"
        elif n_beaten >= n_seeds * 0.75:
            combo_verdict = "BEATEN_p005"
        else:
            combo_verdict = "INCONCLUSIVE"

        if combo_verdict.startswith("BEATS"):
            total_beats += 1
        elif combo_verdict.startswith("BEATEN"):
            total_beaten += 1
        else:
            total_inconclusive += 1
        total_combos += 1

        avg_mse_red = 0.0
        details_for_combo = [r for r in results if r.get("coin") == coin and r.get("horizon") == h and "mse_red_pct" in r]
        if details_for_combo:
            avg_mse_red = np.mean([d["mse_red_pct"] for d in details_for_combo])

        rows.append({
            "coin": coin,
            "horizon": h,
            "seeds": n_seeds,
            "beats": f"{beats_count}/{n_seeds}",
            "avg_mse_red_pct": round(avg_mse_red, 2),
            "combo_verdict": combo_verdict,
        })

    return {
        "per_combo": rows,
        "summary": {
            "total_combos": total_combos,
            "BEATS": total_beats,
            "BEATEN": total_beaten,
            "INCONCLUSIVE": total_inconclusive,
            "model": "M10_Realized_GARCH",
            "params": "7-9 (omega, alpha, beta, xi, phi, sigma_u, gamma1, gamma2)",
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="M10 Realized GARCH training")
    parser.add_argument("--coins", nargs="*", default=COINS)
    parser.add_argument("--horizons", type=int, nargs="*", default=HORIZONS)
    parser.add_argument("--seeds", type=int, nargs="*", default=SEEDS)
    parser.add_argument("--skip-remote", action="store_true")
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--out-json", type=str, default=None)
    args = parser.parse_args()

    t0 = time.time()
    print(f"=== M10 Realized GARCH (Hansen 2012) ===")
    print(f"Coins: {args.coins}")
    print(f"Horizons: {args.horizons}")
    print(f"Seeds: {args.seeds}")
    print(f"Total combos: {len(args.coins) * len(args.horizons) * len(args.seeds)}")
    print()

    results = run_all(
        coins=args.coins,
        horizons=args.horizons,
        seeds=args.seeds,
        skip_remote=args.skip_remote,
        dry_run=args.dry_run,
    )

    summary = summarize_results(results)
    elapsed = time.time() - t0

    print(f"\n=== M10 Results ({elapsed:.0f}s) ===")
    print(f"Model: {summary['summary']['model']}")
    print(f"BEATS: {summary['summary']['BEATS']}")
    print(f"BEATEN: {summary['summary']['BEATEN']}")
    print(f"INCONCLUSIVE: {summary['summary']['INCONCLUSIVE']}")
    print(f"Total combos: {summary['summary']['total_combos']}")

    print("\nPer-combo verdicts:")
    for row in summary["per_combo"]:
        print(f"  {row['coin']} h={row['horizon']}: {row['combo_verdict']} "
              f"(seeds: {row['seeds']}, beats: {row['beats']}, mse_red: {row['avg_mse_red_pct']:.1f}%)")

    out_path = Path(args.out_json) if args.out_json else RESULTS_DIR / "m10_realized_garch.json"
    out_path.parent.mkdir(parents=True, exist_ok=True)
    output = {
        "model": "M10_Realized_GARCH",
        "reference": "Hansen, Huang, Shek (2012)",
        "params": summary["summary"]["params"],
        "elapsed_s": round(elapsed, 1),
        "per_seed_results": results,
        "summary": summary,
    }
    out_path.write_text(json.dumps(output, indent=2, default=str))
    print(f"\n[done] Wrote {out_path}")


if __name__ == "__main__":
    main()
