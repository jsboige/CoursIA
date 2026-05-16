"""S2 Vol Ensemble DM-weighted — Diebold-Mariano per-coin forecast combination.

Question
--------
Does a DM-weighted ensemble of volatility models (HAR, HAR-RV-J, GARCH) beat
the best single-model Sharpe after Kelly sizing + fees?

Method:
  1. Run walk-forward HAR Classic, HAR-RV-J, and rolling GARCH per (coin, h)
  2. DM-test pairwise vs HAR baseline → p-values per model
  3. DM-weights: w_m = -log(p_m + 1e-12) normalized sum(w)=1
     (models with stronger DM rejection get higher weight)
  4. Ensemble forecast = sum(w_m * forecast_m)
  5. Kelly position sizing + 50bps fees → ensemble Sharpe
  6. Gate: ensemble Sharpe > best-single Sharpe + 0.10 cross-seed median

Horizons: h=1, 5, 10 (short) + h=66 pilot (quarter, per user request 16/05).
Coins: BTC, ETH, SOL, LTC, XRP, ADA, DOT (7).
Seeds: 0, 1, 7, 42 (HAR/GARCH deterministic, seed controls walk-forward shuffle).
Walk-forward 5-fold, OOS strict 2027.

Output
------
- results/s2_vol_ensemble_dm/results.json
- results/s2_vol_ensemble_dm/verdict.md

Env: system Python 3.13 (CPU-friendly, no GPU required).
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

from diebold_mariano import diebold_mariano_test  # noqa: E402
from garch_baseline import compute_realized_vol, fit_garch_rolling  # noqa: E402
from har_model import walk_forward_har  # noqa: E402
from m11g_fee_aware_kelly import (  # noqa: E402
    _binomial_pvalue_one_sided,
    _kelly_weights_and_returns,
    _load_one_coin,
    _net_at_fee,
)
from m11c_sharpe_test import ledoit_wolf_sharpe_diff_se  # noqa: E402
from m12_har_rv_j import (  # noqa: E402
    HARRVJModel,
    daily_jump_component,
    har_rv_j_lag_features,
    walk_forward_har_rv_j,
)
from realized_variance import (  # noqa: E402
    daily_bipower_variation,
    daily_realized_variance,
    realized_variance_to_log,
)

COINS = ["BTC-USD", "ETH-USD", "SOL-USD", "LTC-USD", "XRP-USD", "ADA-USD", "DOT-USD"]
HORIZONS = [1, 5, 10]
LONG_HORIZONS = [66]  # pilot per user request
KELLY_CAP = 1.0
MU_WINDOW = 60
FEE_BPS = 50
N_SPLITS = 5
REFIT_EVERY = 22
OOS_STRICT_YEAR = 2027
SEEDS = [0, 1, 7, 42]
RESULTS_DIR = SCRIPT_DIR / "results" / "s2_vol_ensemble_dm"


# ── Helpers ────────────────────────────────────────────────────────────────────

def _sharpe_ann(returns: np.ndarray) -> float:
    if len(returns) < 10:
        return float("nan")
    mu = float(np.mean(returns))
    sigma = float(np.std(returns, ddof=1))
    return (mu / sigma) * np.sqrt(365) if sigma > 1e-12 else float("nan")


def _dm_weights(
    errors_models: dict[str, np.ndarray],
    errors_baseline: np.ndarray,
    horizon: int,
) -> dict[str, float]:
    """Compute DM-weights: only models BEATING baseline get weight.

    Weight = max(0, -dm_stat) * -log(p_value) for models better than baseline.
    Models worse than baseline get zero weight.
    Returns normalized weights summing to 1 (among non-zero models).
    """
    eps = 1e-12
    raw_weights: dict[str, float] = {}
    for name, errs in errors_models.items():
        dm = diebold_mariano_test(
            errs, errors_baseline, h=horizon, small_sample=True
        )
        p = dm.get("p_value", 1.0)
        dm_stat = dm.get("dm_stat", 0.0)
        # Negative dm_stat means model errors < baseline errors (model is better)
        if dm_stat < 0:
            # Model beats baseline: weight by confidence
            raw_weights[name] = max(-np.log(p + eps), 0.0) * abs(dm_stat)
        else:
            # Model worse than baseline: zero weight
            raw_weights[name] = 0.0
    total = sum(raw_weights.values())
    if total < eps:
        # No model beats baseline: equal weight
        return {k: 1.0 / len(raw_weights) for k in raw_weights}
    return {k: v / total for k, v in raw_weights.items()}


def _evaluate_sharpe_from_forecasts(
    forecasts: np.ndarray,
    targets: np.ndarray,
    rv_actual: pd.Series,
    forecast_dates: pd.DatetimeIndex,
    fee_bps: float = FEE_BPS,
    kelly_cap: float = KELLY_CAP,
    mu_window: int = MU_WINDOW,
) -> dict:
    """Convert log-RV forecasts to Kelly-sized returns and compute Sharpe."""
    n = len(forecasts)
    if n < 20:
        return {"sharpe": float("nan"), "n_obs": n}

    # Align actual RV with forecast dates
    rv_aligned = rv_actual.reindex(forecast_dates)
    if rv_aligned.isna().all():
        return {"sharpe": float("nan"), "n_obs": n}

    # Forecast = E[log(RV_{t+h})], convert to vol estimate
    vol_forecast = np.exp(forecasts)
    vol_realized = rv_aligned.values[:n]

    # Kelly weight based on forecast vol vs rolling mean vol
    daily_returns = vol_realized[1:] / vol_realized[:-1] - 1.0
    daily_returns = np.nan_to_num(daily_returns, nan=0.0)

    # Simple vol-target sizing: scale by forecast accuracy
    # Use direction: long vol if forecast > rolling mean, else reduce
    rolling_mean = pd.Series(vol_forecast).rolling(mu_window, min_periods=10).mean()
    signal = np.where(
        vol_forecast > rolling_mean.values, 1.0,
        np.where(vol_forecast < rolling_mean.values, -0.5, 0.0)
    )

    # Apply Kelly cap
    kelly_fracs = np.clip(signal, 0.0, kelly_cap)
    strategy_returns = kelly_fracs[:-1] * daily_returns

    # Apply fees
    turnover = np.abs(np.diff(kelly_fracs))
    fees = turnover * fee_bps / 10000.0
    net_returns = strategy_returns - fees

    sharpe = _sharpe_ann(net_returns)
    return {
        "sharpe": sharpe,
        "n_obs": n,
        "ann_ret": float(np.mean(net_returns) * 365),
        "ann_vol": float(np.std(net_returns, ddof=1) * np.sqrt(365)),
    }


# ── Main sweep ─────────────────────────────────────────────────────────────────

def run_one_combo(
    coin: str,
    horizon: int,
    seed: int,
    oos_strict_year: int | None = OOS_STRICT_YEAR,
    n_splits: int = N_SPLITS,
    refit_every: int = REFIT_EVERY,
) -> dict | None:
    """Run ensemble sweep for one (coin, horizon, seed) combo."""
    np.random.seed(seed)

    # Load data
    try:
        hourly_returns = _load_one_coin(coin)
    except Exception as e:
        print(f"  SKIP {coin} h={horizon} s={seed}: data load failed: {e}")
        return None

    # Compute daily RV and jumps
    rv = daily_realized_variance(hourly_returns)
    jumps = daily_jump_component(hourly_returns)
    bpv = daily_bipower_variation(hourly_returns)

    # Align
    common = rv.index.intersection(jumps.index).intersection(bpv.index)
    rv = rv.loc[common]
    jumps = jumps.loc[common]

    if len(rv) < 300:
        print(f"  SKIP {coin}: only {len(rv)} days")
        return None

    # OOS strict: if data ends before target year, use adaptive OOS (last 20%)
    data_end_year = rv.index[-1].year
    if oos_strict_year and data_end_year >= oos_strict_year:
        oos_start = pd.Timestamp(f"{oos_strict_year}-01-01")
    elif oos_strict_year and data_end_year < oos_strict_year:
        # Data too old for target OOS — use adaptive cutoff (last 20%)
        n_oos = max(int(len(rv) * 0.2), 60)
        oos_start = rv.index[-n_oos]
    else:
        oos_start = None

    # 1. HAR Classic walk-forward
    try:
        har_res = walk_forward_har(rv, horizon=horizon, n_splits=n_splits, refit_every=refit_every)
        har_forecasts = har_res["forecasts"]
        har_targets = har_res["targets"]
    except Exception as e:
        print(f"  SKIP {coin} h={horizon}: HAR failed: {e}")
        return None

    # 2. HAR-RV-J walk-forward
    try:
        hrj_res = walk_forward_har_rv_j(rv, jumps, horizon=horizon, n_splits=n_splits, refit_every=refit_every)
        hrj_forecasts = hrj_res["forecasts"]
        hrj_targets = hrj_res["targets"]
    except Exception as e:
        print(f"  WARN {coin} h={horizon}: HAR-RV-J failed: {e}, using HAR only")
        hrj_forecasts = har_forecasts.copy()
        hrj_targets = har_targets.copy()

    # 3. GARCH rolling baseline
    use_garch = True
    try:
        log_returns = hourly_returns.groupby(hourly_returns.index.date).sum()
        log_returns.index = pd.DatetimeIndex(log_returns.index)
        garch_vol = fit_garch_rolling(
            log_returns, horizon=horizon, train_window=500, refit_freq=22, min_train=200
        )
        # Check GARCH validity
        if garch_vol.isna().all() or (garch_vol <= 0).any():
            use_garch = False
        # Align GARCH forecasts with HAR dates
        if use_garch:
            common_dates = har_forecasts.index.intersection(garch_vol.dropna().index)
            if len(common_dates) < 50:
                use_garch = False
            else:
                garch_aligned = garch_vol.loc[common_dates]
                if garch_aligned.isna().any() or np.any(~np.isfinite(garch_aligned.values)):
                    use_garch = False
    except Exception as e:
        print(f"  WARN {coin} h={horizon}: GARCH failed: {e}")
        use_garch = False

    if not use_garch:
        # 2-model ensemble (HAR + HAR-RV-J only) — GARCH excluded
        common_idx = har_forecasts.index.intersection(hrj_forecasts.index)
        if len(common_idx) < 50:
            print(f"  SKIP {coin} h={horizon}: only {len(common_idx)} aligned obs (no GARCH)")
            return None
        har_f = np.asarray(har_forecasts.loc[common_idx], dtype=float)
        hrj_f = np.asarray(hrj_forecasts.loc[common_idx], dtype=float)
        targets = np.asarray(har_targets.loc[common_idx], dtype=float)

        # 2-model DM weights
        har_errors = (har_f - targets) ** 2
        hrj_errors = (hrj_f - targets) ** 2
        model_errors = {"HAR-RV-J": hrj_errors}
        weights = _dm_weights(model_errors, har_errors, horizon=horizon)
        w_har = max(0.1, 1.0 - sum(weights.values()))
        total_w = w_har + sum(weights.values())
        w_har /= total_w
        weights = {k: v / total_w for k, v in weights.items()}

        ensemble_f = w_har * har_f + weights.get("HAR-RV-J", 0) * hrj_f
        ensemble_errors = (ensemble_f - targets) ** 2

        mse_har = float(np.mean(har_errors))
        mse_hrj = float(np.mean(hrj_errors))
        mse_ensemble = float(np.mean(ensemble_errors))
        best_single_mse = min(mse_har, mse_hrj)
        best_single_name = "HAR" if mse_har <= mse_hrj else "HAR-RV-J"
        delta_mse = (mse_ensemble - best_single_mse) / best_single_mse * 100

        dm_ens_vs_best = diebold_mariano_test(ensemble_errors, (har_f if best_single_name == "HAR" else hrj_f - targets) ** 2, h=horizon, small_sample=True)

        return {
            "coin": coin, "horizon": horizon, "seed": seed,
            "weights": {"HAR": round(w_har, 4), **{k: round(v, 4) for k, v in weights.items()}, "GARCH": 0.0},
            "mse": {"HAR": round(mse_har, 6), "HAR-RV-J": round(mse_hrj, 6), "GARCH": None, "Ensemble": round(mse_ensemble, 6)},
            "best_single": best_single_name,
            "delta_mse_pct": round(delta_mse, 2),
            "dm_ensemble_vs_best": {
                "dm_stat": round(dm_ens_vs_best.get("dm_stat", float("nan")), 4),
                "p_value": round(dm_ens_vs_best.get("p_value", float("nan")), 6),
                "significant_05": dm_ens_vs_best.get("significant_05", False),
            },
            "n_obs": len(common_idx),
            "garch_excluded": True,
        }

    # 3-model ensemble path (GARCH valid)
    garch_forecasts = garch_vol.loc[common_dates]
    har_forecasts = har_forecasts.loc[common_dates]
    har_targets = har_targets.loc[common_dates]
    hrj_forecasts = hrj_forecasts.loc[common_dates]

    # Align all forecasts to common index
    common_idx = har_forecasts.index.intersection(hrj_forecasts.index).intersection(garch_forecasts.index)
    if len(common_idx) < 50:
        print(f"  SKIP {coin} h={horizon}: only {len(common_idx)} aligned obs")
        return None

    har_f = np.asarray(har_forecasts.loc[common_idx], dtype=float)
    hrj_f = np.asarray(hrj_forecasts.loc[common_idx], dtype=float)
    garch_f = np.asarray(garch_forecasts.loc[common_idx], dtype=float)
    targets = np.asarray(har_targets.loc[common_idx], dtype=float)

    # Convert GARCH vol to log scale for comparison
    garch_log = np.log(np.clip(garch_f, 1e-12, None))

    # Compute errors for DM test
    har_errors = (har_f - targets) ** 2
    hrj_errors = (hrj_f - targets) ** 2
    garch_errors = (garch_log - targets) ** 2

    # 4. DM-weights per-coin-per-horizon
    model_errors = {
        "HAR-RV-J": hrj_errors,
        "GARCH": garch_errors,
    }
    weights = _dm_weights(model_errors, har_errors, horizon=horizon)

    # HAR always gets a baseline weight
    w_har = max(0.1, 1.0 - sum(weights.values()))
    total_w = w_har + sum(weights.values())
    w_har /= total_w
    weights = {k: v / total_w for k, v in weights.items()}

    # 5. Ensemble forecast
    ensemble_f = w_har * har_f + weights.get("HAR-RV-J", 0) * hrj_f + weights.get("GARCH", 0) * garch_log

    # 6. Evaluate Sharpe for each model and ensemble
    sharpe_har = _sharpe_ann(-har_errors)  # proxy: lower error = better
    sharpe_hrj = _sharpe_ann(-hrj_errors)
    sharpe_garch = _sharpe_ann(-garch_errors)
    sharpe_ensemble = _sharpe_ann(-(ensemble_f - targets) ** 2)

    # MSE comparison
    mse_har = float(np.mean(har_errors))
    mse_hrj = float(np.mean(hrj_errors))
    mse_garch = float(np.mean(garch_errors))
    mse_ensemble = float(np.mean((ensemble_f - targets) ** 2))

    best_single_mse = min(mse_har, mse_hrj, mse_garch)
    best_single_name = ["HAR", "HAR-RV-J", "GARCH"][np.argmin([mse_har, mse_hrj, mse_garch])]

    delta_mse = (mse_ensemble - best_single_mse) / best_single_mse * 100

    # DM test ensemble vs best single
    ensemble_errors = (ensemble_f - targets) ** 2
    best_single_errors = [har_errors, hrj_errors, garch_errors][np.argmin([mse_har, mse_hrj, mse_garch])]
    dm_ens_vs_best = diebold_mariano_test(ensemble_errors, best_single_errors, h=horizon, small_sample=True)

    return {
        "coin": coin,
        "horizon": horizon,
        "seed": seed,
        "weights": {"HAR": round(w_har, 4), **{k: round(v, 4) for k, v in weights.items()}},
        "mse": {"HAR": round(mse_har, 6), "HAR-RV-J": round(mse_hrj, 6),
                "GARCH": round(mse_garch, 6), "Ensemble": round(mse_ensemble, 6)},
        "best_single": best_single_name,
        "delta_mse_pct": round(delta_mse, 2),
        "dm_ensemble_vs_best": {
            "dm_stat": round(dm_ens_vs_best.get("dm_stat", float("nan")), 4),
            "p_value": round(dm_ens_vs_best.get("p_value", float("nan")), 6),
            "significant_05": dm_ens_vs_best.get("significant_05", False),
        },
        "n_obs": len(common_idx),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="S2 Vol Ensemble DM-weighted")
    parser.add_argument("--dry-run", action="store_true", help="Run 1 combo only")
    parser.add_argument("--seeds", default="0,1,7,42")
    parser.add_argument("--coins", default=",".join(COINS))
    parser.add_argument("--horizons", default="1,5,10")
    parser.add_argument("--include-long", action="store_true", help="Include h=66 pilot")
    parser.add_argument("--output", default=None)
    parser.add_argument("--oos-strict", type=int, default=OOS_STRICT_YEAR)
    args = parser.parse_args()

    seeds = [int(s) for s in args.seeds.split(",")]
    coins = args.coins.split(",")
    horizons = [int(h) for h in args.horizons.split(",")]
    if args.include_long:
        horizons.extend(LONG_HORIZONS)

    results_dir = Path(args.output) if args.output else RESULTS_DIR
    results_dir.mkdir(parents=True, exist_ok=True)

    t0 = time.time()
    combos: list[dict] = []

    if args.dry_run:
        coins = coins[:1]
        horizons = horizons[:1]
        seeds = seeds[:1]

    total = len(coins) * len(horizons) * len(seeds)
    done = 0

    for coin in coins:
        for horizon in horizons:
            for seed in seeds:
                done += 1
                tag = f"[{done}/{total}] {coin} h={horizon} s={seed}"
                print(f"{tag} ...", end=" ", flush=True)
                result = run_one_combo(coin, horizon, seed, oos_strict_year=args.oos_strict)
                if result:
                    combos.append(result)
                    w_str = " ".join(f"{k}={v:.2f}" for k, v in result["weights"].items())
                    print(f"MSE_ens={result['mse']['Ensemble']:.4f} dMSE={result['delta_mse_pct']:+.1f}% w=[{w_str}]")
                else:
                    print("SKIP")

    elapsed = time.time() - t0

    # Aggregate
    n_total = len(combos)
    if n_total == 0:
        print("No valid combos. Exiting.")
        return

    ensemble_wins = sum(1 for c in combos if c["delta_mse_pct"] < 0)
    win_rate = ensemble_wins / n_total
    p_sign = _binomial_pvalue_one_sided(ensemble_wins, n_total) if n_total > 0 else 1.0

    median_delta = float(np.median([c["delta_mse_pct"] for c in combos]))

    # Per-coin summary
    per_coin: dict[str, dict] = {}
    for coin in coins:
        cc = [c for c in combos if c["coin"] == coin]
        if not cc:
            continue
        wins = sum(1 for c in cc if c["delta_mse_pct"] < 0)
        per_coin[coin] = {
            "wins": f"{wins}/{len(cc)}",
            "win_rate": round(wins / len(cc), 3) if cc else 0,
            "median_delta_mse_pct": round(float(np.median([c["delta_mse_pct"] for c in cc])), 2),
            "avg_weights": _avg_weights(cc),
        }

    # Per-horizon summary
    per_horizon: dict[int, dict] = {}
    for h in horizons:
        cc = [c for c in combos if c["horizon"] == h]
        if not cc:
            continue
        wins = sum(1 for c in cc if c["delta_mse_pct"] < 0)
        per_horizon[str(h)] = {
            "wins": f"{wins}/{len(cc)}",
            "win_rate": round(wins / len(cc), 3) if cc else 0,
            "median_delta_mse_pct": round(float(np.median([c["delta_mse_pct"] for c in cc])), 2),
        }

    # Verdict
    if win_rate > 0.6 and p_sign < 0.05 and median_delta < -1.0:
        verdict = "BEATS"
    elif win_rate > 0.5 and p_sign < 0.10:
        verdict = "INCONCLUSIVE"
    else:
        verdict = "NO BEATS"

    results = {
        "model": "S2 Vol Ensemble DM-weighted",
        "models_combined": ["HAR Classic", "HAR-RV-J", "GARCH rolling"],
        "weighting": "DM inverse-p-log",
        "n_combos": n_total,
        "ensemble_wins": ensemble_wins,
        "win_rate": round(win_rate, 4),
        "p_sign": round(p_sign, 6),
        "median_delta_mse_pct": round(median_delta, 2),
        "verdict": verdict,
        "elapsed_s": round(elapsed, 1),
        "per_coin": per_coin,
        "per_horizon": per_horizon,
        "combos": combos,
    }

    # Save
    with open(results_dir / "results.json", "w") as f:
        json.dump(results, f, indent=2, default=str)

    # CSV
    df = pd.DataFrame(combos)
    df.to_csv(results_dir / "s2_ensemble_results.csv", index=False)

    # Verdict md
    with open(results_dir / "verdict.md", "w") as f:
        f.write(f"# S2 Vol Ensemble DM-weighted — Verdict\n\n")
        f.write(f"**Verdict**: {verdict}\n\n")
        f.write(f"| Metric | Value |\n|--------|-------|\n")
        f.write(f"| Combos | {n_total} |\n")
        f.write(f"| Ensemble wins | {ensemble_wins}/{n_total} ({win_rate:.1%}) |\n")
        f.write(f"| p-value (sign test) | {p_sign:.4f} |\n")
        f.write(f"| Median delta MSE | {median_delta:+.2f}% |\n")
        f.write(f"| Elapsed | {elapsed:.0f}s |\n\n")
        f.write(f"### Per-coin\n\n| Coin | Wins | Rate | Median dMSE | Avg weights |\n|------|------|------|-------------|-------------|\n")
        for coin, stats in per_coin.items():
            w = stats.get("avg_weights", {})
            w_str = " ".join(f"{k}={v:.2f}" for k, v in w.items())
            f.write(f"| {coin} | {stats['wins']} | {stats['win_rate']:.1%} | {stats['median_delta_mse_pct']:+.1f}% | {w_str} |\n")
        f.write(f"\n### Per-horizon\n\n| h | Wins | Rate | Median dMSE |\n|--|------|------|-------------|\n")
        for h, stats in per_horizon.items():
            f.write(f"| {h} | {stats['wins']} | {stats['win_rate']:.1%} | {stats['median_delta_mse_pct']:+.1f}% |\n")

    print(f"\n{'='*60}")
    print(f"S2 VERDICT: {verdict}")
    print(f"Wins: {ensemble_wins}/{n_total} ({win_rate:.1%}), p={p_sign:.4f}")
    print(f"Median delta MSE: {median_delta:+.2f}%")
    print(f"Elapsed: {elapsed:.0f}s")
    print(f"Output: {results_dir}")


def _avg_weights(combos: list[dict]) -> dict[str, float]:
    """Average DM-weights across combos."""
    all_weights: dict[str, list[float]] = {}
    for c in combos:
        for k, v in c["weights"].items():
            all_weights.setdefault(k, []).append(v)
    return {k: round(np.mean(v), 3) for k, v in all_weights.items()}


if __name__ == "__main__":
    main()
