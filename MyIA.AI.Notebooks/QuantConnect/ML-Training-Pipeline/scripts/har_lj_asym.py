"""M17 HAR-LJ-Asym: Jump + Semivariance Composite Model.

Combines the M12 jump decomposition (Andersen, Bollerslev & Diebold 2007)
with the M16 asymmetric semivariance decomposition (Andersen, Bollerslev,
Diebold & Patton 2007) into a single 7-regressor HAR model:

    log RV_{t+h} = b0 + b1·log(RV-_t) + b2·log(RV+_t)
                       + b3·log(RV_C_t) + b4·log(RV_J_t)
                       + b5·mean(log RV_{t-5..t-1})
                       + b6·mean(log RV_{t-22..t-6}) + e

Where:
- RV- = downside semivariance (negative intraday returns squared)
- RV+ = upside semivariance (positive intraday returns squared)
- RV_C = continuous component = max(RV_t - J_t, 0) via bipower variation
- RV_J = jump component = max(RV_t - mu·BPV_t, 0), mu = 0.6 (Huang-Tauchen)

Walk-forward 5-fold x 4 seeds x 3 horizons x 7 coins.
DM test vs HAR Classic baseline + DM test vs M12 (paired).

Usage:
    python har_lj_asym.py --horizons 1 5 10 --seeds 0 7 42 99 --skip-remote
    python har_lj_asym.py --horizons 1 5 10 --seeds 0 7 42 99
"""

from __future__ import annotations

import argparse
import json
import time
from pathlib import Path

import numpy as np
import pandas as pd

import sys
sys.path.insert(0, str(Path(__file__).resolve().parent))

RESULTS_DIR = Path(__file__).resolve().parent / "results"

from realized_variance import (
    daily_bipower_variation,
    daily_realized_variance,
    realized_variance_to_log,
)
from dm_test import dm_verdict
from har_asymmetric import (
    daily_semivariance_negative,
    daily_semivariance_positive,
    _load_panel,
)
from har_model import walk_forward_har
from m11g_fee_aware_kelly import (
    _apply_threshold_band,
    _kelly_weights_and_returns,
    _net_at_fee,
)
from m12_har_rv_j import daily_jump_component

COINS = ["BTC-USD", "ETH-USD", "SOL-USD", "LTC-USD", "XRP-USD", "ADA-USD", "DOT-USD"]
LOCAL_COINS = ["BTC-USD", "ETH-USD"]
HORIZONS_DEFAULT = [1, 5, 10]
SEEDS_DEFAULT = [0, 7, 42, 99]
MU_HUANG_TAUCHEN = 0.6
KELLY_CAP = 1.0
MU_WINDOW = 60
FEE_BPS = 50
N_SPLITS = 5
REFIT_EVERY = 22


# ---------------------------------------------------------------------------
# Feature construction
# ---------------------------------------------------------------------------

def lj_asym_features(
    rv_neg: pd.Series,
    rv_pos: pd.Series,
    rv_c: pd.Series,
    rv_j: pd.Series,
    rv: pd.Series,
) -> pd.DataFrame:
    """Build 7-regressor HAR-LJ-Asym feature matrix (log scale).

    Columns: log_rv_neg_d, log_rv_pos_d, log_rv_c_d, log_rv_j_d,
             log_rv_w, log_rv_m + intercept.
    """
    df = pd.DataFrame(index=rv.index)
    df["log_rv_neg_d"] = np.log(rv_neg.clip(lower=1e-12))
    df["log_rv_pos_d"] = np.log(rv_pos.clip(lower=1e-12))
    df["log_rv_c_d"] = np.log(rv_c.clip(lower=1e-12))
    df["log_rv_j_d"] = np.log(rv_j.clip(lower=1e-12))

    log_rv = np.log(rv.clip(lower=1e-12))
    df["log_rv_w"] = log_rv.rolling(5, min_periods=1).mean()
    df["log_rv_m"] = log_rv.shift(5).rolling(22, min_periods=1).mean()
    return df.dropna()


class HARLJAsymModel:
    """OLS-based HAR-LJ-Asym with 7 regressors."""

    def __init__(self) -> None:
        self.coef_: np.ndarray | None = None
        self.intercept_: float | None = None

    def fit(self, X: np.ndarray, y: np.ndarray) -> "HARLJAsymModel":
        X_aug = np.column_stack([np.ones(len(X)), X])
        self.coef_, _, _, _ = np.linalg.lstsq(X_aug, y, rcond=None)
        self.intercept_ = float(self.coef_[0])
        return self

    def predict(self, X: np.ndarray) -> np.ndarray:
        X_aug = np.column_stack([np.ones(len(X)), X])
        return X_aug @ self.coef_

    def predict_h_step(self, features_df: pd.DataFrame, h: int) -> np.ndarray:
        """Multi-step recursive forecast."""
        X = features_df.values
        yhat = self.predict(X[-1:])
        for _ in range(h - 1):
            new_row = np.array([
                yhat[-1], yhat[-1], yhat[-1], yhat[-1],
                yhat[-1],
                np.mean(np.concatenate([yhat[-min(len(yhat), 22):], [yhat[-1]]])[-22:]),
            ]).reshape(1, -1)
            yhat = np.append(yhat, self.predict(new_row))
        return yhat[-1:]


# ---------------------------------------------------------------------------
# Component computation
# ---------------------------------------------------------------------------

def compute_daily_components(
    hourly_returns: dict[str, pd.Series],
) -> dict[str, dict[str, pd.Series]]:
    """Compute all daily components for each coin.

    Returns {coin: {"rv": ..., "rv_neg": ..., "rv_pos": ..., "rv_c": ..., "rv_j": ...}}
    """
    components: dict[str, dict[str, pd.Series]] = {}
    for coin, rets in hourly_returns.items():
        rv = daily_realized_variance(rets)
        rv_neg = daily_semivariance_negative(rets)
        rv_pos = daily_semivariance_positive(rets)
        bpv = daily_bipower_variation(rets)
        jumps = daily_jump_component(rets, mu=MU_HUANG_TAUCHEN)
        rv_c = (rv - jumps).clip(lower=0.0)
        components[coin] = {
            "rv": rv,
            "rv_neg": rv_neg,
            "rv_pos": rv_pos,
            "rv_c": rv_c,
            "rv_j": jumps,
        }
    return components


# ---------------------------------------------------------------------------
# Walk-forward evaluation
# ---------------------------------------------------------------------------

def walk_forward_lj_asym(
    rv: pd.Series,
    rv_neg: pd.Series,
    rv_pos: pd.Series,
    rv_c: pd.Series,
    rv_j: pd.Series,
    horizon: int,
    seed: int,
    n_splits: int = N_SPLITS,
    refit_every: int = REFIT_EVERY,
) -> dict:
    """Walk-forward 5-fold evaluation of HAR-LJ-Asym model.

    Returns dict with forecasts, targets, aggregate_mse_logrv.
    """
    feat = lj_asym_features(rv_neg, rv_pos, rv_c, rv_j, rv)
    log_rv = realized_variance_to_log(rv)

    merged = feat.join(log_rv.rename("log_rv"), how="inner").dropna()
    if len(merged) < 100:
        return {"forecasts": [], "targets": [], "aggregate_mse_logrv": np.nan}

    feature_cols = [
        "log_rv_neg_d", "log_rv_pos_d", "log_rv_c_d", "log_rv_j_d",
        "log_rv_w", "log_rv_m",
    ]
    # Forward h-step target: average log-RV over the next `horizon` days,
    # consistent with walk_forward_har's target_window. Previously y_all used
    # the contemporaneous log_rv, making `horizon` a no-op (MSE identical across
    # h=1/5/10) — the model nowcast instead of forecasting.
    target_fwd = merged["log_rv"].rolling(horizon).mean().shift(-horizon)
    valid = target_fwd.notna().values
    X_all = merged[feature_cols].values[valid]
    y_all = target_fwd.values[valid]

    n = len(X_all)
    fold_size = n // (n_splits + 1)
    forecasts: list[float] = []
    targets: list[float] = []

    for fold in range(n_splits):
        split = (fold + 1) * fold_size
        if split + horizon >= n:
            break
        X_train, X_test = X_all[:split], X_all[split : split + fold_size]
        y_train, y_test = y_all[:split], y_all[split : split + fold_size]

        model = HARLJAsymModel().fit(X_train, y_train)
        yhat = model.predict(X_test)

        forecasts.extend(yhat.tolist())
        targets.extend(y_test.tolist())

    if not forecasts:
        return {"forecasts": [], "targets": [], "aggregate_mse_logrv": np.nan}

    forecasts_arr = np.array(forecasts)
    targets_arr = np.array(targets)
    mse = float(np.mean((forecasts_arr - targets_arr) ** 2))

    return {
        "forecasts": forecasts_arr.tolist(),
        "targets": targets_arr.tolist(),
        "aggregate_mse_logrv": mse,
    }


# ---------------------------------------------------------------------------
# Kelly metrics helper
# ---------------------------------------------------------------------------

def _compute_kelly(
    forecasts: np.ndarray, targets: np.ndarray,
) -> dict:
    """Compute Kelly portfolio metrics from log-RV forecasts."""
    n = min(len(forecasts), len(targets))
    if n < MU_WINDOW + 30:
        return {"sharpe": np.nan, "kelly_active_pct": np.nan}

    fc = forecasts[:n]
    tgt = targets[:n]

    # Create aligned Series for _kelly_weights_and_returns
    idx = pd.RangeIndex(n)
    # Use log-RV diff as daily return proxy
    daily_rets = pd.Series(np.diff(tgt, prepend=tgt[0]), index=idx, name="r")
    fc_series = pd.Series(fc, index=idx, name="logrv")

    result_kelly = _kelly_weights_and_returns(
        daily_rets, fc_series, MU_WINDOW, KELLY_CAP,
    )
    if result_kelly is None:
        return {"sharpe": np.nan, "kelly_active_pct": np.nan}
    kelly_w, port_ret = result_kelly
    net_ret = _net_at_fee(kelly_w, port_ret, fee_bps=FEE_BPS)
    clean_ret = _apply_threshold_band(net_ret, 0.01)

    sharpe = float(np.mean(clean_ret) / np.std(clean_ret) * np.sqrt(252)) if np.std(clean_ret) > 1e-10 else 0.0
    kelly_active_pct = float(np.mean(np.abs(kelly_w) > 0.01))
    return {"sharpe": sharpe, "kelly_active_pct": kelly_active_pct}


# ---------------------------------------------------------------------------
# Per-coin evaluation with Kelly + DM tests
# ---------------------------------------------------------------------------

def _eval_one_coin(
    coin: str,
    horizon: int,
    seed: int,
    components: dict[str, dict[str, pd.Series]],
) -> dict | None:
    """Evaluate one (coin, horizon, seed) combo."""
    comp = components.get(coin)
    if comp is None:
        return None

    rv = comp["rv"]
    rv_neg = comp["rv_neg"]
    rv_pos = comp["rv_pos"]
    rv_c = comp["rv_c"]
    rv_j = comp["rv_j"]

    # --- M17 HAR-LJ-Asym ---
    res_lj = walk_forward_lj_asym(
        rv, rv_neg, rv_pos, rv_c, rv_j, horizon, seed,
    )
    if not res_lj["forecasts"]:
        return None

    # --- HAR Classic baseline ---
    res_har = walk_forward_har(rv, horizon)
    har_fc = res_har.get("forecasts")
    if har_fc is None or (hasattr(har_fc, '__len__') and len(har_fc) == 0):
        return None

    # --- M12 HAR-RV-J baseline ---
    from m12_har_rv_j import walk_forward_har_rv_j
    res_m12 = walk_forward_har_rv_j(rv, rv_j, horizon)
    m12_fc = res_m12.get("forecasts")
    if m12_fc is None or (hasattr(m12_fc, '__len__') and len(m12_fc) == 0):
        return None

    # Align all three models to shortest forecast series
    n = min(
        len(res_lj["forecasts"]),
        len(har_fc),
        len(m12_fc),
    )
    if n < 10:
        return None

    fc_lj = np.array(res_lj["forecasts"][:n])
    fc_har = np.array(har_fc.values[:n]) if hasattr(har_fc, 'values') else np.array(har_fc[:n])
    fc_m12 = np.array(m12_fc.values[:n]) if hasattr(m12_fc, 'values') else np.array(m12_fc[:n])
    tgt = np.array(res_lj["targets"][:n])

    err_lj = fc_lj - tgt
    err_har = fc_har - tgt[:len(fc_har)]
    err_m12 = fc_m12 - tgt[:len(fc_m12)]

    dm_vs_har = dm_verdict(err_lj, err_har, horizon=horizon)
    dm_vs_m12 = dm_verdict(err_lj, err_m12, horizon=horizon)

    # --- Kelly portfolio metrics ---
    kelly_metrics = _compute_kelly(fc_lj, tgt)

    return {
        "coin": coin,
        "horizon": horizon,
        "seed": seed,
        "mse_logrv": res_lj["aggregate_mse_logrv"],
        "dm_vs_har": dm_vs_har,
        "dm_vs_m12": dm_vs_m12,
        **kelly_metrics,
    }


# ---------------------------------------------------------------------------
# Aggregation
# ---------------------------------------------------------------------------

def aggregate_verdicts(rows: list[dict]) -> list[dict]:
    """Aggregate per-(coin, horizon) across seeds."""
    groups: dict[tuple, list[dict]] = {}
    for r in rows:
        key = (r["coin"], r["horizon"])
        groups.setdefault(key, []).append(r)

    results = []
    for (coin, horizon), group in sorted(groups.items()):
        sharpe_vals = [r["sharpe"] for r in group if not np.isnan(r.get("sharpe", np.nan))]
        mse_vals = [r["mse_logrv"] for r in group if not np.isnan(r.get("mse_logrv", np.nan))]

        dm_har_wins = sum(
            1 for r in group if r.get("dm_vs_har", {}).get("verdict") == "BEATS baseline"
        )
        dm_har_total = sum(
            1 for r in group if r.get("dm_vs_har", {}).get("verdict", "") != "NO_M12_BASELINE"
        )
        dm_m12_wins = sum(
            1 for r in group if r.get("dm_vs_m12", {}).get("verdict") == "BEATS baseline"
        )
        dm_m12_total = sum(
            1 for r in group
            if r.get("dm_vs_m12", {}).get("verdict", "") not in ("NO_M12_BASELINE", "")
        )

        avg_sharpe = float(np.mean(sharpe_vals)) if sharpe_vals else np.nan
        avg_mse = float(np.mean(mse_vals)) if mse_vals else np.nan

        results.append({
            "coin": coin,
            "horizon": horizon,
            "n_seeds": len(group),
            "avg_sharpe": avg_sharpe,
            "avg_mse_logrv": avg_mse,
            "dm_vs_har_wins": dm_har_wins,
            "dm_vs_har_total": dm_har_total,
            "dm_vs_m12_wins": dm_m12_wins,
            "dm_vs_m12_total": dm_m12_total,
            "seeds": [r["seed"] for r in group],
        })
    return results


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser(description="M17 HAR-LJ-Asym composite model")
    parser.add_argument(
        "--horizons", nargs="+", type=int, default=HORIZONS_DEFAULT,
    )
    parser.add_argument(
        "--seeds", nargs="+", type=int, default=SEEDS_DEFAULT,
    )
    parser.add_argument(
        "--skip-remote", action="store_true",
        help="Skip remote data fetch (use cached BTC+ETH only)",
    )
    parser.add_argument(
        "--coins", nargs="+", type=str, default=None,
        help="Override coin list (default: all 7, or BTC+ETH with --skip-remote)",
    )
    args = parser.parse_args()

    coins = args.coins
    if coins is None:
        coins = LOCAL_COINS if args.skip_remote else COINS

    print(f"M17 HAR-LJ-Asym: coins={coins}, horizons={args.horizons}, "
          f"seeds={args.seeds}, skip_remote={args.skip_remote}")

    t0 = time.time()

    # Load hourly returns
    panel = _load_panel(skip_remote=args.skip_remote)
    available = [c for c in coins if c in panel]
    if not available:
        print("ERROR: no coins available after loading panel")
        return
    print(f"Panel loaded: {list(panel.keys())} ({len(panel[available[0]])} bars for {available[0]})")

    # Compute daily components
    components = compute_daily_components(panel)
    print(f"Components computed for: {list(components.keys())}")

    # Evaluate all combos
    rows: list[dict] = []
    total = len(available) * len(args.horizons) * len(args.seeds)
    done = 0
    for coin in available:
        for horizon in args.horizons:
            for seed in args.seeds:
                done += 1
                print(f"  [{done}/{total}] {coin} h={horizon} seed={seed}", end="", flush=True)
                result = _eval_one_coin(coin, horizon, seed, components)
                if result is not None:
                    rows.append(result)
                    dm_h = result.get("dm_vs_har", {}).get("verdict", "?")
                    dm_m = result.get("dm_vs_m12", {}).get("verdict", "?")
                    print(f" -> MSE={result['mse_logrv']:.6f} "
                          f"DM_har={dm_h} DM_m12={dm_m}")
                else:
                    print(" -> SKIP (insufficient data)")

    elapsed = time.time() - t0

    # Aggregate
    agg = aggregate_verdicts(rows)

    output = {
        "model": "M17_HAR_LJ_ASYM",
        "params": {
            "regressors": ["log_rv_neg", "log_rv_pos", "log_rv_c", "log_rv_j",
                           "log_rv_w", "log_rv_m"],
            "mu_huang_tauchen": MU_HUANG_TAUCHEN,
            "kelly_cap": KELLY_CAP,
            "mu_window": MU_WINDOW,
            "fee_bps": FEE_BPS,
            "n_splits": N_SPLITS,
            "refit_every": REFIT_EVERY,
        },
        "coins": available,
        "horizons": args.horizons,
        "seeds": args.seeds,
        "skip_remote": args.skip_remote,
        "per_seed_results": rows,
        "aggregated": agg,
        "elapsed_seconds": round(elapsed, 1),
        "n_combos_evaluated": len(rows),
    }

    RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    out_path = RESULTS_DIR / "m17_har_lj_asym.json"
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(output, f, indent=2, default=str)
    print(f"\nResults saved to {out_path}")
    print(f"Total: {len(rows)} combos evaluated in {elapsed:.1f}s")

    # Summary
    if agg:
        print("\n=== Aggregated Results ===")
        for a in agg:
            print(f"  {a['coin']} h={a['horizon']}: "
                  f"MSE={a['avg_mse_logrv']:.6f} Sharpe={a['avg_sharpe']:.4f} "
                  f"DM_har={a['dm_vs_har_wins']}/{a['dm_vs_har_total']} "
                  f"DM_m12={a['dm_vs_m12_wins']}/{a['dm_vs_m12_total']}")


if __name__ == "__main__":
    main()
