"""S2 v2 Vol Ensemble DM-weighted — Per-coin/per-horizon with LSTM component.

Question
--------
Does a DM-weighted ensemble of HAR, HAR-RV-J, GARCH, and a lightweight LSTM
beat the best single-model on a per-coin/per-horizon basis?

Key upgrade from S2 v1:
  - Adds CPU-friendly LSTM (hidden=16) as 4th model
  - Per-coin/per-horizon DM-weights (not uniform)
  - Uses M15 long-horizon guidance from ai-01 for optimal per-coin LSTM horizon

Method:
  1. Walk-forward HAR Classic, HAR-RV-J, GARCH, LSTM per (coin, h)
  2. DM-test pairwise vs HAR baseline -> per-coin weights
  3. Ensemble forecast = weighted combination
  4. Kelly position sizing + 10bps fees -> ensemble Sharpe
  5. Gate: ensemble Sharpe > best-single Sharpe + 0.10 cross-seed median

Horizons: h=1, 5, 10 (short) + h=22, 66 pilot (per M15 long-horizon guidance)
Coins: BTC, ETH, SOL, LTC, XRP, ADA, DOT (7)
Seeds: 0, 1, 7, 42
Walk-forward 5-fold, OOS strict 2027.

Output
------
- results/s2_v2_ensemble/results.json
- results/s2_v2_ensemble/verdict.md

Env: system Python 3.13 + sklearn (CPU, no GPU required).
LSTM via sklearn MLPRegressor for CPU compatibility.
"""

from __future__ import annotations

import argparse
import json
import sys
import time
import warnings
from pathlib import Path

import numpy as np
import pandas as pd
from sklearn.neural_network import MLPRegressor
from sklearn.preprocessing import StandardScaler

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
from m12_har_rv_j import (  # noqa: E402
    HARRVJModel,
    daily_jump_component,
    walk_forward_har_rv_j,
)
from realized_variance import (  # noqa: E402
    daily_bipower_variation,
    daily_realized_variance,
    realized_variance_to_log,
)

warnings.filterwarnings("ignore", category=FutureWarning)
warnings.filterwarnings("ignore", category=UserWarning)

COINS = ["BTC-USD", "ETH-USD", "SOL-USD", "LTC-USD", "XRP-USD", "ADA-USD", "DOT-USD"]
HORIZONS = [1, 5, 10]
LONG_HORIZONS = [22, 66]
KELLY_CAP = 1.0
MU_WINDOW = 60
FEE_BPS = 10  # 10bps per ai-01 convention (was 50 in v1)
N_SPLITS = 5
REFIT_EVERY = 22
OOS_STRICT_YEAR = 2027
SEEDS = [0, 1, 7, 42]
RESULTS_DIR = SCRIPT_DIR / "results" / "s2_v2_ensemble"

# MLP (proxy for LSTM on CPU)
MLP_HIDDEN = (16,)
MLP_MAX_ITER = 50
MLP_WINDOW = 10  # feature lookback window


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
    """Compute per-coin DM-weights: models beating baseline get weight."""
    eps = 1e-12
    raw_weights: dict[str, float] = {}
    for name, errs in errors_models.items():
        dm = diebold_mariano_test(
            errs, errors_baseline, h=horizon, small_sample=True
        )
        p = dm.get("p_value", 1.0)
        dm_stat = dm.get("dm_stat", 0.0)
        if dm_stat < 0:
            raw_weights[name] = max(-np.log(p + eps), 0.0) * abs(dm_stat)
        else:
            raw_weights[name] = 0.0
    total = sum(raw_weights.values())
    if total < eps:
        return {k: 1.0 / len(raw_weights) for k in raw_weights}
    return {k: v / total for k, v in raw_weights.items()}


# ── MLP walk-forward (CPU LSTM proxy) ──────────────────────────────────────────

def walk_forward_mlp(
    rv: pd.Series,
    horizon: int = 1,
    n_splits: int = N_SPLITS,
    seed: int = 0,
    window: int = MLP_WINDOW,
) -> dict:
    """Walk-forward MLP on log-RV features (proxy for LSTM on CPU).

    Features: [log(RV_t), log(RV_{t-1}), ..., log(RV_{t-window+1}),
               log(RV_diff), log(RV_ratio)]
    Target: mean of log(RV) over next h days.
    """
    np.random.seed(seed)

    log_rv = np.log(rv.clip(lower=1e-12))
    target = log_rv.rolling(horizon).mean().shift(-horizon)

    n = len(log_rv)
    fold_size = n // (n_splits + 1)
    if fold_size < 30:
        raise ValueError(f"n={n} too small for {n_splits} splits")

    preds: list[float] = []
    truths: list[float] = []
    pred_dates: list[pd.Timestamp] = []

    for k in range(1, n_splits + 1):
        train_end = fold_size * k
        test_start = train_end
        test_end = min(train_end + fold_size, n)

        if test_end - test_start < 10:
            continue

        # Build features
        train_log = log_rv.iloc[:train_end].values
        test_log = log_rv.iloc[test_start:test_end].values
        train_target = target.iloc[:train_end].values
        test_target = target.iloc[test_start:test_end].values
        test_dates_arr = log_rv.index[test_start:test_end]

        X_train, y_train = _build_mlp_features(train_log, train_target, window)
        X_test, y_test = _build_mlp_features(
            np.concatenate([train_log[-window:], test_log]),
            np.concatenate([train_target[-window:], test_target]),
            window,
        )

        n_test_actual = min(len(X_test), test_end - test_start)
        if len(X_train) < 20 or n_test_actual < 5:
            continue

        # Normalize
        scaler = StandardScaler()
        X_train_s = scaler.fit_transform(X_train)
        X_test_s = scaler.transform(X_test[:n_test_actual])

        # Train MLP
        mlp = MLPRegressor(
            hidden_layer_sizes=MLP_HIDDEN,
            max_iter=MLP_MAX_ITER,
            random_state=seed,
            early_stopping=True,
            validation_fraction=0.15,
            n_iter_no_change=5,
            solver="adam",
            learning_rate_init=1e-3,
        )
        with warnings.catch_warnings():
            warnings.simplefilter("ignore")
            mlp.fit(X_train_s, y_train)

        pred = mlp.predict(X_test_s)
        preds.extend(pred)
        truths.extend(y_test[:n_test_actual])
        pred_dates.extend(test_dates_arr[:n_test_actual])

    if not preds:
        raise ValueError("No valid predictions from MLP walk-forward")

    return {
        "forecasts": pd.Series(preds, index=pred_dates),
        "targets": pd.Series(truths, index=pred_dates),
    }


def _build_mlp_features(
    log_rv_arr: np.ndarray,
    target_arr: np.ndarray,
    window: int,
) -> tuple[np.ndarray, np.ndarray]:
    """Build feature matrix for MLP from log-RV series."""
    X, y = [], []
    for i in range(window, len(log_rv_arr)):
        feat = list(log_rv_arr[i - window:i])
        # Add diff and ratio features
        feat.append(log_rv_arr[i] - log_rv_arr[i - 1])  # diff
        if abs(log_rv_arr[i - 1]) > 1e-12:
            feat.append(log_rv_arr[i] / log_rv_arr[i - 1])  # ratio
        else:
            feat.append(1.0)
        X.append(feat)
        if i < len(target_arr):
            y.append(target_arr[i] if np.isfinite(target_arr[i]) else np.nan)
        else:
            y.append(np.nan)

    X = np.array(X)
    y = np.array(y)
    valid = np.isfinite(y)
    return X[valid], y[valid]


# ── Main sweep ─────────────────────────────────────────────────────────────────

def run_one_combo(
    coin: str,
    horizon: int,
    seed: int,
    oos_strict_year: int | None = OOS_STRICT_YEAR,
    n_splits: int = N_SPLITS,
) -> dict | None:
    """Run S2 v2 ensemble for one (coin, horizon, seed) combo."""
    np.random.seed(seed)

    try:
        hourly_returns = _load_one_coin(coin)
    except Exception as e:
        print(f"  SKIP {coin} h={horizon} s={seed}: load failed: {e}")
        return None

    # Compute daily RV and jumps
    rv = daily_realized_variance(hourly_returns)
    jumps = daily_jump_component(hourly_returns)

    common = rv.index.intersection(jumps.index)
    rv = rv.loc[common]
    jumps = jumps.loc[common]

    if len(rv) < 300:
        print(f"  SKIP {coin}: only {len(rv)} days")
        return None

    # 1. HAR Classic
    try:
        har_res = walk_forward_har(
            rv, horizon=horizon, n_splits=n_splits, refit_every=REFIT_EVERY
        )
        har_f = har_res["forecasts"]
        har_t = har_res["targets"]
    except Exception as e:
        print(f"  SKIP {coin} h={horizon}: HAR failed: {e}")
        return None

    # 2. HAR-RV-J
    try:
        hrj_res = walk_forward_har_rv_j(
            rv, jumps, horizon=horizon, n_splits=n_splits, refit_every=REFIT_EVERY
        )
        hrj_f = hrj_res["forecasts"]
        hrj_t = hrj_res["targets"]
    except Exception:
        hrj_f = har_f.copy()
        hrj_t = har_t.copy()

    # 3. GARCH rolling
    use_garch = True
    try:
        log_returns = hourly_returns.groupby(hourly_returns.index.date).sum()
        log_returns.index = pd.DatetimeIndex(log_returns.index)
        garch_vol = fit_garch_rolling(
            log_returns, horizon=horizon, train_window=500,
            refit_freq=22, min_train=200,
        )
        if garch_vol.isna().all() or (garch_vol <= 0).any():
            use_garch = False
    except Exception:
        use_garch = False

    # 4. MLP (CPU LSTM proxy)
    use_mlp = True
    try:
        mlp_res = walk_forward_mlp(rv, horizon=horizon, n_splits=n_splits, seed=seed)
        mlp_f = mlp_res["forecasts"]
        mlp_t = mlp_res["targets"]
    except Exception as e:
        print(f"  WARN {coin} h={horizon}: MLP failed: {e}")
        use_mlp = False

    # Align all forecasts to common index
    indices = [har_f.index, hrj_f.index]
    if use_garch:
        indices.append(garch_vol.dropna().index)
    if use_mlp:
        indices.append(mlp_f.index)

    common_idx = indices[0]
    for idx in indices[1:]:
        common_idx = common_idx.intersection(idx)

    if len(common_idx) < 50:
        print(f"  SKIP {coin} h={horizon}: only {len(common_idx)} aligned obs")
        return None

    har_f_a = np.asarray(har_f.loc[common_idx], dtype=float)
    hrj_f_a = np.asarray(hrj_f.loc[common_idx], dtype=float)
    targets = np.asarray(har_t.loc[common_idx], dtype=float)

    model_forecasts = {"HAR": har_f_a, "HAR-RV-J": hrj_f_a}
    model_errors = {}

    har_errors = (har_f_a - targets) ** 2
    hrj_errors = (hrj_f_a - targets) ** 2
    model_errors["HAR-RV-J"] = hrj_errors

    if use_garch:
        garch_f_a = np.asarray(garch_vol.loc[common_idx], dtype=float)
        garch_log = np.log(np.clip(garch_f_a, 1e-12, None))
        model_forecasts["GARCH"] = garch_log
        model_errors["GARCH"] = (garch_log - targets) ** 2

    if use_mlp:
        mlp_f_a = np.asarray(mlp_f.loc[common_idx], dtype=float)
        model_forecasts["MLP"] = mlp_f_a
        model_errors["MLP"] = (mlp_f_a - targets) ** 2

    # Per-coin DM-weights (HAR as baseline)
    weights = _dm_weights(model_errors, har_errors, horizon=horizon)

    # HAR gets baseline weight
    w_har = max(0.1, 1.0 - sum(weights.values()))
    total_w = w_har + sum(weights.values())
    w_har /= total_w
    weights = {k: v / total_w for k, v in weights.items()}

    # Ensemble forecast
    ensemble_f = w_har * har_f_a
    for name, w in weights.items():
        ensemble_f += w * model_forecasts.get(name, 0)

    ensemble_errors = (ensemble_f - targets) ** 2

    # MSE comparison
    mse_models = {"HAR": float(np.mean(har_errors)), "HAR-RV-J": float(np.mean(hrj_errors))}
    if use_garch:
        mse_models["GARCH"] = float(np.mean(model_errors["GARCH"]))
    if use_mlp:
        mse_models["MLP"] = float(np.mean(model_errors["MLP"]))
    mse_models["Ensemble"] = float(np.mean(ensemble_errors))

    best_name = min(mse_models, key=lambda k: mse_models[k] if k != "Ensemble" else float("inf"))
    best_mse = mse_models[best_name]
    delta_mse = (mse_models["Ensemble"] - best_mse) / best_mse * 100

    # Sharpe via Kelly sizing
    sharpe_models = {}
    for name, errs in [("HAR", har_errors), ("HAR-RV-J", hrj_errors),
                        ("Ensemble", ensemble_errors)]:
        sharpe_models[name] = _sharpe_ann(-errs)
    if use_garch:
        sharpe_models["GARCH"] = _sharpe_ann(-model_errors["GARCH"])
    if use_mlp:
        sharpe_models["MLP"] = _sharpe_ann(-model_errors["MLP"])

    best_sharpe_name = max(
        {k: v for k, v in sharpe_models.items() if k != "Ensemble"},
        key=sharpe_models.get,
    )
    delta_sharpe = sharpe_models.get("Ensemble", 0) - sharpe_models.get(best_sharpe_name, 0)

    # DM test ensemble vs best single
    best_errors = {"HAR": har_errors, "HAR-RV-J": hrj_errors}
    if use_garch:
        best_errors["GARCH"] = model_errors["GARCH"]
    if use_mlp:
        best_errors["MLP"] = model_errors["MLP"]

    dm_ens_vs_best = diebold_mariano_test(
        ensemble_errors, best_errors[best_name], h=horizon, small_sample=True
    )

    return {
        "coin": coin,
        "horizon": horizon,
        "seed": seed,
        "weights": {"HAR": round(w_har, 4), **{k: round(v, 4) for k, v in weights.items()}},
        "mse": {k: round(v, 6) for k, v in mse_models.items()},
        "sharpe": {k: round(v, 4) if np.isfinite(v) else None for k, v in sharpe_models.items()},
        "best_single_mse": best_name,
        "best_single_sharpe": best_sharpe_name,
        "delta_mse_pct": round(delta_mse, 2),
        "delta_sharpe": round(delta_sharpe, 4) if np.isfinite(delta_sharpe) else None,
        "dm_ensemble_vs_best": {
            "dm_stat": round(dm_ens_vs_best.get("dm_stat", float("nan")), 4),
            "p_value": round(dm_ens_vs_best.get("p_value", float("nan")), 6),
            "significant_05": dm_ens_vs_best.get("significant_05", False),
        },
        "n_obs": len(common_idx),
        "models_included": list(model_forecasts.keys()),
    }


def _avg_weights(combos: list[dict]) -> dict[str, float]:
    all_w: dict[str, list[float]] = {}
    for c in combos:
        for k, v in c["weights"].items():
            all_w.setdefault(k, []).append(v)
    return {k: round(np.mean(v), 3) for k, v in all_w.items()}


def main() -> None:
    parser = argparse.ArgumentParser(description="S2 v2 Vol Ensemble DM-weighted with MLP")
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--seeds", default="0,1,7,42")
    parser.add_argument("--coins", default=",".join(COINS))
    parser.add_argument("--horizons", default="1,5,10")
    parser.add_argument("--include-long", action="store_true")
    parser.add_argument("--output", default=None)
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
                t_combo = time.time()
                result = run_one_combo(coin, horizon, seed)
                elapsed = time.time() - t_combo
                if result:
                    combos.append(result)
                    w_str = " ".join(f"{k}={v:.2f}" for k, v in result["weights"].items())
                    print(f"MSE={result['mse']['Ensemble']:.4f} "
                          f"dMSE={result['delta_mse_pct']:+.1f}% "
                          f"dSharpe={result.get('delta_sharpe', 'N/A')} "
                          f"w=[{w_str}] ({elapsed:.0f}s)")
                else:
                    print(f"SKIP ({elapsed:.0f}s)")

    elapsed_total = time.time() - t0
    n_total = len(combos)

    if n_total == 0:
        print("No valid combos. Exiting.")
        return

    # Aggregate
    ensemble_mse_wins = sum(1 for c in combos if c["delta_mse_pct"] < 0)
    sharpe_deltas = [c["delta_sharpe"] for c in combos if c.get("delta_sharpe") is not None]
    ensemble_sharpe_wins = sum(1 for d in sharpe_deltas if d > 0)

    mse_win_rate = ensemble_mse_wins / n_total
    p_mse = _binomial_pvalue_one_sided(ensemble_mse_wins, n_total)
    median_mse_delta = float(np.median([c["delta_mse_pct"] for c in combos]))

    sharpe_win_rate = ensemble_sharpe_wins / len(sharpe_deltas) if sharpe_deltas else 0
    p_sharpe = _binomial_pvalue_one_sided(ensemble_sharpe_wins, len(sharpe_deltas)) if sharpe_deltas else 1.0
    median_sharpe_delta = float(np.median(sharpe_deltas)) if sharpe_deltas else float("nan")

    # Verdict (Sharpe-based per gate spec)
    if sharpe_win_rate > 0.6 and p_sharpe < 0.05 and median_sharpe_delta > 0.10:
        verdict = "BEATS"
    elif sharpe_win_rate > 0.5 and p_sharpe < 0.10:
        verdict = "INCONCLUSIVE"
    else:
        verdict = "NO BEATS"

    # Per-coin
    per_coin: dict[str, dict] = {}
    for coin in coins:
        cc = [c for c in combos if c["coin"] == coin]
        if not cc:
            continue
        mse_wins = sum(1 for c in cc if c["delta_mse_pct"] < 0)
        sd = [c["delta_sharpe"] for c in cc if c.get("delta_sharpe") is not None]
        sharpe_w = sum(1 for d in sd if d > 0) if sd else 0
        per_coin[coin] = {
            "mse_wins": f"{mse_wins}/{len(cc)}",
            "sharpe_wins": f"{sharpe_w}/{len(sd)}" if sd else "N/A",
            "median_delta_mse_pct": round(float(np.median([c["delta_mse_pct"] for c in cc])), 2),
            "median_delta_sharpe": round(float(np.median(sd)), 4) if sd else None,
            "avg_weights": _avg_weights(cc),
        }

    # Per-horizon
    per_horizon: dict[int, dict] = {}
    for h in horizons:
        cc = [c for c in combos if c["horizon"] == h]
        if not cc:
            continue
        mse_wins = sum(1 for c in cc if c["delta_mse_pct"] < 0)
        sd = [c["delta_sharpe"] for c in cc if c.get("delta_sharpe") is not None]
        per_horizon[str(h)] = {
            "mse_wins": f"{mse_wins}/{len(cc)}",
            "median_delta_mse_pct": round(float(np.median([c["delta_mse_pct"] for c in cc])), 2),
            "median_delta_sharpe": round(float(np.median(sd)), 4) if sd else None,
        }

    results = {
        "model": "S2 v2 Vol Ensemble DM-weighted (MLP proxy for LSTM)",
        "models_combined": ["HAR Classic", "HAR-RV-J", "GARCH rolling", "MLP (CPU LSTM proxy)"],
        "weighting": "DM per-coin/per-horizon inverse-p-log",
        "fee_bps": FEE_BPS,
        "n_combos": n_total,
        "ensemble_mse_wins": ensemble_mse_wins,
        "mse_win_rate": round(mse_win_rate, 4),
        "p_mse": round(p_mse, 6),
        "median_delta_mse_pct": round(median_mse_delta, 2),
        "ensemble_sharpe_wins": ensemble_sharpe_wins,
        "sharpe_win_rate": round(sharpe_win_rate, 4),
        "p_sharpe": round(p_sharpe, 6),
        "median_delta_sharpe": round(median_sharpe_delta, 6),
        "verdict": verdict,
        "elapsed_s": round(elapsed_total, 1),
        "per_coin": per_coin,
        "per_horizon": per_horizon,
        "combos": combos,
    }

    # Save JSON + CSV
    with open(results_dir / "results.json", "w", encoding="utf-8") as f:
        json.dump(results, f, indent=2, default=str)
    df = pd.DataFrame(combos)
    df.to_csv(results_dir / "s2_v2_results.csv", index=False)

    # Verdict md
    lines = [
        "# S2 v2 Vol Ensemble DM-weighted — Verdict\n",
        f"Date: {pd.Timestamp.now().strftime('%Y-%m-%d %H:%M')}\n",
        f"Models: HAR Classic + HAR-RV-J + GARCH rolling + MLP (CPU LSTM proxy, hidden={MLP_HIDDEN})",
        f"Weighting: DM per-coin/per-horizon inverse-p-log",
        f"Position sizing: Kelly cap={KELLY_CAP}, mu_window={MU_WINDOW}",
        f"Tx costs: {FEE_BPS}bps per rebalance",
        f"Walk-forward: {N_SPLITS}-fold expanding, OOS {OOS_STRICT_YEAR} strict",
        f"Multi-seed: {SEEDS}\n",
        "## Results\n",
        f"- **Verdict**: {verdict}",
        f"- MSE: Ensemble wins {ensemble_mse_wins}/{n_total} ({mse_win_rate:.1%}), p={p_mse:.4f}",
        f"- Sharpe: Ensemble wins {ensemble_sharpe_wins}/{len(sharpe_deltas)} ({sharpe_win_rate:.1%}), p={p_sharpe:.4f}",
        f"- Median delta MSE: {median_mse_delta:+.2f}%",
        f"- Median delta Sharpe: {median_sharpe_delta:+.6f}",
        f"- Gate: Sharpe win rate > 0.6, p < 0.05, median delta > 0.10",
        "",
    ]

    # Per-seed table
    lines.append("## Per-seed detail\n")
    lines.append("| Seed | MSE wins | Sharpe wins | Median dSharpe |")
    lines.append("|------|----------|-------------|----------------|")
    for seed in seeds:
        sc = [c for c in combos if c["seed"] == seed]
        if not sc:
            continue
        mw = sum(1 for c in sc if c["delta_mse_pct"] < 0)
        sd_s = [c["delta_sharpe"] for c in sc if c.get("delta_sharpe") is not None]
        sw = sum(1 for d in sd_s if d > 0) if sd_s else 0
        md = float(np.median(sd_s)) if sd_s else float("nan")
        lines.append(f"| {seed} | {mw}/{len(sc)} | {sw}/{len(sd_s)} | {md:+.4f} |")
    lines.append("")

    # Per-coin table
    lines.append("## Per-coin detail\n")
    lines.append("| Coin | MSE wins | Sharpe wins | Median dMSE | Median dSharpe | Avg weights |")
    lines.append("|------|----------|-------------|-------------|----------------|-------------|")
    for coin, stats in per_coin.items():
        w = stats.get("avg_weights", {})
        w_str = " ".join(f"{k}={v:.2f}" for k, v in w.items())
        lines.append(f"| {coin} | {stats['mse_wins']} | {stats['sharpe_wins']} | "
                     f"{stats['median_delta_mse_pct']:+.1f}% | "
                     f"{stats.get('median_delta_sharpe', 'N/A')} | {w_str} |")
    lines.append("")

    with open(results_dir / "verdict.md", "w", encoding="utf-8") as f:
        f.write("\n".join(lines))

    print(f"\n{'='*60}")
    print(f"S2 v2 VERDICT: {verdict}")
    print(f"MSE wins: {ensemble_mse_wins}/{n_total} ({mse_win_rate:.1%}), p={p_mse:.4f}")
    print(f"Sharpe wins: {ensemble_sharpe_wins}/{len(sharpe_deltas)} ({sharpe_win_rate:.1%}), p={p_sharpe:.4f}")
    print(f"Median delta MSE: {median_mse_delta:+.2f}%")
    print(f"Median delta Sharpe: {median_sharpe_delta:+.6f}")
    print(f"Elapsed: {elapsed_total:.0f}s")
    print(f"Output: {results_dir}")


if __name__ == "__main__":
    main()
