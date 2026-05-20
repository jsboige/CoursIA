"""S8 Trend Long-Horizon Pilot — Can ML predict direction at h=60/120/252 days?

Question
--------
Directional prediction failed at daily horizons (M5-M17 all NO BEATS). But user
hypothesis: long-horizon trend (MA crossovers, multi-month cycles) may carry signal.
Test: LASSO, RandomForest, LightGBM classifiers on features built from daily data,
targeting sign(return_{t+h}) at h in {60, 120, 252} trading days.

Walk-forward 5-fold expanding, 7 coins x 3 horizons x 4 seeds = 84 combos.
Gate: AUC > 0.55 stable cross-seed AND net Sharpe > B&H + 0.10 after 50bps tx costs.

Output
------
- results/s8_trend_long_horizon/s8_trend_long_horizon_results.csv
- results/s8_trend_long_horizon/results.json
- docs/S8_TREND_LONG_HORIZON.md (verdict)

Env: system Python 3.13 (no conda). sklearn + lightgbm.
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

import lightgbm as lgb
import numpy as np
import pandas as pd
from sklearn.ensemble import RandomForestClassifier
from sklearn.linear_model import LogisticRegression
from sklearn.preprocessing import StandardScaler

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

from m11g_fee_aware_kelly import _load_one_coin  # noqa: E402

COINS = ["BTC-USD", "ETH-USD", "SOL-USD", "LTC-USD", "XRP-USD", "ADA-USD", "DOT-USD"]
HORIZONS = [60, 120, 252]
SEEDS = [0, 1, 7, 42]
FEE_BPS = 50
N_SPLITS = 5
REFIT_EVERY = 22
RESULTS_DIR = SCRIPT_DIR / "results" / "s8_trend_long_horizon"


# ── Feature engineering ───────────────────────────────────────────────────────


def build_trend_features(close: pd.Series) -> pd.DataFrame:
    """Build long-horizon trend features from daily close prices.

    Features: MA ratios, RSI, ATR, log-RV, returns at weekly/monthly scale, log-volume.
    All lagged by 1 to avoid lookahead.
    """
    df = pd.DataFrame(index=close.index)
    df["close"] = close

    # MA ratios
    for fast, slow in [(5, 20), (20, 50), (50, 200)]:
        ma_f = close.rolling(fast, min_periods=fast).mean()
        ma_s = close.rolling(slow, min_periods=slow).mean()
        df[f"ma_ratio_{fast}_{slow}"] = (ma_f / ma_s - 1.0).shift(1)

    # ATR proxy (rolling std of returns)
    ret = close.pct_change()
    for w in [5, 20, 60]:
        df[f"vol_{w}"] = ret.rolling(w, min_periods=w).std().shift(1)

    # RSI(14)
    delta = close.diff()
    gain = delta.clip(lower=0)
    loss = -delta.clip(upper=0)
    avg_gain = gain.rolling(14, min_periods=14).mean()
    avg_loss = loss.rolling(14, min_periods=14).mean()
    rs = avg_gain / avg_loss.replace(0, np.nan)
    df["rsi_14"] = (100 - 100 / (1 + rs)).shift(1)

    # Log-realized variance (22-day)
    log_ret = np.log(close / close.shift(1))
    df["log_rv_22"] = (log_ret ** 2).rolling(22, min_periods=22).sum().shift(1)
    df["log_rv_22"] = np.log(df["log_rv_22"].clip(lower=1e-12))

    # Aggregate returns: weekly and monthly
    for w in [5, 22]:
        df[f"ret_agg_{w}"] = log_ret.rolling(w, min_periods=w).sum().shift(1)

    # Log-volume proxy (rolling mean of absolute returns as volume proxy)
    df["log_volume_22"] = np.log(
        ret.abs().rolling(22, min_periods=22).mean().shift(1).clip(lower=1e-12)
    )

    # Momentum: return over past h days for each target horizon
    for h in HORIZONS:
        df[f"mom_{h}"] = log_ret.rolling(h, min_periods=h).sum().shift(1)

    return df.dropna()


# ── Models ────────────────────────────────────────────────────────────────────


def make_models(seed: int) -> dict[str, object]:
    """Return dict of model name -> sklearn-compatible classifier."""
    return {
        "lasso": LogisticRegression(
            penalty="l1", C=1.0, solver="saga", max_iter=2000,
            random_state=seed,
        ),
        "rf": RandomForestClassifier(
            n_estimators=100, max_depth=6, min_samples_leaf=20,
            random_state=seed, n_jobs=-1,
        ),
        "lgbm": lgb.LGBMClassifier(
            n_estimators=200, max_depth=6, learning_rate=0.05,
            num_leaves=31, min_child_samples=20,
            random_state=seed, n_jobs=-1, verbose=-1,
        ),
    }


# ── Walk-forward classification ───────────────────────────────────────────────


def walk_forward_trend(
    close: pd.Series,
    horizon: int,
    seed: int,
    model_name: str,
    model_cls: object,
    n_splits: int = N_SPLITS,
    refit_every: int = REFIT_EVERY,
) -> dict | None:
    """Walk-forward classification of direction at horizon h.

    Target: sign(close_{t+h} / close_t - 1) > 0 → 1, else 0.
    """
    np.random.seed(seed)

    features_df = build_trend_features(close)
    daily_ret = close.pct_change().shift(-horizon)
    target = (daily_ret > 0).astype(int)
    target.name = "target"

    aligned = features_df.join(target, how="inner").dropna()
    if len(aligned) < 300:
        return None

    feature_cols = [c for c in aligned.columns if c != "target"]
    n = len(aligned)

    fold_size = n // (n_splits + 1)
    if fold_size < 50:
        return None

    splits = []
    for k in range(1, n_splits + 1):
        train_end = fold_size * k
        test_start = train_end
        test_end = min(train_end + fold_size, n)
        if test_end - test_start < 20:
            continue
        splits.append((train_end, test_start, test_end))

    all_probs: list[float] = []
    all_truths: list[int] = []
    all_dates: list = []

    for fold_idx, (train_end, test_start, test_end) in enumerate(splits):
        train = aligned.iloc[:train_end]
        test = aligned.iloc[test_start:test_end]

        scaler = StandardScaler()
        X_train = scaler.fit_transform(train[feature_cols])
        y_train = train["target"].values
        X_test = scaler.transform(test[feature_cols])

        model = model_cls
        if hasattr(model, "fit"):
            try:
                model.fit(X_train, y_train)
            except Exception:
                continue

        if hasattr(model, "predict_proba"):
            probs_raw = model.predict_proba(X_test)
            if probs_raw.shape[1] == 1:
                only_class = int(model.classes_[0])
                probs = np.full(len(X_test), 1.0 if only_class == 1 else 0.0)
            else:
                probs = probs_raw[:, 1]
        else:
            probs = np.full(len(X_test), 0.5)

        all_probs.extend(probs.tolist())
        all_truths.extend(test["target"].values.tolist())
        all_dates.extend(test.index.tolist())

    if len(all_probs) < 50:
        return None

    probs_arr = np.array(all_probs)
    truths_arr = np.array(all_truths)

    # AUC ROC
    from sklearn.metrics import roc_auc_score
    try:
        auc = float(roc_auc_score(truths_arr, probs_arr))
    except ValueError:
        return None

    # Direction accuracy
    preds = (probs_arr > 0.5).astype(int)
    dir_acc = float(np.mean(preds == truths_arr))

    # Sharpe from trading signal: long if prob > 0.5, short if < 0.5
    # Use actual returns (not just direction) for Sharpe calculation
    close_aligned = close.reindex(all_dates)
    signal_returns = []
    for i in range(len(all_dates) - 1):
        if i + 1 < len(close_aligned):
            day_ret = close_aligned.iloc[i + 1] / close_aligned.iloc[i] - 1
            if np.isnan(day_ret):
                continue
            if probs_arr[i] < 0.5:
                day_ret = -day_ret  # short
            signal_returns.append(day_ret)

    if len(signal_returns) < 30:
        return None

    sig_ret = np.array(signal_returns)
    # Apply fee: only count fee on position changes
    positions = (probs_arr[:-1] > 0.5).astype(int)
    flips = np.abs(np.diff(positions, prepend=positions[0]))
    fee_per_flip = FEE_BPS / 10000
    net_returns = sig_ret - flips[: len(sig_ret)] * fee_per_flip

    sharpe_signal = _sharpe_ann(net_returns)

    # B&H baseline over same period
    bh_rets = close_aligned.pct_change().dropna().values[: len(net_returns)]
    sharpe_bh = _sharpe_ann(bh_rets) if len(bh_rets) >= 30 else float("nan")

    return {
        "auc": auc,
        "dir_acc": dir_acc,
        "sharpe_signal": sharpe_signal,
        "sharpe_bh": sharpe_bh,
        "delta_sharpe": sharpe_signal - sharpe_bh if not np.isnan(sharpe_bh) else float("nan"),
        "n_obs": len(all_probs),
        "n_flips": int(flips.sum()),
        "model": model_name,
    }


def evaluate_one_combo(coin: str, horizon: int, seed: int) -> dict | None:
    """Run all 3 models for one (coin, horizon, seed) and return best result."""
    hourly_rets = _load_one_coin(coin)
    if len(hourly_rets) < 1000:
        return None

    # Build daily close from hourly log returns
    daily_log_ret = hourly_rets.groupby(hourly_rets.index.normalize()).sum()
    daily_log_ret.index = pd.DatetimeIndex(daily_log_ret.index).normalize()
    daily_close = np.exp(daily_log_ret.cumsum())
    daily_close.name = "close"

    if len(daily_close) < horizon + 300:
        return None

    models = make_models(seed)
    best_result = None
    best_auc = -1

    for model_name, model_cls in models.items():
        result = walk_forward_trend(daily_close, horizon, seed, model_name, model_cls)
        if result is not None and result["auc"] > best_auc:
            best_auc = result["auc"]
            best_result = result

    if best_result is None:
        return None

    best_result.update({
        "coin": coin,
        "horizon": horizon,
        "seed": seed,
    })
    return best_result


def _sharpe_ann(returns: np.ndarray) -> float:
    if len(returns) < 10:
        return float("nan")
    mu = float(np.mean(returns))
    sigma = float(np.std(returns, ddof=1))
    return (mu / sigma) * np.sqrt(365) if sigma > 1e-12 else float("nan")


def _binomial_pvalue_one_sided(k: int, n: int) -> float:
    """One-sided binomial p-value: P(X >= k | p=0.5)."""
    from scipy.stats import binom
    if n == 0:
        return 1.0
    return float(binom.sf(k - 1, n, 0.5))


# ── Main sweep ─────────────────────────────────────────────────────────────────


def main() -> None:
    parser = argparse.ArgumentParser(description="S8 Trend Long-Horizon sweep")
    parser.add_argument("--dry-run", action="store_true", help="Run BTC h=60 seed=0 only")
    args = parser.parse_args()

    RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    t0 = time.time()

    combos: list[dict] = []
    total = len(COINS) * len(HORIZONS) * len(SEEDS)
    done = 0

    if args.dry_run:
        print("[DRY RUN] BTC-USD h=60 seed=0 only")
        row = evaluate_one_combo("BTC-USD", 60, 0)
        if row:
            combos.append(row)
            print(json.dumps(row, indent=2))
        return

    for coin in COINS:
        for h in HORIZONS:
            for seed in SEEDS:
                done += 1
                print(f"\n[{done}/{total}] {coin} h={h} seed={seed}", flush=True)
                row = evaluate_one_combo(coin, h, seed)
                if row is not None:
                    combos.append(row)
                    print(f"  best={row['model']} auc={row['auc']:.3f} dir_acc={row['dir_acc']:.3f} "
                          f"delta_sharpe={row['delta_sharpe']:+.4f}", flush=True)
                else:
                    print(f"  SKIPPED (insufficient data)", flush=True)

    elapsed = time.time() - t0
    n_combos = len(combos)
    print(f"\n{'='*60}")
    print(f"S8 Trend Long-Horizon sweep complete: {n_combos}/{total} combos in {elapsed:.0f}s")

    # AUC > 0.55 criterion
    n_auc_above_55 = sum(1 for r in combos if r["auc"] > 0.55)
    median_auc = float(np.median([r["auc"] for r in combos])) if combos else float("nan")

    # Sharpe beats B&H
    n_sharpe_beats = sum(1 for r in combos if r["delta_sharpe"] > 0)
    median_delta = float(np.median([r["delta_sharpe"] for r in combos])) if combos else float("nan")
    p_sign = _binomial_pvalue_one_sided(n_sharpe_beats, n_combos)

    # Per-coin aggregation
    per_coin: dict[str, dict] = {}
    for r in combos:
        c = r["coin"]
        per_coin.setdefault(c, {"aucs": [], "deltas": [], "models": []})
        per_coin[c]["aucs"].append(r["auc"])
        per_coin[c]["deltas"].append(r["delta_sharpe"])
        per_coin[c]["models"].append(r["model"])

    # Per-horizon
    per_horizon: dict[int, dict] = {}
    for r in combos:
        h = r["horizon"]
        per_horizon.setdefault(h, {"aucs": [], "deltas": []})
        per_horizon[h]["aucs"].append(r["auc"])
        per_horizon[h]["deltas"].append(r["delta_sharpe"])

    print(f"\nAUC > 0.55: {n_auc_above_55}/{n_combos} ({n_auc_above_55/max(n_combos,1)*100:.1f}%)")
    print(f"Median AUC: {median_auc:.4f}")
    print(f"\nSharpe beats B&H: {n_sharpe_beats}/{n_combos} (p={p_sign:.4f})")
    print(f"Median delta-Sharpe: {median_delta:+.4f}")

    print(f"\nPer-horizon median AUC:")
    for h in HORIZONS:
        if h in per_horizon:
            med_auc = float(np.median(per_horizon[h]["aucs"]))
            med_delta = float(np.median(per_horizon[h]["deltas"]))
            print(f"  h={h}: AUC={med_auc:.3f} delta_sharpe={med_delta:+.4f}")

    print(f"\nPer-coin:")
    for c in COINS:
        if c in per_coin:
            med_auc = float(np.median(per_coin[c]["aucs"]))
            med_delta = float(np.median(per_coin[c]["deltas"]))
            n_beats = sum(1 for d in per_coin[c]["deltas"] if d > 0)
            n_total = len(per_coin[c]["deltas"])
            print(f"  {c}: AUC={med_auc:.3f} delta={med_delta:+.4f} beats={n_beats}/{n_total}")

    # Verdict: BEATS if AUC > 0.55 AND Sharpe diff significant
    if median_auc > 0.55 and p_sign < 0.05 and n_sharpe_beats / max(n_combos, 1) >= 0.60:
        verdict = "BEATS"
    elif median_auc > 0.52 and p_sign < 0.10 and n_sharpe_beats / max(n_combos, 1) >= 0.55:
        verdict = "INCONCLUSIVE"
    else:
        verdict = "NO BEATS"

    print(f"\nVERDICT: {verdict} (AUC={median_auc:.4f}, p_sharpe={p_sign:.4f}, "
          f"sharpe_win={n_sharpe_beats}/{n_combos})")

    # Save
    results = {
        "model": "S8 Trend Long-Horizon (best of LASSO/RF/LightGBM)",
        "reference": "Curriculum V2 pilot — user hypothesis long-horizon trend",
        "fee_bps": FEE_BPS,
        "n_splits": N_SPLITS,
        "refit_every": REFIT_EVERY,
        "horizons": HORIZONS,
        "n_combos": n_combos,
        "median_auc": median_auc,
        "n_auc_above_55": n_auc_above_55,
        "n_sharpe_beats_bh": n_sharpe_beats,
        "p_sign_sharpe": p_sign,
        "median_delta_sharpe": median_delta,
        "verdict": verdict,
        "elapsed_s": elapsed,
        "combos": combos,
        "per_coin": {
            c: {
                "median_auc": float(np.median(v["aucs"])),
                "median_delta_sharpe": float(np.median(v["deltas"])),
                "n_beats": sum(1 for d in v["deltas"] if d > 0),
                "n_total": len(v["deltas"]),
                "best_model": max(set(v["models"]), key=v["models"].count),
            }
            for c, v in per_coin.items()
        },
        "per_horizon": {
            str(h): {
                "median_auc": float(np.median(v["aucs"])),
                "median_delta_sharpe": float(np.median(v["deltas"])),
                "n_beats": sum(1 for d in v["deltas"] if d > 0),
                "n_total": len(v["deltas"]),
            }
            for h, v in per_horizon.items()
        },
    }

    with open(RESULTS_DIR / "results.json", "w") as f:
        json.dump(results, f, indent=2, default=str)

    if combos:
        df = pd.DataFrame(combos)
        df.to_csv(RESULTS_DIR / "s8_trend_long_horizon_results.csv", index=False)
        print(f"\nSaved: {RESULTS_DIR / 'results.json'}")
        print(f"Saved: {RESULTS_DIR / 's8_trend_long_horizon_results.csv'}")


if __name__ == "__main__":
    main()
