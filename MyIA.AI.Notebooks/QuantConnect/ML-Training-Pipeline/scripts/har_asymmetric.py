"""HAR-RV Asymmetric Semivariance: leverage-effect decomposition.

Extends the Corsi (2009) HAR model by splitting Realized Variance into
upside (RV+) and downside (RV-) semivariance components, following
Andersen, Bollerslev, Diebold & Patton (2007):

    RV_t  = RV+_t + RV-_t
    RV+_t = sum_{h in day t} r²_h × 1_{r_h > 0}
    RV-_t = sum_{h in day t} r²_h × 1_{r_h < 0}

The asymmetric HAR model:
    log RV_{t+h} = b0 + b1·log(RV-_t) + b2·log(RV+_t)
                       + b3·mean(log RV_{t-5..t-1}) + b4·mean(log RV_{t-22..t-6}) + e

Walk-forward 5-fold x 4 seeds x 3 horizons x 7 coins.
Diebold-Mariano vs HAR classic (PR #938 baseline).

Usage:
    python har_asymmetric.py --coins BTC-USD --horizons 1 5 10 \
        --seeds 0 7 42 99 --skip-remote --debias --calibration-size 60
    python har_asymmetric.py --horizons 1 5 10 --seeds 0 7 42 99
"""

from __future__ import annotations

import argparse
import json
import time
from pathlib import Path

import numpy as np
import pandas as pd

from dm_test import dm_verdict
from har_model import HARModel, walk_forward_har
from intraday_loader import (
    hourly_log_returns,
    load_binance_eth,
    load_bitstamp_btc,
    load_yf_intraday,
)
from realized_variance import (
    daily_realized_variance,
    realized_variance_to_log,
)


def daily_semivariance_positive(
    intraday_log_returns: pd.Series,
    min_obs_per_day: int = 6,
) -> pd.Series:
    """Upside semivariance: RV+ = sum(r² × 1_{r>0}) per day."""
    if not isinstance(intraday_log_returns.index, pd.DatetimeIndex):
        raise TypeError("intraday_log_returns must be DatetimeIndex")
    r = intraday_log_returns.astype(float)
    sq_pos = (r ** 2).where(r > 0, other=0.0)
    by_day = sq_pos.groupby(sq_pos.index.normalize())
    rv_pos = by_day.sum()
    counts = r.groupby(r.index.normalize()).count()
    rv_pos = rv_pos[counts >= min_obs_per_day]
    rv_pos.index = pd.DatetimeIndex(rv_pos.index).normalize()
    rv_pos.index.name = "date"
    rv_pos.name = "RV_pos"
    return rv_pos


def daily_semivariance_negative(
    intraday_log_returns: pd.Series,
    min_obs_per_day: int = 6,
) -> pd.Series:
    """Downside semivariance: RV- = sum(r² × 1_{r<0}) per day."""
    if not isinstance(intraday_log_returns.index, pd.DatetimeIndex):
        raise TypeError("intraday_log_returns must be DatetimeIndex")
    r = intraday_log_returns.astype(float)
    sq_neg = (r ** 2).where(r < 0, other=0.0)
    by_day = sq_neg.groupby(sq_neg.index.normalize())
    rv_neg = by_day.sum()
    counts = r.groupby(r.index.normalize()).count()
    rv_neg = rv_neg[counts >= min_obs_per_day]
    rv_neg.index = pd.DatetimeIndex(rv_neg.index).normalize()
    rv_neg.index.name = "date"
    rv_neg.name = "RV_neg"
    return rv_neg


def asymmetric_har_features(
    rv_neg: pd.Series,
    rv_pos: pd.Series,
    rv: pd.Series,
) -> pd.DataFrame:
    """Build asymmetric HAR features.

    Columns:
    - rv_neg_d = log(RV-_t)
    - rv_pos_d = log(RV+_t)
    - rv_w     = mean(log RV_{t-5..t-1})
    - rv_m     = mean(log RV_{t-22..t-6})
    """
    log_neg = np.log(rv_neg.shift(1).clip(lower=1e-12))
    log_pos = np.log(rv_pos.shift(1).clip(lower=1e-12))
    log_rv = np.log(rv.clip(lower=1e-12))
    rv_w = log_rv.shift(1).rolling(window=5, min_periods=5).mean()
    rv_m = log_rv.shift(1).rolling(window=22, min_periods=22).mean()
    return pd.DataFrame({
        "rv_neg_d": log_neg,
        "rv_pos_d": log_pos,
        "rv_w": rv_w,
        "rv_m": rv_m,
    })


class AsymmetricHARModel:
    """OLS asymmetric HAR with semivariance decomposition."""

    def __init__(self) -> None:
        self.coef_: np.ndarray | None = None
        self.n_train_: int = 0
        self.in_sample_mse_: float = float("nan")

    def fit(
        self,
        rv_neg: pd.Series,
        rv_pos: pd.Series,
        rv: pd.Series,
    ) -> "AsymmetricHARModel":
        feats = asymmetric_har_features(rv_neg, rv_pos, rv)
        target = realized_variance_to_log(rv).rename("y")
        df = pd.concat([feats, target], axis=1).dropna()
        if len(df) < 30:
            raise ValueError(f"Asymmetric HAR fit needs >=30 obs, got {len(df)}")
        x = df[["rv_neg_d", "rv_pos_d", "rv_w", "rv_m"]].to_numpy()
        y = df["y"].to_numpy()
        x_aug = np.column_stack([np.ones(len(x)), x])
        coef, *_ = np.linalg.lstsq(x_aug, y, rcond=None)
        resid = y - x_aug @ coef
        self.coef_ = coef
        self.n_train_ = len(df)
        self.in_sample_mse_ = float(np.mean(resid ** 2))
        return self

    def predict_h_step(
        self,
        rv_neg_history: pd.Series,
        rv_pos_history: pd.Series,
        rv_history: pd.Series,
        horizon: int,
    ) -> float:
        """Iterated h-step forecast on log-RV scale."""
        if horizon < 1:
            raise ValueError("horizon must be >= 1")
        if self.coef_ is None:
            raise RuntimeError("Model not fitted")

        neg_hist = list(rv_neg_history.astype(float).values)
        pos_hist = list(rv_pos_history.astype(float).values)
        rv_hist = list(rv_history.astype(float).values)

        forecasts: list[float] = []
        for _ in range(horizon):
            tail_neg = pd.Series(neg_hist[-22:])
            tail_pos = pd.Series(pos_hist[-22:])
            tail_rv = pd.Series(rv_hist[-(22 + horizon):])

            log_neg = float(np.log(tail_neg.clip(lower=1e-12).iloc[-1]))
            log_pos = float(np.log(tail_pos.clip(lower=1e-12).iloc[-1]))
            log_rv = np.log(tail_rv.clip(lower=1e-12))
            rv_w = float(log_rv.iloc[-5:].mean())
            rv_m = float(log_rv.iloc[-22:].mean())

            x_aug = np.array([1.0, log_neg, log_pos, rv_w, rv_m])
            log_pred = float(x_aug @ self.coef_)
            forecasts.append(log_pred)

            exp_pred = float(np.exp(log_pred))
            neg_hist.append(exp_pred * 0.5)
            pos_hist.append(exp_pred * 0.5)
            rv_hist.append(exp_pred)

        return float(np.mean(forecasts))


def _make_split_indices(n: int, n_splits: int) -> list[tuple[int, int, int]]:
    """Walk-forward expanding-window splits."""
    if n_splits < 2:
        raise ValueError("n_splits must be >= 2")
    fold_size = n // (n_splits + 1)
    if fold_size < 30:
        raise ValueError(f"n={n} too small for {n_splits} splits (fold_size={fold_size})")
    splits = []
    for k in range(1, n_splits + 1):
        train_end = fold_size * k
        test_start = train_end
        test_end = min(train_end + fold_size, n)
        splits.append((train_end, test_start, test_end))
    return splits


def _fit_asymmetric_with_train_calibration(
    rv_neg_train: pd.Series,
    rv_pos_train: pd.Series,
    rv_train: pd.Series,
    horizon: int,
    calibration_size: int,
) -> tuple[AsymmetricHARModel, float]:
    """Fit before a train-tail holdout and estimate a signed forecast offset."""
    calibration_size = min(calibration_size, max(0, len(rv_train) - 60))
    if calibration_size < max(10, horizon + 1):
        model = AsymmetricHARModel().fit(rv_neg_train, rv_pos_train, rv_train)
        return model, 0.0

    fit_end = len(rv_train) - calibration_size
    model = AsymmetricHARModel().fit(
        rv_neg_train.iloc[:fit_end],
        rv_pos_train.iloc[:fit_end],
        rv_train.iloc[:fit_end],
    )
    log_rv = np.log(rv_train.clip(lower=1e-12))
    errors: list[float] = []
    for i in range(fit_end, len(rv_train) - horizon):
        prediction = model.predict_h_step(
            rv_neg_train.iloc[:i],
            rv_pos_train.iloc[:i],
            rv_train.iloc[:i],
            horizon=horizon,
        )
        target = float(log_rv.iloc[i:i + horizon].mean())
        errors.append(prediction - target)

    bias = float(np.mean(errors)) if errors else 0.0
    return model, bias


def walk_forward_asymmetric_har(
    rv_neg: pd.Series,
    rv_pos: pd.Series,
    rv: pd.Series,
    horizon: int = 1,
    n_splits: int = 5,
    refit_every: int = 22,
    seed: int = 0,
    calibrate_bias: bool = False,
    calibration_size: int = 60,
) -> dict:
    """Walk-forward evaluation of asymmetric HAR.

    Returns MSE on log-RV scale, forecasts and targets for DM testing.
    """
    # OLS is deterministic; seed is retained to verify exact cross-seed stability.
    rv = rv.dropna().astype(float)
    rv_neg = rv_neg.reindex(rv.index).fillna(0.0).astype(float)
    rv_pos = rv_pos.reindex(rv.index).fillna(0.0).astype(float)

    n = len(rv)
    if n < 200:
        raise ValueError(f"need >=200 daily obs, got {n}")

    log_rv = np.log(rv.clip(lower=1e-12))
    splits = _make_split_indices(n, n_splits)

    preds: list[float] = []
    truths: list[float] = []
    pred_dates: list[pd.Timestamp] = []
    initial_calibration_bias_by_fold: list[float] = []

    for fold_idx, (train_end, test_start, test_end) in enumerate(splits):
        rv_train = rv.iloc[:train_end]
        rv_neg_train = rv_neg.iloc[:train_end]
        rv_pos_train = rv_pos.iloc[:train_end]
        if len(rv_train) < 60:
            continue

        if calibrate_bias:
            model, bias = _fit_asymmetric_with_train_calibration(
                rv_neg_train,
                rv_pos_train,
                rv_train,
                horizon=horizon,
                calibration_size=calibration_size,
            )
        else:
            model = AsymmetricHARModel().fit(rv_neg_train, rv_pos_train, rv_train)
            bias = 0.0
        initial_calibration_bias_by_fold.append(bias)

        for i in range(test_start, test_end - horizon):
            target_window = log_rv.iloc[i:i + horizon].mean()

            tail_neg = rv_neg.iloc[:i]
            tail_pos = rv_pos.iloc[:i]
            tail_rv = rv.iloc[:i]

            log_pred = (
                model.predict_h_step(tail_neg, tail_pos, tail_rv, horizon=horizon)
                - bias
            )

            preds.append(log_pred)
            truths.append(float(target_window))
            pred_dates.append(rv.index[i])

            if (i - test_start) % refit_every == 0 and i > test_start:
                if calibrate_bias:
                    model, bias = _fit_asymmetric_with_train_calibration(
                        rv_neg.iloc[:i],
                        rv_pos.iloc[:i],
                        rv.iloc[:i],
                        horizon=horizon,
                        calibration_size=calibration_size,
                    )
                else:
                    model = AsymmetricHARModel().fit(
                        rv_neg.iloc[:i], rv_pos.iloc[:i], rv.iloc[:i],
                    )
                    bias = 0.0

    preds_arr = np.asarray(preds)
    truths_arr = np.asarray(truths)
    aggregate_mse = float(np.mean((preds_arr - truths_arr) ** 2)) if len(preds_arr) else float("nan")

    forecasts = pd.Series(preds_arr, index=pd.DatetimeIndex(pred_dates), name="asym_har_logrv_pred")
    targets = pd.Series(truths_arr, index=pd.DatetimeIndex(pred_dates), name="logrv_target")

    return {
        "horizon": horizon,
        "seed": seed,
        "n_splits": n_splits,
        "n_total_preds": len(preds_arr),
        "aggregate_mse_logrv": aggregate_mse,
        "calibrate_bias": calibrate_bias,
        "calibration_size": calibration_size,
        "initial_calibration_bias_by_fold": initial_calibration_bias_by_fold,
        "forecasts": forecasts,
        "targets": targets,
    }


def _load_panel(
    skip_remote: bool,
    extra_coins: list[str] | None = None,
) -> dict[str, pd.Series]:
    """Load 7-coin hourly log returns panel."""
    out: dict[str, pd.Series] = {}
    print("[load] BTC Bitstamp 1h ...")
    btc = load_bitstamp_btc()
    out["BTC-USD"] = hourly_log_returns(btc)
    print(f"  BTC: {len(out['BTC-USD'])} obs")
    print("[load] ETH Binance 1h ...")
    eth = load_binance_eth()
    out["ETH-USD"] = hourly_log_returns(eth)
    print(f"  ETH: {len(out['ETH-USD'])} obs")
    if not skip_remote:
        for ticker in ["SOL-USD", "LTC-USD", "XRP-USD", "ADA-USD", "DOT-USD"] + (extra_coins or []):
            try:
                print(f"[load] {ticker} yfinance 1h ...")
                ds = load_yf_intraday(ticker)
                out[ticker] = hourly_log_returns(ds)
                print(f"  {ticker}: {len(out[ticker])} obs")
            except Exception as exc:
                print(f"[WARN] {ticker} skipped ({exc.__class__.__name__}: {exc})")
    return out


def _eval_one_coin(
    coin: str,
    hourly_rets: pd.Series,
    horizons: list[int],
    seeds: list[int],
    n_splits: int = 5,
    refit_every: int = 22,
    debias: bool = False,
    calibration_size: int = 60,
) -> list[dict]:
    """Run asymmetric HAR + classic HAR for one coin, all horizons/seeds."""
    rv = daily_realized_variance(hourly_rets)
    rv_pos = daily_semivariance_positive(hourly_rets)
    rv_neg = daily_semivariance_negative(hourly_rets)
    if len(rv) < 300:
        print(f"  [{coin}] SKIPPED: only {len(rv)} RV days")
        return [{"coin": coin, "horizon": h, "seed": s, "skipped": "rv<300"}
                for h in horizons for s in seeds]

    common = rv.index.intersection(rv_pos.index).intersection(rv_neg.index)
    rv = rv.loc[common]
    rv_pos = rv_pos.loc[common]
    rv_neg = rv_neg.loc[common]

    print(f"\n[{coin}] {len(rv)} RV days, "
          f"RV+ mean={rv_pos.mean():.6f}, RV- mean={rv_neg.mean():.6f}")

    rows: list[dict] = []
    for h in horizons:
        # Classic HAR baseline (seed 0 only for baseline reference)
        try:
            classic_out = walk_forward_har(
                rv,
                horizon=h,
                n_splits=n_splits,
                refit_every=refit_every,
                calibrate_bias=debias,
                calibration_size=calibration_size,
            )
            classic_mse = classic_out["aggregate_mse_logrv"]
            classic_forecasts = classic_out["forecasts"]
            classic_targets = classic_out["targets"]
            classic_errors = (classic_forecasts - classic_targets).dropna().values
            print(f"  h={h} classic HAR MSE={classic_mse:.5f} ({classic_out['n_total_preds']} preds)")
        except Exception as exc:
            print(f"  h={h} classic HAR FAILED: {exc}")
            classic_mse = float("nan")
            classic_errors = None
            classic_forecasts = None
            classic_targets = None

        if classic_forecasts is None or classic_targets is None:
            rows.extend({
                "coin": coin,
                "horizon": h,
                "seed": seed,
                "asym_mse_logrv": float("nan"),
                "classic_mse_logrv": classic_mse,
                "dm_verdict": "BASELINE_FAILED",
            } for seed in seeds)
            continue

        for seed in seeds:
            try:
                asym_out = walk_forward_asymmetric_har(
                    rv_neg,
                    rv_pos,
                    rv,
                    horizon=h,
                    n_splits=n_splits,
                    refit_every=refit_every,
                    seed=seed,
                    calibrate_bias=debias,
                    calibration_size=calibration_size,
                )
                asym_forecasts = asym_out["forecasts"]
                asym_targets = asym_out["targets"]
                common_dates = asym_forecasts.index.intersection(asym_targets.index)
                if classic_forecasts is not None and classic_targets is not None:
                    common_dates = common_dates.intersection(classic_forecasts.index)
                    common_dates = common_dates.intersection(classic_targets.index)
                pred_asym = asym_forecasts.reindex(common_dates).to_numpy(dtype=float)
                pred_classic = classic_forecasts.reindex(common_dates).to_numpy(dtype=float)
                pred_target = asym_targets.reindex(common_dates).to_numpy(dtype=float)
                finite = (
                    np.isfinite(pred_asym)
                    & np.isfinite(pred_classic)
                    & np.isfinite(pred_target)
                )
                common_dates = common_dates[finite]
                pred_asym = pred_asym[finite]
                pred_classic = pred_classic[finite]
                pred_target = pred_target[finite]
                asym_errors = pred_asym - pred_target
                classic_errors_aligned = pred_classic - pred_target
                asym_mse = float(np.mean(asym_errors ** 2))
                classic_mse_aligned = float(np.mean(classic_errors_aligned ** 2))
            except Exception as exc:
                print(f"  h={h} seed={seed} asym HAR FAILED: {exc}")
                rows.append({
                    "coin": coin, "horizon": h, "seed": seed,
                    "asym_mse": float("nan"), "classic_mse": float("nan"),
                    "dm_verdict": "FAILED",
                })
                continue

            # DM test: asymmetric vs classic
            dm_info = {}
            if classic_errors is not None and len(asym_errors) >= 10:
                try:
                    dm = dm_verdict(
                        asym_errors,
                        classic_errors_aligned,
                        horizon=h,
                        loss_fn="mse",
                    )
                    dm_info = {
                        "dm_stat": dm["dm_statistic"],
                        "dm_pvalue": dm["p_value"],
                        "dm_verdict": dm["verdict"],
                        "dm_mean_loss_diff": dm["mean_loss_diff"],
                    }
                    print(f"  h={h} seed={seed} asym MSE={asym_mse:.5f} "
                          f"DM={dm['dm_statistic']:.3f} p={dm['p_value']:.4f} "
                          f"-> {dm['verdict']}")
                except Exception as exc:
                    print(f"  h={h} seed={seed} DM FAILED: {exc}")
                    dm_info = {"dm_verdict": "DM_FAILED"}
            else:
                dm_info = {"dm_verdict": "INSUFFICIENT_DATA"}

            rows.append({
                "coin": coin,
                "horizon": h,
                "seed": seed,
                "n_rv_days": int(len(rv)),
                "n_predictions": int(len(pred_target)),
                "debias": debias,
                "calibration_size": calibration_size,
                "asym_mse_logrv": float(asym_mse),
                "classic_mse_logrv": float(classic_mse_aligned),
                "mse_reduction_pct": (
                    float((classic_mse_aligned - asym_mse) / classic_mse_aligned * 100)
                    if classic_mse_aligned > 0 else float("nan")
                ),
                "asym_bias_oos": float(np.mean(asym_errors)),
                "classic_bias_oos": float(np.mean(classic_errors_aligned)),
                "asym_error_variance": float(np.var(asym_errors)),
                "classic_error_variance": float(np.var(classic_errors_aligned)),
                "pred_dates": [date.strftime("%Y-%m-%d") for date in common_dates],
                "pred_asym": pred_asym.tolist(),
                "pred_classic_har": pred_classic.tolist(),
                "pred_target": pred_target.tolist(),
                **dm_info,
            })

    return rows


def aggregate_verdicts(rows: list[dict]) -> list[dict]:
    """Aggregate per-seed DM verdicts into a per-(coin, horizon) verdict.

    Verdict rules:
    - BEATS: all seeds with significant DM agree (p<0.05, asym lower loss),
             and cross-seed MSE std < mean MSE reduction
    - NO BEATS: any seed shows asym significantly worse
    - INCONCLUSIVE: mixed or no significance
    """
    from collections import defaultdict

    grouped: dict[tuple, list[dict]] = defaultdict(list)
    for r in rows:
        if "skipped" in r or "asym_mse_logrv" not in r:
            continue
        key = (r["coin"], r["horizon"])
        grouped[key].append(r)

    results = []
    for (coin, h), seeds_rows in sorted(grouped.items()):
        n_seeds = len(seeds_rows)
        asym_mses = [r["asym_mse_logrv"] for r in seeds_rows]
        classic_mses = [r["classic_mse_logrv"] for r in seeds_rows]
        verdicts = [r.get("dm_verdict", "UNKNOWN") for r in seeds_rows]
        p_values = [r.get("dm_pvalue", 1.0) for r in seeds_rows]

        mean_asym = float(np.nanmean(asym_mses))
        mean_classic = float(np.nanmean(classic_mses))
        std_asym = float(np.nanstd(asym_mses))
        mse_edges = np.asarray(classic_mses) - np.asarray(asym_mses)
        mean_edge = float(np.nanmean(mse_edges))
        std_edge = float(np.nanstd(mse_edges))
        median_pvalue = float(np.nanmedian(p_values))
        seed_stable = bool(
            np.allclose(asym_mses, asym_mses[0], rtol=0.0, atol=1e-12)
        )
        edge_sigma = None if seed_stable else (
            mean_edge / std_edge if std_edge > 0.0 else 0.0
        )

        mean_reduction = (mean_classic - mean_asym) / mean_classic * 100 if mean_classic > 0 else 0.0

        n_beats = sum(1 for v in verdicts if "BEATS" in v and "BEATEN" not in v)
        n_beaten = sum(1 for v in verdicts if "BEATEN" in v)
        n_inconclusive = sum(1 for v in verdicts if v == "INCONCLUSIVE")

        if n_beaten > 0:
            agg_verdict = "NO BEATS"
        elif (
            n_beats == n_seeds
            and median_pvalue < 0.05
            and (seed_stable or edge_sigma >= 2.0)
        ):
            agg_verdict = "BEATS"
        else:
            agg_verdict = "INCONCLUSIVE"

        results.append({
            "coin": coin,
            "horizon": h,
            "n_seeds": n_seeds,
            "mean_asym_mse": mean_asym,
            "std_asym_mse": std_asym,
            "mean_classic_mse": mean_classic,
            "mean_reduction_pct": mean_reduction,
            "mean_mse_edge": mean_edge,
            "std_mse_edge": std_edge,
            "edge_sigma": edge_sigma,
            "median_dm_pvalue": median_pvalue,
            "seed_stable": seed_stable,
            "n_beats": n_beats,
            "n_beaten": n_beaten,
            "n_inconclusive": n_inconclusive,
            "mean_dm_pvalue": float(np.nanmean(p_values)),
            "verdict": agg_verdict,
        })

    return results


def main() -> None:
    parser = argparse.ArgumentParser(description="HAR-RV Asymmetric Semivariance")
    parser.add_argument("--horizons", type=int, nargs="+", default=[1, 5, 10])
    parser.add_argument("--seeds", type=int, nargs="+", default=[0, 7, 42, 99])
    parser.add_argument("--n-splits", type=int, default=5)
    parser.add_argument("--refit-every", type=int, default=22)
    parser.add_argument("--skip-remote", action="store_true")
    parser.add_argument("--extra-coins", type=str, nargs="*", default=None)
    parser.add_argument("--coins", type=str, nargs="*", default=None)
    parser.add_argument("--debias", action="store_true")
    parser.add_argument("--calibration-size", type=int, default=60)
    parser.add_argument("--out-json", type=str, default="results/m3_har_asymmetric.json")
    args = parser.parse_args()

    t0 = time.time()
    panel = _load_panel(args.skip_remote, extra_coins=args.extra_coins)
    if args.coins:
        requested = set(args.coins)
        missing = sorted(requested.difference(panel))
        if missing:
            raise ValueError(f"requested coins unavailable: {missing}")
        panel = {coin: returns for coin, returns in panel.items() if coin in requested}

    all_rows: list[dict] = []
    for coin, rets in panel.items():
        rows = _eval_one_coin(
            coin=coin,
            hourly_rets=rets,
            horizons=args.horizons,
            seeds=args.seeds,
            n_splits=args.n_splits,
            refit_every=args.refit_every,
            debias=args.debias,
            calibration_size=args.calibration_size,
        )
        all_rows.extend(rows)

    agg = aggregate_verdicts(all_rows)

    print("\n=== M3 HAR Asymmetric Semivariance: Per-(coin, horizon) Verdicts ===")
    agg_df = pd.DataFrame(agg)
    if len(agg_df):
        print(agg_df.to_string(index=False))

    n_beats = sum(1 for r in agg if r["verdict"] == "BEATS")
    n_no = sum(1 for r in agg if r["verdict"] == "NO BEATS")
    n_inc = sum(1 for r in agg if r["verdict"] == "INCONCLUSIVE")
    print(f"\nSummary: {n_beats} BEATS / {n_no} NO BEATS / {n_inc} INCONCLUSIVE "
          f"(out of {len(agg)} configs)")

    out_path = Path(args.out_json)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps({
        "rows": all_rows,
        "aggregated": agg,
        "elapsed_s": time.time() - t0,
        "config": {
            "coins": list(panel),
            "horizons": args.horizons,
            "seeds": args.seeds,
            "n_splits": args.n_splits,
            "refit_every": args.refit_every,
            "debias": args.debias,
            "calibration_size": args.calibration_size,
        },
    }, indent=2))
    print(f"\n[done] {time.time() - t0:.1f}s -- wrote {out_path}")


if __name__ == "__main__":
    main()
