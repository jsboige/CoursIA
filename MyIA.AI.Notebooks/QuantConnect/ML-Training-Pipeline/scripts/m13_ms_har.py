"""M13 Markov-Switching HAR — Hamilton (1989) 2-regime model on log(RV).

Question
--------
Crypto volatility has clear regime shifts (calm vs turbulent). Does a 2-regime
Markov-Switching HAR model, where each regime has its own HAR coefficients,
beat the single-regime HAR Classic baseline?

Model:
    Regime s_t in {0, 1} (0=calm, 1=turbulent)
    Transition: P(s_t = j | s_{t-1} = i) = p_ij (2x2 matrix)

    In regime s_t = k:
        log(RV_{t+1}) = b0_k + b_d_k * log(RV_d) + b_w_k * log(RV_w) + b_m_k * log(RV_m) + e_k

    Forecast = E[log(RV_{t+1})] = sum_k P(s_t = k) * forecast_k

Uses statsmodels.tsa.regime_switching.markov_regression.MarkovRegression.
Walk-forward 5-fold, refit every 22 days.
7 coins x 3 horizons x 4 seeds = 84 combos.
Sign-test paired Sharpe-diff vs HAR Classic baseline.

Cluster revalidation (#18190 port) ------------------------------------
The 7-coin universe this script already sweeps is the family's paired-origin
cluster (BTC=Bitstamp local, ETH=Binance local, the five others via
yfinance). The port adds the family's DM legs beside the published sign
test: the two OOS series are joined on their common ORIGIN DATES through
`joined_pair_errors`, with a fail-closed guard on the shared target, plus
the de-biased (precision) leg and the per-model bias report of
`pr-review-discipline` section C. The sign test, the Sharpe numbers and the
MSE fields keep their original meaning -- the control is added, never
substituted.

Output
------
- results/m13_ms_har/results.json
- results/m13_ms_har/m13_results.csv
- results/m13_ms_har/results.json.checkpoint.jsonl (resume)
- docs/M13_MS_HAR.md (verdict)

Env: system Python 3.13 (no conda). Reuses har_model, realized_variance, m11g infra.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
import time
from pathlib import Path

import numpy as np
import pandas as pd

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

# The bias/precision helpers and the four-state aggregate machine (#14388)
# live in bias_metrics.py, shared by the whole family (M4/M5/M15/M17 and now
# M13). Re-exported here so the tests import them from this module.
from bias_metrics import (  # noqa: E402, F401
    _aggregate_state,
    _dm_centered_mse,
    _is_beats,
    _is_beaten,
    _mse_decomposition,
    joined_pair_errors,
)
from dm_test import dm_verdict  # noqa: E402
from har_model import HARModel, walk_forward_har  # noqa: E402
from intraday_loader import (  # noqa: E402
    hourly_log_returns,
    load_binance_eth,
    load_bitstamp_btc,
    load_yf_intraday,
)
from m11c_sharpe_test import ledoit_wolf_sharpe_diff_se  # noqa: E402
from m11g_fee_aware_kelly import (  # noqa: E402
    _binomial_pvalue_one_sided,
    _kelly_weights_and_returns,
    _load_one_coin,
    _net_at_fee,
)
from realized_variance import (  # noqa: E402
    daily_realized_variance,
    har_lag_features,
    realized_variance_to_log,
)

COINS = ["BTC-USD", "ETH-USD", "SOL-USD", "LTC-USD", "XRP-USD", "ADA-USD", "DOT-USD"]
HORIZONS = [1, 5, 10]
SEEDS = [0, 1, 7, 42]
KELLY_CAP = 1.0
MU_WINDOW = 60
FEE_BPS = 50
N_SPLITS = 5
REFIT_EVERY = 22
N_REGIMES = 2
RESULTS_DIR = SCRIPT_DIR / "results" / "m13_ms_har"

# MS-HAR fitting params
MS_MAX_ITER = 100
MS_TOL = 1e-6
MS_MIN_TRAIN = 100  # Minimum obs for MS-HAR fitting


def _joined_or_sentinel(series_pair, row_extra: dict) -> dict | None:
    """`joined_pair_errors` wrapper that records the refusal instead of dying.

    Cluster protocol #18190 (same wrapper contract as `dlinear_vol.py` and
    `hmm_regime_vol.py`): a shared-target mismatch returns ``None`` and the
    row records the refusal -- the aggregate then counts `n_target_mismatch`
    instead of losing the whole combo to an exception.
    """
    try:
        return joined_pair_errors(*series_pair)
    except ValueError as exc:
        row_extra["dm_target_refusal"] = str(exc)
        return None


def _sharpe_ann(returns: np.ndarray) -> float:
    if len(returns) < 10:
        return float("nan")
    mu = float(np.mean(returns))
    sigma = float(np.std(returns, ddof=1))
    return (mu / sigma) * np.sqrt(365) if sigma > 1e-12 else float("nan")


def _build_har_features(rv: pd.Series) -> pd.DataFrame:
    """Build HAR lag features (daily, weekly, monthly) on log-RV scale."""
    log_rv = realized_variance_to_log(rv).rename("logrv")
    feats = har_lag_features(rv).apply(realized_variance_to_log)
    df = pd.concat(
        [feats.rename(columns={"rv_d": "logrv_d", "rv_w": "logrv_w", "rv_m": "logrv_m"}),
         log_rv.rename("logrv_target")],
        axis=1,
    ).dropna()
    return df


def _fit_ms_har(
    rv_train: pd.Series,
    n_regimes: int = N_REGIMES,
    seed: int = 0,
) -> dict | None:
    """Fit a 2-regime Markov-Switching HAR model.

    Returns dict with coefficients per regime and transition matrix,
    or None if fitting fails.
    """
    df = _build_har_features(rv_train)
    if len(df) < MS_MIN_TRAIN:
        return None

    y = df["logrv_target"].values
    x = df[["logrv_d", "logrv_w", "logrv_m"]].values

    try:
        from statsmodels.tsa.regime_switching.markov_regression import MarkovRegression

        # Use exog with constant included via switching=True for intercept
        # We use k_regimes=2, trend='c' (constant), switching_trend=True
        # exog = HAR features (non-switching or switching)
        # For full regime-switching HAR, all coefficients switch
        model = MarkovRegression(
            y,
            k_regimes=n_regimes,
            trend="c",
            exog=x,
            switching_trend=True,
            switching_exog=True,
            switching_variance=False,
        )
        # Single search_reps for speed (full sweep = 84 combos)
        best_res = None
        best_ll = -np.inf
        for sr in [100]:
            try:
                res = model.fit(
                    search_reps=sr,
                    maxiter=MS_MAX_ITER,
                    em_iter=MS_MAX_ITER,
                )
                # Verify result is usable (params extractable, non-degenerate)
                p = np.array(res.params)
                if len(p) < 11:
                    continue
                # Check degeneracy before accepting
                c0, c1 = float(p[2]), float(p[3])
                bd0, bd1 = float(p[4]), float(p[5])
                if abs(c0 - c1) + abs(bd0 - bd1) < 1e-6:
                    continue
                # Accept if better llf
                if res.llf > best_ll:
                    best_ll = res.llf
                    best_res = res
            except Exception:
                continue

        if best_res is None:
            return None

        # Extract params
        params = np.array(best_res.params)
        try:
            p00 = float(params[0])
            p10 = float(params[1])
            const_0 = float(params[2])
            const_1 = float(params[3])
            beta_d_0 = float(params[4])
            beta_d_1 = float(params[5])
            beta_w_0 = float(params[6])
            beta_w_1 = float(params[7])
            beta_m_0 = float(params[8])
            beta_m_1 = float(params[9])
            sigma2_0 = float(params[10])
            sigma2_1 = float(params[11]) if len(params) > 11 else sigma2_0
        except (IndexError, KeyError):
            return None

        # Smoothed probabilities for training data
        try:
            smooth_probs = best_res.smoothed_marginal_probabilities
            if isinstance(smooth_probs, pd.DataFrame):
                prob_regime1 = smooth_probs.iloc[:, 1].values
            else:
                prob_regime1 = smooth_probs[:, 1]
        except Exception:
            prob_regime1 = None

        return {
            "const": [const_0, const_1],
            "beta_d": [beta_d_0, beta_d_1],
            "beta_w": [beta_w_0, beta_w_1],
            "beta_m": [beta_m_0, beta_m_1],
            "sigma2": [sigma2_0, sigma2_1],
            "p00": p00,
            "p10": p10,
            "p01": 1 - p00,
            "p11": 1 - p10,
            "smooth_prob_r1": prob_regime1,
            "llf": best_ll,
        }

    except Exception as exc:
        return None


def _predict_ms_har(
    ms_model: dict,
    rv_history: pd.Series,
    horizon: int,
) -> float:
    """Iterated h-step MS-HAR forecast.

    Forecast = weighted average of regime-specific forecasts,
    where weights are the steady-state regime probabilities.
    """
    p00, p01 = ms_model["p00"], ms_model["p01"]
    p10, p11 = ms_model["p10"], ms_model["p11"]

    # Steady-state probabilities
    pi1 = p10 / (p10 + p01) if (p10 + p01) > 1e-12 else 0.5
    pi0 = 1 - pi1

    rv_vals = list(rv_history.astype(float).values)
    forecasts: list[float] = []

    for _ in range(horizon):
        tail = pd.Series(rv_vals[-22:])
        log_rv = np.log(tail.clip(lower=1e-12))
        rv_d = float(log_rv.iloc[-1])
        rv_w = float(log_rv.iloc[-5:].mean())
        rv_m = float(log_rv.iloc[-22:].mean())

        # Regime-specific forecasts
        fc_0 = ms_model["const"][0] + ms_model["beta_d"][0] * rv_d + ms_model["beta_w"][0] * rv_w + ms_model["beta_m"][0] * rv_m
        fc_1 = ms_model["const"][1] + ms_model["beta_d"][1] * rv_d + ms_model["beta_w"][1] * rv_w + ms_model["beta_m"][1] * rv_m

        # Weighted forecast
        fc = pi0 * fc_0 + pi1 * fc_1
        forecasts.append(fc)
        rv_vals.append(float(np.exp(fc)))

    return float(np.mean(forecasts))


def walk_forward_ms_har(
    rv: pd.Series,
    horizon: int = 1,
    n_splits: int = 5,
    refit_every: int = 22,
    seed: int = 0,
) -> dict:
    """Walk-forward evaluation of MS-HAR."""
    rv = rv.dropna().astype(float)
    n = len(rv)
    if n < 200:
        raise ValueError(f"need >=200 daily obs, got {n}")
    log_rv = np.log(rv.clip(lower=1e-12))

    fold_size = n // (n_splits + 1)
    if fold_size < 30:
        raise ValueError(f"n={n} too small for {n_splits} splits")

    splits = []
    for k in range(1, n_splits + 1):
        train_end = fold_size * k
        test_start = train_end
        test_end = min(train_end + fold_size, n)
        splits.append((train_end, test_start, test_end))

    preds: list[float] = []
    truths: list[float] = []
    pred_dates: list[pd.Timestamp] = []
    fold_results: list[dict] = []

    for fold_idx, (train_end, test_start, test_end) in enumerate(splits):
        rv_train = rv.iloc[:train_end]
        if len(rv_train) < MS_MIN_TRAIN:
            continue

        ms_model = _fit_ms_har(rv_train, seed=seed)
        if ms_model is None:
            # Fallback to plain HAR for this fold
            try:
                har_model = HARModel().fit(rv_train)
            except Exception:
                continue
            fold_preds: list[float] = []
            fold_truths: list[float] = []
            history = list(rv.iloc[:test_start].values)
            for i in range(test_start, test_end - horizon):
                target_window = log_rv.iloc[i : i + horizon].mean()
                try:
                    fc = har_model.predict_h_step(pd.Series(history[-(22 + horizon) :]), horizon=horizon)
                except Exception:
                    continue
                fold_preds.append(fc)
                fold_truths.append(float(target_window))
                preds.append(fc)
                truths.append(float(target_window))
                pred_dates.append(rv.index[i])
                history.append(float(rv.iloc[i]))
                if (i - test_start) % refit_every == 0 and i > test_start:
                    try:
                        har_model = HARModel().fit(rv.iloc[:i])
                    except Exception:
                        pass
        else:
            fold_preds = []
            fold_truths = []
            history = list(rv.iloc[:test_start].values)
            for i in range(test_start, test_end - horizon):
                target_window = log_rv.iloc[i : i + horizon].mean()
                try:
                    fc = _predict_ms_har(
                        ms_model, pd.Series(history[-(22 + horizon) :]), horizon=horizon
                    )
                except Exception:
                    continue
                fold_preds.append(fc)
                fold_truths.append(float(target_window))
                preds.append(fc)
                truths.append(float(target_window))
                pred_dates.append(rv.index[i])
                history.append(float(rv.iloc[i]))
                if (i - test_start) % refit_every == 0 and i > test_start:
                    new_model = _fit_ms_har(rv.iloc[:i], seed=seed)
                    if new_model is not None:
                        ms_model = new_model

        fp = np.asarray(fold_preds)
        ft = np.asarray(fold_truths)
        fold_mse = float(np.mean((fp - ft) ** 2)) if len(fp) else float("nan")
        fold_results.append({"fold": fold_idx, "n_test": len(fp), "mse_logrv": fold_mse})

    preds_arr = np.asarray(preds)
    truths_arr = np.asarray(truths)
    aggregate_mse = (
        float(np.mean((preds_arr - truths_arr) ** 2)) if len(preds_arr) else float("nan")
    )
    forecasts = pd.Series(
        preds_arr, index=pd.DatetimeIndex(pred_dates), name="ms_har_logrv_pred"
    )
    targets = pd.Series(
        truths_arr, index=pd.DatetimeIndex(pred_dates), name="logrv_target"
    )
    return {
        "horizon": horizon,
        "n_splits": n_splits,
        "n_total_preds": len(preds_arr),
        "aggregate_mse_logrv": aggregate_mse,
        "fold_results": fold_results,
        "forecasts": forecasts,
        "targets": targets,
    }


def evaluate_one_combo(
    coin: str,
    horizon: int,
    seed: int,
) -> dict | None:
    """Run MS-HAR vs HAR Classic for one (coin, horizon, seed) combo."""
    np.random.seed(seed)
    hourly_rets = _load_one_coin(coin)
    if len(hourly_rets) < 1000:
        return None

    rv = daily_realized_variance(hourly_rets)
    if len(rv) < 300:
        return None

    # HAR Classic baseline
    try:
        har_out = walk_forward_har(rv, horizon=horizon, n_splits=N_SPLITS, refit_every=REFIT_EVERY)
    except (ValueError, Exception):
        return None

    # MS-HAR
    try:
        ms_out = walk_forward_ms_har(
            rv, horizon=horizon, n_splits=N_SPLITS, refit_every=REFIT_EVERY, seed=seed
        )
    except (ValueError, Exception):
        return None

    har_fc = har_out["forecasts"]
    ms_fc = ms_out["forecasts"]
    common_fc_idx = har_fc.index.intersection(ms_fc.index)
    if len(common_fc_idx) < 30:
        return None
    har_fc = har_fc.loc[common_fc_idx]
    ms_fc = ms_fc.loc[common_fc_idx]

    # --- Cluster protocol, DM legs (#18190 port) ---------------------------
    #
    # Every DM leg compares the errors of the SAME origin dates, joined by
    # date and refused on shared-target mismatch -- never a positional
    # truncation. Pre-port, this combo reused the HAR leg's target for BOTH
    # predictions (`har_out["targets"].reindex(...)` then reindexing the MS
    # forecasts onto it), which silently ignored any divergence between the
    # two legs' realised targets. The guard closes that: each leg now brings
    # its own target and the join refuses when they disagree.
    #
    # Specificity vs M15: both legs are produced from the same `rv` series on
    # the same split schedule, so the expected join is the IDENTITY -- the
    # guard is the proof that the two legs compare the same days, not the
    # correction of a cross-convention defect.
    row_extra: dict = {}
    joined = _joined_or_sentinel(
        (ms_fc, ms_out["targets"], har_fc, har_out["targets"]),
        row_extra,
    )
    if joined is not None:
        ms_errors = joined["a_errors"]
        har_errors = joined["b_errors"]
        dm_n_aligned = joined["n_joined"]
        dm_target_gap_max = joined["target_gap_max"]
        dm = dm_verdict(ms_errors, har_errors, horizon=horizon, loss_fn="mse")
    else:
        # Refused pairing: keep the per-leg arrays purely as inspectable
        # diagnostics; every DM leg below then carries the TARGET_MISMATCH
        # sentinel, which the aggregate machine counts as neither BEATS nor
        # BEATEN -- a refused comparison never contributes a verdict.
        ms_errors = (ms_fc - ms_out["targets"].reindex(ms_fc.index)).dropna().to_numpy()
        har_errors = (har_fc - har_out["targets"].reindex(har_fc.index)).dropna().to_numpy()
        dm_n_aligned = 0
        dm_target_gap_max = float("nan")
        dm = {"dm_statistic": float("nan"), "p_value": float("nan"),
              "verdict": "TARGET_MISMATCH"}

    # Bias instrumentation (#1454 sub-grain; family pattern of #12742/#12745).
    # `MSE = bias^2 + variance`: a DM on RAW errors answers "which model has
    # the lower loss", not "which model is more precise" -- an edge can be
    # carried entirely by the baseline being miscalibrated. Three legs are
    # persisted and none of them replaces a published one (#10961, section C).
    ms_decomp = _mse_decomposition(ms_errors)
    har_decomp_raw = _mse_decomposition(har_errors)
    ms_mse_joined = ms_decomp["mse"]
    har_mse_joined = har_decomp_raw["mse"]
    ms_bias_oos = float(np.mean(ms_errors)) if len(ms_errors) else float("nan")
    har_bias_oos = float(np.mean(har_errors)) if len(har_errors) else float("nan")

    # De-biased classic HAR: subtract its own OOS bias from its forecasts.
    # The MS-HAR model is left raw -- comparing a raw model to a de-biased
    # baseline is the strict reading of section C (it can only hurt the model).
    har_errors_debiased = har_errors - har_bias_oos
    har_decomp_debiased = _mse_decomposition(har_errors_debiased)
    har_mse_debiased = har_decomp_debiased["mse"]

    if joined is not None:
        dm_centered = _dm_centered_mse(ms_errors, har_errors, horizon=horizon)
    else:
        dm_centered = {"dm_stat": float("nan"), "dm_pvalue": float("nan"),
                       "dm_verdict": "TARGET_MISMATCH", "mean_loss_diff": float("nan")}

    # Daily close returns
    daily_rets = hourly_rets.groupby(hourly_rets.index.normalize()).sum().rename("r_daily")
    daily_rets.index = pd.DatetimeIndex(daily_rets.index).normalize()
    daily_rets = daily_rets.reindex(common_fc_idx).dropna()
    if len(daily_rets) < 30:
        return None
    har_fc = har_fc.reindex(daily_rets.index)
    ms_fc = ms_fc.reindex(daily_rets.index)

    # Kelly weights (each pair has its own aligned returns)
    har_pair = _kelly_weights_and_returns(daily_rets, har_fc, MU_WINDOW, KELLY_CAP)
    ms_pair = _kelly_weights_and_returns(daily_rets, ms_fc, MU_WINDOW, KELLY_CAP)
    if har_pair is None or ms_pair is None:
        return None
    har_w, r_har = har_pair
    ms_w, r_ms = ms_pair
    if len(r_har) < 50 or len(r_ms) < 50:
        return None

    # Align to minimum length (NaN patterns may differ between HAR and MS-HAR)
    n_min = min(len(r_har), len(r_ms))
    r_har = r_har[:n_min]
    r_ms = r_ms[:n_min]
    har_w = har_w[:n_min]
    ms_w = ms_w[:n_min]

    # Net returns
    har_net = _net_at_fee(har_w, r_har, FEE_BPS)
    ms_net = _net_at_fee(ms_w, r_ms, FEE_BPS)
    bh_net = r_har.copy()

    # Sharpe
    sharpe_har = _sharpe_ann(har_net)
    sharpe_ms = _sharpe_ann(ms_net)
    sharpe_bh = _sharpe_ann(bh_net)
    delta_sharpe = sharpe_ms - sharpe_har

    # LW2008 paired Sharpe-diff SE
    _, _, _, se = ledoit_wolf_sharpe_diff_se(ms_net, har_net)
    t_stat = delta_sharpe / se if isinstance(se, float) and se > 1e-12 else float("nan")

    # MSE comparison
    target = har_out["targets"].reindex(common_fc_idx).dropna()
    har_pred = har_fc.reindex(target.index)
    ms_pred = ms_fc.reindex(target.index)
    mse_har = float(np.mean((har_pred - target) ** 2))
    mse_ms = float(np.mean((ms_pred - target) ** 2))
    mse_reduction_pct = (mse_ms - mse_har) / mse_har * 100 if mse_har > 0 else float("nan")

    result = {
        "coin": coin,
        "horizon": horizon,
        "seed": seed,
        "sharpe_har": sharpe_har,
        "sharpe_ms_har": sharpe_ms,
        "sharpe_bh": sharpe_bh,
        "delta_sharpe_ms_vs_har": delta_sharpe,
        "lw_se": se,
        "t_stat": t_stat,
        # Published MSE fields, kept with their pre-port meaning (the HAR
        # leg's target reindexed onto the common dates) so the numbers in
        # docs/M13_MS_HAR.md stay reproducible.
        "mse_har": mse_har,
        "mse_ms_har": mse_ms,
        "mse_reduction_pct": mse_reduction_pct,
        "n_obs": n_min,
        "ms_preds": len(ms_fc),
        "har_preds": len(har_fc),
        # --- cluster protocol: origin-date join + alignment diagnostics ----
        "n_preds": int(len(ms_fc)),
        "dm_n_aligned": dm_n_aligned,
        "dm_target_gap_max": dm_target_gap_max,
        # --- precision leg: DM on mse, raw errors --------------------------
        "dm_statistic": dm["dm_statistic"],
        "dm_p_value": dm["p_value"],
        "dm_verdict": dm["verdict"],
        "ms_mse_joined": ms_mse_joined,
        "har_mse_joined": har_mse_joined,
        "mse_reduction_pct_joined": (
            (har_mse_joined - ms_mse_joined) / har_mse_joined * 100
            if har_mse_joined and har_mse_joined > 0 else 0.0
        ),
        # --- bias report, per model (section C) ----------------------------
        "ms_bias_oos": ms_bias_oos,
        "ms_bias_sq": ms_decomp["bias_sq"],
        "ms_variance": ms_decomp["variance"],
        "har_bias_oos": har_bias_oos,
        "har_bias_sq_raw": har_decomp_raw["bias_sq"],
        "har_variance_raw": har_decomp_raw["variance"],
        # --- edge against the DE-BIASED baseline ---------------------------
        "har_mse_debiased": har_mse_debiased,
        "har_bias_sq_debiased": har_decomp_debiased["bias_sq"],
        "har_variance_debiased": har_decomp_debiased["variance"],
        "har_bias_share_of_mse": (
            har_decomp_raw["bias_sq"] / har_mse_joined
            if har_mse_joined and har_mse_joined > 0 else float("nan")
        ),
        "mse_reduction_pct_vs_debiased_classic": (
            (har_mse_debiased - ms_mse_joined) / har_mse_debiased * 100
            if har_mse_debiased and har_mse_debiased > 0 else 0.0
        ),
        # --- DM on errors centered by their own mean (pure variance) -------
        "dm_centered_stat": dm_centered["dm_stat"],
        "dm_centered_pvalue": dm_centered["dm_pvalue"],
        "dm_centered_verdict": dm_centered["dm_verdict"],
        "dm_centered_mean_loss_diff": dm_centered["mean_loss_diff"],
    }
    if row_extra:
        result.update(row_extra)
    return result


def _aggregate_cell(coin: str, horizon: int, cell: list[dict]) -> dict:
    """Aggregate the seeds of one (coin, horizon) cell into the family's verdict.

    Both legs go through the same four-state machine (`_aggregate_state`,
    #14388) as M4/M5/M15/M17: the raw leg passes `n_beats_parent=None` so its
    `refuted-de-biased` branch never fires, and the precision leg passes the
    raw leg's beat count so it can report the refutation.

    A seed whose leg carries the `TARGET_MISMATCH` sentinel is counted as
    neither BEATS nor BEATEN (the `_is_beats`/`_is_beaten` guards), so a
    refused pairing can never contribute to a verdict.
    """
    n_seeds = len(cell)
    c_beats = sum(1 for r in cell if _is_beats(r["dm_verdict"]))
    c_beaten = sum(1 for r in cell if _is_beaten(r["dm_verdict"]))
    c_beats_centered = sum(1 for r in cell if _is_beats(r["dm_centered_verdict"]))
    c_beaten_centered = sum(1 for r in cell if _is_beaten(r["dm_centered_verdict"]))
    dm_p_median = float(np.median([r["dm_p_value"] for r in cell]))
    dm_centered_p_median = float(np.median([r["dm_centered_pvalue"] for r in cell]))
    return {
        "coin": coin, "horizon": horizon, "seed": "aggregate",
        "n_seeds": n_seeds,
        "n_beats_seeds": f"{c_beats}/{n_seeds}",
        "n_beaten_seeds": f"{c_beaten}/{n_seeds}",
        "mean_ms_mse": float(np.mean([r["ms_mse_joined"] for r in cell])),
        "mean_har_mse": float(np.mean([r["har_mse_joined"] for r in cell])),
        "mean_reduction_pct": float(np.mean([r["mse_reduction_pct_joined"] for r in cell])),
        "std_reduction_pct": float(np.std([r["mse_reduction_pct_joined"] for r in cell], ddof=0)),
        "dm_p_median": dm_p_median,
        "aggregate_verdict": _aggregate_state(
            n_beats=c_beats, n_beaten=c_beaten, n_seeds=n_seeds,
            dm_p_median=dm_p_median,
        ),
        # --- de-biased / precision leg (#1454 sub-grain) -------------------
        "n_beats_seeds_centered": f"{c_beats_centered}/{n_seeds}",
        "n_beaten_seeds_centered": f"{c_beaten_centered}/{n_seeds}",
        "mean_har_mse_debiased": float(np.mean([r["har_mse_debiased"] for r in cell])),
        "mean_reduction_pct_vs_debiased_classic": float(
            np.mean([r["mse_reduction_pct_vs_debiased_classic"] for r in cell])
        ),
        "dm_centered_p_median": dm_centered_p_median,
        "mean_ms_bias_oos": float(np.mean([r["ms_bias_oos"] for r in cell])),
        "mean_har_bias_oos": float(np.mean([r["har_bias_oos"] for r in cell])),
        "mean_har_bias_share_of_mse": float(
            np.mean([r["har_bias_share_of_mse"] for r in cell])
        ),
        "aggregate_verdict_debiased": _aggregate_state(
            n_beats=c_beats_centered, n_beaten=c_beaten_centered, n_seeds=n_seeds,
            dm_p_median=dm_centered_p_median, n_beats_parent=c_beats,
        ),
    }


def _sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _write_cluster_manifest(
    manifest_path: Path,
    all_rows: list[dict],
    aggregate_rows: list[dict],
    out_path: Path,
    horizons_run: list[int],
    seeds_run: list[int],
    elapsed_s: float,
) -> None:
    """Compact in-repo cluster manifest (results-artifact-policy #15890).

    Same shape and SHA canonicalization as the M4 (#18650), M15 (#18664) and
    M5 cluster manifests: verdicts, per-cell alignment diagnostics and
    per-coin SHA-256 anchors of the full rows stay falsifiable in-repo; the
    full run JSON lives outside the repository.
    """
    per_coin: dict[str, list[dict]] = {}
    for r in all_rows:
        if r.get("seed") == "aggregate":
            continue
        per_coin.setdefault(r["coin"], []).append(r)

    alignment = []
    for agg in aggregate_rows:
        rows = [
            r for r in per_coin.get(agg["coin"], [])
            if r.get("horizon") == agg["horizon"]
        ]
        n_joined = [r.get("dm_n_aligned") for r in rows if r.get("dm_n_aligned") is not None]
        gaps = [
            r.get("dm_target_gap_max") for r in rows
            if r.get("dm_target_gap_max") is not None
            and np.isfinite(r["dm_target_gap_max"])
        ]
        alignment.append({
            "cell": f"{agg['coin']}|h={agg['horizon']}",
            "n_seeds": agg.get("n_seeds"),
            "dm_n_aligned_min": min(n_joined) if n_joined else None,
            "dm_n_aligned_max": max(n_joined) if n_joined else None,
            "dm_target_gap_max": max(gaps) if gaps else None,
            "n_target_mismatch": sum(1 for r in rows if "dm_target_refusal" in r),
            "aggregate_verdict": agg["aggregate_verdict"],
            "aggregate_verdict_debiased": agg["aggregate_verdict_debiased"],
            "mean_reduction_pct": agg["mean_reduction_pct"],
            "mean_reduction_pct_vs_debiased_classic": agg["mean_reduction_pct_vs_debiased_classic"],
            "dm_p_median": agg["dm_p_median"],
            "dm_centered_p_median": agg["dm_centered_p_median"],
            "mean_ms_bias_oos": agg["mean_ms_bias_oos"],
            "mean_har_bias_oos": agg["mean_har_bias_oos"],
        })

    full_text = out_path.read_text(encoding="utf-8")
    manifest = {
        "protocol": (
            "paired-origin cluster revalidation (#18190 port): DM legs join "
            "walk-forwards on common origin dates and refuse on shared-target "
            "mismatch, never positional truncation"
        ),
        "config": {
            "coins": sorted(per_coin.keys()),
            "horizons": horizons_run,
            "seeds": seeds_run,
            "n_splits": N_SPLITS,
            "refit_every": REFIT_EVERY,
            "n_regimes": N_REGIMES,
            "loss_fn": "mse",
        },
        "elapsed_s": elapsed_s,
        "total_rows": len(all_rows) + len(aggregate_rows),
        "artifact": {
            "path": out_path.name,
            "bytes": out_path.stat().st_size,
            "sha256": _sha256_text(full_text),
        },
        "per_coin_sha256": {
            coin: _sha256_text(json.dumps(rows, sort_keys=True, default=str))
            for coin, rows in sorted(per_coin.items())
        },
        "alignment": alignment,
    }
    manifest_path.parent.mkdir(parents=True, exist_ok=True)
    manifest_path.write_text(json.dumps(manifest, indent=2), encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="M13 Markov-Switching HAR sweep")
    parser.add_argument("--dry-run", action="store_true", help="Run BTC h=1 seed=0 only")
    parser.add_argument("--coins", nargs="+", default=None, help="Subset of coins")
    parser.add_argument("--out", default=None,
                        help="results JSON path (default: results/m13_ms_har/results.json)")
    parser.add_argument("--manifest-out", type=Path, default=None,
                        help=("Write the compact cluster manifest (verdicts + alignment "
                              "diagnostics + per-coin SHA-256 anchors of the full rows) "
                              "to this path, per the results-artifact policy #15890."))
    args = parser.parse_args()

    RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    t0 = time.time()

    coins = args.coins or COINS
    combos: list[dict] = []
    total = len(coins) * len(HORIZONS) * len(SEEDS)
    done = 0

    if args.dry_run:
        print("[DRY RUN] BTC-USD h=1 seed=0 only")
        row = evaluate_one_combo("BTC-USD", 1, 0)
        if row:
            combos.append(row)
            print(json.dumps(row, indent=2))
        return

    out_path = Path(args.out) if args.out else RESULTS_DIR / "results.json"

    # Checkpoint/resume (per (coin, horizon, seed) combo, dlinear_vol pattern):
    # the cluster grid is 7 coins x 3 horizons x 4 seeds = 84 walk-forwards and
    # the MS-HAR fit is the expensive leg (~63 min for the full grid); a process
    # death must not lose the completed combos. Each finished combo is appended
    # to a JSONL beside the out JSON and skipped on restart.
    checkpoint_path = out_path.with_name(out_path.name + ".checkpoint.jsonl")
    checkpoint_rows: dict[tuple[str, int, int], dict] = {}
    if checkpoint_path.exists():
        with open(checkpoint_path, encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                row = json.loads(line)
                checkpoint_rows[(row["coin"], row["horizon"], row["seed"])] = row
        print(f"[checkpoint] {len(checkpoint_rows)} completed combo(s) resumed "
              f"from {checkpoint_path.name}")

    for coin in coins:
        for h in HORIZONS:
            for seed in SEEDS:
                done += 1
                print(f"\n[{done}/{total}] {coin} h={h} seed={seed}", flush=True)
                ck = checkpoint_rows.get((coin, h, seed))
                if ck is not None:
                    print(f"  [checkpoint] DM p={ck.get('dm_p_value', float('nan')):.4f} "
                          f"{ck.get('dm_verdict')} | de-biased "
                          f"{ck.get('dm_centered_verdict')}", flush=True)
                    combos.append(ck)
                    continue
                row = evaluate_one_combo(coin, h, seed)
                if row is not None:
                    combos.append(row)
                    checkpoint_path.parent.mkdir(parents=True, exist_ok=True)
                    with open(checkpoint_path, "a", encoding="utf-8") as fck:
                        fck.write(json.dumps(row, default=str) + "\n")
                    checkpoint_rows[(coin, h, seed)] = row
                    print(f"  joined={row['dm_n_aligned']}/{row['n_preds']} "
                          f"DM p={row['dm_p_value']:.4f} {row['dm_verdict']} | "
                          f"de-biased {row['dm_centered_verdict']}", flush=True)
                else:
                    print(f"  SKIPPED (insufficient data)", flush=True)

    elapsed = time.time() - t0
    print(f"\n{'='*60}")
    print(f"M13 MS-HAR sweep complete: {len(combos)}/{total} combos in {elapsed:.0f}s")

    # Aggregate
    n_combos = len(combos)
    n_beats = sum(1 for r in combos if r["delta_sharpe_ms_vs_har"] > 0)
    median_delta = float(
        np.median([r["delta_sharpe_ms_vs_har"] for r in combos])
    ) if combos else float("nan")
    median_mse = float(
        np.median([r["mse_reduction_pct"] for r in combos])
    ) if combos else float("nan")
    p_sign = _binomial_pvalue_one_sided(n_beats, n_combos)

    print(f"\nSign-test: {n_beats}/{n_combos} ({n_beats/max(n_combos,1)*100:.1f}%) MS-HAR>HAR")
    print(f"  p-value = {p_sign:.4f}")
    print(f"  median delta-Sharpe = {median_delta:+.4f}")
    print(f"  median MSE change = {median_mse:+.1f}%")

    # Per-coin
    print(f"\nPer-coin:")
    for coin in coins:
        coin_rows = [r for r in combos if r["coin"] == coin]
        if not coin_rows:
            continue
        n_b = sum(1 for r in coin_rows if r["delta_sharpe_ms_vs_har"] > 0)
        med = float(np.median([r["delta_sharpe_ms_vs_har"] for r in coin_rows]))
        med_mse = float(np.median([r["mse_reduction_pct"] for r in coin_rows]))
        print(f"  {coin}: beats={n_b}/{len(coin_rows)} delta={med:+.4f} MSE={med_mse:+.1f}%")

    # Verdict
    if p_sign < 0.05 and n_beats / max(n_combos, 1) >= 0.60:
        verdict = "BEATS"
    elif p_sign < 0.10 and n_beats / max(n_combos, 1) >= 0.55:
        verdict = "INCONCLUSIVE"
    else:
        verdict = "NO BEATS"

    print(f"\nVERDICT: {verdict} (p={p_sign:.4f}, win_rate={n_beats/max(n_combos,1)*100:.1f}%)")

    # ---------------------------------------------------------------
    # Per-cell DM aggregate (#18190 port): the sign test above treats the 84
    # combos as independent Bernoulli trials, which no Diebold-Mariano test
    # backs and which the de-biased leg never controls. The block below adds
    # the family's per-cell verdict -- same four-state machine
    # (`_aggregate_state`, #14388) as M4/M5/M15/M17 -- beside it. The sign
    # test keeps its published meaning; nothing is substituted.
    # ---------------------------------------------------------------
    aggregate_rows: list[dict] = []
    print(f"\nPer-cell DM aggregate (raw / de-biased, 4-state machine):")
    for coin in coins:
        for h in HORIZONS:
            cell = [r for r in combos if r["coin"] == coin and r["horizon"] == h]
            if not cell:
                continue
            row_agg = _aggregate_cell(coin, h, cell)
            print(f"  {coin} h={h}: raw {row_agg['n_beats_seeds']} BEATS -> "
                  f"{row_agg['aggregate_verdict']} | de-biased "
                  f"{row_agg['n_beats_seeds_centered']} BEATS, "
                  f"{row_agg['n_beaten_seeds_centered']} BEATEN -> "
                  f"{row_agg['aggregate_verdict_debiased']}")
            aggregate_rows.append(row_agg)

    # Save
    results = {
        "model": "M13_MS_HAR",
        "reference": "Hamilton (1989) Markov-Switching + Corsi (2009) HAR",
        "n_regimes": N_REGIMES,
        "kelly_cap": KELLY_CAP,
        "fee_bps": FEE_BPS,
        "mu_window": MU_WINDOW,
        "n_splits": N_SPLITS,
        "refit_every": REFIT_EVERY,
        "n_combos": n_combos,
        "n_ms_beats_har": n_beats,
        "win_rate": n_beats / max(n_combos, 1),
        "p_sign": p_sign,
        "median_delta_sharpe": median_delta,
        "median_mse_reduction": median_mse,
        "verdict": verdict,
        "elapsed_s": elapsed,
        # --- cluster revalidation (#18190 port) ---------------------------
        "loss_fn": "mse",
        "dm_centered_errors": True,
        "classic_har_debiased": True,
        "combos": combos,
        "aggregates": aggregate_rows,
    }

    out_path.parent.mkdir(parents=True, exist_ok=True)
    # newline="\n" + encoding : l'empreinte declaree par _write_cluster_manifest est
    # calculee sur le texte normalise en LF (read_text normalise CRLF -> LF) ; les
    # octets sur disque doivent etre ce texte-la, sinon le couple (bytes, sha256)
    # du manifeste decrit deux jeux d'octets differents (meme correctif que
    # merge_m13_partials.py -- dlinear_vol.py / m15_lstm_rv.py : issue dediee).
    with open(out_path, "w", encoding="utf-8", newline="\n") as f:
        json.dump(results, f, indent=2, default=str)

    if combos:
        df = pd.DataFrame(combos)
        csv_path = out_path.with_name("m13_results.csv")
        df.to_csv(csv_path, index=False)
        print(f"\nSaved: {out_path}")
        print(f"Saved: {csv_path}")

    if args.manifest_out is not None:
        _write_cluster_manifest(
            Path(args.manifest_out),
            combos,
            aggregate_rows,
            out_path,
            HORIZONS,
            SEEDS,
            elapsed,
        )
        print(f"Cluster manifest written to {args.manifest_out}")


if __name__ == "__main__":
    main()
