"""M12 HAR-RV-J — Andersen-Bollerslev-Diebold (2007) jump decomposition.

Question
--------
Does adding jump components to HAR improve volatility forecasting vs HAR Classic?
HAR-RV-J extends HAR from 3 regressors to 6 by decomposing RV into continuous
(Bipower Variation) and jump components:

    RV_t = BPV_t + J_t,  where J_t = max(RV_t - mu * BPV_t, 0), mu ≈ 0.6 (Huang-Tauchen)

HAR-RV-J regression:
    log(RV_{t+1}) = b0 + b_d*log(RV_t) + b_w*log(RV_w) + b_m*log(RV_m)
                      + b_dj*J_t + b_wj*J_w + b_mj*J_m + e

Walk-forward 5-fold expanding OLS. Requested seed labels are not applicable to
this deterministic model, which is evaluated once per asset/horizon
(n_seeds_effective=1 per unit; the OLS fit has no stochastic seed input).
Kelly cap=1.0 (M11i confirmed cap=3.0 killed by Calmar).
Sign-test and DM-MSE compare HAR-RV-J with a symmetrically train-calibrated HAR.

Cluster protocol (7 assets, mirrors har_asymmetric.validate_sweep_contract /
cluster_verdict from the M16 seven-asset revalidation):
- The sweep is FAIL-CLOSED: all 7 assets x 3 horizons must evaluate, otherwise
  the run exits non-zero with a per-unit failure report and NO verdict.
- Primary aggregation is COIN-LEVEL (n=7): per-asset horizon collapse
  (BEATS when a strict majority of horizons BEATS), then an exact one-sided
  binomial sign-test across coins.
- The 21 coin x horizon configurations are DESCRIPTIVE ONLY: horizons within
  a coin are dependent and never counted as independent evidence.

Output
------
- results/m12_har_rv_j/m12_har_rv_j_results.csv
- results/m12_har_rv_j/results.json
- docs/M12_HAR_RV_J.md (verdict)

Env: conda coursia-ml-training. Reuses har_model, realized_variance, m11g infra.
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

from dm_test import dm_verdict  # noqa: E402
from har_model import walk_forward_har  # noqa: E402
from m11g_fee_aware_kelly import (  # noqa: E402
    _kelly_weights_and_returns,
    _load_one_coin,
    _net_at_fee,
)
from m11c_sharpe_test import ledoit_wolf_sharpe_diff_se  # noqa: E402
from realized_variance import (  # noqa: E402
    daily_bipower_variation,
    daily_realized_variance,
    har_lag_features,
    realized_variance_to_log,
)

CLUSTER_ASSETS = (
    "BTC-USD", "ETH-USD", "SOL-USD", "LTC-USD", "XRP-USD", "ADA-USD", "DOT-USD",
)
COINS = list(CLUSTER_ASSETS)
HORIZONS = [1, 5, 10]
SEEDS = [0, 7, 42, 99]
# Determinism attestation: the OLS path (np.linalg.lstsq fit + iterated
# walk-forward) has NO stochastic input, so each asset x horizon unit is a
# single effective observation (n_seeds_effective=1). The four requested seed
# labels are recorded as non-applicable controls, never as 84 independent
# units — bit-identity is pinned by test_m12_har_rv_j.py
# (TestDeterminismAttestation). Mirrors har_asymmetric.py (M16 contract).
SEED_ROLE = (
    "OLS déterministe : aucun seed stochastique ; les labels demandés sont "
    "enregistrés comme contrôles non applicables (n_seeds_effective=1 par unité)"
)


class UnitEvaluationError(RuntimeError):
    """A requested asset x horizon unit could not be evaluated (fail-closed).

    Raised (never silently skipped) when a requested unit cannot produce a
    DM-MSE verdict — mirrors the M16 fail-closed sweep contract: the caller
    must report the (coin, horizon, reason) triple and emit NO cluster verdict.
    """


MU_HUANG_TAUCHEN = 0.6  # Huang-Tauchen threshold for jump detection
KELLY_CAP = 1.0
MU_WINDOW = 60
FEE_BPS = 50
N_SPLITS = 5
REFIT_EVERY = 22
# Explicit, identical train-only calibration window for BOTH the calibrated
# HAR baseline and the HAR-RV-J candidate (symmetric protocol).
CALIBRATION_SIZE = 60
RESULTS_DIR = SCRIPT_DIR / "results" / "m12_har_rv_j"


# ── Jump decomposition ──────────────────────────────────────────────────────

def daily_jump_component(
    intraday_log_returns: pd.Series,
    mu: float = MU_HUANG_TAUCHEN,
    min_obs_per_day: int = 6,
) -> pd.Series:
    """Compute daily jump component J_t = max(RV_t - mu*BPV_t, 0).

    Andersen, Bollerslev, Diebold (2007) "Roughing It Up".
    """
    rv = daily_realized_variance(intraday_log_returns, min_obs_per_day=min_obs_per_day)
    bpv = daily_bipower_variation(intraday_log_returns, min_obs_per_day=min_obs_per_day)
    aligned = pd.concat(
        [rv.rename("rv"), bpv.rename("bpv")], axis=1
    ).dropna()
    jumps = np.maximum(aligned["rv"] - mu * aligned["bpv"], 0.0)
    jumps.index.name = "date"
    jumps.name = "J"
    return jumps


def har_rv_j_lag_features(
    rv: pd.Series,
    jumps: pd.Series,
) -> pd.DataFrame:
    """Build HAR-RV-J features: RV d/w/m + Jump d/w/m = 6 regressors.

    Columns: rv_d, rv_w, rv_m (log scale), j_d, j_w, j_m (raw level).
    Jumps are on the raw scale (not log) since they can be zero.
    """
    log_rv_feats = har_lag_features(rv).apply(realized_variance_to_log)
    j_d = jumps.shift(1)
    j_w = jumps.shift(1).rolling(window=5, min_periods=5).mean()
    j_m = jumps.shift(1).rolling(window=22, min_periods=22).mean()
    return pd.DataFrame({
        "rv_d": log_rv_feats["rv_d"],
        "rv_w": log_rv_feats["rv_w"],
        "rv_m": log_rv_feats["rv_m"],
        "j_d": j_d,
        "j_w": j_w,
        "j_m": j_m,
    })


# ── HAR-RV-J model ──────────────────────────────────────────────────────────

class HARRVJModel:
    """OLS HAR-RV-J(1d, 5d, 22d, J_d, J_w, J_m) regression on log-RV."""

    def __init__(self) -> None:
        self.coef_: np.ndarray | None = None
        self.n_train_: int = 0

    def fit(self, rv_train: pd.Series, jumps_train: pd.Series) -> "HARRVJModel":
        feats = har_rv_j_lag_features(rv_train, jumps_train)
        target = realized_variance_to_log(rv_train).rename("y")
        df = pd.concat([feats, target], axis=1).dropna()
        if len(df) < 30:
            raise ValueError(f"HAR-RV-J fit needs >=30 obs, got {len(df)}")
        x = df[["rv_d", "rv_w", "rv_m", "j_d", "j_w", "j_m"]].to_numpy()
        y = df["y"].to_numpy()
        x_aug = np.column_stack([np.ones(len(x)), x])
        coef, *_ = np.linalg.lstsq(x_aug, y, rcond=None)
        self.coef_ = coef
        self.n_train_ = len(df)
        return self

    def predict_h_step(
        self, rv_history: pd.Series, jumps_history: pd.Series, horizon: int
    ) -> float:
        """Iterated h-step forecast on the log-RV scale."""
        if horizon < 1:
            raise ValueError("horizon must be >= 1")
        rv_vals = list(rv_history.astype(float).values)
        j_vals = list(jumps_history.astype(float).values)
        forecasts: list[float] = []
        for _ in range(horizon):
            tail_rv = pd.Series(rv_vals[-22:])
            tail_j = pd.Series(j_vals[-22:])
            log_rv = np.log(tail_rv.clip(lower=1e-12))
            rv_d = float(log_rv.iloc[-1])
            rv_w = float(log_rv.iloc[-5:].mean())
            rv_m = float(log_rv.iloc[-22:].mean())
            j_d = float(tail_j.iloc[-1])
            j_w = float(tail_j.iloc[-5:].mean())
            j_m = float(tail_j.iloc[-22:].mean())
            x_aug = np.array([1.0, rv_d, rv_w, rv_m, j_d, j_w, j_m])
            log_pred = float(x_aug @ self.coef_)
            forecasts.append(log_pred)
            rv_vals.append(float(np.exp(log_pred)))
            # Jumps not forecastable: set next jump to 0 (expected value under null)
            j_vals.append(0.0)
        return float(np.mean(forecasts))


def _fit_har_rv_j_with_train_calibration(
    rv_train: pd.Series,
    jumps_train: pd.Series,
    horizon: int,
    calibration_size: int,
) -> tuple[HARRVJModel, float]:
    """Fit before a train-tail holdout and estimate a signed forecast offset."""
    calibration_size = min(calibration_size, max(0, len(rv_train) - 60))
    if calibration_size < max(10, horizon + 1):
        return HARRVJModel().fit(rv_train, jumps_train), 0.0

    fit_end = len(rv_train) - calibration_size
    model = HARRVJModel().fit(
        rv_train.iloc[:fit_end], jumps_train.iloc[:fit_end]
    )
    log_rv = np.log(rv_train.clip(lower=1e-12))
    errors: list[float] = []
    for i in range(fit_end, len(rv_train) - horizon):
        prediction = model.predict_h_step(
            rv_train.iloc[:i], jumps_train.iloc[:i], horizon=horizon
        )
        target = float(log_rv.iloc[i:i + horizon].mean())
        errors.append(prediction - target)

    bias = float(np.mean(errors)) if errors else 0.0
    return model, bias


def walk_forward_har_rv_j(
    rv: pd.Series,
    jumps: pd.Series,
    horizon: int = 1,
    n_splits: int = 5,
    refit_every: int = 22,
    calibrate_bias: bool = False,
    calibration_size: int = 60,
) -> dict:
    """Walk-forward evaluation of HAR-RV-J.

    Returns aligned forecast series for downstream comparison with HAR Classic.
    """
    rv = rv.dropna().astype(float)
    jumps = jumps.dropna().astype(float)
    # Align RV and jumps
    common_idx = rv.index.intersection(jumps.index)
    rv = rv.loc[common_idx]
    jumps = jumps.loc[common_idx]
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
    initial_calibration_bias_by_fold: list[float] = []

    for fold_idx, (train_end, test_start, test_end) in enumerate(splits):
        rv_train = rv.iloc[:train_end]
        j_train = jumps.iloc[:train_end]
        if len(rv_train) < 60:
            continue
        if calibrate_bias:
            model, bias = _fit_har_rv_j_with_train_calibration(
                rv_train,
                j_train,
                horizon=horizon,
                calibration_size=calibration_size,
            )
        else:
            model = HARRVJModel().fit(rv_train, j_train)
            bias = 0.0
        initial_calibration_bias_by_fold.append(bias)
        fold_preds: list[float] = []
        fold_truths: list[float] = []
        history_rv = list(rv.iloc[:test_start].values)
        history_j = list(jumps.iloc[:test_start].values)
        for i in range(test_start, test_end - horizon):
            target_window = log_rv.iloc[i : i + horizon].mean()
            tail_rv = pd.Series(history_rv[-(22 + horizon) :])
            tail_j = pd.Series(history_j[-(22 + horizon) :])
            log_pred = (
                model.predict_h_step(tail_rv, tail_j, horizon=horizon) - bias
            )
            fold_preds.append(log_pred)
            fold_truths.append(float(target_window))
            preds.append(log_pred)
            truths.append(float(target_window))
            pred_dates.append(rv.index[i])
            history_rv.append(float(rv.iloc[i]))
            history_j.append(float(jumps.iloc[i]))
            if (i - test_start) % refit_every == 0 and i > test_start:
                if calibrate_bias:
                    model, bias = _fit_har_rv_j_with_train_calibration(
                        rv.iloc[:i],
                        jumps.iloc[:i],
                        horizon=horizon,
                        calibration_size=calibration_size,
                    )
                else:
                    model = HARRVJModel().fit(rv.iloc[:i], jumps.iloc[:i])
                    bias = 0.0
        fp = np.asarray(fold_preds)
        ft = np.asarray(fold_truths)
        fold_mse = float(np.mean((fp - ft) ** 2)) if len(fp) else float("nan")
        fold_results.append({
            "fold": fold_idx,
            "n_test": len(fp),
            "mse_logrv": fold_mse,
            # Parity with har_model fold proofs: signed mean residual per fold
            # (must be finite — validated by the sweep contract).
            "mean_resid": float(np.mean(fp - ft)) if len(fp) else float("nan"),
        })

    preds_arr = np.asarray(preds)
    truths_arr = np.asarray(truths)
    aggregate_mse = (
        float(np.mean((preds_arr - truths_arr) ** 2)) if len(preds_arr) else float("nan")
    )
    forecasts = pd.Series(
        preds_arr, index=pd.DatetimeIndex(pred_dates), name="har_rv_j_logrv_pred"
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
        "calibrate_bias": calibrate_bias,
        "calibration_size": calibration_size,
        "initial_calibration_bias_by_fold": initial_calibration_bias_by_fold,
        "forecasts": forecasts,
        "targets": targets,
    }


# ── Evaluation helpers ───────────────────────────────────────────────────────

def _sharpe_ann(returns: np.ndarray) -> float:
    if len(returns) < 10:
        return float("nan")
    mu = float(np.mean(returns))
    sigma = float(np.std(returns, ddof=1))
    return (mu / sigma) * np.sqrt(365) if sigma > 1e-12 else float("nan")


def _fold_summaries(fold_results: list[dict]) -> list[dict]:
    """Compact per-fold proofs for the aggregated artifact: fold id, test
    count, fold MSE and signed mean residual (both must be finite — validated
    by the sweep contract, har_model precedent for ``mean_resid``). Persisted
    for the raw HAR, the calibrated HAR baseline AND the HAR-RV-J candidate
    so the 5-folds-per-config acceptance is falsifiable from results.json."""
    return [
        {
            "fold": int(fr["fold"]),
            "n_test": int(fr["n_test"]),
            "mse_logrv": float(fr["mse_logrv"]),
            "mean_resid": float(fr["mean_resid"]),
        }
        for fr in fold_results
    ]


def evaluate_one_combo(
    coin: str,
    horizon: int,
    seed: int,
    oos_strict_year: int | None = None,
) -> dict:
    """Run HAR-RV-J vs HAR Classic for one asset/horizon unit (fail-closed).

    ``seed`` is retained for CLI compatibility and output provenance but does
    not affect the deterministic OLS fit. If ``oos_strict_year`` is provided,
    all data on/after January 1 of that year is excluded from training and
    walk-forward evaluation for a separate external OOS verdict.

    Raises ``UnitEvaluationError`` with the (coin, horizon, reason) triple on
    every insufficiency path — a requested unit NEVER silently returns None
    (M16 fail-closed sweep contract: the caller reports the failure and emits
    no cluster verdict).
    """
    # OLS is deterministic; the seed label is recorded but not consumed.
    try:
        hourly_rets = _load_one_coin(coin)
    except Exception as exc:
        # Loader failures (missing file, empty yfinance download...) are unit
        # failures too: they must reach the failure manifest, not bypass it.
        raise UnitEvaluationError(
            f"{coin}/h={horizon}: data loader failed "
            f"({type(exc).__name__}: {exc})"
        ) from exc
    if oos_strict_year is not None:
        cutoff = pd.Timestamp(f"{oos_strict_year}-01-01", tz=hourly_rets.index.tz)
        hourly_rets = hourly_rets[hourly_rets.index < cutoff]
    if len(hourly_rets) < 1000:
        raise UnitEvaluationError(
            f"{coin}/h={horizon}: hourly series too short "
            f"({len(hourly_rets)} obs < 1000)"
        )

    rv = daily_realized_variance(hourly_rets)
    jumps = daily_jump_component(hourly_rets)
    if len(rv) < 300 or len(jumps) < 300:
        raise UnitEvaluationError(
            f"{coin}/h={horizon}: daily RV/jump series too short "
            f"(rv={len(rv)}, jumps={len(jumps)}; need >= 300 each)"
        )

    # Align
    common_idx = rv.index.intersection(jumps.index)
    rv = rv.loc[common_idx]
    jumps = jumps.loc[common_idx]

    # HAR Classic baseline, raw and calibrated on train-only residuals.
    # CALIBRATION_SIZE is passed explicitly to BOTH calibrated runs so the
    # baseline and the candidate share an identical train-only protocol.
    try:
        har_out = walk_forward_har(
            rv,
            horizon=horizon,
            n_splits=N_SPLITS,
            refit_every=REFIT_EVERY,
        )
        har_debiased_out = walk_forward_har(
            rv,
            horizon=horizon,
            n_splits=N_SPLITS,
            refit_every=REFIT_EVERY,
            calibrate_bias=True,
            calibration_size=CALIBRATION_SIZE,
        )
    except Exception as exc:
        raise UnitEvaluationError(
            f"{coin}/h={horizon}: HAR walk-forward failed "
            f"({type(exc).__name__}: {exc})"
        ) from exc

    # HAR-RV-J candidate with the same train-only calibration protocol.
    try:
        hrj_out = walk_forward_har_rv_j(
            rv,
            jumps,
            horizon=horizon,
            n_splits=N_SPLITS,
            refit_every=REFIT_EVERY,
            calibrate_bias=True,
            calibration_size=CALIBRATION_SIZE,
        )
    except Exception as exc:
        raise UnitEvaluationError(
            f"{coin}/h={horizon}: HAR-RV-J walk-forward failed "
            f"({type(exc).__name__}: {exc})"
        ) from exc

    har_fc = har_out["forecasts"]
    har_debiased_fc = har_debiased_out["forecasts"]
    hrj_fc = hrj_out["forecasts"]
    common_fc_idx = har_fc.index.intersection(har_debiased_fc.index).intersection(hrj_fc.index)
    if len(common_fc_idx) < 30:
        raise UnitEvaluationError(
            f"{coin}/h={horizon}: too few common walk-forward forecasts "
            f"({len(common_fc_idx)} < 30) across HAR / HAR-debiased / HAR-RV-J"
        )
    har_fc = har_fc.loc[common_fc_idx]
    har_debiased_fc = har_debiased_fc.loc[common_fc_idx]
    hrj_fc = hrj_fc.loc[common_fc_idx]

    # Daily close returns
    daily_rets = hourly_rets.groupby(hourly_rets.index.normalize()).sum().rename("r_daily")
    daily_rets.index = pd.DatetimeIndex(daily_rets.index).normalize()
    daily_rets = daily_rets.reindex(common_fc_idx).dropna()
    if len(daily_rets) < 30:
        raise UnitEvaluationError(
            f"{coin}/h={horizon}: too few daily returns aligned with "
            f"forecasts ({len(daily_rets)} < 30)"
        )
    har_fc = har_fc.reindex(daily_rets.index)
    har_debiased_fc = har_debiased_fc.reindex(daily_rets.index)
    hrj_fc = hrj_fc.reindex(daily_rets.index)

    # Kelly weights for each model
    har_pair = _kelly_weights_and_returns(daily_rets, har_fc, MU_WINDOW, KELLY_CAP)
    har_debiased_pair = _kelly_weights_and_returns(
        daily_rets, har_debiased_fc, MU_WINDOW, KELLY_CAP
    )
    hrj_pair = _kelly_weights_and_returns(daily_rets, hrj_fc, MU_WINDOW, KELLY_CAP)
    if har_pair is None or har_debiased_pair is None or hrj_pair is None:
        missing = [
            name
            for name, pair in (
                ("HAR", har_pair),
                ("HAR-debiased", har_debiased_pair),
                ("HAR-RV-J", hrj_pair),
            )
            if pair is None
        ]
        raise UnitEvaluationError(
            f"{coin}/h={horizon}: insufficient overlap for Kelly weights "
            f"({', '.join(missing)} needs >= MU_WINDOW + 30 daily rows)"
        )
    har_w, r = har_pair
    har_debiased_w, _ = har_debiased_pair
    hrj_w, _ = hrj_pair
    if len(r) < 50:
        raise UnitEvaluationError(
            f"{coin}/h={horizon}: too few Kelly-scaled evaluation periods "
            f"({len(r)} < 50)"
        )

    # Net returns at FEE_BPS
    har_net = _net_at_fee(har_w, r, FEE_BPS)
    har_debiased_net = _net_at_fee(har_debiased_w, r, FEE_BPS)
    hrj_net = _net_at_fee(hrj_w, r, FEE_BPS)
    bh_net = r.copy()

    # Sharpe
    sharpe_har = _sharpe_ann(har_net)
    sharpe_har_debiased = _sharpe_ann(har_debiased_net)
    sharpe_hrj = _sharpe_ann(hrj_net)
    sharpe_bh = _sharpe_ann(bh_net)
    delta_sharpe_hrj_vs_har = sharpe_hrj - sharpe_har
    delta_sharpe_hrj_vs_har_debiased = sharpe_hrj - sharpe_har_debiased

    # LW2008 paired Sharpe-diff SE against the debiased baseline.
    _, _, _, se = ledoit_wolf_sharpe_diff_se(hrj_net, har_debiased_net)
    t_stat = (
        delta_sharpe_hrj_vs_har_debiased / se
        if isinstance(se, float) and se > 1e-12
        else float("nan")
    )

    # Precision comparison on log-RV against the train-calibrated HAR baseline.
    target = har_out["targets"].reindex(common_fc_idx).dropna()
    har_pred_aligned = har_fc.reindex(target.index)
    har_debiased_pred_aligned = har_debiased_fc.reindex(target.index)
    hrj_pred_aligned = hrj_fc.reindex(target.index)
    har_errors = (har_pred_aligned - target).to_numpy(dtype=float)
    har_debiased_errors = (har_debiased_pred_aligned - target).to_numpy(dtype=float)
    hrj_errors = (hrj_pred_aligned - target).to_numpy(dtype=float)
    mse_har = float(np.mean(har_errors ** 2))
    mse_har_debiased = float(np.mean(har_debiased_errors ** 2))
    mse_hrj = float(np.mean(hrj_errors ** 2))
    mse_reduction_pct = (
        (mse_har_debiased - mse_hrj) / mse_har_debiased * 100
        if mse_har_debiased > 0
        else float("nan")
    )
    dm_mse = dm_verdict(
        hrj_errors,
        har_debiased_errors,
        horizon=horizon,
        loss_fn="mse",
    )

    return {
        "coin": coin,
        "horizon": horizon,
        "seed": seed,
        "n_folds_har": len(har_out["fold_results"]),
        "n_folds_har_debiased": len(har_debiased_out["fold_results"]),
        "n_folds_hrj": len(hrj_out["fold_results"]),
        "har_fold_summaries": _fold_summaries(har_out["fold_results"]),
        "har_debiased_fold_summaries": _fold_summaries(
            har_debiased_out["fold_results"]
        ),
        "hrj_fold_summaries": _fold_summaries(hrj_out["fold_results"]),
        # Data manifest fields (per unit; rolled up per coin by main()).
        "data_window_start": str(hourly_rets.index.min()),
        "data_window_end": str(hourly_rets.index.max()),
        "n_hourly_obs": int(len(hourly_rets)),
        "n_rv_days": int(len(rv)),
        # Canonical §C verdict carried by the unit (M16 contract): the DM-MSE
        # precision verdict of the existing evaluation, mapped to the
        # BEATS / NO BEATS / INCONCLUSIVE vocabulary used by cluster_verdict.
        "verdict": _canonical_dm_verdict(str(dm_mse["verdict"])),
        "sharpe_har": sharpe_har,
        "sharpe_har_debiased": sharpe_har_debiased,
        "sharpe_hrj": sharpe_hrj,
        "sharpe_bh": sharpe_bh,
        "delta_sharpe_hrj_vs_har": delta_sharpe_hrj_vs_har,
        "delta_sharpe_hrj_vs_har_debiased": delta_sharpe_hrj_vs_har_debiased,
        "lw_se": se,
        "t_stat": t_stat,
        "har_bias_oos": float(np.mean(har_errors)),
        "har_debiased_bias_oos": float(np.mean(har_debiased_errors)),
        "hrj_debiased_bias_oos": float(np.mean(hrj_errors)),
        "har_calibration_bias_mean": float(np.mean(
            har_debiased_out["initial_calibration_bias_by_fold"]
        )),
        "hrj_calibration_bias_mean": float(np.mean(
            hrj_out["initial_calibration_bias_by_fold"]
        )),
        "mse_har": mse_har,
        "mse_har_debiased": mse_har_debiased,
        "mse_hrj": mse_hrj,
        "mse_reduction_pct_vs_debiased_har": mse_reduction_pct,
        "dm_mse_stat": float(dm_mse["dm_statistic"]),
        "dm_mse_pvalue": float(dm_mse["p_value"]),
        "dm_mse_mean_loss_diff": float(dm_mse["mean_loss_diff"]),
        "dm_mse_verdict": str(dm_mse["verdict"]),
        "n_obs": len(r),
        "hrj_preds": len(hrj_fc),
        "har_preds": len(har_fc),
    }


# ── Cluster aggregation (M16 seven-asset contract, transposed verbatim) ─────
# Source: har_asymmetric.py:697-818 (validate_sweep_contract / cluster_verdict).

def _canonical_dm_verdict(dm_verdict_str: str) -> str:
    """Map dm_verdict strings to the canonical §C verdict vocabulary."""
    if dm_verdict_str == "BEATS baseline":
        return "BEATS"
    if dm_verdict_str == "BEATEN BY baseline":
        return "NO BEATS"
    return "INCONCLUSIVE"


def aggregate_unit_rows(combos: list[dict], seeds: list[int]) -> list[dict]:
    """Project sweep rows onto the M16 aggregate schema.

    Determinism attestation: each unit is ONE effective observation
    (``n_seeds_effective=1``, ``seed_stable=True``) because the OLS fit has no
    stochastic input; the four requested seed labels ride along as
    ``seed_values_requested`` controls and are NEVER counted as independent
    evidence (no 84-unit inflation).
    """
    return [
        {
            "coin": row["coin"],
            "horizon": row["horizon"],
            "n_seeds": len(seeds),
            "n_seeds_requested": len(seeds),
            "n_seeds_effective": 1,
            "seed_replication": "deterministic-ols",
            "seed_values_requested": seeds,
            "seed_stable": True,
            "verdict": row["verdict"],
            "dm_mse_pvalue": row["dm_mse_pvalue"],
            "dm_mse_stat": row["dm_mse_stat"],
            "dm_mse_mean_loss_diff": row["dm_mse_mean_loss_diff"],
            "delta_sharpe_hrj_vs_har_debiased": row[
                "delta_sharpe_hrj_vs_har_debiased"
            ],
            "mse_har": row["mse_har"],
            "mse_har_debiased": row["mse_har_debiased"],
            "mse_hrj": row["mse_hrj"],
            "mse_reduction_pct_vs_debiased_har": row[
                "mse_reduction_pct_vs_debiased_har"
            ],
            "har_bias_oos": row["har_bias_oos"],
            "har_debiased_bias_oos": row["har_debiased_bias_oos"],
            "hrj_debiased_bias_oos": row["hrj_debiased_bias_oos"],
            "n_folds_har": row["n_folds_har"],
            "n_folds_har_debiased": row["n_folds_har_debiased"],
            "n_folds_hrj": row["n_folds_hrj"],
            "har_fold_summaries": row["har_fold_summaries"],
            "har_debiased_fold_summaries": row["har_debiased_fold_summaries"],
            "hrj_fold_summaries": row["hrj_fold_summaries"],
            "data_window_start": row["data_window_start"],
            "data_window_end": row["data_window_end"],
            "n_hourly_obs": row["n_hourly_obs"],
            "n_rv_days": row["n_rv_days"],
        }
        for row in combos
    ]


def cluster_verdict(
    aggregated: list[dict],
    alpha: float = 0.05,
) -> dict:
    """Compute a coin-level sign test without duplicating OLS seed controls.

    Exact transposition of har_asymmetric.cluster_verdict: per-coin horizon
    collapse (BEATS when a strict majority of horizons BEATS, NO BEATS when at
    least one horizon NO BEATS, else INCONCLUSIVE), then an exact one-sided
    binomial sign-test across the coin verdicts (primary, n=7 for the default
    cluster). The coin x horizon configurations are descriptive only.
    """
    from collections import defaultdict
    from scipy.stats import binomtest

    if not aggregated:
        raise ValueError("cluster verdict needs at least one configuration")
    non_deterministic = [
        f"{row['coin']}/h={row['horizon']}"
        for row in aggregated
        if not row.get("seed_stable", False)
        or row.get("n_seeds_effective") != 1
    ]
    if non_deterministic:
        raise ValueError(
            "cluster verdict requires deterministic seed controls: "
            + ", ".join(non_deterministic)
        )

    by_coin: dict[str, list[dict]] = defaultdict(list)
    for row in aggregated:
        by_coin[row["coin"]].append(row)

    coin_verdicts = []
    for coin, rows in sorted(by_coin.items()):
        n_beats = sum(row["verdict"] == "BEATS" for row in rows)
        n_no_beats = sum(row["verdict"] == "NO BEATS" for row in rows)
        if n_beats > len(rows) / 2:
            verdict = "BEATS"
        elif n_no_beats > 0:
            verdict = "NO BEATS"
        else:
            verdict = "INCONCLUSIVE"
        coin_verdicts.append({
            "coin": coin,
            "n_horizons": len(rows),
            "n_beats": n_beats,
            "n_no_beats": n_no_beats,
            "verdict": verdict,
        })

    n_coins = len(coin_verdicts)
    n_coin_beats = sum(row["verdict"] == "BEATS" for row in coin_verdicts)
    p_value = float(binomtest(
        n_coin_beats,
        n_coins,
        p=0.5,
        alternative="greater",
    ).pvalue)
    if p_value < alpha:
        verdict = "BEATS"
    elif n_coin_beats > n_coins / 2:
        verdict = "INCONCLUSIVE"
    else:
        verdict = "NO BEATS"

    return {
        "verdict": verdict,
        "alpha": alpha,
        "primary_coin_level": {
            "n_effective": n_coins,
            "n_beats": n_coin_beats,
            "p_null": 0.5,
            "alternative": "greater",
            "p_value": p_value,
            "horizon_collapse": "BEATS si majorité stricte d'horizons BEATS ; NO BEATS si au moins un horizon NO BEATS",
            "coin_verdicts": coin_verdicts,
        },
        "config_level": {
            "n_effective": len(aggregated),
            "n_beats": sum(row["verdict"] == "BEATS" for row in aggregated),
            "role": "descriptive_only",
            "dependence_caveat": "les horizons d'un même actif sont dépendants",
        },
        "seed_role": (
            "contrôles OLS déterministes ; une seule observation effective "
            "par actif et horizon"
        ),
    }


def validate_sweep_contract(
    rows: list[dict],
    aggregated: list[dict],
    requested: list[str],
    horizons: list[int],
    seeds: list[int],
    n_splits: int,
) -> None:
    """Fail closed when a requested sweep is incomplete (M16 contract).

    Every requested (coin, horizon) couple must be present EXACTLY ONCE (no
    duplicate rows), each unit must carry the requested seed labels as
    non-applicable controls with ONE effective observation (determinism
    attestation), ALL THREE of raw HAR, calibrated HAR baseline and HAR-RV-J
    candidate must have produced exactly ``n_splits`` fold summaries with a
    positive test count, a finite fold MSE and a finite signed mean residual,
    and the key §C metrics must be finite.
    """
    expected_configs = {(coin, horizon) for coin in requested for horizon in horizons}
    actual_configs = {(row["coin"], row["horizon"]) for row in aggregated}
    if actual_configs != expected_configs:
        missing = sorted(expected_configs - actual_configs)
        raise ValueError(f"incomplete sweep configurations: {missing}")
    if len(aggregated) != len(expected_configs):
        # Set equality above passed but counts differ => duplicate rows.
        raise ValueError(
            f"duplicate sweep rows: {len(aggregated)} rows for "
            f"{len(expected_configs)} expected configurations"
        )

    def _finite(value: float) -> bool:
        return isinstance(value, (int, float)) and np.isfinite(value)

    for coin, horizon in sorted(expected_configs):
        config_rows = [
            row for row in rows
            if row.get("coin") == coin and row.get("horizon") == horizon
        ]
        if not config_rows:
            raise ValueError(f"{coin}/h={horizon}: no evaluation rows")
        seed_controls_ok = all(
            row.get("seed_stable") is True
            and row.get("n_seeds_effective") == 1
            and row.get("seed_values_requested") == list(seeds)
            for row in config_rows
        )
        if not seed_controls_ok:
            raise ValueError(
                f"{coin}/h={horizon}: seed control attestation broken "
                "(expected deterministic-ols, n_seeds_effective=1, "
                f"labels {list(seeds)})"
            )
        for row in config_rows:
            if not (
                row.get("n_folds_har") == n_splits
                and row.get("n_folds_har_debiased") == n_splits
                and row.get("n_folds_hrj") == n_splits
            ):
                raise ValueError(
                    f"{coin}/h={horizon} did not produce {n_splits} folds "
                    "for both model and baseline"
                )
            for side, key in (
                ("raw HAR baseline", "har_fold_summaries"),
                ("calibrated HAR baseline", "har_debiased_fold_summaries"),
                ("HAR-RV-J candidate", "hrj_fold_summaries"),
            ):
                summaries = row.get(key, [])
                if len(summaries) != n_splits:
                    raise ValueError(
                        f"{coin}/h={horizon}: {side} has {len(summaries)} "
                        f"fold summaries, expected {n_splits}"
                    )
                for summary in summaries:
                    if int(summary["n_test"]) <= 0:
                        raise ValueError(
                            f"{coin}/h={horizon}: {side} fold "
                            f"{summary['fold']} has n_test={summary['n_test']}"
                        )
                    if not _finite(summary["mse_logrv"]):
                        raise ValueError(
                            f"{coin}/h={horizon}: {side} fold "
                            f"{summary['fold']} has non-finite MSE"
                        )
                    if not _finite(summary["mean_resid"]):
                        raise ValueError(
                            f"{coin}/h={horizon}: {side} fold "
                            f"{summary['fold']} has non-finite mean_resid"
                        )
            if not (
                _finite(row.get("dm_mse_pvalue"))
                and 0.0 <= row["dm_mse_pvalue"] <= 1.0
                and _finite(row.get("dm_mse_stat"))
                and _finite(row.get("dm_mse_mean_loss_diff"))
                and _finite(row.get("delta_sharpe_hrj_vs_har_debiased"))
                and _finite(row.get("mse_har"))
                and row["mse_har"] > 0
                and _finite(row.get("mse_har_debiased"))
                and row["mse_har_debiased"] > 0
                and _finite(row.get("mse_hrj"))
                and row["mse_hrj"] > 0
                and _finite(row.get("har_bias_oos"))
                and _finite(row.get("har_debiased_bias_oos"))
                and _finite(row.get("hrj_debiased_bias_oos"))
            ):
                raise ValueError(
                    f"{coin}/h={horizon}: non-finite key §C metrics "
                    "(DM stat/p/loss-diff, delta-Sharpe, MSEs, signed biases)"
                )


def _build_data_manifest(
    coins: list[str],
    horizons: list[int],
    combos: list[dict],
    failures: list[dict],
    oos_strict_year: int | None,
) -> dict:
    """Requested / loaded / missing data manifest for the aggregated artifact.

    Per coin: load status, unit counts, and (when loaded) the hourly data
    window plus the number of daily RV observations actually evaluated —
    the falsifiable record of WHAT the sweep ran on. The OOS holdout year,
    when requested, is recorded alongside.
    """
    per_coin: dict[str, dict] = {}
    for coin in coins:
        coin_rows = [row for row in combos if row.get("coin") == coin]
        coin_failures = [f for f in failures if f.get("coin") == coin]
        loaded = bool(coin_rows)
        per_coin[coin] = {
            "status": "loaded" if loaded else "missing_or_failed",
            "n_units_ok": len(coin_rows),
            "n_units_failed": len(coin_failures),
            "data_window_start": (
                min(r["data_window_start"] for r in coin_rows) if loaded else None
            ),
            "data_window_end": (
                max(r["data_window_end"] for r in coin_rows) if loaded else None
            ),
            "n_hourly_obs": (
                max(r["n_hourly_obs"] for r in coin_rows) if loaded else None
            ),
            "n_rv_days": coin_rows[0]["n_rv_days"] if loaded else None,
        }
    return {
        "coins_requested": list(coins),
        "horizons_requested": list(horizons),
        "coins_loaded": [c for c in coins if per_coin[c]["status"] == "loaded"],
        "coins_missing_or_failed": [
            c for c in coins if per_coin[c]["status"] != "loaded"
        ],
        "oos_strict_year": oos_strict_year,
        "per_coin": per_coin,
    }


def _csv_list(value: str) -> list[str]:
    return [s.strip() for s in value.split(",") if s.strip()]


def _csv_int_list(value: str) -> list[int]:
    return [int(s.strip()) for s in value.split(",") if s.strip()]


def main() -> None:
    parser = argparse.ArgumentParser(description="M12 HAR-RV-J sweep")
    parser.add_argument("--dry-run", action="store_true", help="Run BTC h=1 seed=0 only")
    parser.add_argument(
        "--seeds",
        type=_csv_int_list,
        default=None,
        help="Comma-separated seed labels override (default: 0,7,42,99; N/A to OLS)",
    )
    parser.add_argument(
        "--coins",
        type=_csv_list,
        default=None,
        help=(
            "Comma-separated coins override (default: the 7-asset cluster "
            "BTC,ETH,SOL,LTC,XRP,ADA,DOT -USD)"
        ),
    )
    parser.add_argument(
        "--horizons",
        type=_csv_int_list,
        default=None,
        help="Comma-separated horizons override (default: 1,5,10)",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=None,
        help="Override results directory (default: results/m12_har_rv_j/)",
    )
    parser.add_argument(
        "--oos-strict",
        type=int,
        default=None,
        metavar="YEAR",
        help=(
            "Hold out all data >= Jan 1st of YEAR from training/walk-forward "
            "(for separate OOS verdict). Example: --oos-strict 2027"
        ),
    )
    args = parser.parse_args()

    coins = args.coins if args.coins is not None else COINS
    horizons = args.horizons if args.horizons is not None else HORIZONS
    seeds = args.seeds if args.seeds is not None else SEEDS
    results_dir = args.output if args.output is not None else RESULTS_DIR
    oos_strict_year = args.oos_strict

    results_dir.mkdir(parents=True, exist_ok=True)
    t0 = time.time()

    combos: list[dict] = []
    total_effective = len(coins) * len(horizons)
    done = 0

    if args.dry_run:
        print("[DRY RUN] BTC-USD h=1 seed=0 only")
        try:
            row = evaluate_one_combo("BTC-USD", 1, 0, oos_strict_year=oos_strict_year)
        except UnitEvaluationError as exc:
            print(f"[DRY RUN] UNIT FAILURE: {exc}", flush=True)
            sys.exit(1)
        combos.append(row)
        print(json.dumps(row, indent=2))
        return

    if oos_strict_year is not None:
        print(f"[OOS-STRICT] Holding out data >= {oos_strict_year}-01-01")

    failures: list[dict] = []
    for coin in coins:
        for h in horizons:
            if not seeds:
                continue
            print(
                f"\n[{done + 1}/{total_effective}] {coin} h={h} "
                f"seed={seeds[0]} (deterministic OLS evaluation)",
                flush=True,
            )
            try:
                row = evaluate_one_combo(
                    coin,
                    h,
                    seeds[0],
                    oos_strict_year=oos_strict_year,
                )
            except UnitEvaluationError as exc:
                # Fail-closed: record the reason and keep sweeping so the
                # failure report enumerates EVERY failing unit in one pass.
                failures.append({
                    "coin": coin,
                    "horizon": h,
                    "reason": str(exc),
                })
                print(f"  UNIT FAILURE: {exc}", flush=True)
                done += 1
                continue
            done += 1

            combos.append({
                **row,
                "seed_values_requested": seeds,
                "seed_applicability": "not_applicable_deterministic_ols",
            })
            print(
                f"  OLS has no stochastic seed input; requested labels {seeds} "
                "are recorded as non-applicable",
                flush=True,
            )

    elapsed = time.time() - t0
    print(f"\n{'='*60}")
    print(
        f"M12 HAR-RV-J sweep finished: {len(combos)}/{total_effective} units "
        f"evaluated, {len(failures)} failed, in {elapsed:.0f}s"
    )

    common_config = {
        "model": "HAR-RV-J",
        "reference": "Andersen, Bollerslev, Diebold (2007)",
        "kelly_cap": KELLY_CAP,
        "fee_bps": FEE_BPS,
        "mu_window": MU_WINDOW,
        "n_splits": N_SPLITS,
        "refit_every": REFIT_EVERY,
        "calibration_size": CALIBRATION_SIZE,
        "mu_huang_tauchen": MU_HUANG_TAUCHEN,
        "baseline": "HAR Classic avec calibration de biais train-only",
        "candidate": "HAR-RV-J avec calibration de biais train-only",
        "dm_loss_fn": "mse",
    }
    data_manifest = _build_data_manifest(
        coins, horizons, combos, failures, oos_strict_year
    )

    if failures:
        # FAIL-CLOSED (M16 contract): an incomplete sweep emits NO verdict.
        print(
            f"\nFAIL-CLOSED: {len(failures)}/{total_effective} units failed — "
            "no cluster verdict is emitted."
        )
        for failure in failures:
            print(f"  {failure['coin']}/h={failure['horizon']}: {failure['reason']}")
        results = {
            **common_config,
            "status": "fail-closed",
            "n_failures": len(failures),
            "failures": failures,
            "data_manifest": data_manifest,
            "combos": combos,
            "elapsed_s": elapsed,
        }
        with open(results_dir / "results.json", "w") as f:
            json.dump(results, f, indent=2, default=str)
        if combos:
            df = pd.DataFrame(combos)
            df.to_csv(results_dir / "m12_har_rv_j_results.csv", index=False)
        sys.exit(1)

    # Complete sweep: enforce the contract, then aggregate (M16 transposition).
    aggregated = aggregate_unit_rows(combos, seeds)
    try:
        validate_sweep_contract(
            rows=aggregated,
            aggregated=aggregated,
            requested=coins,
            horizons=horizons,
            seeds=seeds,
            n_splits=N_SPLITS,
        )
    except ValueError as exc:
        print(f"\nFAIL-CLOSED: sweep contract violated: {exc}")
        results = {
            **common_config,
            "status": "fail-closed",
            "n_failures": 0,
            "contract_violation": str(exc),
            "data_manifest": data_manifest,
            "combos": combos,
            "elapsed_s": elapsed,
        }
        with open(results_dir / "results.json", "w") as f:
            json.dump(results, f, indent=2, default=str)
        sys.exit(1)

    cluster = cluster_verdict(aggregated)

    # OLS has no stochastic seed input: each row is one effective unit, while
    # seed_values_requested preserves the non-applicable protocol labels.
    n_combos = len(combos)
    unique_rows = combos
    n_effective = len(unique_rows)
    n_hrj_beats_har = sum(
        1
        for row in unique_rows
        if row["delta_sharpe_hrj_vs_har_debiased"] > 0
    )
    median_delta = (
        float(np.median([
            row["delta_sharpe_hrj_vs_har_debiased"]
            for row in unique_rows
        ]))
        if unique_rows
        else float("nan")
    )

    # Per-horizon descriptive statistics (config level — NOT the verdict
    # carrier: horizons within a coin are dependent, see cluster_verdict).
    per_horizon: dict[int, dict] = {}
    for horizon in horizons:
        rows = [row for row in unique_rows if row["horizon"] == horizon]
        if not rows:
            continue
        edges = np.asarray([
            row["delta_sharpe_hrj_vs_har_debiased"] for row in rows
        ], dtype=float)
        dm_ps = np.asarray(
            [row["dm_mse_pvalue"] for row in rows], dtype=float
        )
        dm_diffs = np.asarray([
            row["dm_mse_mean_loss_diff"] for row in rows
        ], dtype=float)
        edge_mean = float(np.mean(edges))
        edge_std = float(np.std(edges, ddof=0))
        per_horizon[horizon] = {
            "role": "descriptive_only",
            "n_effective": len(rows),
            "seed_values_requested": seeds,
            "seeds_applicable": False,
            "n_beats_dm_mse": sum(row["verdict"] == "BEATS" for row in rows),
            "n_no_beats_dm_mse": sum(row["verdict"] == "NO BEATS" for row in rows),
            "edge_mean_delta_sharpe": edge_mean,
            "edge_std_delta_sharpe_across_assets": edge_std,
            "cross_asset_edge_ratio": edge_mean / edge_std if edge_std > 0 else None,
            "dm_mse_p_median": float(np.median(dm_ps)),
            "dm_mse_mean_loss_diff_median": float(np.median(dm_diffs)),
            "har_bias_oos_mean": float(np.mean([
                row["har_bias_oos"] for row in rows
            ])),
            "har_debiased_bias_oos_mean": float(np.mean([
                row["har_debiased_bias_oos"] for row in rows
            ])),
            "hrj_debiased_bias_oos_mean": float(np.mean([
                row["hrj_debiased_bias_oos"] for row in rows
            ])),
        }

    # Per-coin descriptive aggregation (signed bias + MSE reduction medians).
    per_coin: dict[str, dict] = {}
    for r in unique_rows:
        c = r["coin"]
        per_coin.setdefault(c, {"deltas": [], "mses": []})
        per_coin[c]["deltas"].append(
            r["delta_sharpe_hrj_vs_har_debiased"]
        )
        per_coin[c]["mses"].append(
            r["mse_reduction_pct_vs_debiased_har"]
        )

    print(
        f"\nCoin-level sign-test (PRIMARY, n="
        f"{cluster['primary_coin_level']['n_effective']}): "
        f"{cluster['primary_coin_level']['n_beats']} coins BEATS / "
        f"{cluster['primary_coin_level']['n_effective']}"
    )
    print(f"  exact one-sided binomial p = {cluster['primary_coin_level']['p_value']:.6f}")
    for coin_row in cluster["primary_coin_level"]["coin_verdicts"]:
        print(
            f"  {coin_row['coin']}: {coin_row['verdict']} "
            f"(horizons BEATS {coin_row['n_beats']}/{coin_row['n_horizons']}, "
            f"NO BEATS {coin_row['n_no_beats']})"
        )
    print(
        f"Config level (DESCRIPTIVE ONLY, n={cluster['config_level']['n_effective']}): "
        f"{cluster['config_level']['n_beats']} BEATS — "
        f"{cluster['config_level']['dependence_caveat']}"
    )
    print(f"  median delta-Sharpe (descriptive) = {median_delta:+.4f}")
    print("\nPer-horizon descriptive statistics:")
    for horizon, row in per_horizon.items():
        ratio = row["cross_asset_edge_ratio"]
        ratio_text = f"{ratio:.2f}" if ratio is not None else "N/A"
        print(
            f"  h={horizon}: DM-MSE BEATS {row['n_beats_dm_mse']}/{row['n_effective']}, "
            f"NO BEATS {row['n_no_beats_dm_mse']} | "
            f"edge={row['edge_mean_delta_sharpe']:+.4f} "
            f"(cross-asset ratio={ratio_text}, seeds N/A for OLS), "
            f"DM-MSE p_med={row['dm_mse_p_median']:.4f}, "
            f"loss_diff={row['dm_mse_mean_loss_diff_median']:+.6f}"
        )

    print(f"\nVERDICT (cluster, coin-level primary): {cluster['verdict']}")

    # Save
    results = {
        **common_config,
        "status": "complete",
        "data_manifest": data_manifest,
        "sweep_contract": {
            "expected_configs": [
                {"coin": c, "horizon": h} for c in coins for h in horizons
            ],
            "n_expected": len(coins) * len(horizons),
            "validated": True,
        },
        "n_combos": n_combos,
        "n_effective": n_effective,
        "seed_labels_requested": seeds,
        "n_seed_labels_requested": len(seeds),
        "seed_labels_counted_as_observations": 0,
        "n_hrj_beats_har_delta_sharpe": n_hrj_beats_har,
        "win_rate_delta_sharpe_descriptive": n_hrj_beats_har / max(n_effective, 1),
        "seed_role": SEED_ROLE,
        "median_delta_sharpe": median_delta,
        "cluster": cluster,
        "verdict": cluster["verdict"],
        "per_horizon": per_horizon,
        "elapsed_s": elapsed,
        "combos": combos,
        "failures": [],
        "per_coin": {
            c: {
                "median_delta_sharpe": float(np.median(v["deltas"])),
                "median_mse_reduction": float(np.median(v["mses"])),
                "n_beats": sum(1 for d in v["deltas"] if d > 0),
                "n_total": len(v["deltas"]),
            }
            for c, v in per_coin.items()
        },
    }

    with open(results_dir / "results.json", "w") as f:
        json.dump(results, f, indent=2, default=str)

    # CSV
    if combos:
        df = pd.DataFrame(combos)
        df.to_csv(results_dir / "m12_har_rv_j_results.csv", index=False)
        print(f"\nSaved: {results_dir / 'results.json'}")
        print(f"Saved: {results_dir / 'm12_har_rv_j_results.csv'}")


if __name__ == "__main__":
    main()
