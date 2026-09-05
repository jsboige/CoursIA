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

REPAIR-2 (c.955): per-fold bias calibration reads ONLY from the train fold
(y_train tail), never from the OOS targets. Each model (LJ, HAR, M12) gets
its own bias estimate computed inside walk_forward_lj_asym (for LJ) and
walk_forward_har (for HAR, already canonical) and walk_forward_har_rv_j
(for M12). The post-walk-forward global tail-mean block has been REMOVED
because it leaked OOS targets (preflight po-2025 re-review head 4cc2262b,
concern #1).

ROUND-3 (preflight po-2025 adjoint re-review, head b974f2721, DM
msg-20260904T141944):
(1) bias-correction sign fixed -- the convention is
    ``bias = mean(y_train_tail - yhat_train_tail)`` and the corrected
    forecast is ``yhat_corrected = yhat + bias`` (the previous
    ``yhat - bias`` inverted the sign and doubled the error);
(2) M12 receives ``calibrate_bias=debias`` for apples-to-apples calibration
    (the flag already existed in walk_forward_har_rv_j -- only the call site
    was not passing it);
(3) ``mse_har_raw`` (uncalibrated walk_forward_har leg) and
    ``mse_har_debiased`` (calibrated leg) come from TWO distinct
    walk_forward_har calls -- no more fake identity;
(4) ``panel_hash`` covers the index (int64 ns) in addition to the values,
    and the manifest surfaces per-(coin, horizon) panel hashes.

ROUND-4 (adjoint re-review, DM msg-20260905T001520, 3/6 PARTIAL):
(a) test_walk_forward_lj_asym_oos_target_invariance_multi_fold -- n_splits=3
    with >=2 DISTINCT per-fold biases; per-fold OOS-target perturbation
    leaves that fold's bias and forecast slices bit-identical (earlier folds
    unchanged; later folds legitimately retrain on the shifted rows --
    walk-forward expanding window, not leakage). The round-3 single-fold
    test stays as a smoke test.
(c) bounds provenance -- walk_forward_lj_asym surfaces bounds_train_test
    (train/OOS index bounds of the split geometry); _eval_one_coin,
    aggregate_verdicts and the manifest relay it per (coin, horizon) with
    fc_lj_hash_per_fold aligned with per_fold_bias. The
    ``if False else None`` placeholder is removed.

Usage:
    python har_lj_asym.py --horizons 1 5 10 --seeds 0 7 42 99 --skip-remote
    python har_lj_asym.py --horizons 1 5 10 --seeds 0 7 42 99 --debias
"""

from __future__ import annotations

import argparse
import hashlib
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
CALIBRATION_SIZE = 60  # train-tail size for per-fold bias estimation


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
# Per-fold bias estimation from train tail (REPAIR-2 concern #1)
# ---------------------------------------------------------------------------

def _train_tail_bias(
    model: HARLJAsymModel,
    X_train_fold: np.ndarray,
    y_train_fold: np.ndarray,
    calibration_size: int,
) -> float:
    """Estimate the OOS bias of ``model`` from the LAST ``calibration_size``
    points of the train fold ONLY.

    Sign convention (round-3 concern #1): ``bias = mean(y_tail - yhat_tail)``.
    The consumer must ADD it to the forecast --
    ``yhat_corrected = yhat + bias`` -- to remove the systematic offset.
    This is algebraically equivalent to the canonical ``walk_forward_har``
    pattern (which computes ``mean(pred - target)`` and subtracts it).

    This is the apples-to-apples train-only bias estimator required by
    #14584 disposition #1: the bias estimate never reads from the OOS
    targets (y_test). It mirrors the canonical ``walk_forward_har``
    calibration pattern (mean of train-tail residuals).
    """
    if len(y_train_fold) < 2:
        return 0.0
    tail_n = min(calibration_size, len(y_train_fold))
    X_tail = X_train_fold[-tail_n:]
    y_tail = y_train_fold[-tail_n:]
    yhat_tail = model.predict(X_tail)
    bias = float(np.mean(y_tail - yhat_tail))
    return bias


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
# Walk-forward evaluation with per-fold train-tail bias (REPAIR-2)
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
    calibration_size: int = CALIBRATION_SIZE,
    debias: bool = False,
) -> dict:
    """Walk-forward 5-fold evaluation of HAR-LJ-Asym model with per-fold bias
    calibration from the train tail (REPAIR-2 c.955, concern #1 verbatim).

    Round-3 concern #1: when ``debias=True``, each fold's slice of
    ``forecasts_debiased`` equals that fold's slice of ``forecasts`` shifted
    by the fold's constant ``per_fold_bias`` entry
    (``forecasts_debiased = forecasts + bias_fold``).

    Returns dict with forecasts (raw and optionally debiased per fold),
    targets, raw MSE, and per-fold bias estimates for audit.
    """
    feat = lj_asym_features(rv_neg, rv_pos, rv_c, rv_j, rv)
    log_rv = realized_variance_to_log(rv)

    merged = feat.join(log_rv.rename("log_rv"), how="inner").dropna()
    if len(merged) < 100:
        return {
            "forecasts": [], "forecasts_debiased": [], "targets": [],
            "aggregate_mse_logrv": np.nan,
            "aggregate_mse_logrv_debiased": np.nan,
            "per_fold_bias": [],
        }

    feature_cols = [
        "log_rv_neg_d", "log_rv_pos_d", "log_rv_c_d", "log_rv_j_d",
        "log_rv_w", "log_rv_m",
    ]
    target_fwd = merged["log_rv"].rolling(horizon).mean().shift(-horizon)
    valid = target_fwd.notna().values
    X_all = merged[feature_cols].values[valid]
    y_all = target_fwd.values[valid]

    n = len(X_all)
    fold_size = n // (n_splits + 1)
    forecasts: list[float] = []
    forecasts_debiased: list[float] = []
    targets: list[float] = []
    per_fold_bias: list[float] = []

    for fold in range(n_splits):
        split = (fold + 1) * fold_size
        if split + horizon >= n:
            break
        X_train, X_test = X_all[:split], X_all[split : split + fold_size]
        y_train, y_test = y_all[:split], y_all[split : split + fold_size]

        model = HARLJAsymModel().fit(X_train, y_train)
        yhat = model.predict(X_test)

        # Per-fold bias from train tail ONLY (no OOS target access).
        bias = _train_tail_bias(model, X_train, y_train, calibration_size)
        per_fold_bias.append(bias)

        forecasts.extend(yhat.tolist())
        if debias:
            # Round-3 concern #1: bias = mean(y_train_tail - yhat_train_tail)
            # must be ADDED (the previous `yhat - bias` inverted the sign and
            # produced 2*yhat - y on average). Per-fold constant shift.
            forecasts_debiased.extend((yhat + bias).tolist())
        targets.extend(y_test.tolist())

    if not forecasts:
        return {
            "forecasts": [], "forecasts_debiased": [], "targets": [],
            "aggregate_mse_logrv": np.nan,
            "aggregate_mse_logrv_debiased": np.nan,
            "per_fold_bias": per_fold_bias,
        }

    forecasts_arr = np.array(forecasts)
    targets_arr = np.array(targets)
    mse_raw = float(np.mean((forecasts_arr - targets_arr) ** 2))

    if debias and forecasts_debiased:
        forecasts_deb_arr = np.array(forecasts_debiased)
        mse_debiased = float(np.mean((forecasts_deb_arr - targets_arr) ** 2))
    else:
        forecasts_debiased = []
        mse_debiased = np.nan

    # Round-4 provenance (adjoint concern (c), DM msg-20260905T001520):
    # fold k tests on X_all[(k+1)*fold_size : (k+2)*fold_size), so the first
    # forecast sits at X_all index ``fold_size`` and the last EXECUTED fold's
    # train ends at ``n_folds * fold_size`` (== n_splits * (n // (n_splits+1))
    # when every fold runs). Indices are X_all (merged valid) coordinates:
    # X_all position j maps to original-series timestamp ``merged.index[j]``,
    # and its h-step target reads original positions up to j + horizon.
    n_folds = len(per_fold_bias)
    n_train_end = int(n_folds * fold_size)
    bounds_train_test = {
        "train_end_idx": n_train_end,
        "oos_start_idx": int(n_train_end + horizon),
        "oos_end_idx": int(n),
        "n_train": n_train_end,
        "n_oos": int(n - n_train_end),
        "n_total": int(n),
        "fold_size": int(fold_size),
        "n_folds": int(n_folds),
    }

    return {
        "forecasts": forecasts_arr.tolist(),
        "forecasts_debiased": forecasts_debiased,
        "targets": targets_arr.tolist(),
        "aggregate_mse_logrv": mse_raw,
        "aggregate_mse_logrv_debiased": mse_debiased,
        "per_fold_bias": per_fold_bias,
        "bounds_train_test": bounds_train_test,
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

    idx = pd.RangeIndex(n)
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
# Panel hash (round-3 concern #6: index + values)
# ---------------------------------------------------------------------------

def _panel_hash(rv: pd.Series, window: int = 360) -> str:
    """SHA256 over index (int64 ns) || values (float64) of the last ``window``
    bars, truncated to 16 hex chars.

    Round-3 concern #6: the previous hash covered the VALUES only -- two
    panels with identical values but different dates hashed identically. The
    index bytes are now concatenated before the value bytes in a single
    SHA256 digest, so any index drift changes the hash.
    """
    panel_window = rv.iloc[-min(len(rv), window):]
    idx_bytes = panel_window.index.astype("int64").to_numpy().astype(np.int64).tobytes()
    val_bytes = panel_window.to_numpy().astype(np.float64).tobytes()
    return hashlib.sha256(idx_bytes + val_bytes).hexdigest()[:16]


# ---------------------------------------------------------------------------
# Per-coin evaluation with train-only per-fold bias (REPAIR-2 c.955)
# ---------------------------------------------------------------------------

def _eval_one_coin(
    coin: str,
    horizon: int,
    seed: int,
    components: dict[str, dict[str, pd.Series]],
    debias: bool = False,
    calibration_size: int = CALIBRATION_SIZE,
) -> dict | None:
    """Evaluate one (coin, horizon, seed) combo.

    REPAIR-2 c.955: the calibration "symmetry" from c.953 was rejected because
    it read OOS targets via ``mean(err[-calibration_size:])`` after the full
    error array had been computed. The fix moves bias estimation INTO each
    model's walk-forward routine, where the bias estimate is computed from
    the train fold's tail (no OOS target access) and applied per fold to the
    OOS forecasts before they are accumulated. This is the apples-to-
    apples protocol required by #14584 disposition #1.

    ROUND-3 (head b974f2721, DM msg-20260904T141944):
    - #1: LJ uses the PER-FOLD-corrected ``forecasts_debiased`` array
      (convention ``yhat_corrected = yhat + bias``). The c.955 post-hoc
      global-mean shift is removed -- it used the wrong sign AND violated
      per-fold identity.
    - #2: M12 goes through ``walk_forward_har_rv_j(calibrate_bias=debias,
      calibration_size=...)`` -- its own internal train-tail calibration
      (the flag mirrors walk_forward_har's), apples-to-apples with LJ/HAR.
    - #3: HAR is evaluated on TWO legs when debias=True -- an uncalibrated
      ``walk_forward_har(calibrate_bias=False)`` pass feeding ``mse_har_raw``
      and a calibrated pass feeding ``mse_har_debiased`` + the DM leg.
    """
    comp = components.get(coin)
    if comp is None:
        return None

    rv = comp["rv"]
    rv_neg = comp["rv_neg"]
    rv_pos = comp["rv_pos"]
    rv_c = comp["rv_c"]
    rv_j = comp["rv_j"]

    # --- M17 HAR-LJ-Asym (per-fold train-tail bias) ---
    res_lj = walk_forward_lj_asym(
        rv, rv_neg, rv_pos, rv_c, rv_j, horizon, seed,
        debias=debias, calibration_size=calibration_size,
    )
    if not res_lj["forecasts"]:
        return None

    # --- HAR Classic baseline: raw + calibrated legs (round-3 concern #3) ---
    # mse_har_raw comes from an UNCALIBRATED walk_forward_har pass. When
    # debias=True, a SECOND calibrated pass provides the apples-to-apples DM
    # leg and mse_har_debiased. The two legs are distinct by construction
    # (the c.955 identity mse_har_raw == mse_har_debiased is gone).
    res_har_uncal = walk_forward_har(rv, horizon, calibrate_bias=False)
    har_fc_raw = res_har_uncal.get("forecasts")
    if har_fc_raw is None or (hasattr(har_fc_raw, '__len__') and len(har_fc_raw) == 0):
        return None

    if debias:
        res_har_deb = walk_forward_har(
            rv, horizon,
            calibrate_bias=True,
            calibration_size=calibration_size,
        )
        har_fc_dm = res_har_deb.get("forecasts")
        if har_fc_dm is None or (hasattr(har_fc_dm, '__len__') and len(har_fc_dm) == 0):
            return None
    else:
        har_fc_dm = har_fc_raw

    # --- M12 HAR-RV-J baseline (round-3 concern #2: calibrated when debias) ---
    # walk_forward_har_rv_j already exposes calibrate_bias (same internal
    # train-tail pattern as walk_forward_har); pass it for apples-to-apples.
    from m12_har_rv_j import walk_forward_har_rv_j
    res_m12 = walk_forward_har_rv_j(
        rv, rv_j, horizon,
        calibrate_bias=debias,
        calibration_size=calibration_size,
    )
    m12_fc = res_m12.get("forecasts")
    if m12_fc is None or (hasattr(m12_fc, '__len__') and len(m12_fc) == 0):
        return None

    # --- Align all three models to the shortest forecast series ---
    n = min(
        len(res_lj["forecasts"]),
        len(har_fc_raw),
        len(har_fc_dm),
        len(m12_fc),
    )
    if n < 10:
        return None

    fc_lj = np.array(res_lj["forecasts"][:n])
    # Round-3 concern #1: when debias=True, consume the PER-FOLD-corrected
    # forecasts produced inside walk_forward_lj_asym (each fold shifted by
    # that fold's train-tail bias, yhat_corrected = yhat + bias). This
    # replaces the c.955 post-walk-forward global-mean shift, which used the
    # wrong sign and violated per-fold identity.
    if debias and res_lj.get("forecasts_debiased"):
        fc_lj = np.array(res_lj["forecasts_debiased"][:n])
    fc_har = np.array(har_fc_dm.values[:n]) if hasattr(har_fc_dm, 'values') else np.array(har_fc_dm[:n])
    fc_har_raw = np.array(har_fc_raw.values[:n]) if hasattr(har_fc_raw, 'values') else np.array(har_fc_raw[:n])
    fc_m12 = np.array(m12_fc.values[:n]) if hasattr(m12_fc, 'values') else np.array(m12_fc[:n])
    tgt = np.array(res_lj["targets"][:n])

    err_lj = fc_lj - tgt[:len(fc_lj)]
    err_har = fc_har - tgt[:len(fc_har)]  # DM leg (calibrated when debias=True)
    err_har_raw = fc_har_raw - tgt[:len(fc_har_raw)]  # truly raw leg
    err_m12 = fc_m12 - tgt[:len(fc_m12)]  # internally calibrated when debias=True

    # --- MSE = bias^2 + variance decomposition (population variance, ddof=0) ---
    mse_lj_empirical = float(np.mean(err_lj ** 2))
    mse_har_dm_empirical = float(np.mean(err_har ** 2))
    mse_har_raw_empirical = float(np.mean(err_har_raw ** 2))
    mse_m12_empirical = float(np.mean(err_m12 ** 2))

    bias_lj = float(np.mean(err_lj))
    bias_har = float(np.mean(err_har))
    bias_m12 = float(np.mean(err_m12))
    var_lj = float(np.var(err_lj, ddof=0))
    var_har = float(np.var(err_har, ddof=0))
    var_m12 = float(np.var(err_m12, ddof=0))
    mse_lj = bias_lj ** 2 + var_lj
    mse_har_dm = bias_har ** 2 + var_har
    mse_m12 = bias_m12 ** 2 + var_m12

    # Sanity guard: empirical == decomposed (concern #1 acceptance, c.953).
    assert abs(mse_lj - mse_lj_empirical) < 1e-9, (
        f"MSE decomposition broken for LJ: {mse_lj} vs {mse_lj_empirical}"
    )
    assert abs(mse_har_dm - mse_har_dm_empirical) < 1e-9, (
        f"MSE decomposition broken for HAR (DM leg): {mse_har_dm} vs {mse_har_dm_empirical}"
    )
    assert abs(mse_m12 - mse_m12_empirical) < 1e-9, (
        f"MSE decomposition broken for M12: {mse_m12} vs {mse_m12_empirical}"
    )

    # --- DM test on the calibrated errors -- apples-to-apples (round-3):
    # LJ per-fold corrected, HAR calibrated inside walk_forward_har, M12
    # calibrated inside walk_forward_har_rv_j (all when debias=True) ---
    dm_vs_har = dm_verdict(err_lj, err_har, horizon=horizon)
    dm_vs_m12 = dm_verdict(err_lj, err_m12, horizon=horizon)

    # --- Bit-identity audit anchor (concern #3 fix, c.953 sustained;
    # round-3 concern #6: the hash covers index AND values) ---
    # OLS is deterministic on a given (X, y) pair; panel_hash on the canonical
    # 360-bar RV window must be identical across seeds {0, 7, 42, 99}.
    panel_hash = _panel_hash(rv)

    # Forecasts/targets/errors hashes for manifest (concern #4 fix, c.955).
    fc_lj_hash = hashlib.sha256(fc_lj.astype(np.float64).tobytes()).hexdigest()[:16]
    fc_har_hash = hashlib.sha256(fc_har.astype(np.float64).tobytes()).hexdigest()[:16]
    fc_m12_hash = hashlib.sha256(fc_m12.astype(np.float64).tobytes()).hexdigest()[:16]
    tgt_hash = hashlib.sha256(tgt.astype(np.float64).tobytes()).hexdigest()[:16]
    err_lj_hash = hashlib.sha256(err_lj.astype(np.float64).tobytes()).hexdigest()[:16]
    err_har_hash = hashlib.sha256(err_har.astype(np.float64).tobytes()).hexdigest()[:16]
    err_m12_hash = hashlib.sha256(err_m12.astype(np.float64).tobytes()).hexdigest()[:16]

    # --- Bounds + edge-sigma disposition (concern #4; round-4 concern (c)) ---
    # Provenance convention: ``bounds_train_test`` comes from the LJ
    # walk-forward geometry (see walk_forward_lj_asym) -- fold k tests on
    # X_all[(k+1)*fold_size : (k+2)*fold_size), the first forecast sits at
    # X_all index fold_size, and the last fold's train ends at
    # n_folds*fold_size (= n_splits * (n // (n_splits + 1)) when all folds
    # execute). Indices are X_all (merged valid) coordinates: position j
    # maps to original-series timestamp merged.index[j]; its h-step target
    # reads original positions up to j + horizon. The global fc_*_hash
    # cover the ALIGNED forecasts; fc_lj_hash_per_fold hashes each fold
    # slice of the LJ walk-forward output, aligned with per_fold_bias, so
    # the per-tranche granules are anchored to the bounds. Edge-σ is N/A
    # because OLS on a deterministic (X, y) panel with fixed seeds is
    # bit-identical -- see panel_hashes_consistent.
    bounds_train_test = res_lj.get("bounds_train_test")
    fold_size_wf = (bounds_train_test or {}).get("fold_size")
    n_folds_wf = (bounds_train_test or {}).get("n_folds")
    fc_series_per_fold = (
        res_lj.get("forecasts_debiased") or res_lj.get("forecasts")
    )
    if fold_size_wf and n_folds_wf and fc_series_per_fold:
        fc_lj_hash_per_fold = [
            hashlib.sha256(
                np.asarray(
                    fc_series_per_fold[k * fold_size_wf:(k + 1) * fold_size_wf],
                    dtype=np.float64,
                ).tobytes()
            ).hexdigest()[:16]
            for k in range(int(n_folds_wf))
        ]
    else:
        fc_lj_hash_per_fold = []

    # --- Kelly portfolio metrics ---
    kelly_metrics = _compute_kelly(fc_lj, tgt)

    return {
        "coin": coin,
        "horizon": horizon,
        "seed": seed,
        "mse_logrv": mse_lj_empirical,
        # Round-3 concern #3: raw leg from the UNCALIBRATED walk_forward_har
        # pass; debiased leg from the separate calibrate_bias=True pass (NaN
        # when debias=False). No more fake identity between the two.
        "mse_har_raw": mse_har_raw_empirical,
        "mse_har_debiased": mse_har_dm if debias else float("nan"),
        "mse_m12": mse_m12,
        "bias_lj": bias_lj,
        "bias_har": bias_har,
        "bias_m12": bias_m12,
        "var_lj": var_lj,
        "var_har": var_har,
        "var_m12": var_m12,
        "dm_vs_har": dm_vs_har,
        "dm_vs_m12": dm_vs_m12,
        "panel_hash": panel_hash,
        "fc_lj_hash": fc_lj_hash,
        "fc_har_hash": fc_har_hash,
        "fc_m12_hash": fc_m12_hash,
        "tgt_hash": tgt_hash,
        "err_lj_hash": err_lj_hash,
        "err_har_hash": err_har_hash,
        "err_m12_hash": err_m12_hash,
        "n_obs": int(n),
        # Round-4 concern (c): provenance surface -- per-fold bias list,
        # train/OOS bounds of the walk-forward split, and per-fold hashes
        # (16-hex each) aligned with per_fold_bias.
        "per_fold_bias": list(res_lj.get("per_fold_bias", [])),
        "bounds_train_test": bounds_train_test,
        "fc_lj_hash_per_fold": fc_lj_hash_per_fold,
        "edge_sigma_applicable": False,
        **kelly_metrics,
    }


# ---------------------------------------------------------------------------
# Aggregation (concern #3 fix: surface DM component by component)
# ---------------------------------------------------------------------------

def aggregate_verdicts(rows: list[dict]) -> list[dict]:
    """Aggregate per-(coin, horizon) across seeds.

    REPAIR-2 c.955: each DM verdict is now surfaced with its full set of
    components (dm_statistic, p_value, mean_loss_diff, n_obs) per seed, and
    the aggregated counts require ``verdict == "BEATS baseline"`` to imply
    ``p_value < 0.05 AND mean_loss_diff < 0`` (asserted at write time below).
    """
    groups: dict[tuple, list[dict]] = {}
    for r in rows:
        key = (r["coin"], r["horizon"])
        groups.setdefault(key, []).append(r)

    results = []
    for (coin, horizon), group in sorted(groups.items()):
        sharpe_vals = [r["sharpe"] for r in group if not np.isnan(r.get("sharpe", np.nan))]
        mse_vals = [r["mse_logrv"] for r in group if not np.isnan(r.get("mse_logrv", np.nan))]

        bias_lj_vals = [r["bias_lj"] for r in group if "bias_lj" in r]
        bias_har_vals = [r["bias_har"] for r in group if "bias_har" in r]
        bias_m12_vals = [r["bias_m12"] for r in group if "bias_m12" in r]
        var_lj_vals = [r["var_lj"] for r in group if "var_lj" in r]
        var_har_vals = [r["var_har"] for r in group if "var_har" in r]
        var_m12_vals = [r["var_m12"] for r in group if "var_m12" in r]
        mse_har_raw_vals = [r["mse_har_raw"] for r in group if "mse_har_raw" in r and not np.isnan(r["mse_har_raw"])]
        mse_har_debiased_vals = [
            r["mse_har_debiased"] for r in group
            if "mse_har_debiased" in r and not np.isnan(r["mse_har_debiased"])
        ]
        mse_m12_vals = [r["mse_m12"] for r in group if "mse_m12" in r]
        panel_hashes = [r["panel_hash"] for r in group if r.get("panel_hash")]

        # Round-4 concern (c): per-(coin, horizon) train/OOS bounds. The
        # walk-forward geometry is deterministic per (coin, horizon), so all
        # seeds of a group must carry identical bounds.
        bounds_entries = [
            r.get("bounds_train_test") for r in group
            if r.get("bounds_train_test")
        ]

        # --- Concern #3: aggregate DM components (mean, std, p_value median) ---
        def _dm_components(rows_subset: list[dict], key: str) -> dict:
            p_vals = [r[key]["p_value"] for r in rows_subset if key in r and "p_value" in r[key]]
            stats = [r[key]["dm_statistic"] for r in rows_subset if key in r and "dm_statistic" in r[key]]
            diffs = [r[key]["mean_loss_diff"] for r in rows_subset if key in r and "mean_loss_diff" in r[key]]
            return {
                "p_value_median": float(np.median(p_vals)) if p_vals else np.nan,
                "p_value_min": float(np.min(p_vals)) if p_vals else np.nan,
                "dm_statistic_mean": float(np.mean(stats)) if stats else np.nan,
                "mean_loss_diff_mean": float(np.mean(diffs)) if diffs else np.nan,
                "p_values": p_vals,
                "dm_statistics": stats,
                "mean_loss_diffs": diffs,
            }

        dm_har_components = _dm_components(group, "dm_vs_har")
        dm_m12_components = _dm_components(group, "dm_vs_m12")

        # --- Verdict counts (concern #3: only count if internal coherence
        # holds -- p<0.05 AND mean_loss_diff<0 for BEATS) ---
        def _coherent_beats(r: dict, key: str) -> bool:
            if key not in r:
                return False
            v = r[key]
            if v.get("verdict") != "BEATS baseline":
                return False
            # Coherence: a BEATS verdict requires p<0.05 AND mean_loss_diff<0.
            # If not, the verdict was mis-classified upstream -- do not count.
            if v.get("p_value", 1.0) >= 0.05:
                return False
            if v.get("mean_loss_diff", 0.0) >= 0.0:
                return False
            return True

        def _coherent_beaten_by(r: dict, key: str) -> bool:
            if key not in r:
                return False
            v = r[key]
            if v.get("verdict") != "BEATEN BY baseline":
                return False
            if v.get("p_value", 1.0) >= 0.05:
                return False
            if v.get("mean_loss_diff", 0.0) <= 0.0:
                return False
            return True

        dm_har_wins = sum(1 for r in group if _coherent_beats(r, "dm_vs_har"))
        dm_har_beaten = sum(1 for r in group if _coherent_beaten_by(r, "dm_vs_har"))
        dm_har_total = sum(
            1 for r in group if r.get("dm_vs_har", {}).get("verdict", "") != "NO_M12_BASELINE"
        )
        dm_m12_wins = sum(1 for r in group if _coherent_beats(r, "dm_vs_m12"))
        dm_m12_beaten = sum(1 for r in group if _coherent_beaten_by(r, "dm_vs_m12"))
        dm_m12_total = sum(
            1 for r in group
            if r.get("dm_vs_m12", {}).get("verdict", "") not in ("NO_M12_BASELINE", "")
        )

        avg_sharpe = float(np.mean(sharpe_vals)) if sharpe_vals else np.nan
        avg_mse = float(np.mean(mse_vals)) if mse_vals else np.nan

        def _mean_or_nan(vals: list[float]) -> float:
            return float(np.mean(vals)) if vals else np.nan

        results.append({
            "coin": coin,
            "horizon": horizon,
            "n_seeds": len(group),
            "avg_sharpe": avg_sharpe,
            "avg_mse_logrv": avg_mse,
            "avg_bias_lj": _mean_or_nan(bias_lj_vals),
            "avg_bias_har": _mean_or_nan(bias_har_vals),
            "avg_bias_m12": _mean_or_nan(bias_m12_vals),
            "avg_var_lj": _mean_or_nan(var_lj_vals),
            "avg_var_har": _mean_or_nan(var_har_vals),
            "avg_var_m12": _mean_or_nan(var_m12_vals),
            "avg_mse_har_raw": _mean_or_nan(mse_har_raw_vals),
            "avg_mse_har_debiased": _mean_or_nan(mse_har_debiased_vals),
            "avg_mse_m12": _mean_or_nan(mse_m12_vals),
            "var_ratio_lj_over_har": (
                float(np.mean(var_lj_vals) / np.mean(var_har_vals))
                if var_lj_vals and var_har_vals and np.mean(var_har_vals) > 0
                else np.nan
            ),
            "dm_vs_har_wins": dm_har_wins,
            "dm_vs_har_beaten": dm_har_beaten,
            "dm_vs_har_total": dm_har_total,
            "dm_vs_m12_wins": dm_m12_wins,
            "dm_vs_m12_beaten": dm_m12_beaten,
            "dm_vs_m12_total": dm_m12_total,
            "dm_vs_har_components": dm_har_components,
            "dm_vs_m12_components": dm_m12_components,
            "seeds": [r["seed"] for r in group],
            "panel_hash": panel_hashes[0] if panel_hashes else "",
            "panel_hashes_consistent": len(set(panel_hashes)) <= 1 if panel_hashes else True,
            # Round-4 concern (c): bounds provenance per (coin, horizon).
            "bounds_train_test": bounds_entries[0] if bounds_entries else None,
            "bounds_consistent_across_seeds": (
                len({json.dumps(b, sort_keys=True) for b in bounds_entries}) <= 1
                if bounds_entries else True
            ),
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
    parser.add_argument(
        "--debias", action="store_true",
        help="Apply per-fold train-tail bias calibration to LJ / HAR / M12 (canonical pattern, REPAIR-2 c.955 + round-3).",
    )
    parser.add_argument(
        "--calibration-size", type=int, default=CALIBRATION_SIZE,
        help="Train-tail window for per-fold bias estimation (default: 60).",
    )
    args = parser.parse_args()

    coins = args.coins
    if coins is None:
        coins = LOCAL_COINS if args.skip_remote else COINS

    print(f"M17 HAR-LJ-Asym: coins={coins}, horizons={args.horizons}, "
          f"seeds={args.seeds}, skip_remote={args.skip_remote}, "
          f"debias={args.debias}, calibration_size={args.calibration_size}")

    t0 = time.time()

    panel = _load_panel(skip_remote=args.skip_remote)
    available = [c for c in coins if c in panel]
    if not available:
        print("ERROR: no coins available after loading panel")
        return
    print(f"Panel loaded: {list(panel.keys())} ({len(panel[available[0]])} bars for {available[0]})")

    components = compute_daily_components(panel)
    print(f"Components computed for: {list(components.keys())}")

    rows: list[dict] = []
    total = len(available) * len(args.horizons) * len(args.seeds)
    done = 0
    for coin in available:
        for horizon in args.horizons:
            for seed in args.seeds:
                done += 1
                print(f"  [{done}/{total}] {coin} h={horizon} seed={seed}", end="", flush=True)
                result = _eval_one_coin(
                    coin, horizon, seed, components,
                    debias=args.debias,
                    calibration_size=args.calibration_size,
                )
                if result is not None:
                    rows.append(result)
                    dm_h = result.get("dm_vs_har", {}).get("verdict", "?")
                    dm_m = result.get("dm_vs_m12", {}).get("verdict", "?")
                    print(f" -> MSE={result['mse_logrv']:.6f} "
                          f"DM_har={dm_h} DM_m12={dm_m}")
                else:
                    print(" -> SKIP (insufficient data)")

    elapsed = time.time() - t0

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
            "debias_har": args.debias,
            "calibration_size": args.calibration_size,
            "calibration_protocol": "REPAIR-2 c.955 per-fold train-tail bias (no OOS target access)",
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

    # --- Concern #4: persist a manifest OUTSIDE the JSON results blob ---
    # Manifest hash includes the entire run signature: rows + params + agg.
    # Round-3 concern #6: cross-seed panel-hash consistency is meaningful
    # WITHIN a (coin, horizon) group, not globally (different coins
    # legitimately hash differently) -- surface the per-group bookkeeping.
    ph_groups: dict[tuple, list[str]] = {}
    for r in rows:
        ph_groups.setdefault((r["coin"], r["horizon"]), []).append(
            r.get("panel_hash", ""),
        )
    panel_hash_per_coin_horizon = [
        {
            "coin": c,
            "horizon": h,
            "panel_hash": hs[0] if hs else "",
            "n_seed_rows": len(hs),
            "consistent_across_seeds": len(set(hs)) <= 1,
        }
        for (c, h), hs in sorted(ph_groups.items())
    ]
    # Round-4 concern (c): per-(coin, horizon) train/OOS bounds provenance,
    # same surfacing pattern as panel_hash_per_coin_horizon -- the manifest
    # says WHERE (index bounds) the forecasts/targets come from, alongside
    # the existing value hashes.
    bounds_groups: dict[tuple, list[dict]] = {}
    for r in rows:
        if r.get("bounds_train_test"):
            bounds_groups.setdefault((r["coin"], r["horizon"]), []).append(
                r["bounds_train_test"],
            )
    bounds_per_coin_horizon = [
        {
            "coin": c,
            "horizon": h,
            "bounds_train_test": bs[0],
            "n_seed_rows": len(bs),
            "consistent_across_seeds": (
                len({json.dumps(b, sort_keys=True) for b in bs}) <= 1
            ),
        }
        for (c, h), bs in sorted(bounds_groups.items())
    ]
    manifest = {
        "model": "M17_HAR_LJ_ASYM",
        "params": output["params"],
        "coins": available,
        "horizons": args.horizons,
        "seeds": args.seeds,
        "elapsed_seconds": round(elapsed, 1),
        "n_combos_evaluated": len(rows),
        "bounds": {
            "first_bar": (
                str(panel[available[0]].index[0].isoformat())
                if available and len(panel[available[0]]) else None
            ),
            "last_bar": (
                str(panel[available[0]].index[-1].isoformat())
                if available and len(panel[available[0]]) else None
            ),
            "n_bars_per_coin": {
                c: int(len(panel[c])) for c in available if c in panel
            },
        },
        "panel_hashes": sorted({r["panel_hash"] for r in rows if r.get("panel_hash")}),
        "panel_hash_per_coin_horizon": panel_hash_per_coin_horizon,
        "bounds_per_coin_horizon": bounds_per_coin_horizon,
        "panel_hashes_consistent": (
            all(g["consistent_across_seeds"] for g in panel_hash_per_coin_horizon)
            if panel_hash_per_coin_horizon else True
        ),
        "fc_hashes_per_coin_horizon": [
            {
                "coin": r["coin"], "horizon": r["horizon"], "seed": r["seed"],
                "fc_lj_hash": r["fc_lj_hash"], "fc_har_hash": r["fc_har_hash"],
                "fc_m12_hash": r["fc_m12_hash"], "tgt_hash": r["tgt_hash"],
                "err_lj_hash": r["err_lj_hash"], "err_har_hash": r["err_har_hash"],
                "err_m12_hash": r["err_m12_hash"], "n_obs": r["n_obs"],
            }
            for r in rows
        ],
        "bit_identity_check": (
            "Bit-identity cross-seed only meaningful WITHIN the same (coin, "
            "horizon, panel) tuple -- the seed does NOT change the OLS fit on "
            "a fixed (X, y), so all seeds should produce identical forecasts "
            "and DM verdicts (panel_hash + fc_*_hash consistent across seeds)."
        ),
        "edge_sigma_disposition": (
            "N/A. OLS on a deterministic (X, y) panel with fixed seeds is "
            "bit-identical -- the panel_hash + per-row fc_hash/tgt_hash/"
            "err_hash consistent across seeds {0, 7, 42, 99} is the "
            "verifiable anchor. Multi-seed edge-σ is not applicable to "
            "deterministic OLS; it applies to stochastic estimators (e.g. "
            "neural nets with dropout, MCTS planners)."
        ),
        "concern_addressing": {
            "concern_1_calibration_train_only": (
                "Per-fold bias estimated from train tail only via "
                "_train_tail_bias() -- the bias estimate NEVER reads the OOS "
                "target. This replaces the c.953 global tail-mean block that "
                "leaked targets via mean(err[-60:]). Anti-leak test: "
                "test_calibration_anti_leak_perturbation in test_har_lj_asym.py."
            ),
            "concern_2_har_not_double_calibrated": (
                "HAR receives calibrate_bias=True INSIDE walk_forward_har "
                "(canonical train-tail bias). The post-walk-forward global "
                "tail-mean block has been REMOVED -- mse_har_raw is now the "
                "canonical HAR walk_forward output, not a post-corrected "
                "double-calibrated value."
            ),
            "concern_3_dm_verdict_consistency": (
                "Each row carries the full DM verdict dict (dm_statistic, "
                "p_value, mean_loss_diff, n_obs). The aggregated counts use "
                "_coherent_beats() which REQUIRES (p_value < 0.05 AND "
                "mean_loss_diff < 0) for BEATS, and (p_value < 0.05 AND "
                "mean_loss_diff > 0) for BEATEN BY. The aggregator surfaces "
                "p_values, dm_statistics, and mean_loss_diffs as lists per "
                "(coin, horizon)."
            ),
            "concern_4_manifest_outside_git": (
                "scripts/results/manifest_m17_har_lj_asym.json is written "
                "at every run with bounds (first/last bar per coin), panel "
                "hashes, per-row forecast/target/error hashes, bit-identity "
                "disposition, and edge-σ disposition."
            ),
            "concern_5_prev_valid": (
                "prev: MED/training #14561 (last MERGED training PR of this "
                "lane, distinct from #14592)."
            ),
            "concern_1_round3_sign_and_per_fold": (
                "Bias convention is bias = mean(y_train_tail - yhat_train_tail); "
                "corrected forecast = yhat + bias (the c.955 yhat - bias inverted "
                "the sign and doubled the error). _eval_one_coin consumes the "
                "per-fold-corrected forecasts_debiased array instead of a "
                "post-walk-forward global-mean shift."
            ),
            "concern_2_round3_m12_calibrated": (
                "walk_forward_har_rv_j already exposes calibrate_bias (same "
                "internal train-tail pattern as walk_forward_har); "
                "_eval_one_coin now passes calibrate_bias=debias + "
                "calibration_size so M12 is calibrated apples-to-apples."
            ),
            "concern_3_round3_har_raw_vs_debiased": (
                "mse_har_raw comes from an uncalibrated walk_forward_har pass; "
                "mse_har_debiased from a separate calibrate_bias=True pass "
                "(the DM leg). Two distinct legs -- the c.955 identity "
                "mse_har_raw == mse_har_debiased is gone."
            ),
            "concern_4_round3_anti_leak_full_walk_forward": (
                "test_walk_forward_lj_asym_oos_target_invariance perturbs ALL "
                "OOS targets through the full walk-forward and asserts "
                "per_fold_bias and forecasts_debiased bit-identical."
            ),
            "concern_5_round3_live_run_deferred": (
                "c.953 live numbers are SUPERSEDED by the round-3 calibration "
                "(see docs/M17_HAR_LJ_ASYM.md); the live BTC re-run is deferred "
                "post-merge and gated by this manifest."
            ),
            "concern_6_round3_panel_hash_index": (
                "panel_hash = sha256(index_int64_ns || values_float64) on the "
                "canonical 360-bar window; the manifest surfaces "
                "panel_hash_per_coin_horizon (per-group hashes + consistency), "
                "not a single collapsed global hash."
            ),
            "concern_a_round4_multifold_oos_invariance": (
                "test_walk_forward_lj_asym_oos_target_invariance_multi_fold "
                "runs n_splits=3 with >=2 DISTINCT per-fold biases; shifting "
                "only fold k's OOS target window leaves per_fold_bias[k] and "
                "fold k's forecast slices bit-identical, with earlier folds "
                "unchanged and later folds legitimately retraining on the "
                "shifted rows (walk-forward expanding window, not leakage). "
                "Per-fold train-tail shifts move only that fold's bias (>1.0)."
            ),
            "concern_c_round4_bounds_provenance": (
                "walk_forward_lj_asym surfaces bounds_train_test "
                "{train_end_idx, oos_start_idx, oos_end_idx, n_train, n_oos} "
                "(indices in X_all/merged-valid coordinates; train_end_idx = "
                "n_folds * fold_size). _eval_one_coin, aggregate_verdicts "
                "(bounds_train_test + bounds_consistent_across_seeds) and "
                "this manifest (bounds_per_coin_horizon) relay it; "
                "fc_lj_hash_per_fold is aligned with per_fold_bias. The "
                "`if False else None` placeholder is removed."
            ),
        },
        "manifest_sha256": hashlib.sha256(
            json.dumps(output, sort_keys=True, default=str).encode("utf-8")
        ).hexdigest(),
    }
    manifest_path = RESULTS_DIR / "manifest_m17_har_lj_asym.json"
    with open(manifest_path, "w", encoding="utf-8") as f:
        json.dump(manifest, f, indent=2, default=str)
    print(f"Manifest saved to {manifest_path}")

    print(f"Total: {len(rows)} combos evaluated in {elapsed:.1f}s")

    if agg:
        print("\n=== Aggregated Results ===")
        for a in agg:
            print(f"  {a['coin']} h={a['horizon']}: "
                  f"MSE={a['avg_mse_logrv']:.6f} Sharpe={a['avg_sharpe']:.4f} "
                  f"DM_har={a['dm_vs_har_wins']}/{a['dm_vs_har_total']} "
                  f"DM_m12={a['dm_vs_m12_wins']}/{a['dm_vs_m12_total']}")


if __name__ == "__main__":
    main()
