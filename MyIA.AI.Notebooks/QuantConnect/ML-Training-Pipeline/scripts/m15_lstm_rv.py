"""M15 Log-LSTM RV -- Neural volatility forecasting on log-realized variance.

Question
--------
Does a small LSTM neural network beat HAR Classic for crypto volatility forecasting?

Architecture:
    Input:  sliding window W=22 days of [log(RV), returns, sign(returns)] -> (W, 3)
    Model:  LSTM(hidden=64, 1 layer) + FC(64, 1)
    Target: log(RV_{t+h}) where h in {1, 5, 10}
    Loss:   MSE on log-RV
    Forecast: exp(pred) -> RV level, then log(RV) for Kelly comparison

Walk-forward 5-fold expanding, 7 coins x 3 horizons x 4 seeds = 84 combos.
Kelly cap=1.0, fee=50bps, sign-test paired Sharpe-diff vs HAR Classic baseline.

Param count: LSTM(3, 64) = 4*(64*64 + 64*3 + 64*4) = 17,408
             + FC(64, 1) = 65
             Total ~17.5K params.
Also tested hidden=32: 4*(32*32 + 32*3 + 32*4) = 4,640 + 33 = ~4.7K params.

Output
------
- results/m15_lstm_rv/results.json
- results/m15_lstm_rv/m15_lstm_rv_results.csv
- docs/M15_LSTM_RV.md (verdict)

Env: conda coursia-ml-training (Python 3.11, PyTorch 2.x + CUDA).
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
import time
import warnings
from pathlib import Path

import numpy as np
import pandas as pd

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))
# Thermal watchdog lives in QuantConnect/shared/ (fix #12661). Without this
# path, a bare `from gpu_training import ...` cannot resolve and callers fall
# back to silent no-op stubs -- the exact failure mode #12661 closed.
sys.path.insert(0, str(SCRIPT_DIR.parents[1] / "shared"))

from gpu_training import thermal_check  # noqa: E402
from har_model import HARModel, walk_forward_har  # noqa: E402
from intraday_loader import load_yf_intraday  # noqa: E402
from m11g_fee_aware_kelly import (  # noqa: E402
    _binomial_pvalue_one_sided,
    _kelly_weights_and_returns,
    _load_one_coin,
    _net_at_fee,
)
from m11c_sharpe_test import ledoit_wolf_sharpe_diff_se  # noqa: E402
from dm_test import diebold_mariano_test  # noqa: E402
from realized_variance import (  # noqa: E402
    daily_realized_variance,
    realized_variance_to_log,
)
from bias_metrics import (  # noqa: E402
    _dm_centered_mse,
    _mse_decomposition,
    joined_pair_errors,
)

COINS = ["BTC-USD", "ETH-USD", "SOL-USD", "LTC-USD", "XRP-USD", "ADA-USD", "DOT-USD"]
HORIZONS = [1, 5, 10]
SEEDS = [0, 1, 7, 42]
KELLY_CAP = 1.0
MU_WINDOW = 60
FEE_BPS = 50
N_SPLITS = 5
REFIT_EVERY = 22
RESULTS_DIR = SCRIPT_DIR / "results" / "m15_lstm_rv"

# LSTM hyperparams
WINDOW = 22
HIDDEN_SIZE = 64
NUM_LAYERS = 1
DROPOUT = 0.0
LEARNING_RATE = 1e-3
MAX_EPOCHS = 100
PATIENCE = 10
BATCH_SIZE = 32


# -- LSTM Model ---------------------------------------------------------------

def build_lstm(input_size: int = 3, hidden_size: int = HIDDEN_SIZE,
               num_layers: int = NUM_LAYERS):
    """Build a minimal LSTM model for log-RV forecasting."""
    import torch
    import torch.nn as nn

    class LSTMVolModel(nn.Module):
        def __init__(self, inp_sz, hid_sz, n_layers):
            super().__init__()
            self.lstm = nn.LSTM(inp_sz, hid_sz, n_layers, batch_first=True)
            self.fc = nn.Linear(hid_sz, 1)

        def forward(self, x):
            out, _ = self.lstm(x)
            return self.fc(out[:, -1, :])

    model = LSTMVolModel(input_size, hidden_size, num_layers)
    return model


def count_params(model) -> int:
    import torch
    return sum(p.numel() for p in model.parameters())


# -- Data preparation ---------------------------------------------------------

def prepare_features(hourly_rets: pd.Series) -> tuple[pd.DataFrame, pd.Series]:
    """Build [log_RV, returns, sign_returns] features aligned to daily RV.

    Returns (features_df, rv_series) both indexed by date.
    """
    rv = daily_realized_variance(hourly_rets)
    log_rv = np.log(rv.clip(lower=1e-12))

    daily_rets = hourly_rets.groupby(hourly_rets.index.normalize()).sum()
    daily_rets.index = pd.DatetimeIndex(daily_rets.index).normalize()
    daily_rets = daily_rets.rename("returns")

    sign_rets = np.sign(daily_rets).rename("sign_returns")

    features = pd.concat([log_rv.rename("log_rv"), daily_rets, sign_rets], axis=1, sort=False)
    features = features.dropna()

    rv = rv.reindex(features.index)
    return features, rv


def make_sequences(features: np.ndarray, targets: np.ndarray,
                   window: int) -> tuple[np.ndarray, np.ndarray]:
    """Create (X, y) sequences for LSTM training.

    X shape: (N - window, window, n_features)
    y shape: (N - window,)
    """
    X, y = [], []
    for i in range(len(features) - window):
        X.append(features[i:i + window])
        y.append(targets[i + window])
    return np.array(X), np.array(y)


# -- Walk-forward LSTM --------------------------------------------------------

def walk_forward_lstm(
    features: pd.DataFrame,
    rv: pd.Series,
    horizon: int = 1,
    n_splits: int = N_SPLITS,
    refit_every: int = REFIT_EVERY,
    window: int = WINDOW,
    hidden_size: int = HIDDEN_SIZE,
    seed: int = 0,
) -> dict:
    """Walk-forward LSTM with expanding window."""
    import torch
    import torch.nn as nn

    torch.manual_seed(seed)
    np.random.seed(seed)

    log_rv = np.log(rv.clip(lower=1e-12))

    # Target: mean of log(RV) over next h days
    target = log_rv.rolling(horizon).mean().shift(-horizon)
    target = target.reindex(features.index)

    feat_vals = features.values
    target_vals = target.values
    n = len(feat_vals)

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

    device = torch.device("cuda" if torch.cuda.is_available() else "cpu")

    for fold_idx, (train_end, test_start, test_end) in enumerate(splits):
        # Thermal watchdog (MAX_TEMP=80C, cool_sleep=30): one cheap nvidia-smi
        # probe per fold and per refit boundary. The LSTM is small but the
        # sweep is long (12 combos x ~5 folds x ~17 refits).
        if device.type == "cuda":
            thermal_check(max_temp=80, cool_sleep=30)

        # Build training sequences
        train_feat = feat_vals[:train_end]
        train_target = target_vals[:train_end]

        # Normalize features (expanding: fit on train, apply to test)
        feat_mean = np.nanmean(train_feat, axis=0)
        feat_std = np.nanstd(train_feat, axis=0) + 1e-8
        train_feat_norm = (train_feat - feat_mean) / feat_std

        X_train, y_train = make_sequences(train_feat_norm, train_target, window)
        if len(X_train) < 20:
            continue

        # Train LSTM
        model = build_lstm(
            input_size=X_train.shape[2],
            hidden_size=hidden_size,
        ).to(device)

        optimizer = torch.optim.Adam(model.parameters(), lr=LEARNING_RATE)
        criterion = nn.MSELoss()

        X_t = torch.FloatTensor(X_train).to(device)
        y_t = torch.FloatTensor(y_train).unsqueeze(1).to(device)

        best_loss = float("inf")
        best_state = None
        no_improve = 0

        for epoch in range(MAX_EPOCHS):
            model.train()
            perm = torch.randperm(len(X_t))
            epoch_loss = 0.0
            n_batches = 0
            for start in range(0, len(perm), BATCH_SIZE):
                idx = perm[start:start + BATCH_SIZE]
                xb = X_t[idx]
                yb = y_t[idx]
                optimizer.zero_grad()
                pred = model(xb)
                loss = criterion(pred, yb)
                loss.backward()
                optimizer.step()
                epoch_loss += loss.item()
                n_batches += 1

            avg_loss = epoch_loss / max(n_batches, 1)
            if avg_loss < best_loss - 1e-6:
                best_loss = avg_loss
                best_state = {k: v.clone() for k, v in model.state_dict().items()}
                no_improve = 0
            else:
                no_improve += 1
            if no_improve >= PATIENCE:
                break

        if best_state is not None:
            model.load_state_dict(best_state)
        model.eval()

        # Evaluate on test set
        fold_preds: list[float] = []
        fold_truths: list[float] = []

        for i in range(test_start, test_end - horizon):
            if i < window:
                continue
            # Use all data up to i for normalization
            feat_so_far = feat_vals[:i]
            f_mean = np.nanmean(feat_so_far, axis=0)
            f_std = np.nanstd(feat_so_far, axis=0) + 1e-8

            seq = (feat_vals[i - window:i] - f_mean) / f_std
            seq_tensor = torch.FloatTensor(seq).unsqueeze(0).to(device)

            with torch.no_grad():
                pred_val = model(seq_tensor).item()
            true_val = target_vals[i]

            if np.isfinite(pred_val) and np.isfinite(true_val):
                fold_preds.append(pred_val)
                fold_truths.append(true_val)
                preds.append(pred_val)
                truths.append(true_val)
                pred_dates.append(features.index[i])

            # Refit periodically
            if (i - test_start) % refit_every == 0 and i > test_start:
                if device.type == "cuda":
                    thermal_check(max_temp=80, cool_sleep=30)
                refit_feat = feat_vals[:i]
                refit_target = target_vals[:i]
                rf_mean = np.nanmean(refit_feat, axis=0)
                rf_std = np.nanstd(refit_feat, axis=0) + 1e-8
                refit_norm = (refit_feat - rf_mean) / rf_std
                X_rf, y_rf = make_sequences(refit_norm, refit_target, window)
                if len(X_rf) >= 20:
                    try:
                        model = build_lstm(
                            input_size=X_rf.shape[2],
                            hidden_size=hidden_size,
                        ).to(device)
                        optimizer = torch.optim.Adam(model.parameters(), lr=LEARNING_RATE)
                        X_rf_t = torch.FloatTensor(X_rf).to(device)
                        y_rf_t = torch.FloatTensor(y_rf).unsqueeze(1).to(device)
                        best_rf_loss = float("inf")
                        best_rf_state = None
                        rf_no_improve = 0
                        for ep in range(MAX_EPOCHS):
                            model.train()
                            perm = torch.randperm(len(X_rf_t))
                            for start in range(0, len(perm), BATCH_SIZE):
                                idx = perm[start:start + BATCH_SIZE]
                                optimizer.zero_grad()
                                pred = model(X_rf_t[idx])
                                loss = criterion(pred, y_rf_t[idx])
                                loss.backward()
                                optimizer.step()
                            model.eval()
                            with torch.no_grad():
                                val_loss = criterion(model(X_rf_t), y_rf_t).item()
                            if val_loss < best_rf_loss - 1e-6:
                                best_rf_loss = val_loss
                                best_rf_state = {k: v.clone() for k, v in model.state_dict().items()}
                                rf_no_improve = 0
                            else:
                                rf_no_improve += 1
                            if rf_no_improve >= PATIENCE:
                                break
                        if best_rf_state:
                            model.load_state_dict(best_rf_state)
                        model.eval()
                    except Exception:
                        pass  # keep previous model

        fp = np.asarray(fold_preds)
        ft = np.asarray(fold_truths)
        fold_mse = float(np.mean((fp - ft) ** 2)) if len(fp) else float("nan")
        fold_results.append({
            "fold": fold_idx,
            "n_test": len(fp),
            "mse_logrv": fold_mse,
            "best_train_loss": best_loss,
            "epochs_trained": epoch + 1,
        })

    preds_arr = np.asarray(preds)
    truths_arr = np.asarray(truths)
    aggregate_mse = (
        float(np.mean((preds_arr - truths_arr) ** 2)) if len(preds_arr) else float("nan")
    )
    forecasts = pd.Series(
        preds_arr, index=pd.DatetimeIndex(pred_dates), name="lstm_logrv_pred"
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


# -- Evaluation helpers -------------------------------------------------------

def _sharpe_ann(returns: np.ndarray) -> float:
    if len(returns) < 10:
        return float("nan")
    mu = float(np.mean(returns))
    sigma = float(np.std(returns, ddof=1))
    return (mu / sigma) * np.sqrt(365) if sigma > 1e-12 else float("nan")


def _joined_or_sentinel(series_pair: tuple, row_extra: dict) -> tuple | None:
    """`joined_pair_errors` wrapper that records the refusal instead of dying.

    A ValueError from the shared-target check means the two walk-forwards did
    not observe the same realised quantity on their common dates: the DM is
    refused (TARGET_MISMATCH) rather than silently run on mispaired errors.
    """
    try:
        return joined_pair_errors(*series_pair)
    except ValueError as exc:
        row_extra.setdefault("dm_target_refusal", str(exc))
        return None


def evaluate_one_combo(
    coin: str,
    horizon: int,
    seed: int,
    hidden_size: int = HIDDEN_SIZE,
    oos_strict_year: int | None = None,
    loss_fn: str = "linear",
    refit_every: int = REFIT_EVERY,
) -> dict | None:
    """Run LSTM vs HAR Classic for one (coin, horizon, seed) combo.

    If oos_strict_year is set, data on/after Jan 1st of that year is held out
    from training/walk-forward (reserved for separate OOS verdict).

    loss_fn selects the DM loss: "mse"/"mae" (precision) are the §C conjunction
    jambe per the #11010 amendment; "linear" (signed) is the bias control only.

    refit_every controls the walk-forward refit cadence (test days between
    LSTM retrains). The legacy research config is 22d; the §C run uses a
    documented 110d cadence to keep the LSTM sweep tractable (the 22d cadence
    retrains ~85 LSTMs per combo, ~50 min/combo on the RTX 3070 — infeasible
    for a 12-combo multi-seed §C validation). The REGISTRY entry records the
    cadence used.
    """
    import torch

    torch.manual_seed(seed)
    np.random.seed(seed)

    hourly_rets = _load_one_coin(coin)
    if oos_strict_year is not None:
        cutoff = pd.Timestamp(f"{oos_strict_year}-01-01", tz=hourly_rets.index.tz)
        hourly_rets = hourly_rets[hourly_rets.index < cutoff]
    if len(hourly_rets) < 1000:
        return None

    rv = daily_realized_variance(hourly_rets)
    if len(rv) < 300:
        return None

    features, rv_aligned = prepare_features(hourly_rets)
    if len(features) < 200:
        return None

    # HAR Classic baseline (raw + train-calibrated legs, #1454 cluster protocol)
    try:
        har_out = walk_forward_har(rv, horizon=horizon, n_splits=N_SPLITS, refit_every=REFIT_EVERY)
        har_cal_out = walk_forward_har(
            rv, horizon=horizon, n_splits=N_SPLITS, refit_every=REFIT_EVERY,
            calibrate_bias=True,
        )
    except Exception:
        return None

    # LSTM
    try:
        lstm_out = walk_forward_lstm(
            features, rv_aligned, horizon=horizon,
            n_splits=N_SPLITS, refit_every=refit_every,
            seed=seed, hidden_size=hidden_size,
        )
    except Exception as e:
        print(f"    LSTM failed: {e}", flush=True)
        return None

    har_fc = har_out["forecasts"]
    lstm_fc = lstm_out["forecasts"]
    common_fc_idx = har_fc.index.intersection(lstm_fc.index)
    if len(common_fc_idx) < 30:
        return None
    har_fc = har_fc.loc[common_fc_idx]
    lstm_fc = lstm_fc.loc[common_fc_idx]

    # Daily close returns
    daily_rets = hourly_rets.groupby(hourly_rets.index.normalize()).sum().rename("r_daily")
    daily_rets.index = pd.DatetimeIndex(daily_rets.index).normalize()
    daily_rets = daily_rets.reindex(common_fc_idx).dropna()
    if len(daily_rets) < 30:
        return None
    har_fc = har_fc.reindex(daily_rets.index)
    lstm_fc = lstm_fc.reindex(daily_rets.index)

    # Kelly weights for each model
    har_pair = _kelly_weights_and_returns(daily_rets, har_fc, MU_WINDOW, KELLY_CAP)
    lstm_pair = _kelly_weights_and_returns(daily_rets, lstm_fc, MU_WINDOW, KELLY_CAP)
    if har_pair is None or lstm_pair is None:
        return None
    har_w, r = har_pair
    lstm_w, _ = lstm_pair
    if len(r) < 50:
        return None

    # Net returns at FEE_BPS
    har_net = _net_at_fee(har_w, r, FEE_BPS)
    lstm_net = _net_at_fee(lstm_w, r, FEE_BPS)
    bh_net = r.copy()

    # Sharpe
    sharpe_har = _sharpe_ann(har_net)
    sharpe_lstm = _sharpe_ann(lstm_net)
    sharpe_bh = _sharpe_ann(bh_net)
    delta_sharpe_lstm_vs_har = sharpe_lstm - sharpe_har

    # LW2008 paired Sharpe-diff SE
    _, _, _, se = ledoit_wolf_sharpe_diff_se(lstm_net, har_net)
    t_stat = delta_sharpe_lstm_vs_har / se if isinstance(se, float) and se > 1e-12 else float("nan")

    # MSE comparison on log-RV
    target = har_out["targets"].reindex(common_fc_idx).dropna()
    har_pred_aligned = har_fc.reindex(target.index)
    lstm_pred_aligned = lstm_fc.reindex(target.index)
    mse_har = float(np.mean((har_pred_aligned - target) ** 2))
    mse_lstm = float(np.mean((lstm_pred_aligned - target) ** 2))
    mse_reduction_pct = (mse_lstm - mse_har) / mse_har * 100 if mse_har > 0 else float("nan")

    # Diebold-Mariano legs (pr-review §C + #1454 cluster protocol).
    # errors_model = LSTM, errors_baseline = HAR: dm < 0 => LSTM wins.
    # All DM legs join the two walk-forwards on their common ORIGIN dates and
    # validate the shared targets first (#18190 protocol, ported from M4 PR
    # #18650): positional pairing silently compares different days as soon as
    # the two date indexes diverge (fold skips, the NaN guard at LSTM
    # prediction time drops days HAR still forecasts).
    dm_info: dict = {"dm_stat": float("nan"), "dm_pvalue": float("nan"),
                     "mean_loss_diff": float("nan"), "dm_verdict": "N/A"}
    row_extra: dict = {}
    raw_join = _joined_or_sentinel(
        (lstm_out["forecasts"], lstm_out["targets"],
         har_out["forecasts"], har_out["targets"]),
        row_extra,
    )
    cal_join = _joined_or_sentinel(
        (lstm_out["forecasts"], lstm_out["targets"],
         har_cal_out["forecasts"], har_cal_out["targets"]),
        row_extra,
    )
    har_bias_oos: float = float("nan")
    har_errors: list = []
    lstm_errors: list = []
    if raw_join is not None and cal_join is not None and min(
        raw_join["n_joined"], cal_join["n_joined"]
    ) >= 10:
        har_err = raw_join["b_errors"]
        lstm_err = raw_join["a_errors"]
        # Issue #12734 (slice 2/2): persist the OOS bias and the raw errors
        # that actually fed the DM legs, so the debiased/centered re-analysis
        # runs post-hoc without re-executing the sweep.
        har_bias_oos = float(np.mean(har_err))
        har_errors = har_err.tolist()
        lstm_errors = lstm_err.tolist()
        try:
            dm = diebold_mariano_test(
                lstm_err, har_err, loss_fn=loss_fn, horizon=horizon
            )
            cal_dm = diebold_mariano_test(
                raw_join["a_errors"], cal_join["b_errors"],
                loss_fn=loss_fn, horizon=horizon,
            )
            dm_info.update({
                "dm_stat": float(dm.dm_statistic),
                "dm_pvalue": float(dm.p_value),
                "mean_loss_diff": float(dm.mean_loss_diff),
                "dm_verdict": _dm_verdict_label(dm.p_value, dm.mean_loss_diff),
                "calibrated_dm_stat": float(cal_dm.dm_statistic),
                "calibrated_dm_pvalue": float(cal_dm.p_value),
                "calibrated_dm_mean_loss_diff": float(cal_dm.mean_loss_diff),
                "calibrated_dm_verdict": _dm_verdict_label(
                    cal_dm.p_value, cal_dm.mean_loss_diff
                ),
                "dm_raw_n_aligned": raw_join["n_joined"],
                "dm_cal_n_aligned": cal_join["n_joined"],
                "dm_target_gap_max": max(
                    raw_join["target_gap_max"], cal_join["target_gap_max"]
                ),
            })
        except ValueError:
            dm_info.update({
                "dm_verdict": "DM_FAILED",
                "calibrated_dm_verdict": "DM_FAILED",
            })
    elif raw_join is None or cal_join is None:
        dm_info.update({
            "dm_verdict": "TARGET_MISMATCH",
            "calibrated_dm_verdict": "TARGET_MISMATCH",
        })
    else:
        dm_info.update({
            "dm_verdict": "INSUFFICIENT_DATA",
            "calibrated_dm_verdict": "INSUFFICIENT_DATA",
        })

    # Bias report + precision leg (Epic #1454, pattern M4): MSE = bias^2 +
    # variance lets an edge be carried by baseline miscalibration (#12745
    # measured har_bias_oos around -0.23 on BTC). The centered-DM leg isolates
    # the pure variance differential (#10961).
    lstm_decomp = (
        _mse_decomposition(raw_join["a_errors"]) if raw_join is not None else {}
    )
    har_decomp_raw = (
        _mse_decomposition(raw_join["b_errors"]) if raw_join is not None else {}
    )
    if raw_join is not None:
        dm_centered = _dm_centered_mse(
            raw_join["a_errors"], raw_join["b_errors"], horizon=horizon
        )
        n_aligned_centered = raw_join["n_joined"]
    else:
        dm_centered = {
            "dm_stat": float("nan"),
            "dm_pvalue": float("nan"),
            "dm_verdict": "TARGET_MISMATCH",
            "mean_loss_diff": float("nan"),
        }
        n_aligned_centered = 0

    # Per-observation persistence (lesson #12684): out-of-bias (recentred
    # error) DM re-validation and direct bias attribution require the forecast
    # series themselves, not only aggregates. All three arrays are aligned on
    # target.index before the finite filter.
    tgt_vals = target.values.astype(float)
    lstm_vals = lstm_pred_aligned.values.astype(float)
    har_vals = har_pred_aligned.values.astype(float)
    fin = np.isfinite(tgt_vals) & np.isfinite(lstm_vals) & np.isfinite(har_vals)
    persistence = {
        "lstm_bias_oos": (
            float(np.mean(lstm_vals[fin] - tgt_vals[fin])) if fin.any() else float("nan")
        ),
        "har_bias_oos": (
            float(np.mean(har_vals[fin] - tgt_vals[fin])) if fin.any() else float("nan")
        ),
        "pred_dates": [
            d.strftime("%Y-%m-%d") for d, f in zip(target.index, fin) if f
        ],
        "pred_lstm": [float(x) for x in lstm_vals[fin]],
        "pred_har": [float(x) for x in har_vals[fin]],
        "pred_target": [float(x) for x in tgt_vals[fin]],
    }

    return {
        "coin": coin,
        "horizon": horizon,
        "seed": seed,
        "sharpe_har": sharpe_har,
        "sharpe_lstm": sharpe_lstm,
        "sharpe_bh": sharpe_bh,
        "delta_sharpe_lstm_vs_har": delta_sharpe_lstm_vs_har,
        "lw_se": se,
        "t_stat": t_stat,
        "mse_har": mse_har,
        "mse_lstm": mse_lstm,
        "mse_reduction_pct": mse_reduction_pct,
        "loss_fn": loss_fn,
        "n_obs": len(r),
        "lstm_preds": len(lstm_fc),
        "har_preds": len(har_fc),
        "har_bias_oos": har_bias_oos,
        "har_errors": har_errors,
        "lstm_errors": lstm_errors,
        "har_calibrated_mse_logrv": float(har_cal_out["aggregate_mse_logrv"]),
        "lstm_debiased_mse_logrv": lstm_decomp.get("variance", float("nan")),
        "har_debiased_mse_logrv": har_decomp_raw.get("variance", float("nan")),
        "edge_calibrated_pct": (
            (har_cal_out["aggregate_mse_logrv"] - mse_lstm)
            / har_cal_out["aggregate_mse_logrv"] * 100
            if np.isfinite(har_cal_out["aggregate_mse_logrv"])
            and har_cal_out["aggregate_mse_logrv"] > 0
            else float("nan")
        ),
        "edge_debiased_pct": (
            (har_decomp_raw.get("variance", float("nan"))
             - lstm_decomp.get("variance", float("nan")))
            / har_decomp_raw["variance"] * 100
            if raw_join is not None
            and np.isfinite(har_decomp_raw.get("variance", float("nan")))
            and har_decomp_raw.get("variance", 0.0) > 0
            else float("nan")
        ),
        "lstm_bias_sq": lstm_decomp.get("bias_sq", float("nan")),
        "lstm_variance": lstm_decomp.get("variance", float("nan")),
        "har_bias_sq_raw": har_decomp_raw.get("bias_sq", float("nan")),
        "har_variance_raw": har_decomp_raw.get("variance", float("nan")),
        "har_bias_share_of_mse": (
            har_decomp_raw["bias_sq"] / har_decomp_raw["mse"]
            if raw_join is not None
            and np.isfinite(har_decomp_raw.get("mse", float("nan")))
            and har_decomp_raw.get("mse", 0.0) > 0
            else float("nan")
        ),
        "dm_centered_stat": dm_centered["dm_stat"],
        "dm_centered_pvalue": dm_centered["dm_pvalue"],
        "dm_centered_verdict": dm_centered["dm_verdict"],
        "dm_centered_mean_loss_diff": dm_centered.get(
            "mean_loss_diff", float("nan")
        ),
        "n_aligned_centered": int(n_aligned_centered),
        "dm_target_refusal": row_extra.get("dm_target_refusal", ""),
        **dm_info,
        **persistence,
    }


def _dm_verdict_label(p_value: float, mean_loss_diff: float) -> str:
    """Label a DM outcome: BEATS / BEATEN BY baseline / INCONCLUSIVE.

    mean_loss_diff < 0 => LSTM loss lower than HAR (LSTM wins). Mirrors the
    sign convention of scripts/dm_test.py dm_verdict().
    """
    if p_value < 0.05 and mean_loss_diff < 0:
        return "BEATS baseline"
    if p_value < 0.05 and mean_loss_diff > 0:
        return "BEATEN BY baseline"
    return "INCONCLUSIVE"


def _csv_list(value: str) -> list[str]:
    return [s.strip() for s in value.split(",") if s.strip()]


def _csv_int_list(value: str) -> list[int]:
    return [int(s.strip()) for s in value.split(",") if s.strip()]


def _sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _write_cluster_manifest(
    manifest_path: Path,
    all_rows: list[dict],
    per_coin_horizon: dict[str, dict],
    out_path: Path,
    args: argparse.Namespace,
    elapsed_s: float,
) -> None:
    """Compact in-repo cluster manifest (results-artifact-policy #15890).

    The full run JSON embeds per-observation forecast series and exceeds the
    512 KB CI bar; the manifest keeps every verdict, the per-combo alignment
    diagnostics and per-coin SHA-256 anchors of the full rows, so the
    aggregate stays falsifiable in-repo without shipping the series.
    """
    per_coin: dict[str, list[dict]] = {}
    for r in all_rows:
        per_coin.setdefault(r["coin"], []).append(r)

    alignment = []
    for key, cell in sorted(per_coin_horizon.items()):
        coin, h = key.split("|h=")
        seed_rows = [r for r in per_coin.get(coin, []) if r.get("horizon") == int(h)]
        n_joined = [
            r.get("dm_cal_n_aligned") for r in seed_rows
            if r.get("dm_cal_n_aligned") is not None
        ]
        gaps = [
            r.get("dm_target_gap_max") for r in seed_rows
            if r.get("dm_target_gap_max") is not None
        ]
        alignment.append({
            "cell": key,
            "dm_cal_n_aligned_min": min(n_joined) if n_joined else None,
            "dm_cal_n_aligned_max": max(n_joined) if n_joined else None,
            "dm_target_gap_max": max(gaps) if gaps else None,
            "n_target_mismatch": cell.get("n_target_mismatch", 0),
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
            "horizons": args.horizons if args.horizons is not None else HORIZONS,
            "seeds": args.seeds if args.seeds is not None else SEEDS,
            "window": WINDOW,
            "hidden_size": args.hidden_size,
            "n_splits": N_SPLITS,
            "refit_every": args.refit_every,
            "loss_fn": args.loss_fn,
            "fee_bps": args.fee_bps,
        },
        "elapsed_s": elapsed_s,
        "total_rows": len(all_rows),
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
        "aggregated": per_coin_horizon,
    }
    manifest_path.parent.mkdir(parents=True, exist_ok=True)
    manifest_path.write_text(json.dumps(manifest, indent=2), encoding="utf-8")
    print(f"[manifest] wrote {manifest_path} ({manifest_path.stat().st_size} bytes)")


def main() -> None:
    global FEE_BPS
    parser = argparse.ArgumentParser(description="M15 Log-LSTM RV sweep")
    parser.add_argument("--dry-run", action="store_true", help="Run BTC h=1 seed=0 only")
    parser.add_argument("--hidden-size", type=int, default=HIDDEN_SIZE,
                        help=f"LSTM hidden size (default: {HIDDEN_SIZE})")
    parser.add_argument(
        "--seeds",
        type=_csv_int_list,
        default=None,
        help="Comma-separated seeds override (default: 0,1,7,42)",
    )
    parser.add_argument(
        "--coins",
        type=_csv_list,
        default=None,
        help="Comma-separated coins override (default: BTC/ETH/SOL/LTC/XRP/ADA/DOT)",
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
        help="Override results directory (default: results/m15_lstm_rv_h{hidden_size}/)",
    )
    parser.add_argument(
        "--loss-fn",
        type=str,
        default="linear",
        choices=["linear", "mse", "mae"],
        help=(
            "DM loss function. §C (amended #11010): mse/mae (precision) are the "
            "conjunction jambe; linear (signed) is the bias control, never the "
            "conjunction jambe. Default: linear."
        ),
    )
    parser.add_argument(
        "--refit-every",
        type=int,
        default=REFIT_EVERY,
        help=(
            f"Walk-forward refit cadence in test days (default: {REFIT_EVERY}, "
            "the legacy research config). The §C run uses a documented 110d "
            "cadence: the 22d cadence retrains ~85 LSTMs per combo (~50 min/combo), "
            "infeasible for a multi-seed §C sweep."
        ),
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
    parser.add_argument(
        "--manifest-out",
        type=Path,
        default=None,
        help=(
            "Write the compact cluster manifest (verdicts + alignment "
            "diagnostics + per-coin SHA anchors of the full rows) to this "
            "path, per the results-artifact policy #15890."
        ),
    )
    parser.add_argument(
        "--fee-bps",
        type=float,
        default=FEE_BPS,
        help=(
            "Round-trip transaction cost in basis points applied to the Kelly "
            "weights before every economic metric (Sharpe, delta-Sharpe, "
            "verdict). Default: %(default)s, the conservative crypto regime "
            "this sweep was first measured under. §C names 10bps for crypto "
            "(5bps SPY), so a verdict read against §C must state which regime "
            "produced it -- a NO BEATS at 50bps and a NO BEATS at 10bps are "
            "different claims, and neither substitutes for the other."
        ),
    )
    args = parser.parse_args()

    FEE_BPS = args.fee_bps

    hidden_size = args.hidden_size
    coins = args.coins if args.coins is not None else COINS
    horizons = args.horizons if args.horizons is not None else HORIZONS
    seeds = args.seeds if args.seeds is not None else SEEDS
    oos_strict_year = args.oos_strict
    loss_fn = args.loss_fn
    refit_every = args.refit_every

    import torch
    print(f"PyTorch {torch.__version__}, CUDA: {torch.cuda.is_available()}")
    if torch.cuda.is_available():
        print(f"  GPU: {torch.cuda.get_device_name(0)}")

    model_demo = build_lstm(3, hidden_size, NUM_LAYERS)
    n_params = count_params(model_demo)
    print(f"LSTM params: {n_params} (hidden={hidden_size}, layers={NUM_LAYERS}, window={WINDOW})")

    results_dir = (
        args.output
        if args.output is not None
        else SCRIPT_DIR / "results" / f"m15_lstm_rv_h{hidden_size}"
    )
    results_dir.mkdir(parents=True, exist_ok=True)
    t0 = time.time()

    checkpoint_path = results_dir / "checkpoint.jsonl"
    combos: list[dict] = []
    completed_keys: set[tuple] = set()
    if checkpoint_path.exists():
        with open(checkpoint_path, "r") as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                row = json.loads(line)
                combos.append(row)
                completed_keys.add((row["coin"], row["horizon"], row["seed"]))
        print(f"[CHECKPOINT] resumed {len(combos)} combos from {checkpoint_path.name}", flush=True)

    total = len(coins) * len(horizons) * len(seeds)
    done = 0

    if args.dry_run:
        print("[DRY RUN] BTC-USD h=1 seed=0 only")
        row = evaluate_one_combo("BTC-USD", 1, 0, hidden_size=hidden_size,
                                 oos_strict_year=oos_strict_year, loss_fn=loss_fn,
                                 refit_every=refit_every)
        if row:
            combos.append(row)
            print(json.dumps(row, indent=2))
        return

    if oos_strict_year is not None:
        print(f"[OOS-STRICT] Holding out data >= {oos_strict_year}-01-01")

    for coin in coins:
        for h in horizons:
            for seed in seeds:
                done += 1
                key = (coin, h, seed)
                if key in completed_keys:
                    print(f"\n[{done}/{total}] {coin} h={h} seed={seed} -- SKIP (checkpoint)", flush=True)
                    continue
                print(f"\n[{done}/{total}] {coin} h={h} seed={seed}", flush=True)
                row = evaluate_one_combo(coin, h, seed, hidden_size=hidden_size,
                                         oos_strict_year=oos_strict_year,
                                         loss_fn=loss_fn, refit_every=refit_every)
                if row is not None:
                    combos.append(row)
                    with open(checkpoint_path, "a") as f:
                        f.write(json.dumps(row, default=str) + "\n")
                else:
                    print(f"  SKIPPED (insufficient data)", flush=True)

    elapsed = time.time() - t0
    print(f"\n{'='*60}")
    print(f"M15 LSTM RV sweep complete: {len(combos)}/{total} combos in {elapsed:.0f}s")

    # Aggregate sign-test
    n_combos = len(combos)
    n_lstm_beats_har = sum(1 for r in combos if r["delta_sharpe_lstm_vs_har"] > 0)
    median_delta = float(np.median([r["delta_sharpe_lstm_vs_har"] for r in combos])) if combos else float("nan")
    median_mse = float(np.median([r["mse_reduction_pct"] for r in combos])) if combos else float("nan")
    p_sign = _binomial_pvalue_one_sided(n_lstm_beats_har, n_combos)

    # Per-coin aggregation
    per_coin: dict[str, dict] = {}
    for r in combos:
        c = r["coin"]
        per_coin.setdefault(c, {"deltas": [], "mses": []})
        per_coin[c]["deltas"].append(r["delta_sharpe_lstm_vs_har"])
        per_coin[c]["mses"].append(r["mse_reduction_pct"])

    # Per-horizon aggregation
    per_horizon: dict[int, dict] = {}
    for r in combos:
        h = r["horizon"]
        per_horizon.setdefault(h, {"deltas": [], "mses": []})
        per_horizon[h]["deltas"].append(r["delta_sharpe_lstm_vs_har"])
        per_horizon[h]["mses"].append(r["mse_reduction_pct"])

    print(f"\nSign-test: {n_lstm_beats_har}/{n_combos} ({n_lstm_beats_har/n_combos*100:.1f}%) LSTM>HAR")
    print(f"  p-value = {p_sign:.4f}")
    print(f"  median delta-Sharpe = {median_delta:+.4f}")
    print(f"  median MSE change = {median_mse:+.1f}%")
    print(f"\nPer-coin:")
    for c in coins:
        if c in per_coin:
            med = float(np.median(per_coin[c]["deltas"]))
            med_mse = float(np.median(per_coin[c]["mses"]))
            n_beats = sum(1 for d in per_coin[c]["deltas"] if d > 0)
            n_total = len(per_coin[c]["deltas"])
            print(f"  {c}: {med:+.4f} (MSE {med_mse:+.1f}%, beats {n_beats}/{n_total})")

    print(f"\nPer-horizon:")
    for h in HORIZONS:
        if h in per_horizon:
            med = float(np.median(per_horizon[h]["deltas"]))
            n_beats = sum(1 for d in per_horizon[h]["deltas"] if d > 0)
            n_total = len(per_horizon[h]["deltas"])
            print(f"  h={h}: {med:+.4f} ({n_beats}/{n_total})")

    # Verdict (G.2 strict)
    if p_sign < 0.05 and n_lstm_beats_har / max(n_combos, 1) >= 0.60:
        verdict = "BEATS"
    elif p_sign < 0.10 and n_lstm_beats_har / max(n_combos, 1) >= 0.55:
        verdict = "INCONCLUSIVE"
    else:
        verdict = "NO BEATS"

    print(f"\nVERDICT: {verdict} (p={p_sign:.4f}, win_rate={n_lstm_beats_har/n_combos*100:.1f}%)")

    # pr-review §C aggregation (per horizon, cross-seed).
    # Conjunction: edge >= 2*std cross-seed AND dm_p_median < 0.05, reported
    # separately (#10228). Dominance guard: any "BEATEN BY baseline" -> NO BEATS.
    # Sign convention: m15's mse_reduction_pct = (lstm - har)/har*100 is NEGATIVE
    # when LSTM improves MSE, the inverse of dlinear_vol.py (positive = model
    # better). edge_pct below restores the dlinear convention (positive = LSTM
    # reduces MSE) so the conjunction reads identically.
    # Cluster protocol (#1454, port #18190): each cell reports THREE legs --
    # raw HAR, train-calibrated HAR (offset removed), centered (variance-only
    # differential) -- so an edge carried by baseline miscalibration reads as
    # such instead of as model precision.
    def _nanmedian(vals: list[float]) -> float:
        return (
            float(np.nanmedian(vals))
            if any(np.isfinite(x) for x in vals) else float("nan")
        )

    def _sc_cell(rows: list[dict]) -> dict:
        p_raw = [r.get("dm_pvalue", float("nan")) for r in rows]
        p_cal = [r.get("calibrated_dm_pvalue", float("nan")) for r in rows]
        p_ctr = [r.get("dm_centered_pvalue", float("nan")) for r in rows]
        reduction_pcts = [r.get("mse_reduction_pct", float("nan")) for r in rows]
        edge_cal = [r.get("edge_calibrated_pct", float("nan")) for r in rows]
        ctr_diff = [r.get("dm_centered_mean_loss_diff", float("nan")) for r in rows]
        mean_reduction = (
            float(np.nanmean(reduction_pcts))
            if any(np.isfinite(x) for x in reduction_pcts) else float("nan")
        )
        edge_pct = -mean_reduction if np.isfinite(mean_reduction) else float("nan")
        edge_std_pct = (
            float(np.nanstd(reduction_pcts))
            if sum(1 for x in reduction_pcts if np.isfinite(x)) > 1 else 0.0
        )
        n_beaten = sum(1 for r in rows if r.get("dm_verdict") == "BEATEN BY baseline")
        n_beaten_cal = sum(
            1 for r in rows if r.get("calibrated_dm_verdict") == "BEATEN BY baseline"
        )
        n_mismatch = sum(
            1 for r in rows if r.get("dm_verdict") == "TARGET_MISMATCH"
        )
        dm_p_median = _nanmedian(p_raw)
        cal_p_median = _nanmedian(p_cal)
        ctr_p_median = _nanmedian(p_ctr)
        mean_edge_cal = (
            float(np.nanmean(edge_cal))
            if any(np.isfinite(x) for x in edge_cal) else float("nan")
        )
        ctr_median = _nanmedian(ctr_diff)
        if n_beaten > 0:
            verdict_sc = "NO BEATS"
        elif edge_pct >= 2.0 * edge_std_pct and dm_p_median < 0.05:
            verdict_sc = "BEATS"
        else:
            verdict_sc = "INCONCLUSIVE"
        if n_beaten_cal > 0:
            verdict_cal = "NO BEATS"
        elif (
            np.isfinite(mean_edge_cal) and mean_edge_cal > 0 and cal_p_median < 0.05
        ):
            verdict_cal = "BEATS"
        else:
            verdict_cal = "INCONCLUSIVE"
        if ctr_p_median < 0.05 and np.isfinite(ctr_median):
            verdict_ctr = "BEATS (variance)" if ctr_median < 0 else "BEATEN (variance)"
        else:
            verdict_ctr = "INCONCLUSIVE"
        return {
            "mean_reduction_pct": mean_reduction,
            "edge_pct": edge_pct,
            "edge_std_pct": edge_std_pct,
            "dm_p_median": dm_p_median,
            "n_beaten": n_beaten,
            "n_rows": len(rows),
            "verdict_sc": verdict_sc,
            "edge_calibrated_pct_mean": mean_edge_cal,
            "calibrated_dm_p_median": cal_p_median,
            "n_beaten_calibrated": n_beaten_cal,
            "verdict_sc_calibrated": verdict_cal,
            "dm_centered_p_median": ctr_p_median,
            "dm_centered_mean_loss_diff_median": ctr_median,
            "verdict_sc_centered": verdict_ctr,
            "n_target_mismatch": n_mismatch,
        }

    per_horizon_sc: dict[int, dict] = {}
    for h in horizons:
        h_rows = [r for r in combos if r["horizon"] == h]
        if not h_rows:
            continue
        cell = _sc_cell(h_rows)
        per_horizon_sc[h] = cell
        print(f"\n§C h={h}: edge={cell['edge_pct']:+.1f}% (σ={cell['edge_std_pct']:.2f}) "
              f"dm_p_median={cell['dm_p_median']:.4f} beaten={cell['n_beaten']} "
              f"-> raw={cell['verdict_sc']} | cal={cell['verdict_sc_calibrated']} "
              f"(p={cell['calibrated_dm_p_median']:.4f}) | "
              f"centered={cell['verdict_sc_centered']} "
              f"(p={cell['dm_centered_p_median']:.4f})")

    per_coin_horizon_sc: dict[str, dict] = {}
    for coin in coins:
        for h in horizons:
            ch_rows = [
                r for r in combos if r["coin"] == coin and r["horizon"] == h
            ]
            if ch_rows:
                per_coin_horizon_sc[f"{coin}|h={h}"] = _sc_cell(ch_rows)

    # Save
    results = {
        "model": "Log-LSTM RV",
        "reference": "LSTM (Hochreiter & Schmidhuber 1997) applied to log-realized variance",
        "kelly_cap": KELLY_CAP,
        "fee_bps": FEE_BPS,
        "mu_window": MU_WINDOW,
        "n_splits": N_SPLITS,
        "refit_every": refit_every,
        "window": WINDOW,
        "hidden_size": hidden_size,
        "num_layers": NUM_LAYERS,
        "n_params": n_params,
        "n_combos": n_combos,
        "n_lstm_beats_har": n_lstm_beats_har,
        "win_rate": n_lstm_beats_har / max(n_combos, 1),
        "p_sign": p_sign,
        "median_delta_sharpe": median_delta,
        "median_mse_change_pct": median_mse,
        "verdict": verdict,
        "loss_fn": loss_fn,
        "per_horizon_sc": per_horizon_sc,
        "per_coin_horizon_sc": per_coin_horizon_sc,
        "runtime_s": elapsed,
        "combos": combos,
    }

    with open(results_dir / "results.json", "w") as f:
        json.dump(results, f, indent=2, default=str)

    # CSV
    df = pd.DataFrame(combos)
    df.to_csv(results_dir / "m15_lstm_rv_results.csv", index=False)

    if args.manifest_out is not None:
        _write_cluster_manifest(
            args.manifest_out, combos, per_coin_horizon_sc,
            results_dir / "results.json", args, elapsed,
        )

    print(f"\nResults saved to {results_dir}")


if __name__ == "__main__":
    main()
