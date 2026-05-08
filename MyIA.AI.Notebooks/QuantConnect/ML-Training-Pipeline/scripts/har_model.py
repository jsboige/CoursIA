"""HAR (Heterogeneous Autoregressive) volatility model — Corsi (2009).

The HAR model is the *gold-standard* baseline for daily realized-variance
forecasting and outperforms GARCH(1,1) on most equity / FX / crypto datasets
in the literature. It is a simple OLS:

    log RV_{t+1} = β0 + β_d * log(RV_t)
                  + β_w * mean_{i=1..5}  log(RV_{t-i+1})
                  + β_m * mean_{i=1..22} log(RV_{t-i+1})
                  + ε

This module supplies:
- `HARModel`: in-sample fit / forecast at horizon h with iterative one-step rollout
- `walk_forward_har`: walk-forward 5-fold evaluation, MSE on log-RV target
- Multi-step forecast via iterated rollout (no in-sample contamination)

References:
- Corsi (2009) "A Simple Approximate Long-Memory Model of Realized Volatility"
- Patton (2011) "Volatility Forecast Comparison Using Imperfect Volatility Proxies"
"""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np
import pandas as pd

from realized_variance import har_lag_features, realized_variance_to_log


@dataclass
class HARFit:
    coef: np.ndarray  # length 4: [intercept, beta_d, beta_w, beta_m]
    n_train: int
    in_sample_mse: float


class HARModel:
    """OLS HAR(1d, 5d, 22d) regression on log-RV."""

    def __init__(self) -> None:
        self.fit_: HARFit | None = None

    def fit(self, rv_train: pd.Series) -> "HARModel":
        feats = har_lag_features(rv_train).apply(realized_variance_to_log)
        target = realized_variance_to_log(rv_train).rename("y")
        df = pd.concat([feats, target], axis=1).dropna()
        if len(df) < 30:
            raise ValueError(f"HAR fit needs >=30 obs after lags, got {len(df)}")
        x = df[["rv_d", "rv_w", "rv_m"]].to_numpy()
        y = df["y"].to_numpy()
        x_aug = np.column_stack([np.ones(len(x)), x])
        coef, *_ = np.linalg.lstsq(x_aug, y, rcond=None)
        resid = y - x_aug @ coef
        self.fit_ = HARFit(coef=coef, n_train=len(df), in_sample_mse=float(np.mean(resid ** 2)))
        return self

    def predict_one_step(self, rv_history: pd.Series) -> float:
        """Predict log(RV_{t+1}) given the full RV history up to t."""
        if self.fit_ is None:
            raise RuntimeError("HARModel.predict_one_step called before fit()")
        if len(rv_history) < 22:
            raise ValueError(f"need >=22 history obs, got {len(rv_history)}")
        rv = rv_history.astype(float)
        log_rv = np.log(rv.clip(lower=1e-12))
        rv_d = float(log_rv.iloc[-1])
        rv_w = float(log_rv.iloc[-5:].mean())
        rv_m = float(log_rv.iloc[-22:].mean())
        x_aug = np.array([1.0, rv_d, rv_w, rv_m])
        return float(x_aug @ self.fit_.coef)

    def predict_h_step(self, rv_history: pd.Series, horizon: int) -> float:
        """Iterated h-step forecast on the log-RV scale.

        Returns the **average** of the h forecasted log-RVs (so it is comparable
        to a target defined as RV averaged over the next h days, which is the
        relevant horizon-h volatility proxy for risk and option pricing).
        """
        if horizon < 1:
            raise ValueError("horizon must be >= 1")
        history = list(rv_history.astype(float).values)
        forecasts: list[float] = []
        for _ in range(horizon):
            tail = pd.Series(history[-22:])
            log_rv = np.log(tail.clip(lower=1e-12))
            rv_d = float(log_rv.iloc[-1])
            rv_w = float(log_rv.iloc[-5:].mean())
            rv_m = float(log_rv.iloc[-22:].mean())
            x_aug = np.array([1.0, rv_d, rv_w, rv_m])
            log_pred = float(x_aug @ self.fit_.coef)
            forecasts.append(log_pred)
            history.append(float(np.exp(log_pred)))
        return float(np.mean(forecasts))


def _make_split_indices(n: int, n_splits: int) -> list[tuple[int, int, int]]:
    """Walk-forward expanding-window splits: returns (train_end, test_start, test_end)."""
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


def walk_forward_har(
    rv: pd.Series,
    horizon: int = 1,
    n_splits: int = 5,
    refit_every: int = 22,
) -> dict:
    """Walk-forward evaluation of HAR on a daily-RV series.

    Returns:
    - fold MSEs and aggregate MSE on the log-RV scale
    - aligned forecast series for downstream Diebold-Mariano testing
    - per-fold residual stats
    """
    rv = rv.dropna().astype(float)
    n = len(rv)
    if n < 200:
        raise ValueError(f"need >=200 daily obs, got {n}")
    log_rv = np.log(rv.clip(lower=1e-12))
    splits = _make_split_indices(n, n_splits)
    fold_results = []
    preds: list[float] = []
    truths: list[float] = []
    pred_dates: list[pd.Timestamp] = []
    for fold_idx, (train_end, test_start, test_end) in enumerate(splits):
        rv_train = rv.iloc[:train_end]
        if len(rv_train) < 60:
            continue
        model = HARModel().fit(rv_train)
        fold_preds: list[float] = []
        fold_truths: list[float] = []
        history = list(rv.iloc[:test_start].values)
        for i in range(test_start, test_end - horizon):
            target_window = log_rv.iloc[i:i + horizon].mean()
            tail = pd.Series(history[-(22 + horizon):])
            log_pred = model.predict_h_step(tail, horizon=horizon)
            fold_preds.append(log_pred)
            fold_truths.append(float(target_window))
            preds.append(log_pred)
            truths.append(float(target_window))
            pred_dates.append(rv.index[i])
            history.append(float(rv.iloc[i]))
            if (i - test_start) % refit_every == 0 and i > test_start:
                model = HARModel().fit(rv.iloc[:i])
        fp = np.asarray(fold_preds)
        ft = np.asarray(fold_truths)
        fold_mse = float(np.mean((fp - ft) ** 2)) if len(fp) else float("nan")
        fold_results.append({
            "fold": fold_idx,
            "n_test": len(fp),
            "mse_logrv": fold_mse,
            "mean_resid": float(np.mean(fp - ft)) if len(fp) else float("nan"),
        })
    preds_arr = np.asarray(preds)
    truths_arr = np.asarray(truths)
    aggregate_mse = float(np.mean((preds_arr - truths_arr) ** 2)) if len(preds_arr) else float("nan")
    forecasts = pd.Series(preds_arr, index=pd.DatetimeIndex(pred_dates), name="har_logrv_pred")
    targets = pd.Series(truths_arr, index=pd.DatetimeIndex(pred_dates), name="logrv_target")
    return {
        "horizon": horizon,
        "n_splits": n_splits,
        "n_total_preds": len(preds_arr),
        "aggregate_mse_logrv": aggregate_mse,
        "fold_results": fold_results,
        "forecasts": forecasts,
        "targets": targets,
    }
