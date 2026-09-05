"""M18 — TimesFM 2.5 zero-shot vs classical baselines on realized variance.

Issue #14768: benchmark TimesFM 2.5 (Apache-2.0) against HAR / Log-HAR /
persistence / EWMA on daily realized variance, under the §C barème of
`pr-review-discipline.md` (walk-forward 5 folds, >=4 seeds, Diebold-Mariano
HAC+HLN, honest verdict BEATS / NO BEATS / INCONCLUSIVE).

Design mirrors `har_lj_asym.py` round-3/4 (M17):
- target = h-day mean of log-RV (`rolling(h).mean().shift(-h)`),
- expanding-window 5-fold walk-forward, fold_size = n // (n_splits + 1),
- per-fold bias calibration from the TRAIN TAIL ONLY, applied SYMMETRICALLY
  to every model as ``yhat_debiased = yhat + bias`` (round-3 sign fix),
- `bounds_train_test` provenance per (coin, horizon),
- panel hash on the canonical 360-bar window, forecast hashes per fold for
  cross-seed bit-identity audit.

Models (all predict the SAME target on the SAME test indices):
- persistence : last observed log-RV (naive random-walk baseline)
- ewma        : exponentially-weighted mean of log-RV, span selected on the
                train tail ONLY among {5, 10, 20, 60}
- log_har     : OLS HAR(1d,5d,22d) on log-RV lags (`har_model.HARModel`),
                iterated h-step path, prediction = mean of the log path
- har_rv      : same HAR structure fit on RV LEVELS (native RV-scale HAR),
                iterated h-step path in RV, prediction = log(mean RV path)
- tsfm        : TimesFM 2.5-200M zero-shot, batched per fold, direct
                multi-horizon path from the last `context_len` log-RV
                points, prediction = mean of the first h steps of the
                point path (point = median channel).

TimesFM tensor layout (verified empirically, see tests): the last axis of
the quantile output is ``[mean, q0.1, q0.2, ..., q0.9]`` — 10 channels —
and the point output equals channel 5 (the median). Quantile columns are
therefore addressed as ``1 + i`` over ``TSFM_QUANTILES``.

Fail-explicit contract (#14768 "gardes anti-faux modèle"): if the real
TimesFM checkpoint cannot be loaded or a forecast call raises, the script
aborts with a non-zero exit — there is NO fallback and nothing else may be
reported under the TimesFM label.

Usage:
    python m18_tsfm_benchmark.py --coins BTC-USD --skip-remote --debias \
        --horizons 1 5 22 --seeds 0 7 42 99 \
        --out-json scripts/results/m18_tsfm_benchmark.json
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

sys.path.insert(0, str(Path(__file__).resolve().parent))

RESULTS_DIR = Path(__file__).resolve().parent / "results"

from realized_variance import daily_realized_variance, realized_variance_to_log
from dm_test import dm_verdict
from har_model import HARModel
from har_asymmetric import _load_panel
from har_lj_asym import _panel_hash

HORIZONS_DEFAULT = [1, 5, 22]  # issue #14768 protocol (not the M4/M17 1/5/10)
SEEDS_DEFAULT = [0, 7, 42, 99]
N_SPLITS = 5
CALIBRATION_SIZE = 60  # train-tail size for per-fold bias estimation
REFIT_EVERY = 22
CONTEXT_LEN_DEFAULT = 512  # log-RV days fed to TimesFM (<= model 2048)
EWMA_SPAN_GRID = [5, 10, 20, 60]
TSFM_REPO_ID = "google/timesfm-2.5-200m-pytorch"
# TimesFM 2.5 native quantile head (model config, verified: [0.1..0.9]).
TSFM_QUANTILES = [0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9]
# Quantile tensor last axis = [mean, q0.1, ..., q0.9]: channel 0 is the mean
# head, quantile i lives at column 1 + i. Channel 5 == median == point output.
TSFM_QUANT_COL_OFFSET = 1
MODELS = ["persistence", "ewma", "log_har", "har_rv", "tsfm"]
BASELINES = [m for m in MODELS if m != "tsfm"]


# ---------------------------------------------------------------------------
# Metrics
# ---------------------------------------------------------------------------

def qlike_loss(rv_true: np.ndarray, rv_pred: np.ndarray) -> float:
    """Patton (2011) QLIKE robust loss on the RV scale.

    Both inputs must be strictly positive. Log-scale forecasts are converted
    with exp() upstream, which is always positive, so the guard is an
    assertion on the contract rather than a clipping workaround.
    """
    rv_true = np.asarray(rv_true, dtype=float)
    rv_pred = np.asarray(rv_pred, dtype=float)
    if np.any(rv_pred <= 0) or np.any(rv_true <= 0):
        raise ValueError("QLIKE requires strictly positive forecasts/targets")
    ratio = rv_true / rv_pred
    return float(np.mean(ratio - np.log(ratio) - 1.0))


def pinball_loss(y: np.ndarray, yhat_q: np.ndarray, q: float) -> float:
    """Mean pinball (quantile) loss at level q."""
    y = np.asarray(y, dtype=float)
    yhat_q = np.asarray(yhat_q, dtype=float)
    diff = y - yhat_q
    return float(np.mean(np.maximum(q * diff, (q - 1.0) * diff)))


def interval_coverage(
    y: np.ndarray, lower: np.ndarray, upper: np.ndarray
) -> tuple[float, float]:
    """Empirical coverage and mean width of a prediction interval."""
    y = np.asarray(y, dtype=float)
    lower = np.asarray(lower, dtype=float)
    upper = np.asarray(upper, dtype=float)
    if np.any(upper < lower):
        raise ValueError("upper band below lower band (quantile crossing)")
    coverage = float(np.mean((y >= lower) & (y <= upper)))
    width = float(np.mean(upper - lower))
    return coverage, width


# ---------------------------------------------------------------------------
# Baseline forecasters (deterministic, refit on expanding window)
# ---------------------------------------------------------------------------

def _har_rv_features(rv: pd.Series) -> pd.DataFrame:
    """Lagged daily / weekly / monthly means of RV LEVELS (Corsi 2009 plain spec).

    Shifted one step back, mirroring ``realized_variance.har_lag_features``:
    row t carries RV_{t-1}, mean(RV_{t-5..t-1}), mean(RV_{t-22..t-1}) so the
    regression in :meth:`HarRvModel.fit` forecasts RV_t from PAST RV only.
    Contemporaneous alignment regresses RV_t on RV_t — a perfect identity fit
    whose iterated forecast degenerates to persistence (#14791).
    """
    rv = rv.astype(float)
    return pd.DataFrame({
        "rv_d": rv.shift(1),
        "rv_w": rv.shift(1).rolling(5, min_periods=5).mean(),
        "rv_m": rv.shift(1).rolling(22, min_periods=22).mean(),
    })


class HarRvModel:
    """OLS HAR(1d,5d,22d) on RV levels with iterated h-step RV path."""

    def __init__(self) -> None:
        self.coef: np.ndarray | None = None

    def fit(self, rv_train: pd.Series) -> "HarRvModel":
        feats = _har_rv_features(rv_train)
        target = rv_train.rename("y")
        df = pd.concat([feats, target], axis=1).dropna()
        if len(df) < 30:
            raise ValueError(f"HAR-RV fit needs >=30 obs after lags, got {len(df)}")
        x = df[["rv_d", "rv_w", "rv_m"]].to_numpy()
        y = df["y"].to_numpy()
        x_aug = np.column_stack([np.ones(len(x)), x])
        self.coef, *_ = np.linalg.lstsq(x_aug, y, rcond=None)
        return self

    def _step_features(self, history: list[float]) -> np.ndarray:
        tail = pd.Series(history[-22:])
        return np.array([
            1.0,
            float(tail.iloc[-1]),
            float(tail.iloc[-5:].mean()),
            float(tail.iloc[-22:].mean()),
        ])

    def predict_h_step_mean_log(self, rv_history: pd.Series, horizon: int) -> float:
        """Iterated h-step RV path; returns log(mean of the RV path).

        The model forecasts natively in RV levels and is projected onto the
        common log-scale evaluation target as log(mean RV path) — the same
        functional of the future the other models predict in log space.
        """
        if self.coef is None:
            raise RuntimeError("HarRvModel.predict before fit()")
        history = list(rv_history.astype(float).values)
        path: list[float] = []
        for _ in range(horizon):
            rv_pred = float(self._step_features(history) @ self.coef)
            path.append(max(rv_pred, 1e-12))
            history.append(rv_pred)
        return float(np.log(np.mean(path)))


class TimesFMWrapper:
    """TimesFM 2.5-200M zero-shot forecaster with fail-explicit contract.

    ``loader`` is injected so tests can pass a deterministic fake; production
    code uses :meth:`production_loader`, which imports timesfm lazily and
    aborts on ANY failure — no silent fallback may ever serve forecasts
    under the TimesFM label (#14768 garde anti-faux modèle).
    """

    def __init__(self, repo_id: str, context_len: int,
                 loader=None, revision: str | None = None) -> None:
        self.repo_id = repo_id
        self.context_len = context_len
        self.n_calls = 0  # individual series actually served by the model
        self.revision = revision
        if loader is not None:
            self._model = loader(repo_id)
        else:
            self._model = None
        self._loader = loader

    @classmethod
    def production_loader(cls, repo_id: str, context_len: int) -> "TimesFMWrapper":
        import timesfm  # lazy: keeps torch off the test-import path
        from huggingface_hub import HfApi

        try:
            info = HfApi().model_info(repo_id)
            revision = getattr(info, "sha", None)
        except Exception as exc:  # provenance must not silently degrade
            raise RuntimeError(f"TimesFM provenance lookup failed for {repo_id}: {exc}")
        try:
            model = timesfm.TimesFM_2p5_200M_torch.from_pretrained(
                repo_id, torch_compile=False,
            )
            model.compile(timesfm.ForecastConfig(
                max_context=context_len, max_horizon=128,
                per_core_batch_size=32,
            ))
        except Exception as exc:
            raise RuntimeError(
                f"TimesFM checkpoint {repo_id} failed to load/compile — "
                f"aborting, no fallback allowed (#14768): {exc}"
            )
        wrapper = cls(repo_id=repo_id, context_len=context_len, revision=revision)
        wrapper._model = model
        return wrapper

    def forecast_paths(
        self, contexts: list[np.ndarray], horizon: int
    ) -> tuple[np.ndarray, np.ndarray]:
        """Batched forecast. Returns (point (B, h), quantiles (B, h, 1+9))."""
        if self._model is None:
            raise RuntimeError("TimesFM model not loaded — aborting (#14768)")
        point, quant = self._model.forecast(horizon=horizon, inputs=list(contexts))
        self.n_calls += len(contexts)
        point = np.asarray(point, dtype=float)[:, :horizon]
        quant = np.asarray(quant, dtype=float)[:, :horizon, :]
        if point.shape[1] < horizon or quant.shape[1] < horizon:
            raise RuntimeError(
                f"TimesFM returned shorter horizon than requested "
                f"({point.shape} < {horizon})"
            )
        if quant.shape[2] != TSFM_QUANT_COL_OFFSET + len(TSFM_QUANTILES):
            raise RuntimeError(
                f"TimesFM quantile axis has {quant.shape[2]} channels, expected "
                f"{TSFM_QUANT_COL_OFFSET + len(TSFM_QUANTILES)} ([mean, q0.1..q0.9])"
            )
        return point, quant


def _tsfm_batch_predictions(
    log_rv: np.ndarray, indices: list[int], horizon: int, tsfm: TimesFMWrapper,
) -> tuple[np.ndarray, np.ndarray]:
    """Batched zero-shot predictions at ``indices``.

    Returns (pred_mean_path (len,), quantiles_last_step (len, 1+9)). The
    point prediction is the mean of the first h steps of the median path;
    the quantiles are the native bands at step h. One forecast call per
    batch — the calibration pass and the OOS pass never re-forecast the
    same context twice.
    """
    contexts = [log_rv[max(0, i - tsfm.context_len):i].astype(np.float32)
                for i in indices]
    point, quant = tsfm.forecast_paths(contexts, horizon)
    preds = point[:, :horizon].mean(axis=1)
    return preds, quant[:, horizon - 1, :]


# ---------------------------------------------------------------------------
# Walk-forward harness — one protocol for ALL models (M17 round-3 symmetry)
# ---------------------------------------------------------------------------

def _rolling_predictions(
    model_name: str,
    log_rv: np.ndarray,
    rv: pd.Series,
    indices: list[int],
    horizon: int,
    refit_every: int = REFIT_EVERY,
    ewma_span: int | None = None,
) -> np.ndarray:
    """Rolling h-step predictions of the h-day mean log-RV at ``indices``.

    Deterministic models only (tsfm is batched separately). Strictly causal:
    the prediction for index i uses log_rv[:i] only — the target
    mean(log_rv[i:i+h]) is never touched.
    """
    preds = np.empty(len(indices), dtype=float)
    log_har: HARModel | None = None
    har_rv: HarRvModel | None = None
    last_fit = -10**9

    for out_i, i in enumerate(indices):
        if model_name in ("log_har", "har_rv") and i - last_fit >= refit_every:
            train = rv.iloc[:i]
            if model_name == "log_har":
                log_har = HARModel().fit(train)
            else:
                har_rv = HarRvModel().fit(train)
            last_fit = i

        if model_name == "persistence":
            preds[out_i] = log_rv[i - 1]
        elif model_name == "ewma":
            if ewma_span is None:
                raise ValueError("ewma model requires ewma_span")
            s = pd.Series(log_rv[:i])
            preds[out_i] = float(s.ewm(span=ewma_span).mean().iloc[-1])
        elif model_name == "log_har":
            assert log_har is not None
            preds[out_i] = log_har.predict_h_step(rv.iloc[:i], horizon=horizon)
        elif model_name == "har_rv":
            assert har_rv is not None
            preds[out_i] = har_rv.predict_h_step_mean_log(rv.iloc[:i], horizon=horizon)
        else:
            raise ValueError(f"unknown/non-deterministic model {model_name!r}")
    return preds


def _select_ewma_span(
    log_rv: np.ndarray, train_end: int, horizon: int,
    calibration_size: int = CALIBRATION_SIZE,
) -> int:
    """Pick the EWMA span minimizing train-tail MSE (train info only)."""
    cal_start = max(22 + horizon, train_end - calibration_size)
    idx = [i for i in range(cal_start, train_end) if i + horizon <= train_end]
    if not idx:
        return EWMA_SPAN_GRID[2]
    targets = np.array([log_rv[i:i + horizon].mean() for i in idx])
    series = pd.Series(log_rv[:train_end])
    ewm_all = {span: series.ewm(span=span).mean().values
               for span in EWMA_SPAN_GRID}
    best_span, best_mse = EWMA_SPAN_GRID[2], np.inf
    for span in EWMA_SPAN_GRID:
        preds = np.array([ewm_all[span][i - 1] for i in idx])
        mse = float(np.mean((preds - targets) ** 2))
        if mse < best_mse:
            best_span, best_mse = span, mse
    return best_span


def _fold_bounds(n: int, n_splits: int) -> list[dict[str, int]]:
    """Expanding-window folds, same arithmetic as har_model._make_split_indices.

    Target validity (``i + horizon <= n``) is enforced per index downstream;
    bounds themselves stay horizon-agnostic so the provenance always reports
    the full fold plan of the canonical splitter.
    """
    fold_size = n // (n_splits + 1)
    bounds = []
    for fold in range(n_splits):
        split = (fold + 1) * fold_size
        test_end = min(split + fold_size, n)
        if split >= test_end:
            break
        bounds.append({
            "fold_idx": int(fold),
            "train_end_idx": int(split),
            "oos_start_idx": int(split),
            "oos_end_idx": int(test_end),
            "n_train": int(split),
            "n_oos": int(test_end - split),
        })
    return bounds


def _sha256_array(arr: np.ndarray) -> str:
    return hashlib.sha256(
        np.ascontiguousarray(arr, dtype=np.float64).tobytes()
    ).hexdigest()


def assert_baselines_distinct(
    deb_arrays: dict[str, np.ndarray], threshold: float = 1e-6,
) -> float:
    """Non-degeneracy control (#14791): baselines declared as distinct models
    must actually differ.

    Two "different" baselines whose forecasts agree to machine precision on
    every OOS point carry no independent information — exactly the har_rv
    defect (identity fit == persistence at 5e-14). Unlike the forecast-hash
    control, which only separates bit-identical from not-bit-identical, this
    check CAN go red on the failure mode it guards against: relative
    agreement below ``threshold`` everywhere means same effective model, and
    the run aborts instead of publishing an empty column.

    Returns the weakest pairwise separation observed (the smallest, across
    baseline pairs, of each pair's maximum relative difference) — recorded in
    the manifest as provenance.
    """
    names = [m for m in BASELINES if m in deb_arrays]
    weakest = np.inf
    for i in range(len(names)):
        for j in range(i + 1, len(names)):
            a, b = names[i], names[j]
            pa, pb = deb_arrays[a], deb_arrays[b]
            denom = np.maximum(np.abs(pa), np.abs(pb))
            rel = np.abs(pa - pb) / np.maximum(denom, 1e-12)
            top = float(np.max(rel))
            weakest = min(weakest, top)
            if top < threshold:
                raise RuntimeError(
                    f"degenerate baselines (#14791): {a!r} and {b!r} agree to "
                    f"{top:.2e} (max relative over {len(pa)} OOS points) — "
                    f"below {threshold:g}: same effective model, the vs-{b} "
                    f"column carries no independent information")
    return float(weakest)


def run_config(
    coin: str,
    hourly_rets: pd.Series,
    horizon: int,
    seed: int,
    n_splits: int,
    calibration_size: int,
    refit_every: int,
    tsfm: TimesFMWrapper | None,
    debias: bool = True,
) -> dict:
    """One (coin, horizon, seed) evaluation of all models under one protocol."""
    rv = daily_realized_variance(hourly_rets).dropna()
    if len(rv) < 300:
        return {"coin": coin, "horizon": horizon, "seed": seed,
                "skipped": f"rv<300 ({len(rv)})"}

    log_rv_series = realized_variance_to_log(rv)
    log_rv = log_rv_series.to_numpy(dtype=float)
    n = len(log_rv)
    folds = _fold_bounds(n, n_splits)
    if not folds:
        return {"coin": coin, "horizon": horizon, "seed": seed,
                "skipped": f"no fold fits (n={n})"}
    # HAR monthly lag (22) + minimum fit size (30 post-lag) + margin: the
    # first fold's training window must clear the HAR lags or every refit
    # inside the walk-forward would raise.
    if folds[0]["train_end_idx"] < 100:
        return {"coin": coin, "horizon": horizon, "seed": seed,
                "skipped": f"first fold too short for HAR lags "
                           f"({folds[0]['train_end_idx']} days)"}

    rows: dict[str, dict] = {}
    fc_hashes: dict[str, list[str]] = {}
    per_fold_bias_out: dict[str, list[float]] = {}
    # tsfm-only: last-step native quantiles on the OOS points (per fold)
    tsfm_quant_folds: list[np.ndarray] = []
    tsfm_y_folds: list[np.ndarray] = []
    # per-model debiased OOS forecasts + common target, for in-situ DM
    deb_arrays: dict[str, np.ndarray] = {}
    tgt_concat: np.ndarray | None = None

    for model in MODELS:
        raw_all, deb_all, tgt_all = [], [], []
        biases: list[float] = []
        hashes: list[str] = []
        quant_folds: list[np.ndarray] = []
        y_folds: list[np.ndarray] = []

        for fold in folds:
            train_end = fold["train_end_idx"]
            oos = [i for i in range(fold["oos_start_idx"], fold["oos_end_idx"])
                   if i + horizon <= n]
            if not oos:
                continue

            # Per-fold train-tail bias (M17 round-3: debiased = yhat + bias,
            # estimated on the TRAIN TAIL only, never on OOS targets).
            cal_start = max(22 + horizon, train_end - calibration_size)
            cal_idx = [i for i in range(cal_start, train_end)
                       if i + horizon <= train_end]
            if cal_idx and debias:
                if model == "tsfm":
                    assert tsfm is not None
                    cal_pred, _ = _tsfm_batch_predictions(
                        log_rv, cal_idx, horizon, tsfm)
                else:
                    ewma_span = (_select_ewma_span(log_rv, train_end, horizon,
                                                   calibration_size)
                                 if model == "ewma" else None)
                    cal_pred = _rolling_predictions(
                        model, log_rv, rv.iloc[:train_end], cal_idx, horizon,
                        refit_every, ewma_span)
                cal_tgt = np.array([log_rv[i:i + horizon].mean() for i in cal_idx])
                bias = float(np.mean(cal_tgt - cal_pred))
            else:
                bias = 0.0
            biases.append(bias)

            if model == "tsfm":
                assert tsfm is not None
                oos_pred, quant_last = _tsfm_batch_predictions(
                    log_rv, oos, horizon, tsfm)
                quant_folds.append(quant_last)
                y_folds.append(log_rv[[i + horizon - 1 for i in oos]])
            else:
                ewma_span = (_select_ewma_span(log_rv, train_end, horizon,
                                               calibration_size)
                             if model == "ewma" else None)
                oos_pred = _rolling_predictions(
                    model, log_rv, rv, oos, horizon, refit_every, ewma_span)
            oos_tgt = np.array([log_rv[i:i + horizon].mean() for i in oos])

            raw_all.extend(oos_pred.tolist())
            deb_all.extend((oos_pred + bias).tolist())
            tgt_all.extend(oos_tgt.tolist())
            hashes.append(_sha256_array(oos_pred))

        raw = np.array(raw_all)
        deb = np.array(deb_all)
        tgt = np.array(tgt_all)
        rv_tgt = np.exp(tgt)  # RV-scale realized proxy for QLIKE
        rows[model] = {
            "mse_raw": float(np.mean((raw - tgt) ** 2)),
            "mse_debiased": float(np.mean((deb - tgt) ** 2)),
            "mae_debiased": float(np.mean(np.abs(deb - tgt))),
            "qlike_debiased": qlike_loss(rv_tgt, np.exp(deb)),
            "signed_bias_debiased": float(np.mean(deb - tgt)),
            "n_oos": int(len(tgt)),
        }
        fc_hashes[model] = hashes
        per_fold_bias_out[model] = biases
        deb_arrays[model] = deb
        tgt_concat = tgt
        if model == "tsfm":
            tsfm_quant_folds = quant_folds
            tsfm_y_folds = y_folds

    # Non-degeneracy control (#14791): a run where two declared baselines
    # agree below 1e-6 everywhere aborts here instead of publishing an
    # empty "vs X" column; the weakest separation is kept as provenance.
    baseline_weakest_rel_sep = assert_baselines_distinct(deb_arrays)

    # In-situ DM, two legs per amended §C (#11010): the CONJUNCTION verdict
    # uses a PRECISION loss ("mse"); the "linear" leg (raw signed errors) is
    # the bias-control diagnostic and is never the conjunction jambe. Both
    # run where the arrays live — never reconstructed from summaries.
    dm_out: dict[str, dict] = {}
    dm_linear_out: dict[str, dict] = {}
    for baseline in BASELINES:
        err_t = deb_arrays["tsfm"] - tgt_concat
        err_b = deb_arrays[baseline] - tgt_concat
        dm_out[baseline] = dm_verdict(err_t, err_b, horizon=horizon,
                                      loss_fn="mse")
        dm_linear_out[baseline] = dm_verdict(err_t, err_b, horizon=horizon,
                                             loss_fn="linear")

    out = {
        "coin": coin,
        "horizon": horizon,
        "seed": seed,
        "models": rows,
        "dm_vs_baselines_mse": dm_out,
        "dm_vs_baselines_linear": dm_linear_out,
        "per_fold_bias": per_fold_bias_out,
        "fc_hash_per_fold": fc_hashes,
        "baseline_weakest_rel_sep": baseline_weakest_rel_sep,
        "n_oos": rows[MODELS[0]]["n_oos"],
        "bounds_train_test": folds[0] | {
            "n_total": int(n),
            "fold_size": int(folds[0]["n_oos"]),
            "n_folds": int(len(folds)),
        },
        "panel_hash": _panel_hash(rv),
    }

    # TimesFM native quantile evaluation at step h. The quantiles target
    # realized log_rv at step h — a different functional than the h-day
    # mean used for point forecasts; both are recorded, never mixed.
    if tsfm_quant_folds:
        quant = np.vstack(tsfm_quant_folds)
        y = np.concatenate(tsfm_y_folds)
        qs = np.array(TSFM_QUANTILES)
        col = {q: TSFM_QUANT_COL_OFFSET + int(np.argmin(np.abs(qs - q)))
               for q in (0.1, 0.5, 0.9)}
        pinball = {}
        for j, q in enumerate(TSFM_QUANTILES):
            pinball[str(q)] = pinball_loss(y, quant[:, TSFM_QUANT_COL_OFFSET + j], q)
        cov80, width80 = interval_coverage(
            y, quant[:, col[0.1]], quant[:, col[0.9]])
        out["tsfm_quantiles"] = {
            "pinball_loss": pinball,
            "coverage_80": cov80,
            "width_80": width80,
            "nominal_80": 0.8,
            "n_obs": int(len(y)),
            "note": "quantiles evaluated on realized log_rv at step h (direct); "
                    "point forecasts on the h-day mean target — separate "
                    "functionals, never mixed",
        }
    return out


# ---------------------------------------------------------------------------
# Aggregate verdict (§C strict)
# ---------------------------------------------------------------------------

def _coherent(dm: dict, direction: str) -> bool:
    if dm.get("verdict") != f"{direction} baseline":
        return False
    if dm.get("p_value", 1.0) >= 0.05:
        return False
    diff = dm.get("mean_loss_diff", 0.0)
    return diff < 0.0 if direction == "BEATS" else diff > 0.0


def aggregate_verdicts(configs: list[dict]) -> list[dict]:
    """Group per-(coin, horizon) DM verdicts of tsfm vs each baseline.

    §C conjunction (amended #11010): BEATS requires dm_p_median < 0.05 on
    the MSE leg AND coherent DM wins on every seed AND (edge >= 2 sigma
    cross-seed, or the seeds are bit-identical in which case the sigma
    jambe is degenerate — M17 OLS precedent: determinism makes edge/sigma
    non-applicable, not artificially infinite). The linear leg is reported
    as a bias diagnostic and never gates the verdict.
    """
    groups: dict[tuple, list[dict]] = {}
    for c in configs:
        if "skipped" in c:
            continue
        groups.setdefault((c["coin"], c["horizon"]), []).append(c)

    out = []
    for (coin, horizon), rows in sorted(groups.items()):
        for baseline in BASELINES:
            dm_rows, dm_lin, edges = [], [], []
            for r in rows:
                dm = r.get("dm_vs_baselines_mse", {}).get(baseline)
                if dm is None:
                    continue
                dm_rows.append(dm)
                dm_lin.append(r.get("dm_vs_baselines_linear", {})
                              .get(baseline, {}).get("p_value"))
                ts = r["models"]["tsfm"]["mse_debiased"]
                base = r["models"][baseline]["mse_debiased"]
                edges.append((base - ts) / base * 100.0)
            if not dm_rows:
                continue
            edge = float(np.mean(edges))
            sigma = float(np.std(edges, ddof=1)) if len(edges) > 1 else 0.0
            p_med = float(np.median([d["p_value"] for d in dm_rows]))
            n_beats = sum(1 for d in dm_rows if _coherent(d, "BEATS"))
            n_been = sum(1 for d in dm_rows if _coherent(d, "BEATEN BY"))
            identical = len({
                tuple(r["fc_hash_per_fold"]["tsfm"]) for r in rows
            }) == 1
            if n_beats == len(dm_rows) and p_med < 0.05 and (
                identical or edge >= 2.0 * sigma
            ):
                verdict = "BEATS"
            elif n_been == len(dm_rows) and p_med < 0.05:
                verdict = "NO BEATS"
            else:
                verdict = "INCONCLUSIVE"
            out.append({
                "coin": coin, "horizon": horizon, "baseline": baseline,
                "edge_pct_mean": edge, "edge_sigma_cross_seed": sigma,
                "dm_p_median": p_med,
                "dm_p_median_linear_leg": float(np.median(
                    [p for p in dm_lin if p is not None])) if any(
                    p is not None for p in dm_lin) else None,
                "n_seeds": len(dm_rows),
                "n_coherent_beats": n_beats, "n_coherent_beaten_by": n_been,
                "seeds_bit_identical": identical,
                "verdict": verdict,
            })
    return out


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser(
        description="M18 TimesFM 2.5 zero-shot vs classical baselines (#14768)")
    parser.add_argument("--coins", nargs="+", default=["BTC-USD"])
    parser.add_argument("--horizons", nargs="+", type=int, default=HORIZONS_DEFAULT)
    parser.add_argument("--seeds", nargs="+", type=int, default=SEEDS_DEFAULT)
    parser.add_argument("--n-splits", type=int, default=N_SPLITS)
    parser.add_argument("--calibration-size", type=int, default=CALIBRATION_SIZE)
    parser.add_argument("--refit-every", type=int, default=REFIT_EVERY)
    parser.add_argument("--context-len", type=int, default=CONTEXT_LEN_DEFAULT)
    parser.add_argument("--skip-remote", action="store_true",
                        help="use cached BTC+ETH hourly data only")
    parser.add_argument("--debias", action="store_true", default=True)
    parser.add_argument("--no-debias", dest="debias", action="store_false")
    parser.add_argument("--out-json", type=Path,
                        default=RESULTS_DIR / "m18_tsfm_benchmark.json")
    args = parser.parse_args()

    t0 = time.time()
    tsfm = TimesFMWrapper.production_loader(TSFM_REPO_ID, args.context_len)
    print(f"[tsfm] loaded {TSFM_REPO_ID} @ {tsfm.revision} "
          f"in {time.time()-t0:.1f}s", flush=True)

    print("[load] panel ...", flush=True)
    panel = _load_panel(args.skip_remote)

    configs: list[dict] = []
    for coin in args.coins:
        if coin not in panel:
            print(f"[WARN] {coin} not in panel — skipped")
            continue
        for horizon in args.horizons:
            for seed in args.seeds:
                try:
                    import torch
                    torch.manual_seed(seed)
                except ImportError as exc:
                    raise SystemExit(
                        f"torch unavailable — TimesFM cannot run (#14768): {exc}")
                np.random.seed(seed)
                t1 = time.time()
                cfg = run_config(
                    coin, panel[coin], horizon, seed, args.n_splits,
                    args.calibration_size, args.refit_every, tsfm,
                    debias=args.debias,
                )
                configs.append(cfg)
                if "skipped" in cfg:
                    print(f"  [{coin} h={horizon} s={seed}] SKIPPED: "
                          f"{cfg['skipped']}", flush=True)
                    continue
                ts = cfg["models"]["tsfm"]["mse_debiased"]
                print(f"  [{coin} h={horizon} s={seed}] tsfm mse_deb={ts:.4f} "
                      f"({time.time()-t1:.1f}s)", flush=True)

    summary = aggregate_verdicts(configs)
    manifest = {
        "module": "M18",
        "issue": 14768,
        "repo_id": TSFM_REPO_ID,
        "checkpoint_revision": tsfm.revision,
        "n_tsfm_series_served": tsfm.n_calls,
        "context_len": args.context_len,
        "n_splits": args.n_splits,
        "calibration_size": args.calibration_size,
        "refit_every": args.refit_every,
        "quantile_levels": TSFM_QUANTILES,
        "quantile_layout": "[mean, q0.1..q0.9] on the last axis; point = median",
        "debias": args.debias,
        "configs": configs,
        "summary": summary,
        "elapsed_s": round(time.time() - t0, 1),
    }
    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(json.dumps(manifest, indent=1), encoding="utf-8")
    print(f"[done] wrote {args.out_json} "
          f"({tsfm.n_calls} TimesFM series served)", flush=True)
    for s in summary:
        print(f"  {s['coin']} h={s['horizon']} vs {s['baseline']}: "
              f"{s['verdict']} (edge {s['edge_pct_mean']:+.1f}%, "
              f"p_med {s['dm_p_median']:.4f})", flush=True)


if __name__ == "__main__":
    main()
