"""PatchTST vs iTransformer head-to-head on BTC daily log-RV (issue #14942).

The two jambes that #14081 (PatchTST vs debiased HAR) and #14860
(iTransformer vs debiased HAR) each leave open: neither compares the two
deep-sequence architectures *against each other* on an aligned support.
This wrapper reuses the existing pipeline modules without modifying them:

- ``PatchTSTModel`` from ``train_patchtst.py`` (Nie et al., ICLR 2023) and
  ``iTransformerModel`` from ``train_itransformer.py`` (Li et al., ICLR
  2024) -- the CLASSES only. The generic CLIs target returns/direction and
  their ``--walk-forward`` flag does not replace the simple split, so this
  log-RV revalidation owns an explicit expanding walk-forward loop instead.
- BTC intraday loader / log-RV primitives: ``intraday_loader``
  (``load_bitstamp_btc``, ``hourly_log_returns``) and ``realized_variance``
  (``daily_realized_variance``, ``realized_variance_to_log``).
- The HAR walk-forward baseline: ``har_model.walk_forward_har`` with
  ``calibrate_bias=True`` (train-only debiasing) -- reported as context, not
  the comparison target.
- ``dlinear_vol.create_sequences`` for the (input, target) windowing.
- ``bias_metrics._mse_decomposition`` / ``bias_metrics._dm_centered_mse``
  (shared torch-free module, issue #14363) for the MSE = bias^2 + variance
  decomposition and the DM test on mean-centered errors (loss_fn="mse" ->
  variance differential, the precision leg of pr-review section C).

Protocol (per horizon h in {1, 5, 10} by default, per seed in {0, 1, 7, 42}):
- Expanding walk-forward, 5 folds (``har_model._make_split_indices``): fold k
  trains on [0, k * fold_size) and tests on [k * fold_size, (k+1) * fold_size),
  fold_size = n // (n_splits + 1).
- ONE model per (fold, seed), for EACH architecture. Normalisation stats
  (mean, std of log-RV) come from the training fold ONLY. Validation is the
  TAIL of the training sequences ONLY; the best-validation epoch state is
  restored before test inference. The test fold never enters fitting,
  normalisation, or model selection.
- The two architectures run the IDENTICAL walk-forward (a single generic
  loop parameterised by a model builder), so any head-to-head difference is
  attributable to the architecture, not to divergent protocol plumbing.
- Target = mean future log-RV over the next h days. Both predict the h-step
  vector (pred_len = horizon) which is averaged at inference; HAR averages
  its h iterated one-step forecasts. The two architectures and the HAR use
  the identical target convention; predictions are aligned BY TIMESTAMP on
  the shared test dates before any comparison metric is computed (guarded by
  an explicit target-consistency check on the aligned support).

Head-to-head statistic (PatchTST as "model", iTransformer as "baseline"):
- ``_dm_centered_mse(patchtst_errors, itransformer_errors, horizon)`` runs the
  DM test on mean-centered errors with loss_fn="mse": biases annihilated,
  d_mean measures the variance differential. verdict "BEATS baseline" means
  PatchTST is significantly more precise; "BEATEN BY baseline" means
  iTransformer is.
- MSE = bias^2 + variance for each architecture; var_ratio
  (patchtst_variance / itransformer_variance) < 1 means PatchTST is more
  precise; edge_vs_itransformer_pct > 0 means PatchTST has lower total MSE.

Aggregation per horizon (pr-review section C, conservative): NO BEATS if any
seed has iTransformer significantly beating PatchTST ("BEATEN BY baseline");
BEATS only if mean edge >= 2 * cross-seed std AND median DM p < 0.05 AND no
seed is lost; otherwise INCONCLUSIVE.

Usage:
    python btc_patchtst_itransformer_head2head.py --dry-run      # synthetic
    python btc_patchtst_itransformer_head2head.py                # real sweep
    python btc_patchtst_itransformer_head2head.py --horizons 1 5 --seeds 0 1 7 42 --device cpu
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

import numpy as np
import pandas as pd
import torch

# Local imports: scripts/ first, then QuantConnect/shared for gpu_training.
_HERE = Path(__file__).resolve().parent
if str(_HERE) not in sys.path:
    sys.path.insert(0, str(_HERE))
_SHARED = _HERE.parent.parent / "shared"
if str(_SHARED) not in sys.path:
    sys.path.append(str(_SHARED))

from gpu_training import batch_thermal_check, setup_amp  # noqa: E402
from train_patchtst import PatchTSTModel  # noqa: E402  (model class reuse only)
from train_itransformer import iTransformerModel  # noqa: E402  (model class reuse only)
from har_model import _make_split_indices as make_expanding_splits  # noqa: E402
from har_model import walk_forward_har  # noqa: E402
from dlinear_vol import create_sequences  # noqa: E402
from bias_metrics import _dm_centered_mse, _mse_decomposition  # noqa: E402
from intraday_loader import hourly_log_returns, load_bitstamp_btc  # noqa: E402
from realized_variance import (  # noqa: E402
    daily_realized_variance,
    realized_variance_to_log,
)

DEFAULT_OUT_JSON = str(_HERE.parent / "results" / "btc_head2head_patchtst_itransformer.json")

# Dry-run overrides (requirement #14942): deterministic synthetic log-RV,
# 2 folds, 1 seed, 1 horizon, tiny model/epochs, CPU, no download.
DRY_RUN_OVERRIDES = {
    "horizons": [1],
    "seeds": [0],
    "n_splits": 2,
    "seq_len": 16,
    "patch_len": 4,
    "stride": 2,
    "d_model": 8,
    "n_heads": 2,
    "n_layers": 1,
    "epochs": 2,
    "batch_size": 16,
    "device": "cpu",
}


def load_btc_rv() -> pd.Series:
    """Daily realized variance of BTC from the Bitstamp hourly CSV."""
    btc = load_bitstamp_btc()
    rets = hourly_log_returns(btc)
    rv = daily_realized_variance(rets)
    print(f"[h2h] BTC: {len(rv)} RV days")
    return rv


def synthetic_rv(n: int = 360, seed: int = 0) -> pd.Series:
    """Deterministic synthetic daily RV (exponential of an AR(1) log-RV)."""
    rng = np.random.default_rng(seed)
    mu, phi, sigma = -12.0, 0.90, 0.25
    eps = rng.normal(0.0, sigma, n)
    log_rv = np.empty(n)
    log_rv[0] = mu
    for t in range(1, n):
        log_rv[t] = mu + phi * (log_rv[t - 1] - mu) + eps[t]
    index = pd.date_range("2021-01-01", periods=n, freq="D")
    return pd.Series(np.exp(log_rv), index=index, name="synthetic_RV")


def make_patchtst_builder(
    seq_len: int,
    patch_len: int,
    stride: int,
    d_model: int,
    n_heads: int,
    n_layers: int,
    dropout: float,
    fc_dropout: float,
):
    """Return a ``build(horizon) -> PatchTSTModel`` factory."""
    def build(horizon: int) -> PatchTSTModel:
        return PatchTSTModel(
            n_vars=1, seq_len=seq_len, pred_len=horizon,
            patch_len=patch_len, stride=stride, d_model=d_model,
            n_heads=n_heads, n_layers=n_layers, dropout=dropout,
            fc_dropout=fc_dropout,
        )
    return build


def make_itransformer_builder(
    seq_len: int,
    d_model: int,
    n_heads: int,
    n_layers: int,
    dropout: float,
    ff_dropout: float,
):
    """Return a ``build(horizon) -> iTransformerModel`` factory."""
    def build(horizon: int) -> iTransformerModel:
        return iTransformerModel(
            n_vars=1, seq_len=seq_len, pred_len=horizon,
            d_model=d_model, n_heads=n_heads, n_layers=n_layers,
            dropout=dropout, ff_dropout=ff_dropout,
        )
    return build


def train_normalization_stats(log_rv: np.ndarray, train_end: int) -> tuple[float, float]:
    """Mean/std of log-RV on [0, train_end) ONLY (no test leakage)."""
    train = np.asarray(log_rv[:train_end], dtype=float)
    return float(np.mean(train)), max(float(np.std(train)), 1e-6)


def train_model_fold(
    build_model,
    x_train: np.ndarray,
    y_train: np.ndarray,
    *,
    horizon: int,
    epochs: int,
    batch_size: int,
    lr: float,
    seed: int,
    device: str = "cpu",
    val_ratio: float = 0.15,
) -> tuple[torch.nn.Module, dict]:
    """Train one model on a single fold's TRAINING sequences.

    Model selection uses a validation split taken from the TAIL of the
    training sequences only -- the test fold never enters this function.
    The best-validation epoch state is restored before returning.
    """
    torch.manual_seed(seed)
    np.random.seed(seed)

    val_cutoff = int(len(x_train) * (1 - val_ratio))
    val_cutoff = max(min(val_cutoff, len(x_train) - 1), 1)
    x_tr, x_val = x_train[:val_cutoff], x_train[val_cutoff:]
    y_tr, y_val = y_train[:val_cutoff], y_train[val_cutoff:]

    model = build_model(horizon).to(device)

    dataset = torch.utils.data.TensorDataset(
        torch.tensor(np.asarray(x_tr), dtype=torch.float32).unsqueeze(-1),
        torch.tensor(np.asarray(y_tr), dtype=torch.float32),
    )
    val_dataset = torch.utils.data.TensorDataset(
        torch.tensor(np.asarray(x_val), dtype=torch.float32).unsqueeze(-1),
        torch.tensor(np.asarray(y_val), dtype=torch.float32),
    )
    loader = torch.utils.data.DataLoader(
        dataset, batch_size=batch_size, shuffle=True,
        generator=torch.Generator().manual_seed(seed),
    )
    val_loader = torch.utils.data.DataLoader(val_dataset, batch_size=batch_size)

    optimizer = torch.optim.AdamW(model.parameters(), lr=lr, weight_decay=1e-4)
    criterion = torch.nn.MSELoss()
    use_amp, grad_scaler = setup_amp(device)

    best_val_loss = float("inf")
    best_state: dict | None = None

    for _epoch in range(epochs):
        model.train()
        for batch_idx, (xb, yb) in enumerate(loader):
            # Thermal watchdog: no-op on CPU (torch.cuda check inside).
            batch_thermal_check(batch_idx, check_every=5, max_temp=80, cool_sleep=30)
            xb, yb = xb.to(device), yb.to(device)
            optimizer.zero_grad()
            with torch.amp.autocast("cuda", enabled=use_amp):
                loss = criterion(model(xb), yb)
            if use_amp:
                grad_scaler.scale(loss).backward()
                grad_scaler.unscale_(optimizer)
                torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
                grad_scaler.step(optimizer)
                grad_scaler.update()
            else:
                loss.backward()
                torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
                optimizer.step()

        model.eval()
        val_loss, val_batches = 0.0, 0
        with torch.no_grad():
            for xb, yb in val_loader:
                xb, yb = xb.to(device), yb.to(device)
                with torch.amp.autocast("cuda", enabled=use_amp):
                    val_loss += criterion(model(xb), yb).item()
                val_batches += 1
        avg_val = val_loss / max(val_batches, 1)
        if avg_val < best_val_loss:
            best_val_loss = avg_val
            best_state = {k: v.cpu().clone() for k, v in model.state_dict().items()}

    if best_state is not None:
        model.load_state_dict(best_state)
    model.eval()
    return model, {
        "best_val_loss": round(best_val_loss, 6),
        "n_train_sequences": int(len(x_tr)),
        "n_val_sequences": int(len(x_val)),
        "epochs": int(epochs),
    }


def walk_forward_logrv(
    log_rv: np.ndarray,
    rv_index: pd.DatetimeIndex,
    build_model,
    *,
    seq_len: int = 64,
    horizon: int = 1,
    n_splits: int = 5,
    epochs: int = 30,
    batch_size: int = 32,
    lr: float = 5e-4,
    seed: int = 0,
    device: str = "cpu",
    val_ratio: float = 0.15,
    min_train_sequences: int = 20,
) -> dict:
    """Expanding walk-forward evaluation of one architecture on daily log-RV.

    Per fold: normalization on the training fold only, one model per
    (fold, seed) trained with train-tail validation, forecasts produced with
    a single forward pass over the fold's test inputs. Target of a forecast
    dated t is mean(log_rv[t : t + horizon]) -- the HAR target convention.
    """
    log_rv = np.asarray(log_rv, dtype=float)
    n = len(log_rv)
    if n < seq_len + horizon + 100:
        raise ValueError(
            f"need >= {seq_len + horizon + 100} obs for walk-forward, got {n}"
        )

    splits = make_expanding_splits(n, n_splits)

    preds: list[float] = []
    truths: list[float] = []
    dates: list[pd.Timestamp] = []
    fold_info: list[dict] = []

    for fold_idx, (train_end, test_start, test_end) in enumerate(splits):
        n_train_seq = train_end - seq_len - horizon + 1
        if n_train_seq < min_train_sequences:
            fold_info.append({
                "fold": fold_idx, "train_end": int(train_end),
                "test_start": int(test_start), "test_end": int(test_end),
                "skipped": f"train_sequences<{min_train_sequences}",
            })
            continue

        train_mean, train_std = train_normalization_stats(log_rv, train_end)
        normed = (log_rv - train_mean) / train_std
        x_all, y_all = create_sequences(normed, seq_len, horizon)

        model, info = train_model_fold(
            build_model, x_all[:n_train_seq], y_all[:n_train_seq],
            horizon=horizon, epochs=epochs, batch_size=batch_size,
            lr=lr, seed=seed, device=device, val_ratio=val_ratio,
        )

        test_indices = [
            i for i in range(test_start, test_end - horizon) if i - seq_len >= 0
        ]
        if not test_indices:
            fold_info.append({
                "fold": fold_idx, "train_end": int(train_end),
                "test_start": int(test_start), "test_end": int(test_end),
                "skipped": "empty_test_window",
                **info,
            })
            continue

        x_test = np.asarray(
            [normed[i - seq_len: i] for i in test_indices], dtype=np.float32
        )[:, :, None]
        with torch.no_grad():
            tensor = torch.tensor(x_test, dtype=torch.float32, device=device)
            pred_matrix = model(tensor).cpu().numpy()  # [n_test, horizon]
        fold_preds = pred_matrix.mean(axis=1) * train_std + train_mean

        for i, pred_raw in zip(test_indices, fold_preds):
            preds.append(float(pred_raw))
            truths.append(float(np.mean(log_rv[i: i + horizon])))
            dates.append(rv_index[i])

        fold_info.append({
            "fold": fold_idx,
            "train_end": int(train_end),
            "test_start": int(test_start),
            "test_end": int(test_end),
            "train_mean": float(train_mean),
            "train_std": float(train_std),
            "n_test": len(test_indices),
            **info,
        })

    preds_arr = np.asarray(preds)
    truths_arr = np.asarray(truths)
    aggregate_mse = (
        float(np.mean((preds_arr - truths_arr) ** 2)) if len(preds_arr) else float("nan")
    )
    return {
        "horizon": horizon,
        "seed": seed,
        "seq_len": seq_len,
        "n_splits": n_splits,
        "n_total_preds": len(preds_arr),
        "aggregate_mse_logrv": aggregate_mse,
        "fold_info": fold_info,
        "forecasts": pd.Series(
            preds_arr, index=pd.DatetimeIndex(dates), name="logrv_pred"
        ),
        "targets": pd.Series(
            truths_arr, index=pd.DatetimeIndex(dates), name="logrv_target"
        ),
    }


def run_debiased_har(
    rv: pd.Series,
    horizon: int,
    n_splits: int,
    refit_every: int = 22,
    calibration_size: int = 60,
) -> dict:
    """Walk-forward HAR with TRAIN-ONLY bias calibration (genuinely OOS)."""
    return walk_forward_har(
        rv,
        horizon=horizon,
        n_splits=n_splits,
        refit_every=refit_every,
        calibrate_bias=True,
        calibration_size=calibration_size,
    )


def align_two_models(
    pb_forecasts: pd.Series,
    pb_targets: pd.Series,
    itr_forecasts: pd.Series,
    itr_targets: pd.Series,
) -> dict:
    """Inner-join the two architectures' forecasts on their shared test dates.

    Both walk-forwards use the same target convention (forecast dated t has
    target mean(log_rv[t:t+h])); the aligned targets must therefore be
    identical on the shared dates -- enforced, so a convention drift between
    the two architectures cannot silently corrupt the comparison.
    """
    df = pd.concat(
        {
            "pb_pred": pb_forecasts,
            "pb_target": pb_targets,
            "itr_pred": itr_forecasts,
            "itr_target": itr_targets,
        },
        axis=1,
    ).dropna()
    if len(df) == 0:
        return {
            "timestamps": [],
            "pb_pred": np.asarray([]),
            "pb_target": np.asarray([]),
            "itr_pred": np.asarray([]),
            "itr_target": np.asarray([]),
        }
    if not np.allclose(
        df["pb_target"].to_numpy(), df["itr_target"].to_numpy(), atol=1e-8
    ):
        raise ValueError(
            "target mismatch on aligned dates: PatchTST and iTransformer target "
            "conventions diverged -- refusing to compare"
        )
    return {
        "timestamps": list(df.index),
        "pb_pred": df["pb_pred"].to_numpy(dtype=float),
        "pb_target": df["pb_target"].to_numpy(dtype=float),
        "itr_pred": df["itr_pred"].to_numpy(dtype=float),
        "itr_target": df["itr_target"].to_numpy(dtype=float),
    }


def evaluate_combo(aligned: dict, horizon: int) -> dict:
    """Head-to-head metrics of one (seed, horizon) combo (PatchTST = model, iTransformer = baseline).

    - ``_mse_decomposition`` reports MSE = bias^2 + variance for each
      architecture (signed bias is reported, never corrected on the test).
    - ``_dm_centered_mse(patchtst_errors, itransformer_errors, horizon)`` runs
      the DM test on mean-centered errors with loss_fn="mse": verdict
      "BEATS baseline" means PatchTST is significantly more precise.
    - ``var_ratio`` < 1 means PatchTST is more precise than iTransformer.
    - ``edge_vs_itransformer_pct`` > 0 means PatchTST has lower total MSE.
    """
    pb_errors = aligned["pb_pred"] - aligned["pb_target"]
    itr_errors = aligned["itr_pred"] - aligned["itr_target"]
    if len(pb_errors) < 10:
        return {
            "n_aligned": int(len(pb_errors)),
            "dm_centered_stat": float("nan"),
            "dm_centered_pvalue": float("nan"),
            "dm_centered_verdict": "INSUFFICIENT_DATA",
            "edge_vs_itransformer_pct": float("nan"),
            "var_ratio_patchtst_over_itransformer": float("nan"),
        }

    pb_decomp = _mse_decomposition(pb_errors)
    itr_decomp = _mse_decomposition(itr_errors)
    dm = _dm_centered_mse(pb_errors, itr_errors, horizon=horizon)

    itr_mse = itr_decomp["mse"]
    pb_mse = pb_decomp["mse"]
    edge_pct = (
        float((itr_mse - pb_mse) / itr_mse * 100.0)
        if np.isfinite(itr_mse) and itr_mse > 0
        else float("nan")
    )
    var_ratio = (
        float(pb_decomp["variance"] / itr_decomp["variance"])
        if np.isfinite(itr_decomp["variance"]) and itr_decomp["variance"] > 0
        else float("nan")
    )

    return {
        "n_aligned": int(len(pb_errors)),
        "patchtst_mse_logrv": float(pb_decomp["mse"]),
        "patchtst_bias": float(np.mean(pb_errors)),
        "patchtst_bias_sq": float(pb_decomp["bias_sq"]),
        "patchtst_variance": float(pb_decomp["variance"]),
        "itransformer_mse_logrv": float(itr_mse),
        "itransformer_bias": float(np.mean(itr_errors)),
        "itransformer_bias_sq": float(itr_decomp["bias_sq"]),
        "itransformer_variance": float(itr_decomp["variance"]),
        "var_ratio_patchtst_over_itransformer": var_ratio,
        "edge_vs_itransformer_pct": edge_pct,
        "dm_centered_stat": float(dm["dm_stat"]),
        "dm_centered_pvalue": float(dm["dm_pvalue"]),
        "dm_centered_verdict": str(dm["dm_verdict"]),
        "dm_centered_mean_loss_diff": float(dm.get("mean_loss_diff", float("nan"))),
    }


def aggregate_by_horizon(rows: list[dict]) -> list[dict]:
    """Aggregate per-horizon head-to-head verdicts across seeds (pr-review C).

    Frame: does PatchTST BEAT iTransformer at horizon h? Conservative:
    NO BEATS as soon as any seed has iTransformer significantly beating
    PatchTST ("BEATEN BY baseline"); BEATS requires mean edge >= 2 * cross-
    seed std AND median DM p < 0.05 AND no seed lost; otherwise INCONCLUSIVE.
    """
    from collections import defaultdict

    grouped: dict[int, list[dict]] = defaultdict(list)
    for r in rows:
        if "skipped" in r or "edge_vs_itransformer_pct" not in r:
            continue
        grouped[r["horizon"]].append(r)

    results: list[dict] = []
    for h, sub in sorted(grouped.items()):
        edges = np.asarray([r["edge_vs_itransformer_pct"] for r in sub], dtype=float)
        pvals = np.asarray([r["dm_centered_pvalue"] for r in sub], dtype=float)
        verdicts = [r["dm_centered_verdict"] for r in sub]
        var_ratios = np.asarray(
            [r["var_ratio_patchtst_over_itransformer"] for r in sub], dtype=float
        )

        mean_edge = float(np.nanmean(edges))
        std_edge = float(np.nanstd(edges)) if len(edges) > 1 else 0.0
        dm_p_median = float(np.nanmedian(pvals))
        n_pb_lost = sum(1 for v in verdicts if "BEATEN" in v)
        n_pb_wins = sum(1 for v in verdicts if v == "BEATS baseline")
        n_inconclusive = sum(1 for v in verdicts if v == "INCONCLUSIVE")

        if n_pb_lost > 0:
            verdict = "NO BEATS"
        elif mean_edge >= 2.0 * std_edge and dm_p_median < 0.05:
            verdict = "BEATS"
        else:
            verdict = "INCONCLUSIVE"

        results.append({
            "horizon": h,
            "n_seeds": len(sub),
            "mean_edge_vs_itransformer_pct": mean_edge,
            "edge_std_pct": std_edge,
            "dm_centered_p_median": dm_p_median,
            "n_patchtst_wins": n_pb_wins,
            "n_itransformer_wins": n_pb_lost,
            "n_inconclusive": n_inconclusive,
            "mean_var_ratio_patchtst_over_itransformer": float(np.nanmean(var_ratios)),
            "mean_patchtst_mse": float(np.nanmean([r["patchtst_mse_logrv"] for r in sub])),
            "mean_itransformer_mse": float(
                np.nanmean([r["itransformer_mse_logrv"] for r in sub])
            ),
            "mean_patchtst_bias": float(np.nanmean([r["patchtst_bias"] for r in sub])),
            "mean_itransformer_bias": float(
                np.nanmean([r["itransformer_bias"] for r in sub])
            ),
            "verdict": verdict,
        })
    return results


def run_pipeline(
    rv: pd.Series,
    *,
    horizons: list[int],
    seeds: list[int],
    seq_len: int = 64,
    n_splits: int = 5,
    refit_every: int = 22,
    calibration_size: int = 60,
    patch_len: int = 16,
    stride: int = 8,
    d_model: int = 64,
    n_heads: int = 4,
    n_layers: int = 2,
    dropout: float = 0.2,
    fc_dropout: float = 0.2,
    ff_dropout: float = 0.2,
    epochs: int = 30,
    batch_size: int = 32,
    lr: float = 5e-4,
    device: str = "cpu",
    val_ratio: float = 0.15,
    out_json: str | Path = DEFAULT_OUT_JSON,
    coin: str = "BTC-USD",
    dry_run: bool = False,
) -> dict:
    """Full head-to-head pipeline: PatchTST vs iTransformer on debiased-HAR protocol.

    Writes the complete payload (rows with persisted per-combo arrays,
    per-horizon aggregation, config) to ``out_json`` and returns it.
    """
    t0 = time.time()
    if device == "cuda" and not torch.cuda.is_available():
        raise SystemExit("ERROR: --device cuda requested but CUDA is not available")

    log_rv = realized_variance_to_log(rv)
    log_rv_arr = log_rv.values.astype(float)
    rv_idx = rv.index
    print(
        f"[h2h] {coin}: {len(rv)} RV days, log_rv var={log_rv.var():.4f} "
        f"(dry_run={dry_run})"
    )

    pb_builder = make_patchtst_builder(
        seq_len, patch_len, stride, d_model, n_heads, n_layers, dropout, fc_dropout
    )
    itr_builder = make_itransformer_builder(
        seq_len, d_model, n_heads, n_layers, dropout, ff_dropout
    )

    rows: list[dict] = []
    for h in horizons:
        har_out = run_debiased_har(
            rv, horizon=h, n_splits=n_splits,
            refit_every=refit_every, calibration_size=calibration_size,
        )
        print(
            f"  h={h} debiased HAR MSE={har_out['aggregate_mse_logrv']:.5f} "
            f"({har_out['n_total_preds']} preds, calibrate_bias=True)"
        )

        for seed in seeds:
            pb_out = walk_forward_logrv(
                log_rv_arr, rv_idx, pb_builder,
                seq_len=seq_len, horizon=h, n_splits=n_splits,
                epochs=epochs, batch_size=batch_size, lr=lr,
                seed=seed, device=device, val_ratio=val_ratio,
            )
            itr_out = walk_forward_logrv(
                log_rv_arr, rv_idx, itr_builder,
                seq_len=seq_len, horizon=h, n_splits=n_splits,
                epochs=epochs, batch_size=batch_size, lr=lr,
                seed=seed, device=device, val_ratio=val_ratio,
            )
            aligned = align_two_models(
                pb_out["forecasts"], pb_out["targets"],
                itr_out["forecasts"], itr_out["targets"],
            )
            metrics = evaluate_combo(aligned, horizon=h)
            if "patchtst_mse_logrv" not in metrics:
                rows.append({
                    "coin": coin, "horizon": h, "seed": seed,
                    "skipped": "insufficient_aligned_obs",
                })
                print(f"  h={h} seed={seed} SKIPPED (aligned obs < 10)")
                continue

            row = {
                "coin": coin,
                "horizon": h,
                "seed": seed,
                "seq_len": seq_len,
                "n_splits": n_splits,
                "epochs": epochs,
                "device": device,
                "dry_run": dry_run,
                "n_rv_days": int(len(rv)),
                "n_predictions_patchtst": int(pb_out["n_total_preds"]),
                "n_predictions_itransformer": int(itr_out["n_total_preds"]),
                "har_debiased_mse_logrv": float(har_out["aggregate_mse_logrv"]),
                "n_aligned": int(metrics["n_aligned"]),
                **metrics,
                "fold_info_patchtst": pb_out["fold_info"],
                "fold_info_itransformer": itr_out["fold_info"],
                "timestamps": [d.strftime("%Y-%m-%d") for d in aligned["timestamps"]],
                "patchtst_predictions": [float(x) for x in aligned["pb_pred"]],
                "itransformer_predictions": [float(x) for x in aligned["itr_pred"]],
                "targets": [float(x) for x in aligned["pb_target"]],
                "patchtst_errors": [
                    float(p - t)
                    for p, t in zip(aligned["pb_pred"], aligned["pb_target"])
                ],
                "itransformer_errors": [
                    float(p - t)
                    for p, t in zip(aligned["itr_pred"], aligned["itr_target"])
                ],
            }
            rows.append(row)
            print(
                f"  h={h} seed={seed} PatchTST MSE={metrics['patchtst_mse_logrv']:.5f} "
                f"bias={metrics['patchtst_bias']:+.5f} | "
                f"iTransf MSE={metrics['itransformer_mse_logrv']:.5f} "
                f"bias={metrics['itransformer_bias']:+.5f} | "
                f"edge={metrics['edge_vs_itransformer_pct']:+.2f}% "
                f"var_ratio={metrics['var_ratio_patchtst_over_itransformer']:.3f} "
                f"DM p={metrics['dm_centered_pvalue']:.4f} "
                f"-> {metrics['dm_centered_verdict']}"
            )

    aggregated = aggregate_by_horizon(rows)
    payload = {
        "rows": rows,
        "aggregated": aggregated,
        "elapsed_s": time.time() - t0,
        "dry_run": dry_run,
        "config": {
            "coin": coin,
            "horizons": horizons,
            "seeds": seeds,
            "seq_len": seq_len,
            "n_splits": n_splits,
            "refit_every": refit_every,
            "calibration_size": calibration_size,
            "patch_len": patch_len,
            "stride": stride,
            "d_model": d_model,
            "n_heads": n_heads,
            "n_layers": n_layers,
            "dropout": dropout,
            "fc_dropout": fc_dropout,
            "ff_dropout": ff_dropout,
            "epochs": epochs,
            "batch_size": batch_size,
            "lr": lr,
            "device": device,
            "val_ratio": val_ratio,
            "har_debias": "train_tail_calibration (calibrate_bias=True, OOS)",
            "dm": "centered errors, loss_fn=mse (variance differential)",
        },
    }

    out_path = Path(out_json)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(payload, indent=2, default=str))
    print(f"\n[done] wrote {out_path}")

    if aggregated:
        print("\n=== PatchTST vs iTransformer head-to-head (BTC) ===")
        print(pd.DataFrame(aggregated).to_string(index=False))
        n_beats = sum(1 for r in aggregated if r["verdict"] == "BEATS")
        n_no = sum(1 for r in aggregated if r["verdict"] == "NO BEATS")
        n_inc = sum(1 for r in aggregated if r["verdict"] == "INCONCLUSIVE")
        print(f"\nSummary: {n_beats} BEATS / {n_no} NO BEATS / {n_inc} INCONCLUSIVE")

    return payload


def main() -> None:
    parser = argparse.ArgumentParser(
        description="PatchTST vs iTransformer head-to-head on BTC daily log-RV "
                    "(issue #14942)"
    )
    parser.add_argument("--horizons", type=int, nargs="+", default=[1, 5, 10])
    parser.add_argument("--seeds", type=int, nargs="+", default=[0, 1, 7, 42])
    parser.add_argument("--seq-len", type=int, default=64)
    parser.add_argument("--n-splits", type=int, default=5)
    parser.add_argument("--refit-every", type=int, default=22,
                        help="HAR mid-fold refit cadence (days)")
    parser.add_argument("--calibration-size", type=int, default=60,
                        help="HAR train-tail holdout size for bias calibration")
    parser.add_argument("--patch-len", type=int, default=16)
    parser.add_argument("--stride", type=int, default=8)
    parser.add_argument("--d-model", type=int, default=64)
    parser.add_argument("--n-heads", type=int, default=4)
    parser.add_argument("--n-layers", type=int, default=2)
    parser.add_argument("--dropout", type=float, default=0.2)
    parser.add_argument("--fc-dropout", type=float, default=0.2)
    parser.add_argument("--ff-dropout", type=float, default=0.2)
    parser.add_argument("--epochs", type=int, default=30)
    parser.add_argument("--batch-size", type=int, default=32)
    parser.add_argument("--lr", type=float, default=5e-4)
    parser.add_argument("--val-ratio", type=float, default=0.15)
    parser.add_argument("--device", default="cpu", choices=["cpu", "cuda"],
                        help="CPU by default; cuda must be forced explicitly")
    parser.add_argument("--out-json", type=str, default=DEFAULT_OUT_JSON)
    parser.add_argument("--dry-run", action="store_true",
                        help="Deterministic synthetic log-RV, 2 folds, 1 seed, "
                             "1 horizon, tiny model/epochs, CPU, no download")
    args = parser.parse_args()

    params = dict(
        horizons=args.horizons, seeds=args.seeds, seq_len=args.seq_len,
        n_splits=args.n_splits, refit_every=args.refit_every,
        calibration_size=args.calibration_size, patch_len=args.patch_len,
        stride=args.stride, d_model=args.d_model, n_heads=args.n_heads,
        n_layers=args.n_layers, dropout=args.dropout,
        fc_dropout=args.fc_dropout, ff_dropout=args.ff_dropout,
        epochs=args.epochs, batch_size=args.batch_size, lr=args.lr,
        device=args.device, val_ratio=args.val_ratio, out_json=args.out_json,
    )

    if args.dry_run:
        print("DRY-RUN: deterministic synthetic log-RV, CPU, tiny model/epochs")
        for key, value in DRY_RUN_OVERRIDES.items():
            params[key] = value
        # Never clobber the real sweep results with a dry-run output.
        if params["out_json"] == DEFAULT_OUT_JSON:
            params["out_json"] = str(
                Path(DEFAULT_OUT_JSON).with_name(
                    "btc_head2head_patchtst_itransformer_dry_run.json"
                )
            )
        rv = synthetic_rv(n=360, seed=0)
        params["dry_run"] = True
    else:
        rv = load_btc_rv()
        if len(rv) < 300:
            raise SystemExit(f"ERROR: only {len(rv)} RV days (need >= 300)")
        params["dry_run"] = False

    run_pipeline(rv, **params)

    if args.dry_run:
        print("DRY-RUN complete. Pipeline validated successfully.")


if __name__ == "__main__":
    main()
