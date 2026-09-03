"""Shared bias/MSE decomposition and centered-DM helpers (#14363).

Extracted from `btc_vol.py` (PR #12742, issue #12734) once a third copy
appeared in `hmm_regime_vol.py` (PR #14359). Deliberately torch-free: the
module must stay importable from CPU-only scripts (`hmm_regime_vol` is HMM +
OLS and needs no torch). The identical-upto-unification docstring below is
the canonical, corrected version (#14362); the three consumers' extra
copies were removed.
"""
from __future__ import annotations

import numpy as np


def _mse_decomposition(errors: np.ndarray) -> dict:
    """Decompose MSE of a forecast into bias^2 + variance on the error support."""
    if errors is None or len(errors) == 0:
        return {"mse": float("nan"), "bias_sq": float("nan"), "variance": float("nan")}
    bias = float(np.mean(errors))
    variance = float(np.var(errors, ddof=0))
    return {
        "mse": float(np.mean(errors ** 2)),
        "bias_sq": bias ** 2,
        "variance": variance,
    }


def _dm_centered_mse(
    errors_a: np.ndarray, errors_b: np.ndarray, horizon: int
) -> dict:
    """DM test on errors centered by their own mean, with loss_fn='mse'.

    Centering annihilates the bias component (`mean(e_a - mean(e_a)) = 0`),
    so the resulting `d_mean` measures only the variance differential. The
    "DM on precision" jambe that #10961 documents is exactly this.

    `loss_fn` stays "mse" on purpose: section C forbids `linear` as the
    conjunction leg, because on raw signed errors `d_mean = bias_a - bias_b`
    is blind to dispersion -- it measures the very quantity centering removes.
    """
    from dm_test import dm_verdict as dm_verdict_fn

    e_a = np.asarray(errors_a, dtype=float)
    e_b = np.asarray(errors_b, dtype=float)
    if e_a.shape != e_b.shape:
        return {"dm_stat": float("nan"), "dm_pvalue": float("nan"), "dm_verdict": "SHAPE_MISMATCH"}
    n = len(e_a)
    if n < 10:
        return {"dm_stat": float("nan"), "dm_pvalue": float("nan"), "dm_verdict": "INSUFFICIENT_DATA"}

    centered_a = e_a - np.mean(e_a)
    centered_b = e_b - np.mean(e_b)
    res = dm_verdict_fn(centered_a, centered_b, horizon=horizon, loss_fn="mse")
    return {
        "dm_stat": float(res["dm_statistic"]),
        "dm_pvalue": float(res["p_value"]),
        "dm_verdict": str(res["verdict"]),
        "mean_loss_diff": float(res["mean_loss_diff"]),
    }