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


def _is_beats(verdict: str) -> bool:
    """True only for `dm_verdict`'s winning verdict.

    `dm_verdict` emits exactly three strings: "BEATS baseline",
    "BEATEN BY baseline" and "INCONCLUSIVE". A bare `"BEATS" in verdict`
    also matches "BEATEN BY baseline" under a substring test on some
    tokenisations, hence the explicit exclusion kept from the original code.
    """
    return "BEATS" in verdict and "BEATEN" not in verdict


def _is_beaten(verdict: str) -> bool:
    """True only for `dm_verdict`'s losing verdict ("BEATEN BY baseline").

    The mirror of `_is_beats`. "BEATEN" appears in exactly one of the three
    strings `dm_verdict` emits, so no exclusion clause is needed here -- but
    the guard rails of `_is_beats` still apply the other way round: the two
    sentinel verdicts `_dm_centered_mse` adds ("SHAPE_MISMATCH",
    "INSUFFICIENT_DATA") contain neither token and are therefore counted as
    neither win nor loss.
    """
    return "BEATEN" in verdict


def _aggregate_state(
    n_beats: int,
    n_beaten: int,
    n_seeds: int,
    dm_p_median: float,
    *,
    n_beats_parent: int | None = None,
) -> str:
    """Single state machine shared by the raw and the de-biased (precision) legs.

    Unified in `hmm_regime_vol.py` (#14388): before that, a raw leg with two
    states ("BEATS" iff 4/4 seeds BEATS, else "INCONCLUSIVE") and a de-biased
    leg with four states coexisted, and the executable could not reproduce its
    own published verdict. Extracted here unchanged once `dlinear_vol.py`
    became the third consumer (the extraction pattern this module documents).

    1. unanimous BEATS + significant median  -> "BEATS"
    2. unanimous BEATEN + significant median -> "NO BEATS"
    3. the parent leg was unanimous BEATS   -> "refuted-de-biased"
    4. otherwise                             -> "INCONCLUSIVE"

    `NO BEATS` deliberately outranks `refuted-de-biased` when both apply (a raw
    win that the precision leg significantly reverses). "Refuted" states that a
    claim was not confirmed; the measurement in that case says more than that --
    it says the model loses. Reporting the weaker of the two would soften a
    measured loss, and the refutation stays legible anyway because every summary
    row prints the raw and the de-biased verdict side by side.

    The significance clause is redundant under unanimity (each per-seed BEATS /
    BEATEN already carries p < alpha, so the median of them does too) and is
    kept explicit only because the pre-existing BEATS branch stated it: an
    asymmetric pair of conditions would read as a deliberate difference.

    `n_seeds == 0` yields "INCONCLUSIVE" rather than a vacuous unanimity.
    `n_beats_parent is None` disables the refuted branch (raw-leg callsite).
    """
    if n_seeds <= 0:
        return "INCONCLUSIVE"
    if n_beats == n_seeds and dm_p_median < 0.05:
        return "BEATS"
    if n_beaten == n_seeds and dm_p_median < 0.05:
        return "NO BEATS"
    if n_beats_parent is not None and n_beats_parent == n_seeds:
        return "refuted-de-biased"
    return "INCONCLUSIVE"
