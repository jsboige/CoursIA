"""Diebold-Mariano test with HAC (Newey-West) variance estimator.

Compares two sets of forecast errors and tests the null hypothesis that
both methods have the same accuracy. Uses the Harvey-Leybourne-Newbold
(HLN) small-sample correction by default.

References:
- Diebold & Mariano (1995) "Comparing Predictive Accuracy", JBES 13, 253-263.
- Newey & West (1987) "A Simple, Positive Semi-Definite, Heteroskedasticity
  and Autocorrelation Consistent Covariance Matrix", Econometrica 55, 703-708.
- Harvey, Leybourne & Newbold (1997) "Testing the Equality of Prediction Mean
  Squared Errors", IJF 13, 281-291.
"""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np
from scipy import stats


@dataclass(frozen=True)
class DMResult:
    """Result of a Diebold-Mariano test."""
    dm_statistic: float
    p_value: float
    mean_loss_diff: float
    hac_variance: float
    n_observations: int
    lag_truncation: int


def _newey_west_variance(x: np.ndarray, max_lag: int) -> float:
    """Compute HAC (Newey-West) variance estimator for a univariate series.

    Uses Bartlett kernel weights: w_j = 1 - j / (max_lag + 1).

    Parameters
    ----------
    x : np.ndarray
        1-D array of loss differentials.
    max_lag : int
        Truncation lag for the kernel. Typical choice: floor(sqrt(n)) or n^(1/3).

    Returns
    -------
    float
        HAC variance estimate (guaranteed non-negative by kernel construction).
    """
    n = len(x)
    if n < 2:
        return float(np.var(x, ddof=1))
    gamma_0 = np.mean(x ** 2) - np.mean(x) ** 2
    total = gamma_0
    for j in range(1, max_lag + 1):
        weight = 1.0 - j / (max_lag + 1)
        gamma_j = np.mean(x[j:] * x[:-j]) - np.mean(x) ** 2
        total += 2.0 * weight * gamma_j
    return max(total, 0.0)


def _optimal_lag(n: int) -> int:
    """Select truncation lag using the rule n^(1/3)."""
    return max(1, int(np.floor(n ** (1.0 / 3.0))))


def diebold_mariano_test(
    errors_a: np.ndarray,
    errors_b: np.ndarray,
    loss_fn: str = "mse",
    hln_correction: bool = True,
    max_lag: int | None = None,
    horizon: int = 1,
) -> DMResult:
    """Diebold-Mariano test for equal predictive accuracy.

    Tests H0: E[L(e_a)] = E[L(e_b)] vs H1: E[L(e_a)] != E[L(e_b)].

    Parameters
    ----------
    errors_a : np.ndarray
        Forecast errors from model A (1-D).
    errors_b : np.ndarray
        Forecast errors from model B (1-D), same length as errors_a.
    loss_fn : str
        "mse" for squared-error loss, "mae" for absolute-error loss.
    hln_correction : bool
        Apply Harvey-Leybourne-Newbold (1997) small-sample correction.
    max_lag : int | None
        HAC truncation lag. If None, uses n^(1/3).
    horizon : int
        Forecast horizon h (used in HLN correction). Default 1.

    Returns
    -------
    DMResult with test statistic, p-value, and diagnostics.
    """
    errors_a = np.asarray(errors_a, dtype=float)
    errors_b = np.asarray(errors_b, dtype=float)
    if errors_a.shape != errors_b.shape:
        raise ValueError(
            f"Shape mismatch: errors_a {errors_a.shape} vs errors_b {errors_b.shape}"
        )
    if errors_a.ndim != 1:
        raise ValueError(f"Expected 1-D arrays, got {errors_a.ndim}-D")
    n = len(errors_a)
    if n < 10:
        raise ValueError(f"Need >=10 paired observations for DM test, got {n}")

    if loss_fn == "mse":
        loss_a = errors_a ** 2
        loss_b = errors_b ** 2
    elif loss_fn == "mae":
        loss_a = np.abs(errors_a)
        loss_b = np.abs(errors_b)
    else:
        raise ValueError(f"loss_fn must be 'mse' or 'mae', got '{loss_fn}'")

    d = loss_a - loss_b
    d_mean = float(np.mean(d))
    lag = max_lag if max_lag is not None else _optimal_lag(n)
    hac_var = _newey_west_variance(d, lag)
    if hac_var < 1e-15:
        hac_var = float(np.var(d, ddof=1))

    if hac_var < 1e-15:
        return DMResult(
            dm_statistic=0.0,
            p_value=1.0,
            mean_loss_diff=d_mean,
            hac_variance=0.0,
            n_observations=n,
            lag_truncation=lag,
        )

    dm_stat = d_mean / np.sqrt(hac_var / n)

    if hln_correction:
        correction = np.sqrt((n + 1 - 2 * horizon + horizon * (horizon - 1) / n) / n)
        dm_stat_corrected = dm_stat * correction
        p_value = 2.0 * (1.0 - stats.t.cdf(np.abs(dm_stat_corrected), df=n - 1))
        reported_stat = dm_stat_corrected
    else:
        p_value = 2.0 * (1.0 - stats.norm.cdf(np.abs(dm_stat)))
        reported_stat = dm_stat

    return DMResult(
        dm_statistic=float(reported_stat),
        p_value=float(p_value),
        mean_loss_diff=d_mean,
        hac_variance=hac_var,
        n_observations=n,
        lag_truncation=lag,
    )


def dm_verdict(
    errors_model: np.ndarray,
    errors_baseline: np.ndarray,
    alpha: float = 0.05,
    horizon: int = 1,
) -> dict:
    """Run DM test and return a verdict dict with human-readable result.

    Positive mean_loss_diff means baseline has higher loss (model wins).
    """
    result = diebold_mariano_test(errors_model, errors_baseline, loss_fn="mse", horizon=horizon)
    if result.p_value < alpha and result.mean_loss_diff < 0:
        verdict = "BEATS baseline"
    elif result.p_value < alpha and result.mean_loss_diff > 0:
        verdict = "BEATEN BY baseline"
    else:
        verdict = "INCONCLUSIVE"
    return {
        "dm_statistic": result.dm_statistic,
        "p_value": result.p_value,
        "mean_loss_diff": result.mean_loss_diff,
        "hac_variance": result.hac_variance,
        "n_obs": result.n_observations,
        "lag": result.lag_truncation,
        "verdict": verdict,
        "significant_at": alpha,
    }
