"""Diebold-Mariano test with Newey-West HAC variance correction.

Tests H0: model A and model B have equal forecast accuracy against
H1: they differ (two-sided) or one is better (one-sided).

References:
- Diebold & Mariano (1995) "Comparing Predictive Accuracy"
- Newey & West (1987) "A Simple, Positive Semi-Definite, Heteroskedasticity
  and Autocorrelation Consistent Covariance Matrix"
- Harvey, Leybourne & Newbold (1997) small-sample correction
"""

from __future__ import annotations

import numpy as np
from scipy import stats


def newey_west_variance(x: np.ndarray, lag: int) -> float:
    """Newey-West HAC long-run variance estimator.

    Parameters
    ----------
    x : array
        Series to estimate variance of (typically loss differentials).
    lag : int
        Truncation lag. DM recommend lag = h-1 for h-step forecasts.

    Returns
    -------
    float
        HAC variance estimate.
    """
    n = len(x)
    if n < 2:
        return float(np.var(x, ddof=1))
    x = x - np.mean(x)
    gamma_0 = float(np.dot(x, x) / n)
    gamma_sum = gamma_0
    for k in range(1, lag + 1):
        weight = 1.0 - k / (lag + 1)
        gamma_k = float(np.dot(x[k:], x[:-k]) / n)
        gamma_sum += 2.0 * weight * gamma_k
    return max(gamma_sum, 1e-15)


def diebold_mariano_test(
    errors_model: np.ndarray,
    errors_baseline: np.ndarray,
    loss_function: str = "squared",
    alternative: str = "two-sided",
    h: int = 1,
    small_sample: bool = True,
) -> dict:
    """Diebold-Mariano test for equal predictive accuracy.

    Parameters
    ----------
    errors_model : array
        Forecast errors from the candidate model (y_true - y_pred).
    errors_baseline : array
        Forecast errors from the baseline (y_true - y_pred).
    loss_function : str
        "squared" (MSE) or "absolute" (MAE).
    alternative : str
        "two-sided", "less" (model better), or "greater" (baseline better).
    h : int
        Forecast horizon (used for Newey-West lag = h-1).
    small_sample : bool
        Apply Harvey-Leybourne-Newbold (1997) small-sample correction.

    Returns
    -------
    dict with keys:
        dm_stat: float — DM test statistic (negative = model better)
        p_value: float — p-value
        significant_05: bool — significant at 5%
        significant_01: bool — significant at 1%
        n_obs: int — number of observations
        interpretation: str — human-readable
    """
    errors_model = np.asarray(errors_model, dtype=float)
    errors_baseline = np.asarray(errors_baseline, dtype=float)
    n = min(len(errors_model), len(errors_baseline))
    errors_model = errors_model[:n]
    errors_baseline = errors_baseline[:n]

    if n < 10:
        return {
            "dm_stat": float("nan"),
            "p_value": float("nan"),
            "significant_05": False,
            "significant_01": False,
            "n_obs": n,
            "interpretation": "Too few observations for DM test",
        }

    if loss_function == "squared":
        loss_a = errors_model ** 2
        loss_b = errors_baseline ** 2
    elif loss_function == "absolute":
        loss_a = np.abs(errors_model)
        loss_b = np.abs(errors_baseline)
    else:
        raise ValueError(f"Unknown loss function: {loss_function}")

    d = loss_a - loss_b
    d_mean = float(np.mean(d))

    if np.allclose(d, d_mean):
        return {
            "dm_stat": 0.0,
            "p_value": 1.0,
            "significant_05": False,
            "significant_01": False,
            "n_obs": n,
            "interpretation": "Identical errors — equal accuracy",
        }

    lag = max(1, h - 1)
    hac_var = newey_west_variance(d, lag=lag)
    dm_stat = d_mean / np.sqrt(hac_var / n)

    if small_sample:
        correction = np.sqrt((n + 1 - 2 * h + h * (h - 1) / n) / n)
        dm_stat = dm_stat * correction

    if alternative == "two-sided":
        p_value = float(2 * stats.norm.sf(np.abs(dm_stat)))
    elif alternative == "less":
        p_value = float(stats.norm.cdf(dm_stat))
    elif alternative == "greater":
        p_value = float(stats.norm.sf(dm_stat))
    else:
        raise ValueError(f"Unknown alternative: {alternative}")

    if dm_stat < 0 and p_value < 0.05:
        interp = f"Model significantly better (DM={dm_stat:.3f}, p={p_value:.4f})"
    elif dm_stat > 0 and p_value < 0.05:
        interp = f"Baseline significantly better (DM={dm_stat:.3f}, p={p_value:.4f})"
    else:
        interp = f"No significant difference (DM={dm_stat:.3f}, p={p_value:.4f})"

    return {
        "dm_stat": float(dm_stat),
        "p_value": float(p_value),
        "significant_05": p_value < 0.05,
        "significant_01": p_value < 0.01,
        "n_obs": n,
        "interpretation": interp,
    }


def bonferroni_dm(
    errors_model: np.ndarray,
    errors_baseline: np.ndarray,
    n_tests: int,
    loss_function: str = "squared",
    h: int = 1,
) -> dict:
    """DM test with Bonferroni correction for multiple comparisons.

    Parameters
    ----------
    n_tests : int
        Total number of DM tests being conducted (for Bonferroni correction).
    """
    result = diebold_mariano_test(
        errors_model, errors_baseline,
        loss_function=loss_function, h=h,
    )
    adjusted_p = min(result["p_value"] * n_tests, 1.0)
    result["p_value_adjusted"] = float(adjusted_p)
    result["significant_05_bonferroni"] = adjusted_p < 0.05
    result["n_tests"] = n_tests
    return result
