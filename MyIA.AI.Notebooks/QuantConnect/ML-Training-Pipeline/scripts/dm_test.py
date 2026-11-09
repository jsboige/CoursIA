"""Diebold-Mariano test with HAC (Newey-West) variance estimator.

Compares two sets of forecast errors and tests the null hypothesis that
both methods have the same accuracy. Uses the Harvey-Leybourne-Newbold
(HLN) small-sample correction by default.

Truncation rule (frozen since #21945): the default HAC lag is n^(1/3)
(see _optimal_lag), NOT the h-1 rule of the legacy diebold_mariano
module. On the consumer shapes measured for #21945 the two rules diverge
by 0.3-7.7% on the DM statistic (sign never flipped on the measured
shapes); the divergence is frozen by test_dm.py::TestTruncationRule.
Pass max_lag explicitly to reproduce a legacy lag.

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
    """Result of a Diebold-Mariano test.

    p_value follows the ``alternative`` selected on the call: two-sided
    (default), "less" or "greater".
    """
    dm_statistic: float
    p_value: float
    mean_loss_diff: float
    hac_variance: float
    n_observations: int
    lag_truncation: int


def newey_west_variance(x: np.ndarray, max_lag: int) -> float:
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
    # Lags >= n have no paired products; np.mean of an empty slice is
    # nan, so cap the loop there (the legacy estimator returned 0.0 for
    # those lags via np.dot on empty arrays).
    for j in range(1, min(max_lag, n - 1) + 1):
        weight = 1.0 - j / (max_lag + 1)
        gamma_j = np.mean(x[j:] * x[:-j]) - np.mean(x) ** 2
        total += 2.0 * weight * gamma_j
    return max(total, 0.0)


# Retro-compat alias: historical private name kept for existing imports
# (test_dm.py imports _newey_west_variance).
_newey_west_variance = newey_west_variance


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
    alternative: str = "two-sided",
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
        "mse" for squared-error loss, "mae" for absolute-error loss,
        "linear" for signed linear loss L(e) = e.
        mse/mae measure PRECISION and are symmetric in sign: a forecast-error
        series and its exact opposite are bit-identical (equally precise), by
        construction. "linear" computes d_mean = mean(e_a) - mean(e_b) =
        bias_a - bias_b: it compares BIASES, not precision -- it is blind to
        dispersion, and a strictly more precise forecast can lose the test to
        a more biased one (#10956). Do NOT use "linear" as the precision jambe
        of a verdict; it is a bias-differential diagnostic only.
    hln_correction : bool
        Apply Harvey-Leybourne-Newbold (1997) small-sample correction.
    max_lag : int | None
        HAC truncation lag. If None, uses n^(1/3).
    horizon : int
        Forecast horizon h (used in HLN correction). Default 1.
    alternative : str
        "two-sided" (default), "less" (H1: E[d] < 0, model better) or
        "greater" (H1: E[d] > 0, baseline better). Selects the p-value
        tail; Student-t under HLN, normal otherwise.

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
    if alternative not in ("two-sided", "less", "greater"):
        raise ValueError(
            f"alternative must be 'two-sided', 'less' or 'greater', got '{alternative}'"
        )

    if loss_fn == "mse":
        loss_a = errors_a ** 2
        loss_b = errors_b ** 2
    elif loss_fn == "mae":
        loss_a = np.abs(errors_a)
        loss_b = np.abs(errors_b)
    elif loss_fn == "linear":
        # Signed linear loss L(e) = e. d_mean = mean(e_a) - mean(e_b) is a
        # BIAS differential (bias_a - bias_b), not a precision measure: blind
        # to dispersion, a strictly more precise forecast can lose to a more
        # biased one (#10956). Bias diagnostic only -- not a §C precision jambe.
        loss_a = errors_a
        loss_b = errors_b
    else:
        raise ValueError(f"loss_fn must be 'mse', 'mae' or 'linear', got '{loss_fn}'")

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
        if alternative == "two-sided":
            # sf (survival function) instead of 1 - cdf: no catastrophic
            # cancellation in the far tail (#21945).
            p_value = float(2.0 * stats.t.sf(np.abs(dm_stat_corrected), df=n - 1))
        elif alternative == "less":
            p_value = float(stats.t.cdf(dm_stat_corrected, df=n - 1))
        else:  # greater
            p_value = float(stats.t.sf(dm_stat_corrected, df=n - 1))
        reported_stat = dm_stat_corrected
    else:
        if alternative == "two-sided":
            p_value = float(2.0 * stats.norm.sf(np.abs(dm_stat)))
        elif alternative == "less":
            p_value = float(stats.norm.cdf(dm_stat))
        else:  # greater
            p_value = float(stats.norm.sf(dm_stat))
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
    loss_fn: str = "mse",
) -> dict:
    """Run DM test and return a verdict dict with human-readable result.

    mean_loss_diff = mean(loss_a - loss_b) with a = model, b = baseline:
    NEGATIVE means the model has lower loss (model wins); positive means
    the baseline wins. With loss_fn="linear" the DM differential compares
    raw signed errors, so mean_loss_diff is the model-vs-baseline bias gap.

    ``loss_fn`` selects the loss applied to forecast errors before the DM
    differential: ``"mse"`` (squared), ``"mae"`` (absolute), ``"linear"``
    (raw signed errors — bias control, never the conjunction jambe;
    per amended §C (#11010) the conjunction DM must use a precision loss).
    """
    result = diebold_mariano_test(errors_model, errors_baseline, loss_fn=loss_fn, horizon=horizon)
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


def bonferroni_dm(
    errors_model: np.ndarray,
    errors_baseline: np.ndarray,
    n_tests: int,
    loss_fn: str = "mse",
    horizon: int = 1,
    alternative: str = "two-sided",
) -> dict:
    """DM test with Bonferroni correction for multiple comparisons.

    Runs diebold_mariano_test then adjusts p_value by n_tests. The dict
    carries both key families so consumers of the legacy
    diebold_mariano.bonferroni_dm (p_value_adjusted,
    significant_05_bonferroni, n_tests, dm_stat, p_value, significant_05,
    significant_01, n_obs) migrate without key changes, plus the
    canonical diagnostics (dm_statistic, mean_loss_diff, hac_variance,
    lag).
    """
    result = diebold_mariano_test(
        errors_model, errors_baseline,
        loss_fn=loss_fn, horizon=horizon, alternative=alternative,
    )
    adjusted_p = min(result.p_value * n_tests, 1.0)
    return {
        "dm_stat": result.dm_statistic,
        "p_value": result.p_value,
        "significant_05": result.p_value < 0.05,
        "significant_01": result.p_value < 0.01,
        "n_obs": result.n_observations,
        "dm_statistic": result.dm_statistic,
        "mean_loss_diff": result.mean_loss_diff,
        "hac_variance": result.hac_variance,
        "lag": result.lag_truncation,
        "p_value_adjusted": float(adjusted_p),
        "significant_05_bonferroni": adjusted_p < 0.05,
        "n_tests": n_tests,
    }
