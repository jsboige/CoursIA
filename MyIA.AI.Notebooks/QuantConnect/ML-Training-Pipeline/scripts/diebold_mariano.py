"""DEPRECATED -- thin compatibility shim over the canonical dm_test module.

The canonical implementation lives in dm_test.py (DMResult dataclass,
Student-t p-values with the HLN correction, n^(1/3) truncation rule,
Bonferroni helper). This module preserves the historical dict-based API
(dm_stat / p_value / significant_05 / significant_01 / n_obs /
interpretation, loss_function="squared"/"absolute", h=, small_sample=,
alternative=, bonferroni keys) so existing callers keep working; it
computes nothing itself.

Behavioral deltas vs the pre-#21945 implementation (frozen by
tests/test_diebold_mariano.py):
- truncation lag: legacy max(1, h-1) -> canonical n^(1/3); to pin a
  legacy lag, import dm_test and pass max_lag explicitly;
- p-value distribution: legacy normal-based -> canonical Student-t when
  small_sample=True (the default);
- Newey-West floor: legacy 1e-15 -> canonical 0.0 (the DM path already
  treats hac_var < 1e-15 as degenerate).

Deprecated since #21945 -- import dm_test instead.

References:
- Diebold & Mariano (1995) "Comparing Predictive Accuracy", JBES 13, 253-263.
- Harvey, Leybourne & Newbold (1997) small-sample correction.
"""

from __future__ import annotations

import warnings

import numpy as np

import dm_test

warnings.warn(
    "diebold_mariano is deprecated since #21945; import dm_test instead "
    "(diebold_mariano_test, bonferroni_dm, newey_west_variance).",
    DeprecationWarning,
    stacklevel=2,
)


def newey_west_variance(x: np.ndarray, lag: int) -> float:
    """Delegate to dm_test.newey_west_variance (floor now 0.0, was 1e-15)."""
    return dm_test.newey_west_variance(np.asarray(x, dtype=float), max_lag=lag)


def diebold_mariano_test(
    errors_model: np.ndarray,
    errors_baseline: np.ndarray,
    loss_function: str = "squared",
    alternative: str = "two-sided",
    h: int = 1,
    small_sample: bool = True,
) -> dict:
    """Deprecated adapter over dm_test.diebold_mariano_test.

    Maps the legacy signature to the canonical one (loss_function
    squared/absolute -> loss_fn mse/mae, h -> horizon, small_sample ->
    hln_correction, alternative unchanged), pre-truncates to the shorter
    series (canonical raises on shape mismatch) and rebuilds the legacy
    dict with interpretation string.
    """
    errors_model = np.asarray(errors_model, dtype=float)
    errors_baseline = np.asarray(errors_baseline, dtype=float)
    n = min(len(errors_model), len(errors_baseline))
    errors_model = errors_model[:n]
    errors_baseline = errors_baseline[:n]

    if loss_function not in ("squared", "absolute"):
        raise ValueError(f"Unknown loss function: {loss_function}")
    if alternative not in ("two-sided", "less", "greater"):
        raise ValueError(f"Unknown alternative: {alternative}")

    if n < 10:
        return {
            "dm_stat": float("nan"),
            "p_value": float("nan"),
            "significant_05": False,
            "significant_01": False,
            "n_obs": n,
            "interpretation": "Too few observations for DM test",
        }

    loss_fn = "mse" if loss_function == "squared" else "mae"
    result = dm_test.diebold_mariano_test(
        errors_model, errors_baseline,
        loss_fn=loss_fn, hln_correction=small_sample, horizon=h,
        alternative=alternative,
    )
    dm_stat = result.dm_statistic
    p_value = result.p_value

    if dm_stat == 0.0 and p_value == 1.0:
        interp = "Identical errors — equal accuracy"
    elif dm_stat < 0 and p_value < 0.05:
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
        "n_obs": result.n_observations,
        "interpretation": interp,
    }


def bonferroni_dm(
    errors_model: np.ndarray,
    errors_baseline: np.ndarray,
    n_tests: int,
    loss_function: str = "squared",
    h: int = 1,
) -> dict:
    """Deprecated adapter: legacy diebold_mariano_test + Bonferroni keys.

    Goes through the shim's own diebold_mariano_test so pre-truncation
    and the n<10 NaN path keep their legacy semantics (the canonical
    dm_test.bonferroni_dm raises instead).
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
