"""Significance of a walk-forward regime strategy against its references.

Protocol #21329 / #21633: the delta-Sharpe of the strategy versus each
reference (50/50 SPY-TLT rebalanced, SPY held) is tested by Ledoit-Wolf (2008)
on the paired daily returns, with a Newey-West HAC truncation lag, and the
p-values are corrected by Holm. All Sharpes are at zero risk-free rate,
annualised by sqrt(252).

This module reuses the pipeline's existing significance organs
(`m11c_sharpe_test.ledoit_wolf_sharpe_diff_se`,
`m11c_sharpe_test.stationary_bootstrap_sharpe_diff`) on raw paired daily
returns. It does not re-implement the Ledoit-Wolf or bootstrap math.

Verdict semantics (pre-registered, #21633 protocol point 8):
  BEATS        : delta positive against EVERY reference AND every
                 Holm-adjusted Ledoit-Wolf p < 0.05
  INCONCLUSIVE : delta positive against every reference, at least one
                 stationary-bootstrap 95% CI covers 0, no Holm p < 0.05
  NO BEATS     : otherwise
"""
from __future__ import annotations

import math

import numpy as np

from m11c_sharpe_test import (  # noqa: E402
    ledoit_wolf_sharpe_diff_se,
    stationary_bootstrap_sharpe_diff,
)

ANNUAL = math.sqrt(252.0)


def hac_lag(t: int) -> int:
    """HAC truncation lag: floor(T^0.25), at least 1 (same as #21329 organ)."""
    return max(1, int(math.floor(t ** 0.25)))


def two_sided_p(z: float) -> float:
    """Two-sided p-value of a centred-reduced normal statistic."""
    return math.erfc(abs(z) / math.sqrt(2.0))


def holm(pvalues: dict[str, float]) -> dict[str, float]:
    """Holm-Bonferroni adjusted p-values (monotone, capped at 1)."""
    order = sorted(pvalues, key=pvalues.get)
    m = len(order)
    adjusted: dict[str, float] = {}
    running = 0.0
    for i, key in enumerate(order):
        running = max(running, min(1.0, (m - i) * pvalues[key]))
        adjusted[key] = running
    return adjusted


def compare_to_references(
    strategy: np.ndarray,
    refs: dict[str, np.ndarray],
    n_boot: int = 2000,
    seed: int = 0,
) -> dict:
    """Compare a strategy's daily net returns against named references.

    Parameters
    ----------
    strategy : (T,) daily net returns of the regime strategy.
    refs : {name: (T,) daily returns} — each reference paired on the same index.

    Returns
    -------
    dict with per-reference Sharpes, Ledoit-Wolf p, Holm p, bootstrap 95% CI,
    plus the aggregate pre-registered verdict.
    """
    strategy = np.asarray(strategy, dtype=float).ravel()
    comps: dict[str, dict] = {}
    raw: dict[str, float] = {}
    for name, r_b in refs.items():
        r_b = np.asarray(r_b, dtype=float).ravel()
        sa, sb, diff, se = ledoit_wolf_sharpe_diff_se(strategy, r_b, q=hac_lag(len(strategy)))
        z = diff / se if se > 0 else 0.0
        p_lw = two_sided_p(z)
        p_one, _obs, boots = stationary_bootstrap_sharpe_diff(
            strategy, r_b, n_boot=n_boot, mean_block=10.0, rng_seed=seed
        )
        lo, hi = np.percentile(boots, [2.5, 97.5])
        comps[name] = {
            "sharpe_strategy": sa * ANNUAL,
            "sharpe_reference": sb * ANNUAL,
            "sharpe_diff": diff * ANNUAL,
            "ledoit_wolf_p": p_lw,
            "bootstrap_ci95": [float(lo) * ANNUAL, float(hi) * ANNUAL],
            "bootstrap_ci_covers_zero": bool(lo <= 0.0 <= hi),
        }
        raw[name] = p_lw
    p_holm = holm(raw)
    for name in comps:
        comps[name]["holm_p"] = p_holm[name]

    diffs = [c["sharpe_diff"] for c in comps.values()]
    all_pos = all(d > 0 for d in diffs)
    all_sig = all(p_holm[n] < 0.05 for n in p_holm)
    any_ci_zero = any(c["bootstrap_ci_covers_zero"] for c in comps.values())
    if all_pos and all_sig:
        verdict = "BEATS"
    elif all_pos and any_ci_zero:
        verdict = "INCONCLUSIVE"
    else:
        verdict = "NO BEATS"
    return {"comparisons": comps, "p_raw": raw, "p_holm": p_holm, "verdict": verdict}
