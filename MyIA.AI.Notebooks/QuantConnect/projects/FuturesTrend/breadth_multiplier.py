# -*- coding: utf-8 -*-
"""Pure-numpy Carver breadth multiplier (instantaneous, sign-invariant).

Carver #13 (Carver 2023, *Advanced Futures Trading Strategies*, Harriman House,
ISBN 9780857199683) — soft cap on gross leverage driven by the effective
breadth of absolute forecast magnitudes.

Formula (REPAIR-7 c.1113, semantic correction by adjoint po-2025 habilite n°3
Tell c.15069 strict):

    breadth = sum(|f_i|) / sqrt(sum(f_i^2))

The ratio ranges from **1.0** (one |f_i| dominates, the rest are zero —
MINIMUM effective breadth, MAXIMUM concentration) to **sqrt(N)** (all |f_i|
equal — MAXIMUM effective breadth, ZERO concentration). This is the
*inverse* of a concentration measure.

Sign-invariance: `abs()` removes the sign at the input, so `[10, 10]` and
`[10, -10]` yield the same breadth (sqrt(2)). The final portfolio weight
`forecast / abs_sum` (in `_rebalance`) preserves the sign; only this
multiplier is sign-invariant.

This module is intentionally **pure numpy** so the unit tests in
`tests/test_breadth_multiplier.py` can import `breadth_multiplier` directly
without dragging in `AlgorithmImports` (which requires the QC Cloud
runtime). The production code path (`main_carver13.CarverThirteen`) calls
this same function; the in-class `_breadth_multiplier` method is a thin
wrapper kept only to preserve the API surface.
"""

import numpy as np

BREADTH_MULTIPLIER_MIN = 1.0
BREADTH_MULTIPLIER_MAX = 2.0


def breadth_multiplier(forecasts):
    """Effective breadth multiplier — inverse concentration, sign-invariant.

    Parameters
    ----------
    forecasts : sequence of float
        Per-instrument forecasts (any sign). The sign is removed at the
        input via `abs()`, so `[10, 10]` and `[10, -10]` yield the same
        multiplier.

    Returns
    -------
    float
        Multiplier clipped to [BREADTH_MULTIPLIER_MIN, BREADTH_MULTIPLIER_MAX].
        Returns BREADTH_MULTIPLIER_MIN (=1.0) on an empty input or on an
        input that sums to zero magnitude.
    """
    arr = np.asarray([abs(float(f)) for f in forecasts], dtype=float)
    if arr.size == 0:
        return BREADTH_MULTIPLIER_MIN
    sq_sum = float(np.sum(arr * arr))
    if sq_sum <= 0.0:
        return BREADTH_MULTIPLIER_MIN
    raw = float(np.sum(arr)) / float(np.sqrt(sq_sum))
    return float(np.clip(raw, BREADTH_MULTIPLIER_MIN, BREADTH_MULTIPLIER_MAX))
