"""Paired-origin DM protocol tests for the M13 cluster revalidation (#18190 port).

M13 specifics vs the M4/M15 ports: the Markov-Switching HAR leg and the classic
HAR baseline are produced from the SAME `rv` series on the SAME split schedule,
so the two OOS series share their origin dates by construction -- the date-join
is expected to be the identity, and the guard is the proof, not the correction.

The pre-port `evaluate_one_combo` reused the HAR leg's target for BOTH
predictions (`har_out["targets"].reindex(...)` then reindexing the MS forecasts
onto it), which silently ignored any divergence between the two legs' realised
targets. These tests pin the contract that replaced it: each leg brings its own
target, the join refuses on a shared-target mismatch, and a refused pairing can
never contribute a verdict.
"""

from __future__ import annotations

import numpy as np
import pandas as pd
import pytest

from bias_metrics import joined_pair_errors
from m13_ms_har import _aggregate_cell, _joined_or_sentinel

DATES = pd.date_range("2024-01-01", periods=8, freq="D")


def _series(dates, values, name):
    return pd.Series(values, index=pd.DatetimeIndex(dates), name=name)


def _row(
    *,
    dm_verdict: str,
    dm_centered_verdict: str,
    dm_p: float = 1e-4,
    dm_centered_p: float = 1e-4,
    ms_mse: float = 0.9,
    har_mse: float = 1.0,
    har_mse_debiased: float = 0.8,
    reduction: float = 10.0,
    reduction_debiased: float = 20.0,
) -> dict:
    """One synthetic per-seed row carrying every field `_aggregate_cell` reads."""
    return {
        "dm_verdict": dm_verdict,
        "dm_centered_verdict": dm_centered_verdict,
        "dm_p_value": dm_p,
        "dm_centered_pvalue": dm_centered_p,
        "ms_mse_joined": ms_mse,
        "har_mse_joined": har_mse,
        "har_mse_debiased": har_mse_debiased,
        "mse_reduction_pct_joined": reduction,
        "mse_reduction_pct_vs_debiased_classic": reduction_debiased,
        "ms_bias_oos": 0.01,
        "har_bias_oos": 0.05,
        "har_bias_share_of_mse": 0.0025,
    }


# --- the shared organ's contract, as M13 consumes it ------------------------


def test_join_pairs_on_origin_dates_with_shared_targets() -> None:
    tg = np.linspace(-7.0, -6.0, 8)
    ms_fc = tg + 0.1
    har_fc = tg - 0.2

    join = joined_pair_errors(
        _series(DATES, ms_fc, "ms"), _series(DATES, tg, "ms_tg"),
        _series(DATES, har_fc, "har"), _series(DATES, tg, "har_tg"),
    )

    assert join["n_joined"] == 8
    assert join["target_gap_max"] == pytest.approx(0.0, abs=1e-12)
    np.testing.assert_allclose(join["a_errors"], ms_fc - tg)
    np.testing.assert_allclose(join["b_errors"], har_fc - tg)


def test_join_refuses_on_shared_target_mismatch() -> None:
    tg_ms = np.linspace(-7.0, -6.0, 8)
    tg_har = tg_ms + 1e-3  # not the same realised quantity

    with pytest.raises(ValueError, match="shared-target mismatch"):
        joined_pair_errors(
            _series(DATES, tg_ms + 0.1, "ms"), _series(DATES, tg_ms, "ms_tg"),
            _series(DATES, tg_har - 0.2, "har"), _series(DATES, tg_har, "har_tg"),
        )


def test_sentinel_wrapper_records_refusal_without_raising() -> None:
    tg = np.linspace(-7.0, -6.0, 8)
    row_extra: dict = {}

    out = _joined_or_sentinel(
        (_series(DATES, tg, "ms"), _series(DATES, tg, "ms_tg"),
         _series(DATES, tg, "har"), _series(DATES, tg + 1e-3, "har_tg")),
        row_extra,
    )

    assert out is None
    assert "shared-target mismatch" in row_extra["dm_target_refusal"]


# --- the per-cell four-state aggregate --------------------------------------


def test_aggregate_cell_unanimous_beats_on_both_legs() -> None:
    cell = [
        _row(dm_verdict="BEATS baseline", dm_centered_verdict="BEATS baseline")
        for _ in range(4)
    ]

    agg = _aggregate_cell("BTC-USD", 1, cell)

    assert agg["n_seeds"] == 4
    assert agg["n_beats_seeds"] == "4/4"
    assert agg["aggregate_verdict"] == "BEATS"
    assert agg["aggregate_verdict_debiased"] == "BEATS"
    assert agg["seed"] == "aggregate"
    assert agg["mean_ms_mse"] == pytest.approx(0.9)


def test_aggregate_cell_refuted_when_raw_wins_but_precision_leg_does_not() -> None:
    """A raw 4/4 win the de-biased leg does not confirm -> `refuted-de-biased`.

    The raw leg is unanimous BEATS while the centered leg splits -- the edge
    came from the baseline's miscalibration, which is exactly the state
    `_aggregate_state` reserves for this verdict (#12788 formulation).
    """
    cell = [
        _row(dm_verdict="BEATS baseline", dm_centered_verdict="BEATS baseline"),
        _row(dm_verdict="BEATS baseline", dm_centered_verdict="INCONCLUSIVE"),
        _row(dm_verdict="BEATS baseline", dm_centered_verdict="INCONCLUSIVE"),
        _row(dm_verdict="BEATS baseline", dm_centered_verdict="BEATEN BY baseline"),
    ]

    agg = _aggregate_cell("ETH-USD", 5, cell)

    assert agg["aggregate_verdict"] == "BEATS"
    assert agg["aggregate_verdict_debiased"] == "refuted-de-biased"
    assert agg["n_beats_seeds_centered"] == "1/4"
    assert agg["n_beaten_seeds_centered"] == "1/4"


def test_aggregate_cell_counts_target_mismatch_as_neither_win_nor_loss() -> None:
    """A refused pairing never contributes to a verdict.

    Every seed carries the `TARGET_MISMATCH` sentinel emitted by the port when
    `joined_pair_errors` refuses: the four-state machine then sees 0 BEATS and
    0 BEATEN out of 4 and reports INCONCLUSIVE rather than a vacuous unanimity.
    """
    cell = [
        _row(dm_verdict="TARGET_MISMATCH", dm_centered_verdict="TARGET_MISMATCH",
             dm_p=float("nan"), dm_centered_p=float("nan"))
        for _ in range(4)
    ]

    agg = _aggregate_cell("SOL-USD", 10, cell)

    assert agg["n_beats_seeds"] == "0/4"
    assert agg["n_beaten_seeds"] == "0/4"
    assert agg["aggregate_verdict"] == "INCONCLUSIVE"
    assert agg["aggregate_verdict_debiased"] == "INCONCLUSIVE"


def test_aggregate_cell_unanimous_beaten_is_no_beats() -> None:
    cell = [
        _row(dm_verdict="BEATEN BY baseline", dm_centered_verdict="BEATEN BY baseline")
        for _ in range(4)
    ]

    agg = _aggregate_cell("DOT-USD", 10, cell)

    assert agg["aggregate_verdict"] == "NO BEATS"
    assert agg["aggregate_verdict_debiased"] == "NO BEATS"
