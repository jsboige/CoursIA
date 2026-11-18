"""Paired-origin DM protocol tests for the M5 cluster revalidation (#18190 port).

M5 specifics vs the M4/M15 ports: the regime-switching HAR and the classic HAR
baselines are produced by the SAME walk-forward loop, so the two OOS series
share their origin dates by construction -- the date-join is expected to be
the identity, and the guard is the proof, not the correction. A future edit
that drops or skips an origin on one leg only (dropna, fold guard, refit
boundary) must be refused, never silently paired positionally.
"""

from __future__ import annotations

import numpy as np
import pandas as pd
import pytest

from bias_metrics import joined_pair_errors
from hmm_regime_vol import _joined_or_sentinel, walk_forward_regime_switching


def _series(dates, values, name):
    return pd.Series(values, index=pd.DatetimeIndex(dates), name=name)


DATES = pd.date_range("2024-01-01", periods=8, freq="D")


def test_join_pairs_on_origin_dates_with_shared_targets() -> None:
    tg = np.linspace(-7.0, -6.0, 8)
    a_fc = tg + 0.1
    b_fc = tg - 0.2
    join = joined_pair_errors(
        _series(DATES, a_fc, "a"), _series(DATES, tg, "a_tg"),
        _series(DATES, b_fc, "b"), _series(DATES, tg, "b_tg"),
    )

    assert join["n_joined"] == 8
    assert join["target_gap_max"] == pytest.approx(0.0, abs=1e-12)
    np.testing.assert_allclose(join["a_errors"], a_fc - tg)
    np.testing.assert_allclose(join["b_errors"], b_fc - tg)


def test_join_drops_unmatched_origins_instead_of_pairing_positionally() -> None:
    tg = np.linspace(-7.0, -6.0, 8)
    a_fc = tg + 0.5
    b_fc = np.delete(tg - 0.2, 1)
    b_tg = np.delete(tg, 1)
    b_dates = DATES.delete(1)

    join = joined_pair_errors(
        _series(DATES, a_fc, "a"), _series(DATES, tg, "a_tg"),
        _series(b_dates, b_fc, "b"), _series(b_dates, b_tg, "b_tg"),
    )

    assert join["n_joined"] == 7
    assert DATES[1] not in join["joined_dates"]
    np.testing.assert_allclose(join["a_errors"], np.delete(a_fc - tg, 1))
    np.testing.assert_allclose(join["b_errors"], b_fc - b_tg)


def test_join_refuses_on_shared_target_mismatch() -> None:
    tg_a = np.linspace(-7.0, -6.0, 8)
    tg_b = tg_a + 1e-3  # not the same realised quantity

    with pytest.raises(ValueError, match="shared-target mismatch"):
        joined_pair_errors(
            _series(DATES, tg_a + 0.1, "a"), _series(DATES, tg_a, "a_tg"),
            _series(DATES, tg_a - 0.2, "b"), _series(DATES, tg_b, "b_tg"),
        )


def test_sentinel_wrapper_records_refusal_without_raising() -> None:
    tg = np.linspace(-7.0, -6.0, 8)
    row_extra: dict = {}

    out = _joined_or_sentinel(
        (_series(DATES, tg, "a"), _series(DATES, tg, "a_tg"),
         _series(DATES, tg, "b"), _series(DATES, tg + 1e-3, "b_tg")),
        row_extra,
    )

    assert out is None
    assert "shared-target mismatch" in row_extra["dm_target_refusal"]


def test_join_tolerates_ulp_level_target_difference() -> None:
    dates = pd.date_range("2024-01-01", periods=64)
    tg = np.linspace(-7.0, -6.0, 64)
    a_fc = tg + 0.05
    b_fc = tg - 0.05
    tg_b = tg.copy()
    tg_b[7] = np.nextafter(tg_b[7], tg_b[7] + 1.0)

    join = joined_pair_errors(
        _series(dates, a_fc, "a"), _series(dates, tg, "a_tg"),
        _series(dates, b_fc, "b"), _series(dates, tg_b, "b_tg"),
    )

    assert join["n_joined"] == 64
    assert join["target_gap_max"] <= 1e-8


def test_walk_forward_pairs_both_legs_on_all_origins() -> None:
    """The harness's own legs join on every origin date (identity pairing).

    Both legs come out of the same loop, so `dm_n_aligned` must equal
    `n_preds`, the target gap must be exactly 0 and no refusal may be
    recorded -- the cluster protocol's proof that M5 never compares
    positionally.
    """
    rng = np.random.default_rng(0)
    idx = pd.bdate_range("2023-01-02", periods=260)
    log_rv = np.cumsum(rng.normal(0.0, 0.05, 260)) - 9.0
    rv = pd.Series(np.exp(log_rv), index=idx)

    res = walk_forward_regime_switching(rv, horizon=1, seed=0, n_splits=3, refit_every=22)

    assert res["n_preds"] > 0
    assert res["dm_n_aligned"] == res["n_preds"]
    assert res["dm_target_gap_max"] == pytest.approx(0.0, abs=1e-12)
    assert "dm_target_refusal" not in res
