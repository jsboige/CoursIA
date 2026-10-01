"""Paired-origin DM protocol tests for the M15 cluster revalidation (#18190 port)."""

from __future__ import annotations

import numpy as np
import pandas as pd
import pytest

from bias_metrics import joined_pair_errors
from m15_lstm_rv import _joined_or_sentinel


def _series(dates, values, name):
    return pd.Series(values, index=pd.DatetimeIndex(dates), name=name)


DATES = pd.date_range("2024-01-01", periods=8, freq="D")


def test_join_pairs_on_origin_dates_with_shared_targets() -> None:
    tg = np.linspace(-7.0, -6.0, 8)
    lstm_fc = tg + 0.1
    har_fc = tg - 0.2
    join = joined_pair_errors(
        _series(DATES, lstm_fc, "lstm"), _series(DATES, tg, "lstm_tg"),
        _series(DATES, har_fc, "har"), _series(DATES, tg, "har_tg"),
    )

    assert join["n_joined"] == 8
    assert join["target_gap_max"] == pytest.approx(0.0, abs=1e-12)
    np.testing.assert_allclose(join["a_errors"], lstm_fc - tg)
    np.testing.assert_allclose(join["b_errors"], har_fc - tg)


def test_join_drops_lstm_nan_guard_days_instead_of_pairing_positionally() -> None:
    # walk_forward_lstm drops non-finite predictions day by day (its NaN
    # guard) while HAR still forecasts those days: positional pairing would
    # compare errors from different origin dates.
    tg = np.linspace(-7.0, -6.0, 8)
    har_fc = tg - 0.2
    keep = [0, 2, 3, 4, 5, 6, 7]  # day 1 dropped by the LSTM guard
    lstm_dates = DATES.delete(1)

    join = joined_pair_errors(
        _series(lstm_dates, (tg - 0.1)[keep], "lstm"),
        _series(lstm_dates, tg[keep], "lstm_tg"),
        _series(DATES, har_fc, "har"), _series(DATES, tg, "har_tg"),
    )

    assert join["n_joined"] == 7
    assert DATES[1] not in join["joined_dates"]
    np.testing.assert_allclose(join["a_errors"], np.delete((tg - 0.1) - tg, 1))
    np.testing.assert_allclose(join["b_errors"], np.delete(har_fc - tg, 1))


def test_join_refuses_on_shared_target_mismatch() -> None:
    tg_a = np.linspace(-7.0, -6.0, 8)
    tg_b = tg_a + 1e-3  # not the same realised quantity

    with pytest.raises(ValueError, match="shared-target mismatch"):
        joined_pair_errors(
            _series(DATES, tg_a + 0.1, "lstm"), _series(DATES, tg_a, "lstm_tg"),
            _series(DATES, tg_a - 0.2, "har"), _series(DATES, tg_b, "har_tg"),
        )


def test_sentinel_wrapper_records_refusal_without_raising() -> None:
    tg = np.linspace(-7.0, -6.0, 8)
    row_extra: dict = {}

    out = _joined_or_sentinel(
        (_series(DATES, tg, "lstm"), _series(DATES, tg, "lstm_tg"),
         _series(DATES, tg, "har"), _series(DATES, tg + 1e-3, "har_tg")),
        row_extra,
    )

    assert out is None
    assert "shared-target mismatch" in row_extra["dm_target_refusal"]


def test_join_tolerates_ulp_level_target_difference() -> None:
    # The same realised target computed by two code paths (HAR's rolling mean
    # vs the LSTM's array-built mean) can differ by float association order:
    # the tolerance exists for exactly that and must not refuse.
    dates = pd.date_range("2024-01-01", periods=64)
    tg = np.linspace(-7.0, -6.0, 64)
    lstm_fc = tg + 0.05
    har_fc = tg - 0.05
    tg_b = tg.copy()
    tg_b[7] = np.nextafter(tg_b[7], tg_b[7] + 1.0)

    join = joined_pair_errors(
        _series(dates, lstm_fc, "lstm"), _series(dates, tg, "lstm_tg"),
        _series(dates, har_fc, "har"), _series(dates, tg_b, "har_tg"),
    )

    assert join["n_joined"] == 64
    assert join["target_gap_max"] <= 1e-8
