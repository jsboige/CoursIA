"""Paired-origin DM protocol tests for the M15 cluster revalidation (#18190 port)."""

from __future__ import annotations

import numpy as np
import pandas as pd
import pytest

from bias_metrics import joined_pair_errors
from m15_lstm_rv import _joined_or_sentinel, _relabel_har_to_lstm_origin


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


@pytest.mark.parametrize("horizon", [1, 5, 10])
def test_relabel_pairs_har_and_lstm_conventions_on_same_window(horizon: int) -> None:
    # Measured defect (2026-10-01, BTC h=1): HAR origin t targets window
    # [t, t+h-1]; the LSTM rolling target at origin t-1 addresses the SAME
    # window. After relabeling HAR onto the previous origin, a date join of
    # the two target series must show gap 0 -- the same realised quantity.
    dates = pd.date_range("2024-01-01", periods=40, freq="D")
    log_rv = pd.Series(np.linspace(-7.0, -5.5, 40) + 0.3 * np.sin(np.arange(40)), index=dates)

    # HAR convention: origin i -> mean(log_rv[i:i+h]). Start at position 10:
    # the real walk-forward first entry sits one fold deep (fold_size >= 30),
    # never on the first trading date of the series.
    out_pos = list(range(10, 40 - horizon))
    har_targets = pd.Series(
        [float(log_rv.iloc[i:i + horizon].mean()) for i in out_pos],
        index=dates[out_pos], name="har_tg",
    )
    har_forecasts = pd.Series(
        har_targets.values - 0.1, index=har_targets.index, name="har_fc"
    )

    # LSTM convention (m15 line: log_rv.rolling(h).mean().shift(-h))
    lstm_targets = log_rv.rolling(horizon).mean().shift(-horizon).dropna()
    lstm_targets.name = "lstm_tg"
    lstm_forecasts = pd.Series(
        lstm_targets.values + 0.1, index=lstm_targets.index, name="lstm_fc"
    )

    har_fc_p, har_tg_p = _relabel_har_to_lstm_origin(
        har_forecasts, har_targets, pd.DatetimeIndex(dates)
    )

    join = joined_pair_errors(
        lstm_forecasts, lstm_targets, har_fc_p, har_tg_p,
    )
    assert join["n_joined"] > 10
    assert join["target_gap_max"] <= 1e-8
    # HAR[t] relabeled to t-1: the paired HAR error at date t-1 equals the
    # HAR error originally at t (same forecast, same window target). No
    # entry is dropped -- each maps to the previous trading date.
    np.testing.assert_allclose(join["b_errors"], (har_forecasts - har_targets).values)


@pytest.mark.parametrize("horizon", [1, 5])
def test_relabel_survives_fold_boundaries_in_the_har_output(horizon: int) -> None:
    # Second measured defect (2026-10-01, run v2, max gap 3.51): both
    # walk-forward loops stop at `test_end - horizon`, so the concatenated
    # HAR output SKIPS h positions at each fold boundary. A positional
    # relabel (values[1:] on index[:-1]) crosses that boundary and pairs
    # windows one day apart. The index-based relabel maps each entry to the
    # previous TRADING date of the full series and must stay gap-free.
    dates = pd.date_range("2024-01-01", periods=60, freq="D")
    log_rv = pd.Series(
        np.linspace(-7.0, -5.0, 60) + 0.5 * np.sin(np.arange(60)), index=dates
    )

    # HAR output with a fold gap: fold A covers positions [10, 30 - h) (one
    # fold deep, as in the real harness), fold B [30, 60 - h) -- the h
    # positions at the boundary are absent, exactly as
    # `range(test_start, test_end - horizon)` produces per fold.
    out_pos = list(range(10, 30 - horizon)) + list(range(30, 60 - horizon))
    har_targets = pd.Series(
        [float(log_rv.iloc[i:i + horizon].mean()) for i in out_pos],
        index=dates[out_pos], name="har_tg",
    )
    har_forecasts = pd.Series(
        har_targets.values - 0.1, index=har_targets.index, name="har_fc"
    )

    full_index = pd.DatetimeIndex(dates)
    har_fc_p, har_tg_p = _relabel_har_to_lstm_origin(
        har_forecasts, har_targets, full_index
    )

    # Each relabeled entry keeps its own value and lands on the previous
    # TRADING date -- including the fold-B opener, which a positional shift
    # would land on the fold-A closer's date instead.
    for d, v in har_fc_p.items():
        origin = full_index[full_index.get_loc(d) + 1]
        assert v == har_forecasts[origin]

    lstm_targets = log_rv.rolling(horizon).mean().shift(-horizon).dropna()
    lstm_targets.name = "lstm_tg"
    lstm_forecasts = pd.Series(
        lstm_targets.values + 0.1, index=lstm_targets.index, name="lstm_fc"
    )

    join = joined_pair_errors(
        lstm_forecasts, lstm_targets, har_fc_p, har_tg_p,
    )
    assert join["n_joined"] > 10
    assert join["target_gap_max"] <= 1e-8
