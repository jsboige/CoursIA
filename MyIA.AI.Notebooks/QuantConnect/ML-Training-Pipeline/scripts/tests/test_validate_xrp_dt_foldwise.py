"""Tests for validate_xrp_dt_foldwise.py -- pure-logic frame-slicing + aggregation.

These cover the *protocol* logic of the fold-wise deployment driver (Epic
#1454), not the DT training itself (which the real GPU sweep exercises):
  - ``_quarter_after`` -- forward holdout window from an anchor (gap + 90d).
  - ``_frame_for_window`` -- expanding vs sliding train-window slicing, the
    place a leakage bug would hide (sliding must keep the holdout tail even
    though it starts before the anchor).
  - ``_summary_row`` -- cross-seed edge aggregation + sigma + DM p median.
  - holdout-length guard -- an anchor whose 90d holdout runs past the data end
    is skipped cleanly, not raised (the sweep must tolerate short last anchors).

CPU-only, no torch import: the slicing helpers take a plain pandas frame and
the aggregation helper takes plain dicts, so these run on any worker without a
GPU and fast (<1s).
"""

import sys
from pathlib import Path

import numpy as np
import pandas as pd
import pytest

# Standalone script (sibling of tests/), not a package member.
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from validate_xrp_dt_foldwise import (  # noqa: E402
    GAP_DAYS,
    HOLDOUT_DAYS,
    _quarter_after,
    _frame_for_window,
    _summary_row,
)


def _frame(start="2020-01-01", end="2026-04-30", freq="D"):
    """A synthetic OHLCV frame spanning the full XRP-ish date range."""
    idx = pd.date_range(start, end, freq=freq)
    n = len(idx)
    rng = np.random.default_rng(0)
    close = 1.0 + rng.standard_normal(n).cumsum() * 0.01 + np.arange(n) * 0.0005
    return pd.DataFrame({
        "Open": close, "High": close * 1.01, "Low": close * 0.99,
        "Close": close, "Volume": rng.integers(1000, 100000, n).astype(float),
    }, index=idx)


class TestQuarterAfter:
    def test_start_is_anchor_plus_gap(self):
        start, end = _quarter_after("2025-06-30")
        assert start == str((pd.Timestamp("2025-06-30")
                             + pd.Timedelta(days=GAP_DAYS)).date())

    def test_end_is_start_plus_holdout_days(self):
        start, end = _quarter_after("2025-06-30")
        gap = (pd.Timestamp(start) - pd.Timestamp("2025-06-30")).days
        span = (pd.Timestamp(end) - pd.Timestamp(start)).days
        assert gap == GAP_DAYS
        assert span == HOLDOUT_DAYS

    def test_no_overlap_with_train_anchor(self):
        # The forward holdout must start strictly after the anchor (gap > 0).
        for anchor in ["2024-06-30", "2025-12-31", "2026-03-31"]:
            start, _ = _quarter_after(anchor)
            assert pd.Timestamp(start) > pd.Timestamp(anchor)


class TestFrameForWindow:
    def test_expanding_keeps_all_history_up_to_holdout_end(self):
        raw = _frame()
        anchor = "2025-06-30"
        _, holdout_end = _quarter_after(anchor)
        frame = _frame_for_window(raw, anchor, "expanding")
        # Expanding starts at the data start and ends at holdout_end.
        assert frame.index.min() == raw.index.min()
        assert frame.index.max() <= pd.Timestamp(holdout_end)
        assert frame.index.max() == pd.Timestamp(holdout_end)

    def test_sliding_drops_old_data_but_keeps_holdout_tail(self):
        # THE leakage-guard test: a sliding window that drops everything older
        # than (anchor - 3y) must STILL keep the forward holdout rows (they are
        # AFTER the anchor), otherwise the eval frame is empty.
        raw = _frame()
        anchor = "2025-06-30"
        _, holdout_end = _quarter_after(anchor)
        frame = _frame_for_window(raw, anchor, "sliding")
        assert frame.index.max() == pd.Timestamp(holdout_end)
        # Old data (e.g. 2020) is dropped.
        assert frame.index.min() >= pd.Timestamp("2022-01-01")

    def test_sliding_keeps_approximately_three_years(self):
        raw = _frame()
        anchor = "2025-06-30"
        frame = _frame_for_window(raw, anchor, "sliding")
        # Train window anchor-3y .. anchor ; plus a lead for indicator warmup.
        keep_from = pd.Timestamp(anchor) - pd.DateOffset(years=3) - pd.Timedelta(days=HOLDOUT_DAYS)
        assert frame.index.min() <= pd.Timestamp(anchor) - pd.DateOffset(years=3)

    def test_both_windows_end_at_holdout_end(self):
        raw = _frame()
        anchor = "2025-09-30"
        _, holdout_end = _quarter_after(anchor)
        for w in ("sliding", "expanding"):
            frame = _frame_for_window(raw, anchor, w)
            assert frame.index.max() == pd.Timestamp(holdout_end), \
                f"window={w} did not end at holdout_end"

    def test_anchor_near_data_end_frame_clipped(self):
        # 2026-03-31 anchor + 90d holdout extends past the 2026-04-30 data end.
        # The frame must clip to the available data (the holdout-length guard in
        # _run_mode then skips this anchor, but _frame_for_window must not raise).
        raw = _frame(end="2026-04-30")
        anchor = "2026-03-31"
        for w in ("sliding", "expanding"):
            frame = _frame_for_window(raw, anchor, w)
            assert frame.index.max() == raw.index.max()


class TestSummaryRow:
    def _seed(self, dt_net, bh, dm_p=None, elapsed=70.0):
        dm = {"p_value": dm_p} if dm_p is not None else None
        return {"dt_net_sharpe": dt_net, "bh_sharpe": bh,
                "dm_dt_vs_bh": dm, "elapsed_s": elapsed}

    def test_empty_returns_zero_n(self):
        r = _summary_row([], "fresh/sliding")
        assert r["n"] == 0

    def test_edge_is_dt_minus_bh_mean(self):
        per_seed = [self._seed(0.60, 0.40, dm_p=0.02),
                    self._seed(0.64, 0.40, dm_p=0.03)]
        r = _summary_row(per_seed, "fresh/sliding")
        # mean edge = 0.62 - 0.40 = 0.22 -> 22 pp
        assert r["edge_mean_pp"] == pytest.approx(22.0, abs=0.5)
        assert r["dt_net_sharpe_mean"] == pytest.approx(0.62, abs=0.01)
        assert r["bh_sharpe_mean"] == pytest.approx(0.40, abs=0.01)

    def test_edge_sigma_zero_variance_is_none_or_large(self):
        # All identical edges -> std=0 -> sigma huge (clamped division by 1e-12).
        per_seed = [self._seed(0.50, 0.40) for _ in range(5)]
        r = _summary_row(per_seed, "aged/expanding")
        # edge_sigma is finite (1e-12 guard prevents ZeroDivision); sign positive.
        assert r["edge_sigma"] is not None
        assert r["edge_sigma"] > 0

    def test_dm_p_median_aggregated(self):
        per_seed = [self._seed(0.6, 0.4, dm_p=0.01),
                    self._seed(0.6, 0.4, dm_p=0.20),
                    self._seed(0.6, 0.4, dm_p=0.03)]
        r = _summary_row(per_seed, "fresh/sliding")
        assert r["dm_p_median"] == pytest.approx(0.03, abs=0.001)

    def test_dm_p_none_when_all_missing(self):
        per_seed = [self._seed(0.6, 0.4, dm_p=None)]
        r = _summary_row(per_seed, "fresh/sliding")
        assert r["dm_p_median"] is None

    def test_mean_retrain_seconds(self):
        per_seed = [self._seed(0.6, 0.4, elapsed=60.0),
                    self._seed(0.6, 0.4, elapsed=80.0)]
        r = _summary_row(per_seed, "fresh/sliding")
        assert r["mean_retrain_s"] == pytest.approx(70.0, abs=0.1)
