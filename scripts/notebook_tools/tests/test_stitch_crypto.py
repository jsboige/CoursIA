"""Tests for stitch_crypto.py — crypto dataset stitching pure functions."""

import importlib.util
import sys
from pathlib import Path

import pandas as pd
import pytest

# Load module directly by file path to avoid conflict with HuggingFace 'datasets'
_MOD_PATH = Path(__file__).resolve().parent.parent.parent / "datasets" / "stitch_crypto.py"
_spec = importlib.util.spec_from_file_location("stitch_crypto", _MOD_PATH)
_mod = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_mod)

validate_overlap = _mod.validate_overlap
stitch_datasets = _mod.stitch_datasets
quality_report = _mod.quality_report


def _make_df(rows: list[tuple]) -> pd.DataFrame:
    """Build a minimal DataFrame with timestamp, close, source columns.

    rows: list of (timestamp_str, close_value, source_name)
    """
    return pd.DataFrame(rows, columns=["timestamp", "close", "source"]).assign(
        timestamp=lambda d: pd.to_datetime(d["timestamp"]),
        close=lambda d: pd.to_numeric(d["close"]),
        open=lambda d: d["close"],
        high=lambda d: d["close"],
        low=lambda d: d["close"],
        volume_btc=1.0,
        volume_usd=100.0,
    )


# --- validate_overlap ---


class TestValidateOverlap:
    def test_no_overlap(self):
        a = _make_df([("2020-01-01", 100, "A"), ("2020-01-02", 101, "A")])
        b = _make_df([("2021-01-01", 200, "B"), ("2021-01-02", 201, "B")])
        result = validate_overlap(a, b)
        assert result["has_overlap"] is False

    def test_perfect_overlap(self):
        a = _make_df([("2020-01-01", 100, "A"), ("2020-01-02", 101, "A")])
        b = _make_df([("2020-01-01", 100, "B"), ("2020-01-02", 101, "B")])
        result = validate_overlap(a, b)
        assert result["has_overlap"] is True
        assert result["common_points"] == 2
        assert result["mean_diff_pct"] == 0.0
        assert result["within_threshold"] is True

    def test_close_price_mismatch(self):
        """Two overlapping periods with different close prices."""
        a = _make_df([("2020-01-01", 100, "A"), ("2020-01-02", 101, "A")])
        b = _make_df([("2020-01-01", 200, "B"), ("2020-01-02", 202, "B")])
        result = validate_overlap(a, b)
        assert result["has_overlap"] is True
        assert result["common_points"] == 2
        assert result["mean_diff_pct"] >= 50.0
        assert result["within_threshold"] is False

    def test_partial_overlap(self):
        """Overlap of a single point where periods touch at boundary.

        Note: validate_overlap uses overlap_start >= overlap_end to detect
        no overlap, so periods sharing only an endpoint have no overlap
        (strict inequality). Use wider overlap for single-point match.
        """
        a = _make_df([("2020-01-01", 100, "A"), ("2020-01-02", 101, "A"), ("2020-01-03", 102, "A")])
        b = _make_df([("2020-01-02", 101, "B"), ("2020-01-03", 102, "B"), ("2020-01-04", 103, "B")])
        result = validate_overlap(a, b)
        assert result["has_overlap"] is True
        assert result["common_points"] == 2

    def test_empty_dataframe_crashes(self):
        """Empty DataFrame with NaT min/max causes TypeError in validate_overlap.

        This is a known behavior — validate_overlap doesn't guard against
        empty inputs.
        """
        a = pd.DataFrame(columns=["timestamp", "close", "source"])
        b = _make_df([("2020-01-01", 100, "B")])
        with pytest.raises(TypeError):
            validate_overlap(a, b)


# --- stitch_datasets ---


class TestStitchDatasets:
    def test_single_source(self):
        a = _make_df([("2020-01-01", 100, "A"), ("2020-01-02", 101, "A")])
        result = stitch_datasets([a])
        assert len(result) == 2

    def test_non_overlapping_sources(self):
        a = _make_df([("2020-01-01", 100, "A")])
        b = _make_df([("2020-01-02", 101, "B")])
        result = stitch_datasets([a, b])
        assert len(result) == 2
        assert result.iloc[0]["source"] == "A"
        assert result.iloc[1]["source"] == "B"

    def test_overlapping_priority_first(self):
        """First dataset wins on overlap (keep='first')."""
        a = _make_df([("2020-01-01", 100, "A")])
        b = _make_df([("2020-01-01", 200, "B")])
        result = stitch_datasets([a, b])
        assert len(result) == 1
        assert result.iloc[0]["close"] == 100
        assert result.iloc[0]["source"] == "A"

    def test_sorted_output(self):
        b = _make_df([("2020-01-03", 102, "B")])
        a = _make_df([("2020-01-01", 100, "A")])
        result = stitch_datasets([b, a])
        assert result.iloc[0]["close"] == 100
        assert result.iloc[1]["close"] == 102

    def test_empty_sources_crashes(self):
        """pd.concat([]) raises ValueError — stitch_datasets doesn't guard against empty input."""
        with pytest.raises(ValueError):
            stitch_datasets([])

    def test_three_sources(self):
        a = _make_df([("2020-01-01", 100, "A")])
        b = _make_df([("2020-01-02", 101, "B")])
        c = _make_df([("2020-01-03", 102, "C")])
        result = stitch_datasets([a, b, c])
        assert len(result) == 3


# --- quality_report ---


class TestQualityReport:
    def test_basic_report(self):
        df = _make_df([
            ("2020-01-01 00:00", 100, "A"),
            ("2020-01-01 01:00", 101, "A"),
            ("2020-01-01 02:00", 102, "A"),
        ])
        report = quality_report(df)
        assert report["total_rows"] == 3
        assert report["num_gaps"] == 0
        assert report["nan_close"] == 0

    def test_gap_detection(self):
        df = _make_df([
            ("2020-01-01 00:00", 100, "A"),
            ("2020-01-01 01:00", 101, "A"),
            # Gap: missing 02:00, 03:00
            ("2020-01-01 04:00", 102, "A"),
        ])
        report = quality_report(df)
        assert report["num_gaps"] >= 1

    def test_source_breakdown(self):
        df = _make_df([
            ("2020-01-01 00:00", 100, "bitstamp"),
            ("2020-01-01 01:00", 101, "binance"),
            ("2020-01-01 02:00", 102, "bitstamp"),
        ])
        report = quality_report(df)
        assert report["sources"]["bitstamp"] == 2
        assert report["sources"]["binance"] == 1

    def test_price_range(self):
        df = _make_df([
            ("2020-01-01 00:00", 100, "A"),
            ("2020-01-01 01:00", 200, "A"),
            ("2020-01-01 02:00", 150, "A"),
        ])
        report = quality_report(df)
        assert report["min_close"] == 100.0
        assert report["max_close"] == 200.0


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
