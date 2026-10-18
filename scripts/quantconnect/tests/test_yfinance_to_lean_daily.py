"""Offline unit tests for yfinance_to_lean_daily.py (no network, no yfinance).

These validate the LEAN daily FORMAT conversion + zip layout -- the part that
must be byte-correct for DefaultDataProvider to read the data. The yfinance
fetch is lazy and not exercised here; a real end-to-end run is documented in
the module docstring + the quantbook re-exec (#8401 lineage).
"""

import sys
import zipfile
from datetime import datetime
from pathlib import Path

import numpy as np
import pandas as pd
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from yfinance_to_lean_daily import (  # noqa: E402
    PRICE_SCALE,
    df_to_lean_rows,
    write_lean_zip,
    build_factor_file_rows,
    write_lean_factor_file,
)


def _sample_df():
    """A 3-day OHLCV frame mimicking yfinance daily output."""
    idx = pd.DatetimeIndex(["2007-01-03", "2007-01-04", "2007-01-05"])
    return pd.DataFrame(
        {
            "Open": [73.40, 73.51, 73.80],
            "High": [73.90, 74.10, 74.00],
            "Low": [73.20, 73.45, 73.60],
            "Close": [73.51, 73.95, 73.70],
            "Volume": [1_234_500, 987_000, 1_100_250],
        },
        index=idx,
    )


class TestDfToLeanRows:
    def test_format_and_scaling(self):
        rows = df_to_lean_rows(_sample_df())
        assert len(rows) == 3
        # First row: 2007-01-03, close 73.51 -> 735100 (x10000 int).
        # Time is 00:00 -- the LEAN daily-format convention (midnight), not the
        # equity session close (verified firsthand vs the in-repo reference zips,
        # ai-01 c.26).
        o, h, low, c, v = 734000, 739000, 732000, 735100, 1234500
        assert rows[0] == f"20070103 00:00,{o},{h},{low},{c},{v}"

    def test_no_header(self):
        rows = df_to_lean_rows(_sample_df())
        # LEAN daily files have NO header row -- first line is data.
        assert not rows[0].lower().startswith("date")
        assert "," in rows[0]

    def test_date_only_no_seconds(self):
        rows = df_to_lean_rows(_sample_df())
        # Time stamp is YYYYMMDD HH:MM (no seconds); time is 00:00 (LEAN daily).
        assert rows[0].split(",")[0] == "20070103 00:00"

    def test_volume_is_raw_int(self):
        rows = df_to_lean_rows(_sample_df())
        # Volume is NOT scaled (raw share count).
        assert rows[0].split(",")[-1] == "1234500"

    def test_tz_aware_index_handled(self):
        df = _sample_df().tz_localize("America/New_York")
        rows = df_to_lean_rows(df)
        # tz is dropped; date preserved.
        assert rows[0].startswith("20070103")

    def test_price_scale_rounding(self):
        # 73.515 -> round(735150.0) = 735150.
        df = pd.DataFrame(
            {"Open": [73.5], "High": [73.5], "Low": [73.5],
             "Close": [73.515], "Volume": [0]},
            index=pd.DatetimeIndex(["2020-01-02"]),
        )
        rows = df_to_lean_rows(df)
        close = int(rows[0].split(",")[4])
        assert close == 735150

    def test_PRICE_SCALE_constant(self):
        assert PRICE_SCALE == 10_000


class TestWriteLeanZip:
    def test_zip_layout_and_inner_naming(self, tmp_path):
        rows = df_to_lean_rows(_sample_df())
        zip_path = write_lean_zip("EFA", rows, tmp_path)
        assert zip_path == tmp_path / "efa.zip"
        assert zip_path.exists()
        with zipfile.ZipFile(zip_path) as zf:
            names = zf.namelist()
            # Inner CSV is named after the ticker (LOWERCASE), no header.
            assert names == ["efa.csv"]
            body = zf.read("efa.csv").decode("utf-8")
        body_lines = body.strip().split("\n")
        assert body_lines[0].startswith("20070103 00:00,")
        assert len(body_lines) == 3

    def test_ticker_lowercased(self, tmp_path):
        # Ticker is lowercased unconditionally: a lowercase input stays lowercase,
        # an UPPERCASE input is lowercased (LEAN equity data is lowercase; on a
        # case-sensitive FS an upper SPY.zip next to spy.zip is invisible).
        zip_lower = write_lean_zip("spy", ["20200102 00:00,1,2,3,4,5"], tmp_path)
        assert zip_lower.name == "spy.zip"
        with zipfile.ZipFile(zip_lower) as zf:
            assert zf.namelist() == ["spy.csv"]
        zip_upper = write_lean_zip("SPY", ["20200102 00:00,1,2,3,4,5"], tmp_path)
        assert zip_upper.name == "spy.zip"

    def test_creates_out_folder(self, tmp_path):
        nested = tmp_path / "equity" / "usa" / "daily"
        write_lean_zip("GLD", ["20200102 00:00,1,2,3,4,5"], nested)
        assert (nested / "gld.zip").exists()

    def test_empty_rows_writes_empty_csv(self, tmp_path):
        zip_path = write_lean_zip("SHY", [], tmp_path)
        assert zip_path.name == "shy.zip"
        with zipfile.ZipFile(zip_path) as zf:
            assert zf.read("shy.csv").decode("utf-8") == ""


def _sample_df_with_adj_close():
    """3-day frame mimicking yfinance daily output WITH 'Adj Close'.

    'Adj Close' is the dividend-adjusted close; on this model frame we keep
    Adj Close == Close so factor_price == 1 everywhere (no dividend paid).
    The split adjustment is already baked into 'Close' (the bug we fix here).
    """
    idx = pd.DatetimeIndex(["2007-01-03", "2007-01-04", "2007-01-05"])
    return pd.DataFrame(
        {
            "Open": [73.40, 73.51, 73.80],
            "High": [73.90, 74.10, 74.00],
            "Low": [73.20, 73.45, 73.60],
            "Close": [73.51, 73.95, 73.70],
            "Adj Close": [73.51, 73.95, 73.70],
            "Volume": [1_234_500, 987_000, 1_100_250],
        },
        index=idx,
    )


def _aapl_split_2020_df():
    """Synthesise the AAPL 2020-08-31 4:1 split scenario at factor-file level.

    Three dates covering the issue #21122 measurement:

    - 2020-08-28 (Friday, BEFORE split): Close=499.23, Adj Close=124.36
      (499.23 / 4 = 124.8075, rounded). factor_price = 124.36/499.23 = 0.2491.
    - 2020-08-31 (Monday, split ex-date): Close=499.23 (already split-adjusted
      by yfinance -- this is what we ship), Adj Close=124.06 (further
      dividend). factor_price = 124.06/499.23 = 0.2485.
    - 2020-09-01 (Tuesday, post-split, NO dividend): Close=131.40
      (= 525.60 / 4 raw, fully split-adjusted), Adj Close=131.40 (no dividend
      that day). factor_price = 1.0 (this is the normalisation anchor).

    After normalisation to factor_price=1 on the LAST date, the previous dates
    carry the cumulative-dividend ratio backwards:
        2020-08-31: 0.2485 / 1.0 = 0.2485
        2020-08-28: 0.2491 / 1.0 = 0.2491
        2020-09-01: 1.0000000

    Note: in production the LastBar carries the latest dividend ratio. For
    the test we anchor on 2020-09-01 (a no-dividend day, ratio = 1.0) to
    exercise the normalisation path explicitly. Real AAPL data would have
    many ex-dividend dates -- each becomes a row in the factor file.
    """
    idx = pd.DatetimeIndex(["2020-08-28", "2020-08-31", "2020-09-01"])
    return pd.DataFrame(
        {
            "Open": [499.23, 499.23, 131.40],
            "High": [499.23, 499.23, 131.40],
            "Low": [499.23, 499.23, 131.40],
            "Close": [499.23, 499.23, 131.40],
            "Adj Close": [124.36, 124.06, 131.40],
            "Volume": [0, 0, 0],
        },
        index=idx,
    )


class TestBuildFactorFileRows:
    def test_factor_split_always_one(self):
        """FactorSplit must be 1 everywhere: yfinance has already split-adjusted
        Close, so LEAN must NOT re-apply any split. Regression on this would
        reintroduce the +1362.9 % vs +275.1 % discrepancy of issue #21122."""
        rows = build_factor_file_rows(_sample_df_with_adj_close())
        assert len(rows) >= 1
        for line in rows:
            parts = line.split(",")
            assert len(parts) == 3, f"factor file row must have 3 fields: {line!r}"
            assert parts[2] == "1", f"FactorSplit must be 1, got {parts[2]!r} in {line!r}"

    def test_last_date_normalised_to_one(self):
        """The normalisation contract: the LAST date of the downloaded window
        carries factor_price == 1.0 (and only that date does)."""
        rows = build_factor_file_rows(_sample_df_with_adj_close())
        assert len(rows) == 1
        parts = rows[0].split(",")
        assert parts[0] == "20070105 00:00"
        assert float(parts[1]) == pytest.approx(1.0, abs=1e-8)

    def test_only_changed_values_emitted(self):
        """A row is emitted only when factor_price changes vs the previous
        emitted row. On a 3-day frame with Adj Close == Close, only the last
        day (the anchor) is emitted (one row total)."""
        rows = build_factor_file_rows(_sample_df_with_adj_close())
        assert len(rows) == 1

    def test_ex_dividend_dates_emit_one_row_each(self):
        """Each ex-dividend date (a step in factor_price) emits one row."""
        idx = pd.DatetimeIndex([
            "2020-02-14",  # most recent: least cumulative dividend
            "2019-11-07",  # ex-div date: factor jumps (down)
            "2019-08-09",  # ex-div date: factor jumps again
            "2019-05-10",  # oldest ex-div date (anchor for normalisation)
        ])
        # Adj Close / Close = 0.985, 0.960, 0.940, 0.925 -- decreasing through
        # time as cumulative dividends grow. After normalising to 1.0 on the
        # last (oldest) date, every earlier row has factor_price > 1.0 because
        # it has LESS cumulative dividend adjustment.
        df = pd.DataFrame(
            {
                "Open": [100.0] * 4,
                "High": [100.0] * 4,
                "Low": [100.0] * 4,
                "Close": [100.0] * 4,
                "Adj Close": [98.50, 96.00, 94.00, 92.50],
                "Volume": [0] * 4,
            },
            index=idx,
        )
        rows = build_factor_file_rows(df)
        # All four dates carry distinct factor_prices -> 4 rows.
        assert len(rows) == 4
        # Last row (2019-05-10) is normalised to 1.0.
        parts = rows[-1].split(",")
        assert parts[0] == "20190510 00:00"
        assert float(parts[1]) == pytest.approx(1.0, abs=1e-8)
        # Earlier rows carry the cumulative ratio (> 1.0): the cumulative
        # dividend adjustment at earlier dates is LESS than at the last date,
        # so dividing the earlier raw ratio by the smaller last raw ratio
        # yields a value > 1.
        for line in rows[:-1]:
            assert float(line.split(",")[1]) > 1.0, (
                f"earlier-than-anchor factor_price must be > 1.0 (less "
                f"cumulative dividend adjustment), got {line!r}"
            )
        # And the chronological order is preserved -- factor_prices are
        # non-increasing as we advance through the rows (the index of this
        # test frame runs most-recent -> oldest, so the most recent date
        # carries the largest cumulative-dividend ratio and the oldest date
        # carries the 1.0 anchor).
        ratio_values = [float(line.split(",")[1]) for line in rows]
        assert all(ratio_values[i] >= ratio_values[i + 1]
                   for i in range(len(ratio_values) - 1)), (
            f"factor_prices must be non-increasing in row order. Got: "
            f"{ratio_values}"
        )

    def test_aapl_split_2020_factor_split_is_one(self):
        """The motivating scenario of issue #21122. Even though AAPL had a
        4:1 split on 2020-08-31, the factor file carries FactorSplit = 1
        everywhere -- because yfinance's Close is already split-adjusted.
        """
        rows = build_factor_file_rows(_aapl_split_2020_df())
        assert len(rows) >= 2  # at least 2 distinct factor_price values
        for line in rows:
            parts = line.split(",")
            assert parts[2] == "1", (
                f"AAPL 2020-08-31 split: FactorSplit must be 1 (yfinance has "
                f"already split-adjusted Close), got {parts[2]!r} in {line!r}"
            )

    def test_aapl_split_2020_last_date_anchored_to_one(self):
        """The last date (2020-09-01, a no-dividend day) carries factor_price=1."""
        rows = build_factor_file_rows(_aapl_split_2020_df())
        last = rows[-1].split(",")
        assert last[0] == "20200901 00:00"
        assert float(last[1]) == pytest.approx(1.0, abs=1e-8)

    def test_aapl_split_2020_no_double_count_of_split(self):
        """Quantitatively the factor file must NOT carry the 4:1 split. We
        assert that the ratio of factor_prices between the pre-split and
        post-split dates is the dividend-only adjustment (not the 4x split).

        Raw (Adj Close / Close) before normalisation:
            2020-08-28: 124.36 / 499.23 = 0.249085...
            2020-08-31: 124.06 / 499.23 = 0.248502...
            2020-09-01: 131.40 / 131.40 = 1.000000...

        After normalising to 1.0 on 2020-09-01:
            2020-08-28: 0.249085 / 1.000000 = 0.249085
            2020-08-31: 0.248502 / 1.000000 = 0.248502
            2020-09-01: 1.000000 / 1.000000 = 1.000000

        The ratio between 2020-08-28 and 2020-09-01 is ~0.249, NOT 4.0
        (which would indicate the split was still being applied).
        """
        rows = build_factor_file_rows(_aapl_split_2020_df())
        # Build a dict date -> factor_price
        d = {r.split(",")[0]: float(r.split(",")[1]) for r in rows}
        pre_split = d.get("20200828 00:00")
        post_split = d.get("20200901 00:00")
        assert pre_split is not None, (
            f"2020-08-28 row missing in factor output: {rows}"
        )
        assert post_split is not None, (
            f"2020-09-01 row missing in factor output: {rows}"
        )
        # If the split had been double-counted, pre_split would carry a 4x
        # ratio; here it's the dividend-only ratio (~0.249).
        assert pre_split < 1.0
        assert post_split == pytest.approx(1.0, abs=1e-8)
        # Crucially: NOT 4.0 (which would be the 4:1 split back-end).
        ratio = pre_split / post_split
        assert ratio == pytest.approx(0.249085, abs=1e-4), (
            f"factor ratio pre/post split = {ratio}, expected ~0.249 "
            f"(dividend-only); if ~4.0 the split is being double-counted"
        )

    def test_missing_adj_close_raises(self):
        """A frame without 'Adj Close' cannot be converted -- the factor
        price IS Adj Close / Close, so both columns are required."""
        df = _sample_df_with_adj_close().drop(columns=["Adj Close"])
        with pytest.raises(KeyError):
            build_factor_file_rows(df)

    def test_missing_close_raises(self):
        df = _sample_df_with_adj_close().drop(columns=["Close"])
        with pytest.raises(KeyError):
            build_factor_file_rows(df)

    def test_empty_after_dropna(self):
        df = _sample_df_with_adj_close().copy()
        df["Close"] = np.nan
        df["Adj Close"] = np.nan
        assert build_factor_file_rows(df) == []


class TestWriteLeanFactorFile:
    def test_lowercase_filename(self, tmp_path):
        rows = ["20200102 00:00,1.0,1", "20200103 00:00,0.998,1"]
        path = write_lean_factor_file("AAPL", rows, tmp_path)
        assert path == tmp_path / "aapl.csv"
        assert path.exists()

    def test_uppercase_input_lowercased(self, tmp_path):
        path = write_lean_factor_file("SPY", ["20200102 00:00,1.0,1"], tmp_path)
        assert path.name == "spy.csv"

    def test_creates_factor_folder(self, tmp_path):
        nested = tmp_path / "equity" / "usa" / "factor_files"
        write_lean_factor_file("SPY", ["20200102 00:00,1.0,1"], nested)
        assert (nested / "spy.csv").exists()

    def test_body_format(self, tmp_path):
        rows = ["20200102 00:00,1.0,1", "20200831 00:00,0.249085,1"]
        path = write_lean_factor_file("AAPL", rows, tmp_path)
        body = path.read_text(encoding="utf-8")
        assert body == "20200102 00:00,1.0,1\n20200831 00:00,0.249085,1\n"

    def test_empty_rows_writes_empty(self, tmp_path):
        path = write_lean_factor_file("SHY", [], tmp_path)
        assert path.name == "shy.csv"
        assert path.read_text(encoding="utf-8") == ""


class TestRoundTripAgainst8401Spec:
    """The conversion must match the #8401 firsthand-proven format:
    file value 735100 <-> quantbook reads close 73.51 for EFA 2007-01-03."""

    def test_close_735100_decodes_to_73_51(self):
        df = pd.DataFrame(
            {"Open": [73.51], "High": [73.51], "Low": [73.51],
             "Close": [73.51], "Volume": [100]},
            index=pd.DatetimeIndex(["2007-01-03"]),
        )
        rows = df_to_lean_rows(df)
        close_scaled = int(rows[0].split(",")[4])
        assert close_scaled == 735100
        # A LEAN reader divides by PRICE_SCALE to recover the price.
        assert close_scaled / PRICE_SCALE == pytest.approx(73.51)


# Path to the in-repo LEAN reference data (gitignored lean-workspace/, present
# only where the workspace is checked out). Used by the conditional anchor below.
REPO_ROOT = Path(__file__).resolve().parents[3]
REF_DAILY = REPO_ROOT / "MyIA.AI.Notebooks" / "QuantConnect" / "ESGF-2026" / "lean-workspace" / "data" / "equity" / "usa" / "daily"


class TestAnchorAgainstReferenceLEANData:
    """Anchor the output format on the in-repo LEAN reference data (ai-01 c.26).

    The prior version regressed on TWO of three conventions (time 16:00 vs 00:00,
    uppercase vs lowercase) because the tests asserted the bug. These anchors pin
    all three against an external, firsthand-proven reference so a third regression
    on the same file is caught.
    """

    # ai-01 read this line firsthand from the in-repo reference ``spy.zip``:
    #   19980102 00:00,973100,975300,965300,973600,2150000
    # (Open 97.31, High 97.53, Low 96.53, Close 97.36, Vol 2150000).
    REF_SPY_19980102 = "19980102 00:00,973100,975300,965300,973600,2150000"

    def test_anchor_line_matches_firsthand_reference_spy(self):
        """Generate the SPY 1998-01-02 line from its raw OHLCV and assert it
        reproduces the reference line byte-for-byte. Pins all three conventions:
        time 00:00 (not 16:00), scale x10000 (97.31 -> 973100), field order."""
        df = pd.DataFrame(
            {"Open": [97.31], "High": [97.53], "Low": [96.53],
             "Close": [97.36], "Volume": [2_150_000]},
            index=pd.DatetimeIndex(["1998-01-02"]),
        )
        assert df_to_lean_rows(df)[0] == self.REF_SPY_19980102

    def test_reference_zip_is_lowercase_and_midnight_when_present(self, tmp_path):
        """When the gitignored in-repo reference ``spy.zip`` is checked out, read
        its first line and assert the SAME conventions our converter produces:
        the time field is ``00:00`` and ``write_lean_zip`` writes lowercase. This
        is the direct 'compare to a real spy.zip line' anchor; skipped where the
        reference workspace is absent (CI, machines without lean-workspace)."""
        ref_zip = REF_DAILY / "spy.zip"
        if not ref_zip.exists():
            pytest.skip(f"reference {ref_zip} not present (lean-workspace gitignored)")
        with zipfile.ZipFile(ref_zip) as zf:
            inner = [n for n in zf.namelist() if n.lower().endswith(".csv")]
            assert len(inner) == 1, f"expected one inner csv in spy.zip, got {zf.namelist()}"
            # Inner CSV name is lowercase (spy.csv), not SPY.CSV.
            assert inner[0] == inner[0].lower(), f"reference inner csv not lowercase: {inner[0]}"
            first_line = zf.read(inner[0]).decode("utf-8").splitlines()[0]
        # The reference's time field is 00:00 -- the convention our converter adopts.
        assert first_line.split(",")[0].endswith(" 00:00"), (
            f"reference spy.zip first line not 00:00: {first_line!r}")
        # And our converter writes a lowercase zip next to it, not an invisible SPY.zip.
        zip_path = write_lean_zip("SPY", [first_line], tmp_path)
        assert zip_path.name == "spy.zip"
