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
