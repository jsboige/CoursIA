"""Tests for the #12681 log-line fix -- print the baseline the verdict uses.

The M15 ETF logs showed a model MSE sitting BETWEEN the walk-forward
aggregate and the aligned HAR MSE: printing only the aggregate next to the
DM verdict let a reader invert the model-vs-baseline conclusion (10/12
checkpoint lines, #12681). These tests rebuild exactly that discriminating
case and check the printed verdict line carries the number the verdict is
computed on. One wiring test per executor (m15_etf_vol, etf_vol): the shared
formatter existing is not the fix -- each executor calling it is.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from log_lines import (
    format_dm_verdict_line,
    format_har_baseline_line,
)

SCRIPTS_DIR = Path(__file__).resolve().parent.parent

# Real numbers from bg_logs/m15_etf_wA_20260823T204511Z.log (issue #12681):
# the aggregate says "model 5.9% worse than baseline", the aligned sample the
# verdict is computed on says "model more precise" -- the sign inverts.
HAR_MSE_AGGREGATE = 0.70531
LSTM_MSE = 0.74678
HAR_MSE_ALIGNED = 0.77957


class TestDiscriminatingCase:
    """The case that made the old line a misleading proof."""

    def test_case_is_discriminating(self):
        # Guard the fixture itself: aggregate and aligned must sit on
        # opposite sides of the model MSE, else the case proves nothing.
        assert HAR_MSE_AGGREGATE < LSTM_MSE < HAR_MSE_ALIGNED

    def test_verdict_line_carries_the_aligned_baseline(self):
        line = format_dm_verdict_line(
            "LSTM", 1, 42, LSTM_MSE, HAR_MSE_ALIGNED, 0.04619,
            -2.147, 0.0319, "BEATS baseline",
        )
        assert "vs HAR aligne 0.77957" in line
        # The aggregate must no longer be the implicit baseline of the
        # verdict line: the reader comparing the two MSEs on the line must
        # get the same sign as the verdict (model more precise -> BEATS).
        assert f"{HAR_MSE_AGGREGATE:.5f}" not in line
        assert LSTM_MSE < HAR_MSE_ALIGNED

    def test_baseline_line_labels_the_aggregate(self):
        line = format_har_baseline_line(1, HAR_MSE_AGGREGATE, -0.15566, 4525)
        assert "HAR MSE(agrege)=0.70531" in line
        assert "4525 preds" in line


class TestWiringM15:
    """Executor 1: m15_etf_vol must print through the shared formatters."""

    SOURCE = (SCRIPTS_DIR / "m15_etf_vol.py").read_text(encoding="utf-8")

    def test_dm_line_wired(self):
        assert "format_dm_verdict_line(" in self.SOURCE
        assert "mse_har_aligned" in self.SOURCE

    def test_har_line_wired(self):
        assert "format_har_baseline_line(" in self.SOURCE


class TestWiringEtfVol:
    """Executor 2: etf_vol must print through the shared formatters."""

    SOURCE = (SCRIPTS_DIR / "etf_vol.py").read_text(encoding="utf-8")

    def test_dm_line_wired(self):
        assert "format_dm_verdict_line(" in self.SOURCE
        # The aligned value fed to the line is computed on the truncated
        # sample the DM verdict itself uses (min of the two error lengths).
        assert "mse_har_aligned" in self.SOURCE
        assert "har_errors[:min_len]" in self.SOURCE

    def test_har_line_wired(self):
        assert "format_har_baseline_line(" in self.SOURCE

    def test_row_json_carries_aligned(self):
        assert '"har_mse_aligned": mse_har_aligned' in self.SOURCE
