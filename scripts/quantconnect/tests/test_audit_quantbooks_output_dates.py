"""Tests for audit_quantbooks_output_dates.py -- output-date freshness (#8734, ai-01 c.40)."""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from audit_quantbooks_output_dates import (  # noqa: E402
    _all_dates_in_text,
    _cell_output_text,
    _classify_freshness,
    _guard_present,
    scan_notebook,
)


# --- _all_dates_in_text ---

class TestAllDatesInText:
    def test_iso_dates(self):
        assert _all_dates_in_text("ran on 2026-07-28, data to 2025-12-31") == ["2025-12-31", "2026-07-28"]

    def test_compact_dates(self):
        assert _all_dates_in_text("window 20150102 to 20251231") == ["2015-01-02", "2025-12-31"]

    def test_dedup_and_sort(self):
        text = "2026-07-28 and 2026-07-28 and 2025-01-01"
        assert _all_dates_in_text(text) == ["2025-01-01", "2026-07-28"]

    def test_invalid_calendar_dropped(self):
        # 13th month / 32nd day are not real dates -> dropped, not normalized.
        assert _all_dates_in_text("bogus 2025-13-01 and 2025-12-32") == []

    def test_empty(self):
        assert _all_dates_in_text("") == []
        assert _all_dates_in_text(None) == []

    def test_no_19xx_false_matches(self):
        # Only 20xx captured; a stray 1999-01-01 is ignored.
        assert _all_dates_in_text("legacy 1999-01-01 real 2024-06-15") == ["2024-06-15"]


# --- _cell_output_text ---

class TestCellOutputText:
    def test_stream_text_string(self):
        cell = {"outputs": [{"output_type": "stream", "text": "hello 2026-07-28"}]}
        assert "2026-07-28" in _cell_output_text(cell)

    def test_stream_text_list(self):
        cell = {"outputs": [{"output_type": "stream", "text": ["line1\n", "2025-12-31\n"]}]}
        assert "2025-12-31" in _cell_output_text(cell)

    def test_data_text_plain(self):
        cell = {"outputs": [{"output_type": "execute_result",
                             "data": {"text/plain": "array([2024-01-01])"}}]}
        assert "2024-01-01" in _cell_output_text(cell)

    def test_data_text_list(self):
        cell = {"outputs": [{"data": {"text/plain": ["a", "2023-06-01"]}}]}
        assert "2023-06-01" in _cell_output_text(cell)

    def test_ignores_non_text_data(self):
        cell = {"outputs": [{"data": {"image/png": "base64..."}}]}
        assert _cell_output_text(cell) == ""

    def test_empty(self):
        assert _cell_output_text({}) == ""
        assert _cell_output_text({"outputs": []}) == ""


# --- _guard_present ---

class TestGuardPresent:
    def test_detects_filldataforward(self):
        assert _guard_present({"cells": [{"source": "if not fillDataForward: raise"}]}) is True

    def test_detects_flat_tail(self):
        assert _guard_present({"cells": [{"source": "# C942 flat-tail guard"}]}) is True

    def test_detects_c941_c942_c951(self):
        for needle in ("c941", "c942", "c951"):
            assert _guard_present({"cells": [{"source": f"# see {needle}"}]}) is True

    def test_detects_provisioner_ref(self):
        assert _guard_present({"cells": [{"source": "# regenerate via provision_lean_data"}]}) is True

    def test_absent(self):
        assert _guard_present({"cells": [{"source": "x = 1"}]}) is False

    def test_empty_nb(self):
        assert _guard_present({"cells": []}) is False


# --- scan_notebook (end-to-end on a tmp JSON) ---

def _write_nb(path: Path, cells: list[dict]) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps({"cells": cells, "metadata": {}, "nbformat": 4}), encoding="utf-8")
    return path


def _code(source: str, ec=None, outputs=None):
    return {"cell_type": "code", "execution_count": ec,
            "source": source, "outputs": outputs or []}


class TestScanNotebook:
    def test_incomplete(self, tmp_path):
        nb = tmp_path / "Proj" / "quantbook.ipynb"
        _write_nb(nb, [_code("x=1", ec=1), _code("y=2", ec=None)])  # 1/2 executed
        r = scan_notebook(nb)
        assert r["verdict"] == "INCOMPLETE"
        assert r["exec_cells"] == 1 and r["total_code_cells"] == 2

    def test_has_errors(self, tmp_path):
        nb = tmp_path / "Proj" / "quantbook.ipynb"
        _write_nb(nb, [_code("x=1", ec=1, outputs=[{"output_type": "error", "ename": "V", "evalue": "x"}])])
        r = scan_notebook(nb)
        assert r["verdict"] == "HAS_ERRORS"
        assert r["error_cells"] == 1

    def test_exec_proved_no_date(self, tmp_path):
        nb = tmp_path / "Proj" / "quantbook.ipynb"
        _write_nb(nb, [_code("x=1", ec=1, outputs=[{"output_type": "stream", "text": "no dates here"}])])
        r = scan_notebook(nb)
        assert r["verdict"] == "EXEC_PROVED_NO_DATE"
        assert r["latest_exec_date"] is None

    def test_extracts_output_date(self, tmp_path):
        nb = tmp_path / "Proj" / "quantbook.ipynb"
        _write_nb(nb, [_code("x=1", ec=1,
                             outputs=[{"output_type": "stream", "text": "window to 2026-07-28 ok"}])])
        r = scan_notebook(nb)
        assert r["verdict"] == "EXEC_PROVED"
        assert r["latest_exec_date"] == "2026-07-28"

    def test_period_date_collected_from_output(self, tmp_path):
        nb = tmp_path / "Proj" / "quantbook.ipynb"
        _write_nb(nb, [_code("x=1", ec=1,
                             outputs=[{"output_type": "stream", "text": "Periode: 2020-01-01 a 2024-12-31"}])])
        r = scan_notebook(nb)
        assert r["latest_backtest_period_date"] == "2024-12-31"
        assert r["latest_exec_date"] == "2024-12-31"

    def test_period_date_collected_from_source(self, tmp_path):
        # An ISO date inside a period-hint SOURCE line is collected as a period date.
        nb = tmp_path / "Proj" / "quantbook.ipynb"
        _write_nb(nb, [_code("# Periode: 2020-01-01 a 2024-12-31", ec=1, outputs=[])])
        r = scan_notebook(nb)
        assert r["latest_backtest_period_date"] == "2024-12-31"

    def test_comma_form_setenddate_not_parsed(self, tmp_path):
        # Known limitation: SetEndDate(2024,12,31) uses comma-separated args and is
        # NOT matched by the ISO/compact regexes. Period detection relies on the
        # ISO form that Lean prints when resolving the date (see test_period_date_
        # collected_from_output above).
        nb = tmp_path / "Proj" / "quantbook.ipynb"
        _write_nb(nb, [_code("qb.SetStartDate(2020,1,1)\nqb.SetEndDate(2024,12,31)", ec=1,
                             outputs=[{"output_type": "stream", "text": "ran"}])])
        r = scan_notebook(nb)
        assert r["latest_backtest_period_date"] is None
        assert r["latest_exec_date"] is None

    def test_read_error(self, tmp_path):
        nb = tmp_path / "Proj" / "quantbook.ipynb"
        _write_nb(nb, [_code("x=1", ec=1)])
        # Corrupt it after writing.
        nb.write_text("{not valid json", encoding="utf-8")
        r = scan_notebook(nb)
        assert r["verdict"] == "READ_ERROR"
        assert r["error"] is not None

    def test_guard_detection_end_to_end(self, tmp_path):
        nb = tmp_path / "Proj" / "quantbook.ipynb"
        _write_nb(nb, [_code("# C942 flat tail guard\nx=1", ec=1,
                             outputs=[{"output_type": "stream", "text": "2026-07-28"}])])
        r = scan_notebook(nb)
        assert r["guard_present"] is True


# --- _classify_freshness (the c.40 false-positive guard) ---

class TestClassifyFreshness:
    def test_period_dominated_aged_not_stale(self):
        # The c.40 false-positive guard: latest == period -> PERIOD_DOMINATED, never STALE.
        r = {"latest_exec_date": "2024-12-31", "latest_backtest_period_date": "2024-12-31",
             "verdict": "EXEC_PROVED"}
        assert _classify_freshness(r, 2025) == "PERIOD_DOMINATED_AGED"

    def test_period_dominated_recent(self):
        r = {"latest_exec_date": "2025-12-31", "latest_backtest_period_date": "2025-12-31",
             "verdict": "EXEC_PROVED"}
        assert _classify_freshness(r, 2025) == "PERIOD_DOMINATED_RECENT"

    def test_non_period_fresh(self):
        # A freshness-guard print (2026-07-28) != the period (2025-12-31) -> FRESH.
        r = {"latest_exec_date": "2026-07-28", "latest_backtest_period_date": "2025-12-31",
             "verdict": "EXEC_PROVED"}
        assert _classify_freshness(r, 2025) == "EXEC_PROVED_FRESH"

    def test_non_period_stale(self):
        # A non-period old date below threshold -> genuine STALE (not period-dominated).
        r = {"latest_exec_date": "2023-06-01", "latest_backtest_period_date": "2025-12-31",
             "verdict": "EXEC_PROVED"}
        assert _classify_freshness(r, 2025) == "STALE_OUTPUTS"

    def test_no_period_treated_as_non_period(self):
        # No period date at all -> judge by the exec date alone.
        r = {"latest_exec_date": "2026-07-28", "latest_backtest_period_date": None,
             "verdict": "EXEC_PROVED"}
        assert _classify_freshness(r, 2025) == "EXEC_PROVED_FRESH"

    def test_no_date_returns_verdict(self):
        r = {"latest_exec_date": None, "latest_backtest_period_date": None,
             "verdict": "EXEC_PROVED_NO_DATE"}
        assert _classify_freshness(r, 2025) == "EXEC_PROVED_NO_DATE"
