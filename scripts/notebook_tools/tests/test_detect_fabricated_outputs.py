"""Tests for scripts/notebook_tools/detect_fabricated_outputs.py — fabricated text output detector.

Why this test file exists
-------------------------
`detect_fabricated_outputs.py` (registre #3801, Prong-A sweep, axe-2 SOTA) is
the TEXT sibling of `detect_blank_figures.py` (#6918 MERGED, axe-1). It detects
fabricated textual outputs in pedagogical notebooks:

  - `Row N` placeholders (Pandas default dataframe index, signature d'un
    dataframe bidon qui n'a pas eu d'index nommé par le vrai code)
  - Zero-stats dataframes (Sharpe/CAGR/MaxDD/NetProfit toutes à 0.0 = backtest
    qui n'a pas tourné)

Founding incident #6891 (8 quantbook.ipynb files, 7/8 avec Row N placeholders
+ 3/8 avec zero-stats dataframes, + 8/8 avec blank PNG — axe 1). Ces deux
détecteurs sont SIBLINGS : axe 1 (images) + axe 2 (texte) = couverture complète
du pattern fabrication. Un notebook peut être flaggé par l'un sans l'autre
(cas QC-Py-15 = axe 2 uniquement, EMA-Cross-Alpha = axe 1 uniquement).

Sept clusters mirroring the detector's documented decision logic :

  1. TestRowNRegex            -- regex compilation, start-of-line, end-of-line/space
  2. TestZeroValueRegex       -- numeric zero token parsing (0, 0.0, 0.00, -0.0)
  3. TestHasRowN              -- positive (single/multiple Row N), negative (real index)
  4. TestHasZeroStatsDataframe-- positive (3+ cols + zeros), negative (real values, partial)
  5. TestDetectCell           -- code-cell routing, multi-signal stacking, output capture
  6. TestScanNotebook         -- end-to-end dict contract, kernel extraction, error handling
  7. TestMainExitCodes        -- CLI: --check / --json / missing-notebook / family-not-found

Test data design : minimal in-memory notebook JSON, no fixture files. The
detector is pure-Python and operates on `cells[]` dicts, so we synthesize the
exact structures that Jupyter produces. Each test isolates one conjunct of the
decision so a regression in any conjunct surfaces as a single failure.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from detect_fabricated_outputs import (  # noqa: E402
    BACKTEST_STATS,
    MIN_STATS_HIT,
    ROW_N_RE,
    ZERO_VALUE_RE,
    _cell_text_outputs,
    _has_row_n,
    _has_zero_stats_dataframe,
    _human_report,
    _iter_notebooks,
    _kernel,
    _should_skip,
    detect_cell,
    main,
    scan_notebook,
)


# ---------------------------------------------------------------------------
# Helpers -- minimal notebook cell factories
# ---------------------------------------------------------------------------

def code_cell(source: str = "", outputs: list | None = None, execution_count: int | None = 1) -> dict:
    """Build a minimal code cell dict mimicking nbformat v4."""
    return {
        "cell_type": "code",
        "execution_count": execution_count,
        "metadata": {},
        "outputs": outputs or [],
        "source": source,
    }


def text_output(text: str) -> dict:
    """Build a stdout stream output (like print())."""
    return {"output_type": "stream", "name": "stdout", "text": text}


def display_data_output(text: str) -> dict:
    """Build a display_data output with text/plain (like display() or repr)."""
    return {"output_type": "display_data", "data": {"text/plain": text}, "metadata": {}}


# ---------------------------------------------------------------------------
# 1. TestRowNRegex -- the row_N regex itself
# ---------------------------------------------------------------------------

class TestRowNRegex:
    """The regex is the core detector -- anchor semantics matter."""

    def test_matches_single_row_n(self):
        assert ROW_N_RE.search("Row 1")

    def test_matches_multi_digit_row_n(self):
        assert ROW_N_RE.search("Row 42")
        assert ROW_N_RE.search("Row 123")

    def test_matches_with_leading_whitespace(self):
        assert ROW_N_RE.search("    Row 5")
        assert ROW_N_RE.search("\tRow 7")

    def test_matches_in_multiline_context(self):
        blob = "header\n  Sharpe  CAGR\nRow 1     0.5   0.1\nRow 2     0.6   0.2\nfooter"
        assert ROW_N_RE.search(blob)
        assert len(ROW_N_RE.findall(blob)) == 2

    def test_does_not_match_no_space_after_number(self):
        # "Row 123abc" -- word boundary should prevent this (Row prefix only)
        assert not ROW_N_RE.search("Row 123abc")

    def test_does_not_match_real_index_named(self):
        # Real backtests use named indices like "2020-01-01", "SPY", "Strategy_A"
        assert not ROW_N_RE.search("2020-01-01  0.5  0.1")
        assert not ROW_N_RE.search("SPY       0.5  0.1")
        assert not ROW_N_RE.search("Strategy_A   0.5  0.1")

    def test_does_not_match_row_in_middle_of_word(self):
        # "Borrow" or "Rowing" should not match (Row is followed by space + digit)
        assert not ROW_N_RE.search("Borrow 100")
        assert not ROW_N_RE.search("Rowing club")


# ---------------------------------------------------------------------------
# 2. TestZeroValueRegex -- numeric zero token parsing
# ---------------------------------------------------------------------------

class TestZeroValueRegex:
    """Zero-value detection -- used by the dataframe check."""

    def test_matches_integer_zero(self):
        assert ZERO_VALUE_RE.match("0")

    def test_matches_float_zero(self):
        assert ZERO_VALUE_RE.match("0.0")
        assert ZERO_VALUE_RE.match("0.00")
        assert ZERO_VALUE_RE.match("0.000")

    def test_matches_signed_zero(self):
        assert ZERO_VALUE_RE.match("-0")
        assert ZERO_VALUE_RE.match("+0")
        assert ZERO_VALUE_RE.match("-0.0")
        assert ZERO_VALUE_RE.match("+0.00")

    def test_does_not_match_nonzero(self):
        assert not ZERO_VALUE_RE.match("0.5")
        assert not ZERO_VALUE_RE.match("1")
        assert not ZERO_VALUE_RE.match("-0.5")
        assert not ZERO_VALUE_RE.match("100")

    def test_does_not_match_nonnumeric_token(self):
        # The regex only matches actual numeric zero forms, not arbitrary tokens
        assert not ZERO_VALUE_RE.match("zero")
        assert not ZERO_VALUE_RE.match("abc")
        assert not ZERO_VALUE_RE.match("null")


# ---------------------------------------------------------------------------
# 3. TestHasRowN -- the Row N detection on cell lines
# ---------------------------------------------------------------------------

class TestHasRowN:
    """`_has_row_n(lines)` returns True when Row N placeholders are present."""

    def test_single_row_n_detected(self):
        assert _has_row_n(["Row 1     0.5   0.1"])

    def test_multiple_row_n_detected(self):
        assert _has_row_n(
            ["Row 1     0.5   0.1", "Row 2     0.6   0.2", "Row 3     0.4   0.05"]
        )

    def test_real_index_named_not_detected(self):
        # Real dataframe with named indices like dates or tickers -- not Row N
        assert not _has_row_n(
            ["2020-01-01  0.5  0.1", "2020-02-01  0.6  0.2"]
        )

    def test_empty_lines_not_detected(self):
        assert not _has_row_n([])

    def test_unrelated_text_not_detected(self):
        assert not _has_row_n(["Some output", "More output", "Even more"])

    def test_count_attribute_in_detect_cell(self):
        # detect_cell should record the count of Row N placeholders.
        cell = code_cell(outputs=[
            display_data_output("\n".join([
                "Sharpe  CAGR",
                "Row 1   0.5  0.1",
                "Row 2   0.6  0.2",
                "Row 3   0.4  0.05",
            ])),
        ])
        findings = detect_cell(cell)
        row_findings = [f for f in findings if f["signal"] == "row_n_placeholder"]
        assert len(row_findings) == 1
        assert row_findings[0]["count"] == 3


# ---------------------------------------------------------------------------
# 4. TestHasZeroStatsDataframe -- dataframe fabrication with zero stats
# ---------------------------------------------------------------------------

class TestHasZeroStatsDataframe:
    """`_has_zero_stats_dataframe` -- dataframe avec 3+ colonnes canoniques et valeurs nulles."""

    def test_canonical_backtest_zero_stats_detected(self):
        # AllWeather pattern : 3 colonnes (Sharpe, CAGR, MaxDD), toutes 0.0
        assert _has_zero_stats_dataframe([
            "       Sharpe  CAGR  MaxDD",
            "A        0.0   0.0   0.0",
            "B        0.0   0.0   0.0",
        ])

    def test_all_four_columns_zero_stats_detected(self):
        # RiskParity pattern : 4 colonnes, toutes 0.0
        assert _has_zero_stats_dataframe([
            "       Sharpe  CAGR  MaxDD  NetProfit",
            "A        0.0   0.0   0.0      0.0",
            "B        0.0   0.0   0.0      0.0",
        ])

    def test_real_nonzero_values_not_detected(self):
        # Real backtest with non-zero values -- the dataframe has structure but
        # the values are NOT all zero (backtest did run).
        assert not _has_zero_stats_dataframe([
            "       Sharpe  CAGR  MaxDD",
            "A       0.78  0.12  -0.18",
            "B       0.65  0.09  -0.22",
        ])

    def test_partial_columns_not_detected(self):
        # Only 2 of 4 canonical columns = not enough signal to claim "backtest result"
        assert not _has_zero_stats_dataframe([
            "       Sharpe  CAGR",
            "A        0.0   0.0",
        ])

    def test_unrelated_dataframe_not_detected(self):
        # Dataframe without backtest-stat columns = not in our pattern
        assert not _has_zero_stats_dataframe([
            "       name    age   city",
            "A      Alice   30    NYC",
            "B      Bob     25    LA",
        ])

    def test_mostly_zero_with_one_nonzero_not_detected(self):
        # 1 value nonzero out of 4 = below 0.5 threshold, no fabrication
        assert not _has_zero_stats_dataframe([
            "       Sharpe  CAGR  MaxDD",
            "A        0.0   0.0   0.0",
            "B        0.5   0.0   0.0",  # 1/6 zeros != all-zero
        ])

    def test_empty_input_not_detected(self):
        assert not _has_zero_stats_dataframe([])


# ---------------------------------------------------------------------------
# 5. TestDetectCell -- cell-level routing + signal stacking
# ---------------------------------------------------------------------------

class TestDetectCell:
    """`detect_cell` -- code-cell routing + multi-signal stacking per cell."""

    def test_markdown_cell_returns_empty(self):
        cell = {"cell_type": "markdown", "source": "Row 1 0.5", "metadata": {}}
        assert detect_cell(cell) == []

    def test_code_cell_no_outputs_returns_empty(self):
        cell = code_cell(outputs=[])
        assert detect_cell(cell) == []

    def test_code_cell_with_clean_outputs_returns_empty(self):
        cell = code_cell(outputs=[
            display_data_output("Result: Sharpe = 0.78, CAGR = 0.12"),
        ])
        assert detect_cell(cell) == []

    def test_code_cell_with_row_n_returns_finding(self):
        cell = code_cell(outputs=[
            display_data_output("Row 1     0.530    7.2%  -12.7%"),
        ])
        findings = detect_cell(cell)
        assert len(findings) == 1
        assert findings[0]["signal"] == "row_n_placeholder"

    def test_code_cell_with_zero_stats_returns_finding(self):
        cell = code_cell(outputs=[
            display_data_output("\n".join([
                "Sharpe  CAGR  MaxDD",
                "0.0     0.0   0.0",
            ])),
        ])
        findings = detect_cell(cell)
        assert any(f["signal"] == "zero_stats_dataframe" for f in findings)

    def test_cell_can_have_both_signals(self):
        # Row N + zero stats in same cell -- should stack both findings.
        # Header separation matters : a multi-section dataframe output where the
        # header for the zero-stats section appears LATER (after a Row N block)
        # is detected as zero_stats because we scan the LAST header, not the first.
        cell = code_cell(outputs=[
            display_data_output("\n".join([
                "Row 1   0.530    7.2%  -12.7%",
                "Row 2   0.612    8.1%  -15.3%",
                "",
                "       Sharpe  CAGR  MaxDD",
                "A       0.0    0.0   0.0",
                "B       0.0    0.0   0.0",
            ])),
        ])
        findings = detect_cell(cell)
        signals = {f["signal"] for f in findings}
        assert "row_n_placeholder" in signals
        assert "zero_stats_dataframe" in signals


# ---------------------------------------------------------------------------
# 6. TestScanNotebook -- end-to-end dict contract
# ---------------------------------------------------------------------------

class TestScanNotebook:
    """`scan_notebook` -- file loading + per-cell aggregation + error handling."""

    def test_missing_file_returns_error_dict(self, tmp_path):
        result = scan_notebook(tmp_path / "missing.ipynb")
        assert result["error"] is not None
        assert result["hits"] == []

    def test_clean_notebook_returns_no_hits(self, tmp_path):
        nb = {
            "cells": [
                {"cell_type": "markdown", "source": "# Title", "metadata": {}},
                code_cell(outputs=[display_data_output("OK result: Sharpe = 0.78")]),
            ],
            "metadata": {"kernelspec": {"name": "python3"}},
        }
        nb_path = tmp_path / "clean.ipynb"
        nb_path.write_text(json.dumps(nb), encoding="utf-8")
        result = scan_notebook(nb_path)
        assert result["error"] is None
        assert result["hits"] == []
        assert result["kernel"] == "python3"

    def test_fabricated_notebook_returns_hits(self, tmp_path):
        nb = {
            "cells": [
                code_cell(outputs=[display_data_output("Row 1     0.530    7.2%")]),
                code_cell(outputs=[display_data_output("\n".join([
                    "Sharpe  CAGR  MaxDD",
                    "0.0     0.0   0.0",
                ]))]),
            ],
            "metadata": {"kernelspec": {"name": "python3"}},
        }
        nb_path = tmp_path / "fab.ipynb"
        nb_path.write_text(json.dumps(nb), encoding="utf-8")
        result = scan_notebook(nb_path)
        assert len(result["hits"]) == 2
        signals = [h["signal"] for h in result["hits"]]
        assert "row_n_placeholder" in signals
        assert "zero_stats_dataframe" in signals

    def test_kernel_extraction_handles_missing_kernelspec(self, tmp_path):
        nb = {"cells": [], "metadata": {}}
        nb_path = tmp_path / "no_kernel.ipynb"
        nb_path.write_text(json.dumps(nb), encoding="utf-8")
        result = scan_notebook(nb_path)
        assert result["kernel"] == "?"


# ---------------------------------------------------------------------------
# 7. TestMainExitCodes -- CLI contract
# ---------------------------------------------------------------------------

class TestMainExitCodes:
    """`main` -- CLI exit codes + JSON output + family scan."""

    def test_missing_notebook_returns_2(self, tmp_path, capsys):
        result = main(["--root", str(tmp_path), "does_not_exist.ipynb"])
        assert result == 2
        captured = capsys.readouterr()
        assert "not found" in captured.err.lower()

    def test_missing_family_returns_2(self, tmp_path, capsys):
        result = main(["--root", str(tmp_path), "--family", "NoSuchFamily"])
        assert result == 2
        captured = capsys.readouterr()
        assert "not found" in captured.err.lower()

    def test_clean_notebook_exit_0(self, tmp_path):
        nb = {"cells": [code_cell(outputs=[display_data_output("OK")])], "metadata": {"kernelspec": {"name": "python3"}}}
        nb_path = tmp_path / "clean.ipynb"
        nb_path.write_text(json.dumps(nb), encoding="utf-8")
        result = main(["--root", str(tmp_path), str(nb_path)])
        assert result == 0

    def test_fabricated_notebook_check_exit_1(self, tmp_path):
        nb = {"cells": [code_cell(outputs=[display_data_output("Row 1     0.530")])], "metadata": {"kernelspec": {"name": "python3"}}}
        nb_path = tmp_path / "fab.ipynb"
        nb_path.write_text(json.dumps(nb), encoding="utf-8")
        result = main(["--root", str(tmp_path), "--check", str(nb_path)])
        assert result == 1

    def test_json_output_is_machine_readable(self, tmp_path, capsys):
        nb = {"cells": [code_cell(outputs=[display_data_output("Row 1     0.530")])], "metadata": {"kernelspec": {"name": "python3"}}}
        nb_path = tmp_path / "fab.ipynb"
        nb_path.write_text(json.dumps(nb), encoding="utf-8")
        main(["--root", str(tmp_path), "--json", str(nb_path)])
        captured = capsys.readouterr()
        payload = json.loads(captured.out)
        assert "results" in payload
        assert "total_hits" in payload
        assert payload["total_hits"] == 1


# ---------------------------------------------------------------------------
# 8. TestShouldSkip -- SKIP_DIRS + _output.ipynb suffix logic
# ---------------------------------------------------------------------------

class TestShouldSkip:
    """`_should_skip` -- SKIP_DIRS + _output suffix matching the sibling detector."""

    def test_skips_lake_packages(self):
        from detect_blank_figures import SKIP_DIRS  # reference sibling
        assert SKIP_DIRS  # ensure sibling still uses these names
        assert _should_skip(Path(".lake/packages/some/file.ipynb"))

    def test_skips_git_dir(self):
        assert _should_skip(Path(".git/hooks/file.ipynb"))

    def test_skips_output_suffix(self):
        assert _should_skip(Path("MyIA.AI.Notebooks/foo/_output.ipynb"))

    def test_keeps_canonical_notebook(self):
        assert not _should_skip(Path("MyIA.AI.Notebooks/QuantConnect/projects/TurnOfMonth/quantbook.ipynb"))


# ---------------------------------------------------------------------------
# 9. TestHumanReport -- formatting
# ---------------------------------------------------------------------------

class TestHumanReport:
    """`_human_report` -- summary + per-notebook section + fix footer."""

    def test_empty_results_show_no_fabrication_message(self):
        report = _human_report([])
        assert "0" in report or "No fabricated" in report

    def test_affected_notebook_section_present(self):
        result = {"path": "foo/bar.ipynb", "kernel": "python3", "hits": [{"cell_index": 5, "signal": "row_n_placeholder", "count": 2}]}
        report = _human_report([result])
        assert "bar.ipynb" in report
        assert "cell [5]" in report
        assert "row_n_placeholder" in report
        assert "x2" in report

    def test_fix_message_present(self):
        result = {"path": "foo.ipynb", "kernel": "python3", "hits": [{"cell_index": 5, "signal": "row_n_placeholder"}]}
        report = _human_report([result])
        assert "re-execute" in report.lower()
        assert "stop&repair" in report.lower() or "stop and repair" in report.lower() or "stop&repair" in report.lower()


# ---------------------------------------------------------------------------
# 10. TestIncident6891Baseline -- regression test on the actual 8 quantbooks
# ---------------------------------------------------------------------------

@pytest.mark.skipif(
    not Path("MyIA.AI.Notebooks/QuantConnect/projects").exists(),
    reason="Run from repo root with QuantConnect family present",
)
class TestIncident6891Baseline:
    """Regression test : on the actual 8 quantbook.ipynb files from incident #6891,
    post-strip (cf PR #7439 strip_fabricated_quantbook_outputs), the detector
    must NOT flag any Row N placeholders (Side A = strip honest, cf #6891).

    Originally (pre-strip commit) the detector flagged >=7/8 quantbooks with
    Row N placeholders. The 26 fabricated cells were stripped + 26 markdown
    warnings inserted. The detector must now report zero Row N findings on
    the 7 Row-N quantbooks (EMA-Cross-Alpha was always Row-N clean, only
    blank-PNG via axe 1).
    """

    TARGETS = [
        "AllWeather", "DualMomentum", "EMA-Cross-Alpha", "FuturesTrend",
        "MomentumStrategy", "RiskParity", "SectorMomentum", "TurnOfMonth",
    ]

    def _scan(self, root):
        out = []
        for proj in self.TARGETS:
            nb_path = root / "QuantConnect" / "projects" / proj / "quantbook.ipynb"
            if nb_path.exists():
                out.append(scan_notebook(nb_path))
        return out

    def test_zero_row_n_after_strip(self):
        """Post-strip : zero Row N findings across all 8 quantbooks."""
        results = self._scan(Path("MyIA.AI.Notebooks"))
        flagged_with_row_n = sum(
            1 for r in results
            if any(h["signal"] == "row_n_placeholder" for h in r["hits"])
        )
        assert flagged_with_row_n == 0, (
            f"Post-strip should have 0 Row N flags, got {flagged_with_row_n}. "
            f"This means the strip from PR #7439 was incomplete or reverted. "
            f"Re-run `python scripts/notebook_tools/strip_fabricated_quantbook_outputs.py --apply --include-blank-png`."
        )

    def test_zero_axis2_findings_post_strip(self):
        """Post-strip : zero axis-2 (text fabrication) findings -- Row N + zero_stats_dataframe.
        EMA-Cross-Alpha may still carry a blank-PNG signature (axe 1 sibling detector,
        not covered by this detector)."""
        results = self._scan(Path("MyIA.AI.Notebooks"))
        for r in results:
            axis2_hits = [
                h for h in r["hits"]
                if h["signal"] in ("row_n_placeholder", "zero_stats_dataframe")
            ]
            assert axis2_hits == [], (
                f"{r['path']}: residual axis-2 fabrication findings: {axis2_hits}"
            )

    def test_pre_strip_baseline_evidence_doc(self):
        """Documentation-only test : the original #6891 Row N evidence counts.

        This is NOT a runtime check (we cannot go back in time). It serves as
        an audit anchor + reference for verifying post-strip == 0.
        Issue #6891 evidence table :
          AllWeather 9, DualMomentum 3, FuturesTrend 15,
          MomentumStrategy 3, RiskParity 11, SectorMomentum 3, TurnOfMonth 16,
          EMA-Cross-Alpha 0 (blank-PNG only, axe 1 sibling).
        Total Row N hits pre-strip = 60.
        """
        expected_pre_strip = {
            "AllWeather": 9, "DualMomentum": 3, "FuturesTrend": 15,
            "MomentumStrategy": 3, "RiskParity": 11, "SectorMomentum": 3,
            "TurnOfMonth": 16, "EMA-Cross-Alpha": 0,
        }
        # Inventory check (sum matches issue body evidence table).
        assert sum(expected_pre_strip.values()) == 60
        # EMA-Cross-Alpha explicitly excluded (blank-PNG signature only).
        assert expected_pre_strip["EMA-Cross-Alpha"] == 0
