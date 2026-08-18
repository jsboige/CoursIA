"""Regression tests for check_markdown_claims_output.py (c.331 / c.290 guard).

The script detects markdown cells that cite numeric values absent from the
previous code cell's output (c.290 pathologie, where prose fabricated
quantitative claims that didn't match the cell it was supposed to
interpolate).

The c.290 case in the wild: PR #11435 (myia-po-2023) on FT-02-QLoRA-
Quantization.ipynb introduced a cell with `~0,09 %` and `~1,2 M` claims
whose code cell output actually printed `0.2385` and `3,145,728`. The
markdown and the output pointed at two different things.

These tests pin the detector's invariants on synthetic fixtures so the
guard cannot regress to false-negative (missing the fabrication) without
the test runner catching it.

Test classes (one per direction):

* **TestCanonicalClean** — markdown that quotes numbers from the previous
  code output is CLEAN. The detector must NOT raise a fabrication
  finding when the number is present in the output.
* **TestFabricationDetected** — markdown that quotes a number NOT in
  the previous code output is flagged. The c.290 pathologie live case.
* **TestLiteratureSkip** — explicit headers ("## Bibliographie",
  "## References") skip the cell -- the literature convention is a
  HEADER, not a length.
* **TestSubstantiveFilter** — short numbers (one/two digits) like
  section markers ("## 7. Comparaison") are NOT flagged. Only
  substantive numbers (>= 4 chars normalized) trigger a finding.
* **TestWindowLookup** — the scan window covers the previous N code
  cells (default 3). A claim present in cell idx-2 is accepted as
  anchored even if idx-1 has no output.
* **TestVerdictLogic** — verdict CLEAN / FABRICATION_DETECTED / ERROR
  on the fixtures above.
* **TestStripMdStructure** — heading lines and table headers are
  dropped from the prose that the regex scans (so "## 7. ..." does
  not raise a numeric claim).
* **TestOutputExtraction** — stream + execute_result outputs are both
  flattened into searchable text.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

# Make the script importable
ROOT = Path(__file__).resolve().parent.parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

from check_markdown_claims_output import (  # noqa: E402
    _fuzzy_present,
    _is_md_heading_line,
    _lit_skip,
    _normalize_num,
    _output_text,
    _strip_md_structure,
    _substantive,
    check_notebook,
)


def _mk_nb(cells: list[dict]) -> dict:
    """Wrap a list of cells into a minimal valid notebook structure."""
    return {
        "cells": cells,
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }


def _code_cell(source: str, outputs: list) -> dict:
    return {
        "cell_type": "code",
        "execution_count": 1,
        "metadata": {},
        "source": source.splitlines(keepends=True),
        "outputs": outputs,
    }


def _md_cell(source: str) -> dict:
    return {
        "cell_type": "markdown",
        "metadata": {},
        "source": source.splitlines(keepends=True),
    }


def _stream_output(text: str) -> dict:
    return {"output_type": "stream", "name": "stdout", "text": text}


def _exec_output(text: str) -> dict:
    return {
        "output_type": "execute_result",
        "data": {"text/plain": text},
        "metadata": {},
    }


class TestNormalizeNum:
    """Pure-function tests for the numeric normalization."""

    def test_strip_si_suffix(self):
        assert _normalize_num("3,1 M") == "3.1"
        assert _normalize_num("1.3B") == "1.3"
        assert _normalize_num("1,16 Go") == "1.16"
        assert _normalize_num("0,09 %") == "0.09"
        assert _normalize_num("75 steps") == "75"
        assert _normalize_num("15 epochs") == "15"

    def test_whitespace_and_nbsp(self):
        assert _normalize_num("3\xa0145") == "3145"

    def test_comma_vs_dot(self):
        assert _normalize_num("3,145,728") == "3145.728"

    def test_units_whitespace(self):
        assert _normalize_num("  256 tokens") == "256"


class TestSubstantiveFilter:
    """The substantive filter rejects short / sentinel numbers."""

    def test_short_numbers_rejected(self):
        assert not _substantive("0")
        assert not _substantive("7")
        assert not _substantive("01")
        assert not _substantive("5.")

    def test_zero_rejected(self):
        assert not _substantive("0")
        assert not _substantive("0.0")
        assert not _substantive("0.00")

    def test_long_numbers_accepted(self):
        assert _substantive("0.09")
        assert _substantive("0.24")
        assert _substantive("3.1")
        assert _substantive("1.32")
        assert _substantive("3145")
        assert _substantive("23.5")


class TestLiteratureSkip:
    """The lit-skip convention is a HEADER, not a length."""

    def test_bibliographie_skipped(self):
        assert _lit_skip("## Bibliographie\n\n- [1] ...\n")

    def test_references_skipped(self):
        assert _lit_skip("## References\n\n1. ...\n")

    def test_long_pedagogical_cell_NOT_skipped(self):
        """The c.290 pathologie sat in a 3000+ char pedagogical cell."""
        prose = ("## Lecture du résultat : le moment où la quantization prend effet\n"
                 + "lorem ipsum " * 200)
        assert not _lit_skip(prose)

    def test_short_quant_cell_NOT_skipped(self):
        assert not _lit_skip("On attend ~0,09 % de paramètres entraînables.")


class TestHeadingLine:
    def test_heading_lines_detected(self):
        assert _is_md_heading_line("## 7. Comparaison")
        assert _is_md_heading_line("### Lecture")
        assert _is_md_heading_line("   # title")
        assert not _is_md_heading_line("not a heading")
        assert not _is_md_heading_line("`code with # in it`")


class TestStripMdStructure:
    def test_headings_dropped(self):
        src = "## 7. Comparaison\n\nLe ratio est 0.24."
        prose = _strip_md_structure(src)
        assert "##" not in prose
        assert "Le ratio est 0.24" in prose

    def test_table_lines_dropped(self):
        src = "| col1 | col2 |\n| --- | --- |\n| 0.24 | 0.99 |\nConclusion: 0.24."
        prose = _strip_md_structure(src)
        assert "Conclusion: 0.24" in prose
        assert "| col1" not in prose

    def test_code_fences_dropped(self):
        src = "```python\nprint(0.24)\n```\nLe ratio est 0.24."
        prose = _strip_md_structure(src)
        assert "print" not in prose
        assert "Le ratio est 0.24" in prose


class TestOutputExtraction:
    def test_stream_output(self):
        text = _output_output = _output_text([_stream_output("hello 0.24")])
        assert "hello 0.24" in text

    def test_execute_result_output(self):
        text = _output_text([_exec_output("Params: 3,145,728")])
        assert "3,145,728" in text

    def test_mixed_outputs(self):
        text = _output_text([
            _stream_output("Loading...\n"),
            _exec_output("Result: 0.2385"),
        ])
        assert "Loading" in text
        assert "0.2385" in text

    def test_empty_outputs(self):
        assert _output_text([]) == ""


class TestFuzzyPresent:
    def test_full_match(self):
        assert _fuzzy_present("0.24", "0.2385")

    def test_no_match(self):
        assert not _fuzzy_present("0.09", "0.2385")

    def test_prefix_with_non_digit(self):
        assert _fuzzy_present("1.3", "1.3B")

    def test_prefix_then_digit_blocked(self):
        """'1.3' must NOT match '1.32' (different magnitude)."""
        assert not _fuzzy_present("1.3", "1.32 Go")

    def test_short_norm_skipped(self):
        assert not _fuzzy_present("7", "0.2385")


class TestCanonicalClean:
    """Markdown that quotes numbers from the previous code output is CLEAN."""

    def test_quote_from_output(self, tmp_path: Path):
        nb = _mk_nb([
            _code_cell("print('trainable params: 3,145,728')", [
                _stream_output("trainable params: 3,145,728 (0.24%)"),
            ]),
            _md_cell("On attend ~3,1 M de paramètres, soit ~0,24 %."),
        ])
        nb_path = tmp_path / "clean.ipynb"
        nb_path.write_text(json.dumps(nb), encoding="utf-8")
        res = check_notebook(nb_path)
        assert res["verdict"] == "CLEAN", res


class TestFabricationDetected:
    """The c.290 pathologie: prose cites numbers NOT in the previous output."""

    def test_fabrication_in_cell_10(self, tmp_path: Path):
        nb = _mk_nb([
            _code_cell("print('trainable params: 3,145,728')", [
                _stream_output("trainable params: 3,145,728 (0.24%)"),
            ]),
            _md_cell("On attend ~1,2 M de paramètres, soit ~0,09 %."),
        ])
        nb_path = tmp_path / "fabricated.ipynb"
        nb_path.write_text(json.dumps(nb), encoding="utf-8")
        res = check_notebook(nb_path)
        assert res["verdict"] == "FABRICATION_DETECTED", res
        findings = res["findings"]
        # The fabricated claims should be among the findings
        norms = {f["normalized"] for f in findings}
        assert "0.09" in norms, findings

    def test_missing_previous_code(self, tmp_path: Path):
        """Markdown without any preceding code cell is skipped, not flagged."""
        nb = _mk_nb([
            _md_cell("On attend ~0,09 %."),
        ])
        nb_path = tmp_path / "no_prev.ipynb"
        nb_path.write_text(json.dumps(nb), encoding="utf-8")
        res = check_notebook(nb_path)
        assert res["verdict"] == "CLEAN", res
        assert res["stats"]["skipped_no_prev_code"] == 1


class TestWindowLookup:
    """The scan window covers the previous N code cells (default 3)."""

    def test_preceding_code_within_window(self, tmp_path: Path):
        """A claim present in code[idx-2] is accepted via window=2 even
        if code[idx-1] has no output."""
        nb = _mk_nb([
            _code_cell("print('ratio: 0.24')", [_stream_output("ratio: 0.24")]),
            _code_cell("x = 1", []),  # no output
            _md_cell("Le ratio observé est 0,24."),
        ])
        nb_path = tmp_path / "window.ipynb"
        nb_path.write_text(json.dumps(nb), encoding="utf-8")
        res = check_notebook(nb_path)
        # With window=3 (default), the 2 preceding code cells are both scanned
        assert res["verdict"] == "CLEAN", res


class TestVerdictLogic:
    def test_clean(self, tmp_path: Path):
        nb = _mk_nb([
            _code_cell("print(0.24)", [_stream_output("0.24")]),
            _md_cell("Le ratio est 0,24."),
        ])
        nb_path = tmp_path / "v_clean.ipynb"
        nb_path.write_text(json.dumps(nb), encoding="utf-8")
        assert check_notebook(nb_path)["verdict"] == "CLEAN"

    def test_fabricated(self, tmp_path: Path):
        nb = _mk_nb([
            _code_cell("print(0.24)", [_stream_output("0.24")]),
            _md_cell("Le ratio est 0,09."),
        ])
        nb_path = tmp_path / "v_fab.ipynb"
        nb_path.write_text(json.dumps(nb), encoding="utf-8")
        r = check_notebook(nb_path)
        assert r["verdict"] == "FABRICATION_DETECTED"
        assert r["findings"]

    def test_error_on_bad_json(self, tmp_path: Path):
        nb_path = tmp_path / "broken.ipynb"
        nb_path.write_text("{not json", encoding="utf-8")
        r = check_notebook(nb_path)
        assert r["verdict"] == "ERROR"
        assert r["errors"]
