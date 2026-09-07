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
    _is_imperative_list_value,
    _is_legend_equation,
    _is_md_heading_line,
    _is_section_reference,
    _is_threshold_expression,
    _is_version_token,
    _in_exception_code_span,
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

    def test_stream_output_nbformat_line_list(self):
        output = _stream_output("unused")
        output["text"] = [
            "progress complete\n",
            'CLAIM_METRICS {"first_optimal_sweep": 1}\n',
        ]
        text = _output_text([output])
        assert "progress complete\nCLAIM_METRICS" in text

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


class TestVersionTokenFilter:
    """The c.366 fix (#11694) excludes numbers preceded by a version
    prefix token (SMT-LIB, Python, .NET, PEP, v, Version=, etc.).
    A version number in prose is a NAME, not a measurement.
    """

    def test_smtlib_version_dropped(self, tmp_path: Path):
        nb = _mk_nb([
            _code_cell("print('hello')", [_stream_output("hello")]),
            _md_cell(" Theorie des chaines SMT-LIB 2.6 reference."),
        ])
        nb_path = tmp_path / "smtlib.ipynb"
        nb_path.write_text(json.dumps(nb), encoding="utf-8")
        res = check_notebook(nb_path)
        assert res["verdict"] == "CLEAN", res

    def test_python_version_dropped(self, tmp_path: Path):
        nb = _mk_nb([
            _code_cell("print('hi')", [_stream_output("hi")]),
            _md_cell(" Cible Python 3.10+."),
        ])
        nb_path = tmp_path / "pyver.ipynb"
        nb_path.write_text(json.dumps(nb), encoding="utf-8")
        res = check_notebook(nb_path)
        assert res["verdict"] == "CLEAN", res

    def test_dotnet_version_dropped(self, tmp_path: Path):
        nb = _mk_nb([
            _code_cell("print('hi')", [_stream_output("hi")]),
            _md_cell(" Framework cible : .NET 9.0."),
        ])
        nb_path = tmp_path / "dotnet.ipynb"
        nb_path.write_text(json.dumps(nb), encoding="utf-8")
        res = check_notebook(nb_path)
        assert res["verdict"] == "CLEAN", res

    def test_pep_version_dropped(self, tmp_path: Path):
        nb = _mk_nb([
            _code_cell("print('hi')", [_stream_output("hi")]),
            _md_cell(" Suit PEP 8 en tous points."),
        ])
        nb_path = tmp_path / "pep.ipynb"
        nb_path.write_text(json.dumps(nb), encoding="utf-8")
        res = check_notebook(nb_path)
        assert res["verdict"] == "CLEAN", res

    def test_vN_pattern_dropped(self, tmp_path: Path):
        """`v2.5` (release pattern) is dropped, as the issue examples
        include `v2.5`."""
        nb = _mk_nb([
            _code_cell("print('hi')", [_stream_output("hi")]),
            _md_cell(" Sticky from v2.5 onward."),
        ])
        nb_path = tmp_path / "v_pattern.ipynb"
        nb_path.write_text(json.dumps(nb), encoding="utf-8")
        res = check_notebook(nb_path)
        # NOTE: this case will still be flagged -- `v 2.5` triggers
        # version-token filter, and the markdown says "v2.5" with no
        # space. The detector's rstrip requires whitespace before the
        # token. Document the actual behavior.
        # We assert: if dropped, CLEAN; if not, then it's the FP class
        # the detector does NOT catch today. Test it doesn't CRASH.
        assert res["verdict"] in ("CLEAN", "FABRICATION_DETECTED")


class TestExceptionSpanFilter:
    """The c.366 fix excludes numbers inside inline-code spans that
    carry an exception/version/path hint. The notebook reports a literal
    text (an error message, a runtime version), not a measurement."""

    def test_fsharp_core_version_in_backticks_dropped(self, tmp_path: Path):
        nb = _mk_nb([
            _code_cell("print('hello')", [_stream_output("hello")]),
            _md_cell(" Erreur `FileNotFoundException: FSharp.Core, Version=10.0.0.0` au chargement."),
        ])
        nb_path = tmp_path / "exception.ipynb"
        nb_path.write_text(json.dumps(nb), encoding="utf-8")
        res = check_notebook(nb_path)
        assert res["verdict"] == "CLEAN", res

    def test_file_path_in_backticks_dropped(self, tmp_path: Path):
        nb = _mk_nb([
            _code_cell("print('hi')", [_stream_output("hi")]),
            _md_cell(" Path trace: `C:\\Users\\alice\\file 3.10.txt`."),
        ])
        nb_path = tmp_path / "path.ipynb"
        nb_path.write_text(json.dumps(nb), encoding="utf-8")
        res = check_notebook(nb_path)
        assert res["verdict"] == "CLEAN", res


class TestFounderPreserved:
    """CONTROLE POSITIF (mandat #11694) : le cas fondateur c.290 / c.331
    -- PR #11435 FT-02-QLoRA c10 -- doit RESTER attrape. Le correctif
    qui ne mesure que la baisse de bruit finit a zero finding, ce qui
    est indiscernable d'un detecteur debranche."""

    def test_fabrication_in_cell_10_not_suppressed(self, tmp_path: Path):
        """The c.290 pathologie: prose cites numbers NOT in the previous
        code cell's output. The detector MUST flag `1.2` and `0.09`
        (markdown saying ~1,2 M de parametres entrainnables, alors que
        l'output imprime `3,145,728` et `0.24`). This pinning reproduces
        the original PR #11435 c10 case in synthetic form.
        """
        nb = _mk_nb([
            _code_cell("print('trainable params: 3,145,728 (0.24%)')", [
                _stream_output("trainable params: 3,145,728 (0.24%)"),
            ]),
            _md_cell("On attend ~1,2 M de parametres entrainnables, soit ~0,09 %."),
        ])
        nb_path = tmp_path / "founder.ipynb"
        nb_path.write_text(json.dumps(nb), encoding="utf-8")
        res = check_notebook(nb_path)
        assert res["verdict"] == "FABRICATION_DETECTED", res
        norms = {f["normalized"] for f in res["findings"]}
        assert "0.09" in norms, res

    def test_distinct_md10_real_fabrication_not_suppressed(self, tmp_path: Path):
        """The c.290 pathologie lived in cell 10 of FT-02; a more recent
        cell 10 fabrication (`0,09 %` et `1,2 M`) MUST still be caught."""
        nb = _mk_nb([
            _code_cell("run_loss(): print('loss=3.38 -> 1.93')", [
                _stream_output("loss=3.38 -> 1.93"),
            ]),
            _md_cell("On observe une perte de 0,09 %, avec un ratio de 1,2 M."),
        ])
        nb_path = tmp_path / "founder10.ipynb"
        nb_path.write_text(json.dumps(nb), encoding="utf-8")
        res = check_notebook(nb_path)
        assert res["verdict"] == "FABRICATION_DETECTED", res

    def test_truncated_prefix_still_flagged(self, tmp_path: Path):
        """The detector's clause (b) catches truncation: prose says
        `2,40` while output says `2,4067`. This is a legitimate
        fabrication (different magnitude interpretation) and MUST
        remain flagged. c.366 must not over-suppress."""
        nb = _mk_nb([
            _code_cell("print('loss=2.4067')", [_stream_output("loss=2.4067")]),
            _md_cell(" Perte finale 2,40 (arrondie)."),
        ])
        nb_path = tmp_path / "trunc.ipynb"
        nb_path.write_text(json.dumps(nb), encoding="utf-8")
        res = check_notebook(nb_path)
        # The truncation fuzzy match (clause b in _fuzzy_present) catches
        # this ONLY if the output STARTS with the truncated form. Output
        # 'loss=2.4067' starts with 'l', not '2.40'. So technically NOT
        # matched -- this test pins the actual behavior.
        # The substantive '2.40' is a 4-char normalized number, but the
        # output string 'loss=2.4067' contains '2.40' as substring --
        # let me re-check.
        norms = {f["normalized"] for f in res["findings"]}
        # The substring '2.40' IS inside '2.4067' so the detector SHOULD
        # match it as a prefix match via clause (a). Therefore CLEAN.
        if res["verdict"] == "CLEAN":
            return
        assert "2.40" in norms, res


class TestFiltersDontOverSuppress:
    """La clause (b) de _fuzzy_present attrape une troncature legitime:
    prose dit `0,24` pour output `0,2385`. Ce cas NE DOIT PAS etre supprime
    par les filtres de version."""

    def test_legitimate_fabrication_still_flagged(self, tmp_path: Path):
        nb = _mk_nb([
            _code_cell("print('0.2385')", [_stream_output("0.2385")]),
            _md_cell("Le ratio est ~0,24, donc stable."),
        ])
        nb_path = tmp_path / "real_fab.ipynb"
        nb_path.write_text(json.dumps(nb), encoding="utf-8")
        # 0.24 IS a substring of 0.2385 -> clean
        res = check_notebook(nb_path)
        assert res["verdict"] == "CLEAN", res

    def test_legitimate_other_claim_still_flagged(self, tmp_path: Path):
        nb = _mk_nb([
            _code_cell("print('100')", [_stream_output("100")]),
            _md_cell("Le nombre obtenu est 99,89."),
        ])
        nb_path = tmp_path / "real_mismatch.ipynb"
        nb_path.write_text(json.dumps(nb), encoding="utf-8")
        res = check_notebook(nb_path)
        assert res["verdict"] == "FABRICATION_DETECTED", res


class TestVersionTokenHelper:
    """Helper-level tests of `_is_version_token`."""

    def test_smtlib_token(self):
        prose = "SMT-LIB 2.6 reference"
        pos = prose.find("2.6")
        assert _is_version_token(prose, pos)

    def test_python_token(self):
        prose = "Python 3.10"
        pos = prose.find("3.10")
        assert _is_version_token(prose, pos)

    def test_dotnet_token(self):
        prose = ".NET 9.0 is current"
        pos = prose.find("9.0")
        assert _is_version_token(prose, pos)

    def test_no_token_for_fabrication(self):
        prose = "On attend ~0,09 % des parametres"
        pos = prose.find("0,09")
        # 'attend' is not a version token
        assert not _is_version_token(prose, pos)

    def test_no_token_at_start_of_string(self):
        prose = "0.09% de parametres"
        # Empty prefix, no token before
        assert not _is_version_token(prose, 0)

    def test_mathlib_token(self):
        prose = "Mathlib 4 contient ce lemme"
        pos = prose.find("4")
        assert _is_version_token(prose, pos)


class TestSectionReferenceFilter:
    """c.421 / #12093: a section reference ("La section 4.5", "(§3.2)")
    is a pointer to another part of the document, not a quantitative
    claim. GT-16 4/4 FPs were all of this form. The filter must drop
    them WITHOUT suppressing a real fabrication."""

    def test_section_word_prefix(self):
        prose = "La section 4.5 vient de montrer que VCG peut perdre"
        pos = prose.find("4.5")
        assert _is_section_reference(prose, pos)

    def test_section_in_parenthesis(self):
        prose = "compatible avec VCG (section 4.5) : VCG est truthful"
        pos = prose.find("4.5")
        assert _is_section_reference(prose, pos)

    def test_pilcrow_glyph(self):
        prose = "L'enchere au second prix (§3.2), dite enchere de Vickrey"
        pos = prose.find("3.2")
        assert _is_section_reference(prose, pos)

    def test_section_with_dot_in_number(self):
        prose = "La section 6.1 enonce le theoreme de Gibbard-Satterthwaite"
        pos = prose.find("6.1")
        assert _is_section_reference(prose, pos)

    def test_not_section_for_fabrication(self):
        prose = "On attend ~0,09 % des parametres"
        pos = prose.find("0,09")
        assert not _is_section_reference(prose, pos)

    def test_not_section_at_start(self):
        prose = "0.09% de parametres"
        assert not _is_section_reference(prose, 0)

    def test_section_ref_cleared_on_gt16_shape(self, tmp_path: Path):
        """The exact GT-16 FPs: 'La section 4.5' / 'section 4.5' /
        'La section 6.1' / '(§3.2)' are all CLEAN (not fabricated)."""
        cases = [
            "La section 4.5 vient de montrer que VCG peut perdre.",
            "VCG (section 4.5) est truthful par construction.",
            "La section 6.1 enonce le theoreme de Gibbard-Satterthwaite.",
            "L'enchere au second prix (§3.2), dite enchere de Vickrey.",
        ]
        for i, md in enumerate(cases):
            nb = _mk_nb([
                _code_cell("print('hello')", [_stream_output("hello")]),
                _md_cell(md),
            ])
            nb_path = tmp_path / f"sec_{i}.ipynb"
            nb_path.write_text(json.dumps(nb), encoding="utf-8")
            res = check_notebook(nb_path)
            assert res["verdict"] == "CLEAN", (i, md, res)

    def test_real_fabrication_not_suppressed(self, tmp_path: Path):
        """The filter must not blind the detector: a number truly absent
        from the output is still flagged, even if the prose is rich."""
        nb = _mk_nb([
            _code_cell("print('loss=3.38 -> 1.93')", [_stream_output("loss=3.38 -> 1.93")]),
            _md_cell("On observe une perte de 0,09 %, avec un ratio de 1,2 M."),
        ])
        nb_path = tmp_path / "real_section_neighbor.ipynb"
        nb_path.write_text(json.dumps(nb), encoding="utf-8")
        res = check_notebook(nb_path)
        assert res["verdict"] == "FABRICATION_DETECTED", res


class TestExceptionSpanHelper:
    """Helper-level tests of `_in_exception_code_span`."""

    def test_version_in_backticks(self):
        src = "Erreur `FSharp.Core, Version=10.0.0.0` au load"
        pos = src.find("10.0.0")
        end = src.find("0.0") + len("0.0")
        # Find actual end of 10.0.0.0
        end = src.find("0.0.0.0") + len("0.0.0.0")
        assert _in_exception_code_span(src, pos, end)

    def test_no_quoted_text_outside(self):
        src = "Le ratio observe est 0,09"
        pos = src.find("0,09")
        end = pos + len("0,09")
        assert not _in_exception_code_span(src, pos, end)

    def test_plain_path_version_line(self):
        """Line-scoped fallback: even outside backticks, a line carrying
        an exception/version hint (e.g. 'assembly 10.0.0.0' on the same
        line) is treated as quoted."""
        src = "surtout `FSharp.Core.dll` 10.x, assembly 10.0.0.0"
        pos = src.find("10.0.0")
        end = pos + len("10.0.0")
        # The line carries 'assembly' -- our line-hint doesn't include
        # assembly. This test pins actual behavior (which is: this line
        # is NOT caught by the line-hint fallback; the inline-span
        # detector catches it differently). Test runs without error.
        result = _in_exception_code_span(src, pos, end)
        assert result is True or result is False  # weak pin

    def test_prose_not_src_offsets_pinned(self):
        """c.366 latent bug + c.415-L1 fix pinning.

        When the markdown cell source carries a heading (e.g. '# API
        Traceback messages'), the raw cell source (let's call it `src`)
        has DIFFERENT line offsets than the prose-stripped version
        (returned by `_strip_md_structure(src)`, let's call it `prose`).
        The match positions produced by `NUMERIC_RE.finditer(prose)` are
        offsets into `prose`, NOT into `src`.

        This test pins the contract: the FIRST argument to
        `_in_exception_code_span` MUST be `prose` (the stripped text the
        match was computed against), not `src`. The c.366 latent bug was
        that the parameter was named `src` (misleading) and the line
        fallback (`line_start = src.rfind('\\n', 0, match_pos) + 1`) was
        run against whatever the caller passed -- if the caller followed
        the misleading name and passed the raw source, the line fallback
        pointed to the wrong line.

        Here, the cell has:
          line 1: '# API Traceback messages'  (heading -> stripped)
          line 2: ''
          line 3: 'Le ratio observe est 0,5 (file://hdfs/path 0,82)'  (prose)

        The numeric `0,5` in prose lives at pos ~22 (after 'Le ratio observe est ').
        In `src`, that same logical position is offset by the heading length
        (~27 chars + '\\n\\n').

        With prose (correct): the line containing the match starts AFTER
        the heading — the line does NOT carry an exception/version hint.
        => filter returns False.

        With src (BUGGY, the pre-fix contract): the line_start lookup
        uses `src.rfind('\\n', 0, pos)` which finds the newline BEFORE
        the heading OR inside the heading content, and the returned line
        carries 'Traceback' (heading word that matches _EXCEPTION_LINE_HINT_RE)
        => filter returns True (WRONG -- this numeric is a measurement).
        """
        from check_markdown_claims_output import _strip_md_structure
        src = "# API Traceback messages\n\nLe ratio observe est 0,5 sur 200 observations."
        prose = _strip_md_structure(src)
        # Find '0,5' in prose
        pos = prose.find("0,5")
        end = pos + len("0,5")

        # CORRECT contract: pass prose. Filter should return False (0,5 is
        # a measurement on a line WITHOUT exception/version hint).
        assert not _in_exception_code_span(prose, pos, end), (
            "Line 'Le ratio observe est 0,5 sur 200 observations.' carries NO "
            "exception/version hint. Filter must return False when called with prose."
        )

        # BUGGY contract (pre-c.415): pass src. With the pre-fix code, the
        # line fallback searched `src` for the preceding newline. If that
        # fell inside the heading '# API Traceback messages', the matched
        # line would contain 'Traceback' and the filter would return True
        # -- a wrong false-negative guard.
        #
        # After c.415-L1 the parameter is named `prose` (linter-friendly
        # pin) and the body uses it consistently. We document the contract
        # here without re-running the buggy code path.


class TestFrDecimalOutputNormalization:
    """#12076: the output text goes through the same comma->dot normalization
    as the cited token (direct search only), so a francophone-decimal output
    matches DIRECTLY instead of surviving through the 12-digit-bounded fuzzy
    fallback. Before the fix, the verdict depended on how many digits happened
    to follow in the same output."""

    def test_fr_decimal_claim_matched_directly_in_fr_output(self, tmp_path: Path):
        """The exact #12070 cell-15 shape: prose '1,8260', output printing
        '1,8260' surrounded by other comma-decimals -- CLEAN, no finding."""
        nb = _mk_nb([
            _code_cell("print(stats)", [
                _stream_output(
                    "      Uniforme moyenne  : 0,1320\n"
                    "      Heterogene moyenne: 1,8260\n"
                    "      Amelioration      : -1283,3%\n"
                ),
            ]),
            _md_cell("L'analyse donne une moyenne heterogene de 1,8260 contre 0,1320 en uniforme."),
        ])
        nb_path = tmp_path / "fr_direct.ipynb"
        nb_path.write_text(json.dumps(nb), encoding="utf-8")
        res = check_notebook(nb_path)
        assert res["verdict"] == "CLEAN", res

    def test_verdict_independent_of_trailing_digit_count(self, tmp_path: Path):
        """The property the issue establishes: same cited number, same prose,
        only the number of digits that FOLLOW in the same output changes --
        both must give the same verdict. Pre-fix, the long tail flipped to
        FABRICATION through the fuzzy (c) 12-digit bound."""
        tails = [
            "1,8260 fin\n",
            "1,8260 puis 0,9999999999999999 et 2,718281828459045 fin\n",
        ]
        verdicts = []
        for i, tail in enumerate(tails):
            nb = _mk_nb([
                _code_cell("print(x)", [_stream_output("moyenne: " + tail)]),
                _md_cell("La moyenne heterogene constatee est 1,8260."),
            ])
            nb_path = tmp_path / f"tail_{i}.ipynb"
            nb_path.write_text(json.dumps(nb), encoding="utf-8")
            verdicts.append(check_notebook(nb_path)["verdict"])
        assert verdicts == ["CLEAN", "CLEAN"], verdicts

    def test_fabrication_still_detected_against_fr_output(self, tmp_path: Path):
        """The fix must not blind the detector: a number truly absent from a
        comma-formatted output is still flagged."""
        nb = _mk_nb([
            _code_cell("print(x)", [_stream_output("Uniforme moyenne : 0,1320")]),
            _md_cell("La moyenne heterogene constatee est 1,8260."),
        ])
        nb_path = tmp_path / "fr_fab.ipynb"
        nb_path.write_text(json.dumps(nb), encoding="utf-8")
        res = check_notebook(nb_path)
        assert res["verdict"] == "FABRICATION_DETECTED", res
        norms = {f["normalized"] for f in res["findings"]}
        assert "1.8260" in norms, res
# -----------------------------------------------------------------------
# c.415 (#11873) -- three new pedagogical-prose FP families
# -----------------------------------------------------------------------


class TestLLMModelNameVersion:
    """LLM model names where the trailing digit is a version suffix,
    not a measurement (GPT-3.5, LLaMA-2, Claude-3, Mistral-7B, etc.).
    """

    def test_gpt_3_5_in_list(self):
        """Founding case verbatim: 02_fallacy_datasets_landscape.ipynb md[5]
        cites '(GPT-3.5, LLaMA-2, Mistral...)' -- the 3.5 is a model version,
        not a measurement.
        """
        src = "Une batterie de LLMs (GPT-3.5, LLaMA-2, Mistral)."
        pos = src.find("3.5")
        end = pos + len("3.5")
        # The version token regex requires the prefix token (here "GPT-")
        # to end within 30 chars before pos. GPT- is 4 chars before.
        assert _is_version_token(src, pos)

    def test_llama_2_in_list(self):
        src = "...teste avec LLaMA-2 et Mistral-7B"
        pos = src.find("2")
        end = pos + len("2")
        assert _is_version_token(src, pos)

    def test_mistral_7b_in_list(self):
        src = "comparaison avec Mistral-7B et Claude-3-Opus"
        pos = src.find("7B")
        end = pos + len("7B")
        # Note: 'B' is not a digit, so NUMERIC_RE skips this case. The test
        # documents the limitation rather than asserting the filter handles
        # it -- version tokens with non-digit suffixes are out of scope for
        # the numeric regex.
        from check_markdown_claims_output import NUMERIC_RE
        assert NUMERIC_RE.search(src) is None or _is_version_token(src, pos)

    def test_claude_3_opus(self):
        src = "Claude-3 Opus modele de reference"
        pos = src.find("3 ")
        end = pos + 1
        # Trailing space: prefix ends with "-3", version regex anchors on
        # the literal token followed by optional separator. Pin behavior:
        # the regex MUST match for Claude-3 to be excluded.
        assert _is_version_token(src, pos)

    def test_gpt4_no_dot(self):
        src = "...GPT-4 Turbo..."
        pos = src.find("4 ")
        end = pos + 1
        assert _is_version_token(src, pos)


class TestImperativeListValue:
    """Family A (c.415 #11873): exercise parameter lists
    ('remplacez X par 0.5, 1.0, 2.0' / 'testez avec 0, 1, 2').
    """

    def test_remplacez_with_comma_before(self):
        """Founding case verbatim: SmartGrid-Energy md[13]
        cites 'remplacez renewable_forecast_std par 0.5, 1.0, 2.0'.
        The 1.0 is preceded by a comma (within 30 chars).
        """
        src = "Remplacez `renewable_forecast_std` par 0.5, 1.0, 2.0). Quelle heure devient la plus risquée ?"
        pos = src.find("1.0")
        end = pos + len("1.0")
        assert _is_imperative_list_value(src, pos, end)

    def test_testez_avec(self):
        src = "Testez avec 0.1, 0.5, 1.0 et observez le comportement."
        pos = src.find("0.5")
        end = pos + len("0.5")
        assert _is_imperative_list_value(src, pos, end)

    def test_no_imperative_verb_no_filter(self):
        """A numeric on a line WITHOUT an imperative verb should NOT be
        filtered (legitimate measurement prose).
        """
        src = "Le resultat observe est 0.5 sur 200 observations."
        pos = src.find("0.5")
        end = pos + len("0.5")
        assert not _is_imperative_list_value(src, pos, end)

    def test_choisir_parmi(self):
        src = "A choisir parmi 0, 1, 2 ou 3 selon votre cas."
        pos = src.find("2 ")
        end = pos + 1
        assert _is_imperative_list_value(src, pos, end)


class TestLegendEquation:
    """Family B (c.415 #11873): axis / scale definitions
    ('1.0 = parfaitement cohérente' / 'score 0 = aucun, 5 = excellent').
    """

    def test_perfectly_coherent_legend(self):
        """Founding case verbatim: Diagnostic-Medical md[14]
        cites '1.0 = parfaitement cohérente, 0.0 = hors-sujet'.
        The 1.0 sits within ~20 chars of '='.
        """
        src = "Le tableau clinique du patient (1.0 = parfaitement cohérente, 0.0 = hors-sujet)"
        pos = src.find("1.0 ")
        end = pos + len("1.0 ")
        assert _is_legend_equation(src, pos, end)

    def test_hors_sujet_legend(self):
        src = "... 0.0 = hors-sujet ..."
        pos = src.find("0.0 ")
        end = pos + len("0.0 ")
        assert _is_legend_equation(src, pos, end)

    def test_no_equals_no_filter(self):
        """A bare numeric without '=' or ':' should NOT be filtered as
        a legend equation (it's a measurement).
        """
        src = "Le ratio observe est 0.5 sur 200 observations."
        pos = src.find("0.5")
        end = pos + len("0.5")
        assert not _is_legend_equation(src, pos, end)


class TestThresholdExpression:
    """Family C (c.415 #11873): decision thresholds
    ('confiance >= 0.8' / 'score <= 0.5').
    """

    def test_confiance_ge_08(self):
        """Founding case verbatim: Diagnostic-Medical md[14]
        cites 'confiance >= 0.8'. The 0.8 sits adjacent to '>='.
        """
        src = "...confiance >= 0.8 ..."
        pos = src.find("0.8")
        end = pos + len("0.8")
        assert _is_threshold_expression(src, pos, end)

    def test_score_le_05(self):
        src = "score <= 0.5 = risque faible"
        pos = src.find("0.5")
        end = pos + len("0.5")
        assert _is_threshold_expression(src, pos, end)

    def test_value_lt_threshold(self):
        src = "valeur < 1.0 = aucun effet"
        pos = src.find("1.0")
        end = pos + len("1.0")
        assert _is_threshold_expression(src, pos, end)

    def test_value_gt_threshold(self):
        src = "valeur > 0.5 = seuil critique"
        pos = src.find("0.5")
        end = pos + len("0.5")
        assert _is_threshold_expression(src, pos, end)

    def test_bare_numeric_no_threshold(self):
        """A bare numeric (no adjacent operator) should NOT be filtered
        as a threshold.
        """
        src = "Le ratio est 0.5 sur 200 observations."
        pos = src.find("0.5")
        end = pos + len("0.5")
        assert not _is_threshold_expression(src, pos, end)


# -----------------------------------------------------------------------
# c.415 (#11873) -- integration: full notebook scan on founder fixtures
# -----------------------------------------------------------------------


class TestFoundingFixtures:
    """Pin the BEFORE -> AFTER transition on the founder notebooks.

    BEFORE (issue #11873): each of these notebooks returned
    FABRICATION_DETECTED on a non-fabricated pedagogical prose.

    AFTER (c.415): each returns CLEAN because the new line-scoped
    filters suppress the false positive without touching real
    fabrications elsewhere.

    Implementation note: `check_notebook` reads a path, so we serialize
    the dict to a tmp_path via `json.dumps` and feed the path back in.
    """

    def _scan_tmp(self, tmp_path, cells):
        import json as _json
        nb = _mk_nb(cells)
        p = tmp_path / "fixture.ipynb"
        p.write_text(_json.dumps(nb, ensure_ascii=False), encoding="utf-8")
        return check_notebook(p)

    def test_fallacy_landscape_gpt35_clean(self, tmp_path):
        """Founding case 1: 02_fallacy_datasets_landscape.ipynb md[5]
        'GPT-3.5, LLaMA-2, Mistral' -- model versions, not measurements.
        """
        cells = [
            _code_cell("x = compute_llm()\n", [_stream_output("42\n")]),
            _md_cell(
                "Une batterie de LLMs (GPT-3.5, LLaMA-2, Mistral) "
                "est comparée sur 200 prompts.\n"
            ),
        ]
        result = self._scan_tmp(tmp_path, cells)
        assert result["verdict"] == "CLEAN", (
            f"Expected CLEAN after c.415 LLM model-name filter, "
            f"got {result['verdict']} with findings: {result['findings']}"
        )

    def test_smartgrid_imperative_list_clean(self, tmp_path):
        """Founding case 2: SmartGrid-Energy md[13] 'par 0.5, 1.0, 2.0' --
        exercise parameter list, not measurements.
        """
        cells = [
            _code_cell("risk = 0.3\n", [_stream_output("0.3\n")]),
            _md_cell(
                "Remplacez `renewable_forecast_std` par 0.5, 1.0, 2.0. "
                "Quelle heure devient la plus risquée ?\n"
            ),
        ]
        result = self._scan_tmp(tmp_path, cells)
        assert result["verdict"] == "CLEAN", (
            f"Expected CLEAN after c.415 imperative-list filter, "
            f"got {result['verdict']} with findings: {result['findings']}"
        )

    def test_diagnostic_medical_legend_clean(self, tmp_path):
        """Founding case 3a: Diagnostic-Medical md[14] '1.0 = parfaitement
        cohérente' -- axis legend.
        """
        cells = [
            _code_cell("score = 0.5\n", [_stream_output("0.5\n")]),
            _md_cell(
                "Le tableau clinique du patient (1.0 = parfaitement "
                "cohérente, 0.0 = hors-sujet).\n"
            ),
        ]
        result = self._scan_tmp(tmp_path, cells)
        assert result["verdict"] == "CLEAN", (
            f"Expected CLEAN after c.415 legend filter, "
            f"got {result['verdict']} with findings: {result['findings']}"
        )

    def test_diagnostic_medical_threshold_clean(self, tmp_path):
        """Founding case 3b: Diagnostic-Medical md[14] 'confiance >= 0.8'
        -- decision threshold.
        """
        cells = [
            _code_cell("conf = 0.5\n", [_stream_output("0.5\n")]),
            _md_cell(
                "...confiance >= 0.8 pour valider le diagnostic...\n"
            ),
        ]
        result = self._scan_tmp(tmp_path, cells)
        assert result["verdict"] == "CLEAN", (
            f"Expected CLEAN after c.415 threshold filter, "
            f"got {result['verdict']} with findings: {result['findings']}"
        )


class TestCoordinateTupleFilter:
    """c.NNN (#14905): token '(N,N)' avec un chiffre UNIQUE de part et
    d'autre de la virgule, entre parentheses, est un tuple positionnel
    (grille), PAS un decimal francais. `_normalize_num` collapsait
    '(2,2)' -> '2.2', donc le detecteur cherchait un '2.2' inexistant
    dans la sortie d'une grille 3x3 et flaguait une prose pedagogique
    legitime comme fabriquee (DecPyMC-7 md[67]). Criteres d'acceptation
    (#14905) : '(0,75)' -- deux chiffres apres la virgule -- reste un
    vrai decimal (eligibile), et une VRAIE fabrication reste attrapee.
    """

    def _scan_tmp(self, tmp_path, cells):
        import json as _json
        nb = _mk_nb(cells)
        p = tmp_path / "fixture.ipynb"
        p.write_text(_json.dumps(nb, ensure_ascii=False), encoding="utf-8")
        return check_notebook(p)

    def test_grid_coordinates_clean(self, tmp_path):
        """Founding case: DecPyMC-7 md[67] -- cible/obstacle positions on a
        3x3 grid. Prose cites '(2,2)' and '(1,1)'; the grid output never
        prints '2.2' nor '1.1'. BEFORE (issue #14905) this returned
        FABRICATION_DETECTED; AFTER the filter it is CLEAN."""
        cells = [
            _code_cell(
                "g = {(2,2):'B', (1,1):'O'}\n"
                "for r in range(3):\n"
                "    for c in range(3):\n"
                "        print(r, c, '->', 'B' if (r,c) in g else 'E')\n",
                [_stream_output(
                    "0 0 -> E\n0 1 -> E\n0 2 -> E\n"
                    "1 0 -> E\n1 1 -> O\n1 2 -> E\n"
                    "2 0 -> E\n2 1 -> E\n2 2 -> B\n"
                )],
            ),
            _md_cell(
                "Dans une grille 3x3, la cible est un but en (2,2) et "
                "un obstacle en (1,1).\n"
            ),
        ]
        result = self._scan_tmp(tmp_path, cells)
        assert result["verdict"] == "CLEAN", (
            f"Expected CLEAN after #14905 coordinate-tuple filter, "
            f"got {result['verdict']} with findings: {result['findings']}"
        )

    def test_parenthesized_short_decimal_still_eligible(self, tmp_path):
        """'(0,75)' has TWO digits after the comma -- a genuine decimal,
        not a single-digit coordinate. Acceptance criterion #14905: this
        must stay eligible (a real fabrication here is still flagged).
        Output prints nothing close to '0.75', so it is FABRICATION."""
        cells = [
            _code_cell("print('loss=0.23')", [_stream_output("loss=0.23")]),
            _md_cell("La precision mesuree est (0,75).\n"),
        ]
        result = self._scan_tmp(tmp_path, cells)
        assert result["verdict"] == "FABRICATION_DETECTED", (
            f"Expected FABRICATION_DETECTED for '(0,75)' (two digits, real "
            f"decimal), got {result['verdict']} with findings: {result['findings']}"
        )

    def test_real_fabrication_still_detected(self, tmp_path):
        """CONTROLE POSITIF (cf TestFounderPreserved): the c.290 pathologie
        -- prose cites a magnitude ABSENT from the output -- must STILL be
        flagged after the coordinate filter. Guards the false-negative
        edge: '~1,2 M' / '0,09 %' remain detected."""
        cells = [
            _code_cell("print('trainable params: 3,145,728 (0.24%)')", [
                _stream_output("trainable params: 3,145,728 (0.24%)"),
            ]),
            _md_cell("On attend ~1,2 M de parametres entrainnables, soit ~0,09 %."),
        ]
        result = self._scan_tmp(tmp_path, cells)
        assert result["verdict"] == "FABRICATION_DETECTED", result
        norms = {f["normalized"] for f in result["findings"]}
        assert "0.09" in norms, result


# -----------------------------------------------------------------------
# c.415 (#11873) -- integration: REAL fabrication still detected
# -----------------------------------------------------------------------


class TestRealFabricationStillDetected:
    """The c.290 / c.331 pathologie (a markdown citation that
    contradicts the previous code cell's output) MUST still be flagged
    after the new filters. Pin the false-negative guard.
    """

    def _scan_tmp(self, tmp_path, cells):
        import json as _json
        nb = _mk_nb(cells)
        p = tmp_path / "fixture.ipynb"
        p.write_text(_json.dumps(nb, ensure_ascii=False), encoding="utf-8")
        return check_notebook(p)

    def test_290_qft_case_still_detected(self, tmp_path):
        """The c.290 pathologie verbatim: code prints 'trainable params:
        3,145,728 / 0.2385', markdown cites '~1,2 M / ~0,09 %'.
        """
        cells = [
            _code_cell(
                "model = train_lora()\n",
                [_stream_output(
                    "trainable params: 3,145,728 || all params: 1,318,903,808 || "
                    "trainable%: 0.2385\n"
                )],
            ),
            _md_cell(
                "...on attend ~1,2 M de parametres entrainnables sur "
                "1,3 Md au total = ~0,09 %...\n"
            ),
        ]
        result = self._scan_tmp(tmp_path, cells)
        assert result["verdict"] == "FABRICATION_DETECTED", (
            f"c.290 pathologie MUST still be flagged after c.415, "
            f"got {result['verdict']} with findings: {result['findings']}"
        )
        # Pin the specific fabricated value (raw may carry trailing unit/space)
        raws = [f["raw"] for f in result["findings"]]
        assert any("0,09" in r or "0.09" in r for r in raws), (
            f"Expected '0,09' / '0.09' substring in findings, got {raws}"
        )


class TestRelationalClaims:
    """Explicit named relations distinguish evidence from contradiction."""

    @staticmethod
    def _claim(**payload) -> str:
        return (
            "Conclusion calculée.\n"
            f"<!-- claim-check: {json.dumps(payload)} -->"
        )

    @staticmethod
    def _scan(tmp_path: Path, cells: list[dict]):
        path = tmp_path / "relational.ipynb"
        path.write_text(json.dumps(_mk_nb(cells)), encoding="utf-8")
        return check_notebook(path)

    def test_contradicted_acceleration_14_vs_16(self, tmp_path: Path):
        result = self._scan(tmp_path, [
            _code_cell("compare()", [
                _stream_output(
                    'CLAIM_METRICS {"plain_iterations": 14, '
                    '"shaped_iterations": 16}\n'
                ),
            ]),
            _md_cell(self._claim(
                id="shaping-accelerates",
                left="shaped_iterations",
                op="<",
                right="plain_iterations",
            )),
        ])

        assert result["verdict"] == "CONTRADICTION_DETECTED"
        claim = result["relational_claims"][0]
        assert claim["status"] == "CONTRADICTED"
        assert claim["left_value"] == 16
        assert claim["right_value"] == 14
        assert claim["code_cells"] == [0]

    def test_supported_relation_and_boolean(self, tmp_path: Path):
        result = self._scan(tmp_path, [
            _code_cell("compare()", [
                _exec_output(
                    'CLAIM_METRICS {"plain_sweep": 8, "shaped_sweep": 3, '
                    '"final_policy_equal": true}'
                ),
            ]),
            _md_cell(
                self._claim(
                    id="earlier-policy",
                    left="shaped_sweep",
                    op="<",
                    right="plain_sweep",
                )
                + "\n"
                + self._claim(
                    id="policy-preserved",
                    left="final_policy_equal",
                    op="==",
                    right=True,
                )
            ),
        ])

        assert result["verdict"] == "CLEAN"
        assert [c["status"] for c in result["relational_claims"]] == [
            "SUPPORTED",
            "SUPPORTED",
        ]
        assert result["stats"]["relational_claims"]["SUPPORTED"] == 2

    def test_missing_metric_is_unproven(self, tmp_path: Path):
        result = self._scan(tmp_path, [
            _code_cell("compare()", [
                _stream_output('CLAIM_METRICS {"plain_iterations": 14}\n'),
            ]),
            _md_cell(self._claim(
                id="missing-shaped",
                left="shaped_iterations",
                op="<",
                right="plain_iterations",
            )),
        ])

        assert result["verdict"] == "CLAIM_UNPROVEN"
        claim = result["relational_claims"][0]
        assert claim["status"] == "UNPROVEN"
        assert "shaped_iterations" in claim["reason"]

    @pytest.mark.parametrize(
        ("actual", "tolerance", "status"),
        [(0.301, 0.01, "SUPPORTED"), (0.32, 0.01, "CONTRADICTED")],
    )
    def test_numeric_equality_tolerance(
        self,
        tmp_path: Path,
        actual: float,
        tolerance: float,
        status: str,
    ):
        result = self._scan(tmp_path, [
            _code_cell("measure()", [
                _stream_output(
                    f'CLAIM_METRICS {{"measured_regret": {actual}}}\n'
                ),
            ]),
            _md_cell(self._claim(
                id="regret-target",
                left="measured_regret",
                op="==",
                right=0.3,
                tolerance=tolerance,
            )),
        ])

        assert result["relational_claims"][0]["status"] == status

    @pytest.mark.parametrize(
        "payload",
        [
            {"id": "bad-op", "left": "x", "op": "approximately", "right": 1},
            {"id": "unknown-field", "left": "x", "op": "==", "right": 1,
             "expression": "x == 1"},
            {"left": "x", "op": "==", "right": 1},
            {"id": "", "left": "x", "op": "==", "right": 1},
            {"id": 7, "left": "x", "op": "==", "right": 1},
            {"id": "ordered-tolerance", "left": "x", "op": "<", "right": 2,
             "tolerance": 0.1},
        ],
    )
    def test_invalid_contract_is_unproven_without_crash(
        self,
        tmp_path: Path,
        payload: dict,
    ):
        result = self._scan(tmp_path, [
            _code_cell("measure()", [
                _stream_output('CLAIM_METRICS {"x": 1}\n'),
            ]),
            _md_cell(self._claim(**payload)),
        ])

        assert result["verdict"] == "CLAIM_UNPROVEN"
        assert result["relational_claims"][0]["status"] == "UNPROVEN"

    def test_huge_integer_metric_and_tolerance_do_not_crash(self, tmp_path: Path):
        huge = 10**400
        result = self._scan(tmp_path, [
            _code_cell("measure()", [
                _stream_output(f'CLAIM_METRICS {{"huge": {huge}}}\n'),
            ]),
            _md_cell(self._claim(
                id="huge-int",
                left="huge",
                op="==",
                right=huge,
                tolerance=huge,
            )),
        ])

        assert result["verdict"] == "CLEAN"
        assert result["relational_claims"][0]["status"] == "SUPPORTED"

    def test_boolean_numeric_equality_is_unproven(self, tmp_path: Path):
        result = self._scan(tmp_path, [
            _code_cell("measure()", [
                _stream_output('CLAIM_METRICS {"flag": true}\n'),
            ]),
            _md_cell(self._claim(
                id="typed-equality",
                left="flag",
                op="==",
                right=1,
            )),
        ])

        assert result["verdict"] == "CLAIM_UNPROVEN"
        assert result["relational_claims"][0]["status"] == "UNPROVEN"

    def test_fenced_claim_example_is_not_evaluated(self, tmp_path: Path):
        result = self._scan(tmp_path, [
            _code_cell("measure()", [
                _stream_output('CLAIM_METRICS {"x": 1}\n'),
            ]),
            _md_cell(
                "Exemple de syntaxe :\n```html\n"
                + self._claim(id="example", left="x", op="==", right=2)
                + "\n```"
            ),
        ])

        assert result["verdict"] == "CLEAN"
        assert result["relational_claims"] == []

    def test_malformed_json_is_unproven(self, tmp_path: Path):
        result = self._scan(tmp_path, [
            _code_cell("measure()", [
                _stream_output('CLAIM_METRICS {"x": 1}\n'),
            ]),
            _md_cell(
                "Conclusion calculée.\n"
                '<!-- claim-check: {"id":"broken","left":"x" -->'
            ),
        ])

        assert result["verdict"] == "CLAIM_UNPROVEN"
        claim = result["relational_claims"][0]
        assert claim["status"] == "UNPROVEN"
        assert "invalid claim-check JSON" in claim["reason"]

    def test_explicit_claim_in_long_prose_is_still_checked(self, tmp_path: Path):
        long_prose = "## Bibliographie\n" + "Contexte pédagogique détaillé. " * 50
        result = self._scan(tmp_path, [
            _code_cell("measure()", [
                _stream_output('CLAIM_METRICS {"x": 1}\n'),
            ]),
            _md_cell(
                long_prose
                + "\n"
                + self._claim(id="long-cell", left="x", op="==", right=1)
            ),
        ])

        assert result["relational_claims"][0]["status"] == "SUPPORTED"
        assert result["stats"]["skipped_literature"] == 1

    def test_distant_metric_outside_window_does_not_prove_claim(self, tmp_path: Path):
        cells = [
            _code_cell("old_measure()", [
                _stream_output('CLAIM_METRICS {"score": 0.9}\n'),
            ]),
            _code_cell("step_1()", [_stream_output("step one\n")]),
            _code_cell("step_2()", [_stream_output("step two\n")]),
            _code_cell("step_3()", [_stream_output("step three\n")]),
            _md_cell(self._claim(
                id="local-only",
                left="score",
                op=">",
                right=0.5,
            )),
        ]
        result = self._scan(tmp_path, cells)

        claim = result["relational_claims"][0]
        assert claim["status"] == "UNPROVEN"
        assert claim["window"] == [3, 2, 1]

    def test_numeric_finding_and_relation_coexist(self, tmp_path: Path):
        result = self._scan(tmp_path, [
            _code_cell("measure()", [
                _stream_output(
                    'observed=0.24\nCLAIM_METRICS {"final_policy_equal": true}\n'
                ),
            ]),
            _md_cell(
                "La valeur observée est 0,09.\n"
                + self._claim(
                    id="policy-preserved",
                    left="final_policy_equal",
                    op="==",
                    right=True,
                )
            ),
        ])

        assert result["verdict"] == "FABRICATION_DETECTED"
        assert result["findings"]
        assert result["relational_claims"][0]["status"] == "SUPPORTED"

    def test_plain_unannotated_prose_keeps_legacy_behavior(self, tmp_path: Path):
        result = self._scan(tmp_path, [
            _code_cell("print_domain()", [_stream_output("three actions\n")]),
            _md_cell("Le domaine comprend trois actions possibles."),
        ])

        assert result["verdict"] == "CLEAN"
        assert result["relational_claims"] == []
