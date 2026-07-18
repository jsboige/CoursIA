"""Tests for scripts/notebook_tools/detect_ascii_workaround.py — Prong-A ASCII detector.

Why this test file exists
-------------------------
`detect_ascii_workaround.py` (registre #3801, SOTA axe-2 Prong-A) is the canonical
DETECTOR for ASCII-workaround visualisations: code cells that draw a quantitative
bar/trajectory in ASCII (a fill-char multiplied by a data-derived length) instead
of invoking a real charting tool (matplotlib/Plotly). The detection half is
formally tested here; the conversion (ASCII -> real chart) remains manual by
design (per-notebook substance: re-exec, fidelity, C548-L2 for .NET).

Six clusters, mirroring the detector's documented contract (docstring L83-L98):

  1. TestInlineBar       -- INLINE_BAR_RE  ('#' * score)
  2. TestBarHelperReturn -- BAR_HELPER_RE  (return '#' * n)
  3. TestBarHelperCall   -- _bar_helper_call (PyMC-17 cell6 canonical form)
  4. TestCSharpBar       -- CSHARP_BAR_RE  (new string('#', barLen))
  5. TestFalsePositiveFilters -- charting-lib / discrete-state-grid / separators
  6. TestScanNotebook + TestMainExitCodes -- end-to-end + exit contract

Test data design follows the detector's "Known blind spots" + "Filtres
faux-positifs" sections (docstring L41-L98): every positive case uses a fill char
from DATA_BAR_CHAR (#, *, |, @, blocks), and every negative case exercises one
documented exclusion (charting lib, grid/board, separator chars, math helpers,
constant-width borders, C# literal-count separators).

The baseline validated c.543 on 935 pedagogical notebooks is **1 genuine defect**
(PyMC-17 cell6, #6834). These tests pin the contract so a regression that floods
the detector with false positives (or, conversely, misses a known form) is caught
before it pollutes the Prong-A sweep.
"""
import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from detect_ascii_workaround import (  # noqa: E402
    BAR_HELPER_RE,
    CSHARP_BAR_RE,
    DATA_BAR_CHAR,
    INLINE_BAR_RE,
    _bar_helper_call,
    _is_discrete_state_viz,
    _uses_charting_lib,
    detect_cell,
    main,
    scan_notebook,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _code(source: str) -> dict:
    """A code cell with given source (str)."""
    return {"cell_type": "code", "source": source}


def _code_list(lines: list[str]) -> dict:
    """A code cell with source as nbformat list-of-strings (each carries trailing \\n)."""
    return {"cell_type": "code",
            "source": [ln if ln.endswith("\n") else ln + "\n" for ln in lines]}


def _write_nb(path: Path, cells: list[dict], kernel: str = "python3") -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    nb = {
        "cells": cells,
        "metadata": {"kernelspec": {"name": kernel, "display_name": kernel}},
        "nbformat": 4, "nbformat_minor": 5,
    }
    path.write_text(json.dumps(nb, ensure_ascii=False), encoding="utf-8")
    return path


# ---------------------------------------------------------------------------
# INLINE_BAR_RE -- '#' * score  (literal fill-char * data variable)
# ---------------------------------------------------------------------------

class TestInlineBar:
    def test_hash_times_variable_detected(self):
        # Canonical inline form: '#' * score (hash fill * data-derived variable).
        finding = detect_cell('print("#" * score)')
        assert finding is not None
        assert "inline_bar_multiplication" in finding["signatures"]

    def test_pipe_times_variable_detected(self):
        # '|' is a fill char (DATA_BAR_CHAR); '|' * n is a bar.
        finding = detect_cell('print("|" * n)')
        assert finding is not None
        assert "inline_bar_multiplication" in finding["signatures"]

    def test_star_times_variable_detected(self):
        # '*' fill char.
        finding = detect_cell('print("*" * count)')
        assert finding is not None
        assert "inline_bar_multiplication" in finding["signatures"]

    def test_digit_multiplier_excluded(self):
        # '#' * 50 is a CONSTANT-width bar, not data-derived -> NOT a defect.
        # INLINE_BAR_RE has (?!\d) to exclude literal int multipliers.
        assert detect_cell('print("#" * 50)') is None

    def test_builtin_multiplier_excluded(self):
        # '#' * len(x) and '#' * int(x) are formatting/cast, not data bars.
        # INLINE_BAR_RE negative-lookahead excludes builtins len/int/round/str...
        assert detect_cell('print("#" * len(header))') is None
        assert detect_cell('print("#" * int(x))') is None

    def test_separator_char_excluded(self):
        # '-' / '=' / '.' / '_' are SEPARATOR chars, NOT in DATA_BAR_CHAR.
        # print("-" * 50) is a table border, not a data bar.
        assert detect_cell('print("-" * 50)') is None
        assert detect_cell('print("=" * width)') is None
        assert detect_cell('print("." * n)') is None

    def test_inline_bar_context_captured(self):
        # The finding["context"] is the first line carrying a bar signature.
        src = "import numpy as np\nprint('#' * score)\nprint('done')"
        finding = detect_cell(src)
        assert finding is not None
        assert "print('#' * score)" in finding["context"]

    def test_scalar_length_flag_reported(self):
        # int(round(v * W)) is a bar-length-from-scalar FLAG (reported, not gated).
        src = "W = 40\nn = int(round((v - lo) / (hi - lo) * W))\nprint('#' * n)"
        finding = detect_cell(src)
        assert finding is not None
        assert finding["scalar_length"] is True


# ---------------------------------------------------------------------------
# BAR_HELPER_RE -- return '#' * n  (literal fill-char * word in a return)
# ---------------------------------------------------------------------------

class TestBarHelperReturn:
    def test_return_hash_times_n_detected(self):
        src = "def bar(n):\n    return '#' * n"
        finding = detect_cell(src)
        assert finding is not None
        assert "bar_helper_literal_return" in finding["signatures"]

    def test_math_helper_excluded(self):
        # return a * b multiplies VARIABLES, not a drawing-char literal -> not a bar.
        assert detect_cell("def ev(belief, r):\n    return belief * r") is None

    def test_regression_slope_excluded(self):
        # return slope*time+intercept -- math, no char literal.
        assert detect_cell("def line(t):\n    return slope * t + intercept") is None

    def test_blackscholes_helper_excluded(self):
        # return K * np.exp(...) -- math, no char literal.
        assert detect_cell("def payoff(K, S):\n    return K * np.exp(-r * T)") is None


# ---------------------------------------------------------------------------
# _bar_helper_call -- canonical PyMC-17 cell6 form (#6834)
#   def bar(v, c): n = ...; return c * n   called as bar(x, '|')
# ---------------------------------------------------------------------------

class TestBarHelperCall:
    def test_pymc17_canonical_detected(self):
        # The exact canonical form from the detector docstring (L26-L31).
        src = (
            "def bar(v, c):\n"
            "    n = int(round((v - lo) / (hi - lo) * W))\n"
            "    return c * n\n"
            'print(f"VRAI {bar(trueState[t], "|")}")'
        )
        finding = detect_cell(src)
        assert finding is not None
        # _bar_helper_call ties the call-site '|' literal to param c.
        sigs = finding["signatures"]
        assert any(s.startswith("bar_helper_call(param=") for s in sigs), sigs

    def test_bar_helper_call_returns_param_name(self):
        src = (
            "def bar(v, c):\n"
            "    return c * n\n"
            'print(bar(x, "|"))'
        )
        # The helper itself returns the matched param name.
        assert _bar_helper_call(src) == "c"

    def test_dict_default_not_a_bar_call(self):
        # grid.get(nxt, "#") -- get() does not repeat a param; '#' here is a dict
        # default, not a bar fill. Must NOT match.
        assert detect_cell('print(grid.get(nxt, "#"))') is None

    def test_long_param_name_not_matched(self):
        # The matcher requires a 1-4 char param (c/ch/sym/char). A helper whose
        # repeated param is longer (e.g. `belief`) is treated as math, not a bar.
        src = (
            "def ev(belief, r):\n"
            "    return belief * r\n"
            'print(ev(x, "#"))'
        )
        # No short param is repeated -> _bar_helper_call returns None, and the
        # call-site '#' is a bare arg (no inline multiplication) -> overall None.
        assert _bar_helper_call(src) is None
        assert detect_cell(src) is None


# ---------------------------------------------------------------------------
# CSHARP_BAR_RE -- new string('#', barLen) / Enumerable.Repeat('#', n)
# (.NET Interactive equivalent of Python '#' * n)
# ---------------------------------------------------------------------------

class TestCSharpBar:
    def test_new_string_hash_variable_detected(self):
        # new string('#', barLen) -- fill char, data-derived length -> defect.
        src = 'Console.WriteLine(new string(\'#\', barLen));'
        finding = detect_cell(src)
        assert finding is not None
        assert "csharp_new_string_bar" in finding["signatures"]

    def test_enumerable_repeat_detected(self):
        src = "var bar = string.Concat(Enumerable.Repeat('#', n));"
        finding = detect_cell(src)
        assert finding is not None
        assert "csharp_new_string_bar" in finding["signatures"]

    def test_new_string_literal_count_excluded(self):
        # new string('=', 60) -- separator char AND literal int count -> border.
        # '=' is NOT in DATA_BAR_CHAR; 60 is a literal int -> double exclusion.
        assert detect_cell('var sep = new string(\'=\', 60);') is None

    def test_new_string_separator_char_excluded(self):
        # new string('-', 40) -- '-' separator, even with variable count.
        assert detect_cell('var border = new string(\'-\', width);') is None

    def test_csharp_bar_regex_direct(self):
        # Direct regex contract: data fill char + data expression -> match.
        assert CSHARP_BAR_RE.search("new string('#', barLen)") is not None
        # Literal int count -> excluded by the (?!\s*\d+\s*[),]) lookahead.
        assert CSHARP_BAR_RE.search("new string('#', 40)") is None
        # Separator char -> excluded (not in DATA_BAR_CHAR).
        assert CSHARP_BAR_RE.search("new string('=', 60)") is None


# ---------------------------------------------------------------------------
# False-positive filters (the documented exclusions, docstring L41-L64)
# ---------------------------------------------------------------------------

class TestFalsePositiveFilters:
    def test_charting_lib_present_not_flagged(self):
        # matplotlib present -> not a workaround, even if a companion ASCII
        # quick-check exists (ICT-16 cell10+11 pattern, #5736).
        src = (
            "import matplotlib.pyplot as plt\n"
            "print('#' * score)  # quick ASCII check\n"
            "plt.bar(range(len(scores)), scores)\n"
            "plt.show()"
        )
        assert detect_cell(src) is None

    def test_plotly_present_not_flagged(self):
        src = "import plotly.graph_objects as go\nprint('#' * score)\nfig = go.Figure()"
        assert detect_cell(src) is None

    def test_uses_charting_lib_helper(self):
        assert _uses_charting_lib("import matplotlib.pyplot as plt") is True
        assert _uses_charting_lib("plt.show()") is True
        assert _uses_charting_lib("plt.bar(x, y)") is True
        assert _uses_charting_lib("import plotly.express as px") is True
        assert _uses_charting_lib("print('no chart here')") is False

    def test_discrete_state_grid_not_flagged(self):
        # A Sudoku/Demineur board: nested loop over a state matrix, char chosen
        # PER STATE (not bar-length-from-scalar). This is LEGITIMATE ASCII.
        src = (
            "# Affiche la grille Sudoku\n"
            "for row in grid:\n"
            "    for cell in row:\n"
            "        print(state_char(cell), end='')\n"
            "    print()"
        )
        assert detect_cell(src) is None

    def test_is_discrete_state_viz_helper(self):
        # grid keyword + nested loop + no bar-scalar -> True (legitimate).
        legit = (
            "for row in grid:\n"
            "    for cell in row:\n"
            "        print(cell)"
        )
        assert _is_discrete_state_viz(legit) is True

    def test_discrete_state_with_bar_scalar_is_not_pure_grid(self):
        # grid keyword + nested loop BUT bar-scalar present -> leans data-viz.
        mixed = (
            "for row in grid:\n"
            "    for cell in row:\n"
            "        n = int(round(v * W))\n"
            "        print(cell)"
        )
        # _is_discrete_state_viz returns False when bar-scalar is present.
        assert _is_discrete_state_viz(mixed) is False

    def test_table_separator_loop_excluded(self):
        # SL-6 row border loop: "  ".join("-" * width for width in w).
        # '-' is a separator char, and the loop builds table borders, not data bars.
        src = 'print("  ".join("-" * width for width in widths))'
        assert detect_cell(src) is None

    def test_empty_source_returns_none(self):
        assert detect_cell("") is None
        assert detect_cell("   \n  \t  ") is None

    def test_markdown_table_not_flagged(self):
        # Pure prose/markdown-style content (no code execution semantics) that
        # happens to contain a pipe char is not a data bar.
        # (detect_cell only inspects code cells, but guard against stray matches.)
        assert detect_cell("| col1 | col2 |") is None


# ---------------------------------------------------------------------------
# scan_notebook -- end-to-end detection contract (returns DICT)
# ---------------------------------------------------------------------------

class TestScanNotebook:
    def test_clean_notebook_no_hits(self, tmp_path):
        cells = [
            _code("import matplotlib.pyplot as plt\nplt.plot(x, y)\nplt.show()"),
            _code("result = sum(values) / len(values)\nprint(result)"),
        ]
        p = _write_nb(tmp_path / "clean.ipynb", cells)
        result = scan_notebook(p)
        assert isinstance(result, dict)
        assert result["error"] is None
        assert result["hits"] == []
        assert result["kernel"] == "python3"

    def test_inline_bar_hit_with_cell_index(self, tmp_path):
        cells = [
            _code("scores = [3, 7, 5]"),
            _code('for s in scores:\n    print("#" * s)'),
        ]
        p = _write_nb(tmp_path / "bars.ipynb", cells)
        result = scan_notebook(p)
        assert result["error"] is None
        assert len(result["hits"]) == 1
        h = result["hits"][0]
        assert h["cell_index"] == 1  # the printing cell, not the data cell
        assert "inline_bar_multiplication" in h["signatures"]

    def test_helper_call_hit_canonical(self, tmp_path):
        # PyMC-17 cell6 canonical form.
        src = (
            "def bar(v, c):\n"
            "    n = int(round((v - lo) / (hi - lo) * W))\n"
            "    return c * n\n"
            'print(f"VRAI {bar(trueState[t], "|")}")'
        )
        p = _write_nb(tmp_path / "kalman.ipynb", [_code(src)])
        result = scan_notebook(p)
        assert len(result["hits"]) == 1
        assert any(s.startswith("bar_helper_call") for s in result["hits"][0]["signatures"])

    def test_charting_lib_cell_skipped(self, tmp_path):
        # A cell that uses matplotlib is NOT reported even with an ASCII companion.
        src = (
            "import matplotlib.pyplot as plt\n"
            'print("#" * score)\n'
            "plt.bar(range(n), scores); plt.show()"
        )
        p = _write_nb(tmp_path / "ict16.ipynb", [_code(src)])
        result = scan_notebook(p)
        assert result["hits"] == []

    def test_markdown_cells_ignored(self, tmp_path):
        # Only code cells are scanned; markdown cells (even with '#') are skipped.
        cells = [
            {"cell_type": "markdown", "source": "# Title with hash\n| pipe | table |"},
            _code('print("#" * score)'),
        ]
        p = _write_nb(tmp_path / "mixed.ipynb", cells)
        result = scan_notebook(p)
        assert len(result["hits"]) == 1
        assert result["hits"][0]["cell_index"] == 1

    def test_nbformat_list_source_scanned(self, tmp_path):
        # nbformat source-as-list must be joined before detection.
        cells = [_code_list(['scores = [1, 2, 3]', 'for s in scores:', '    print("#" * s)'])]
        p = _write_nb(tmp_path / "nbformat.ipynb", cells)
        result = scan_notebook(p)
        assert len(result["hits"]) == 1
        assert "inline_bar_multiplication" in result["hits"][0]["signatures"]

    def test_unreadable_notebook_returns_error_dict(self, tmp_path):
        # scan_notebook returns {"error": str, "hits": []} on parse failure.
        bad = tmp_path / "bad.ipynb"
        bad.write_text("{ not json", encoding="utf-8")
        result = scan_notebook(bad)
        assert isinstance(result, dict)
        assert result["error"] is not None
        assert isinstance(result["error"], str)
        assert result["hits"] == []

    def test_path_field_recorded(self, tmp_path):
        p = _write_nb(tmp_path / "named.ipynb", [_code("x = 1")])
        result = scan_notebook(p)
        assert result["path"] == str(p)


# ---------------------------------------------------------------------------
# main() exit codes (0 clean / 1 hit with --check / 2 error)
# ---------------------------------------------------------------------------

class TestMainExitCodes:
    def test_check_clean_exit_0(self, tmp_path):
        p = _write_nb(tmp_path / "clean.ipynb",
                      [_code("import matplotlib.pyplot as plt\nplt.plot(x,y)\nplt.show()")])
        assert main([str(p), "--check"]) == 0

    def test_check_hit_exit_1(self, tmp_path):
        p = _write_nb(tmp_path / "bars.ipynb",
                      [_code('for s in scores:\n    print("#" * s)')])
        assert main([str(p), "--check"]) == 1

    def test_missing_notebook_exit_2(self, tmp_path):
        assert main([str(tmp_path / "nope.ipynb")]) == 2

    def test_no_check_exits_0_even_with_hits(self, tmp_path):
        # Without --check, hits do NOT trigger non-zero exit (informational mode).
        p = _write_nb(tmp_path / "bars.ipynb",
                      [_code('for s in scores:\n    print("#" * s)')])
        assert main([str(p)]) == 0

    def test_json_mode_emits_valid_json(self, tmp_path, capsys):
        p = _write_nb(tmp_path / "bars.ipynb",
                      [_code('for s in scores:\n    print("#" * s)')])
        rc = main([str(p), "--json"])
        out = capsys.readouterr().out
        payload = json.loads(out)
        assert payload["total_hits"] == 1
        assert payload["notebooks_scanned"] == 1
        assert rc == 0  # no --check => exit 0

    def test_family_not_found_exit_2(self, tmp_path):
        # --family pointing to a non-existent family -> exit 2.
        assert main(["--family", "NoSuchFamily", "--root", str(tmp_path)]) == 2


# ---------------------------------------------------------------------------
# DATA_BAR_CHAR alphabet self-consistency
# ---------------------------------------------------------------------------

def _is_fill_char(c: str) -> bool:
    """True if `c` is a member of the DATA_BAR_CHAR regex class (a single char)."""
    import re
    return bool(re.fullmatch(DATA_BAR_CHAR, c))


class TestDataBarCharAlphabet:
    def test_fill_chars_present(self):
        # The fill chars named in the docstring must be in the alphabet.
        for c in ["#", "*", "|", "@"]:
            assert _is_fill_char(c), f"fill char {c!r} must be in DATA_BAR_CHAR"

    def test_separator_chars_absent(self):
        # Separator chars (- = + . _) are deliberately EXCLUDED from DATA_BAR_CHAR
        # (they are table borders / axis lines, not data-bar fills).
        for sep in ["-", "=", "+", "."]:
            assert not _is_fill_char(sep), (
                f"separator {sep!r} must NOT be in DATA_BAR_CHAR"
            )
