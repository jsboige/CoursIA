"""Tests for scripts/notebook_tools/detect_solution_leaks.py — solution leak scanner.

Tests focus on pure functions: is_stub_code, scan_notebook, discover_notebooks.
Uses synthetic notebook dicts and tmp_path for filesystem isolation.
"""

import json
import re
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from detect_solution_leaks import (
    EXERCISE_HEADER_RE,
    SOUMIS_PAR_RE,
    SOLUTION_MARKER_RE,
    STUB_PATTERNS,
    closest_preceding_header_is_example,
    discover_notebooks,
    is_stub_code,
    scan_notebook,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _nb(cells: list[dict]) -> dict:
    return {"cells": cells, "metadata": {}}


def _code(source: str) -> dict:
    return {"cell_type": "code", "source": [source]}


def _md(source: str) -> dict:
    return {"cell_type": "markdown", "source": [source]}


def _write_nb(path: Path, cells: list[dict]) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    nb = {"cells": cells, "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
    path.write_text(json.dumps(nb), encoding="utf-8")
    return path


# ---------------------------------------------------------------------------
# is_stub_code
# ---------------------------------------------------------------------------

class TestIsStubCode:
    def test_pass_is_stub(self):
        assert is_stub_code("pass") is True

    def test_indented_pass_is_stub(self):
        # Regression: the `^\s*pass\s*$` stub pattern requires re.MULTILINE to
        # match an INDENTED `pass` inside a function body (the real-world stub
        # case). Without MULTILINE it only matched a top-level `pass` at the
        # start of the cell, so function-stub exercises (def f(): ... pass)
        # were systematically false-positive as HIGH leaks across the Python
        # notebooks (e.g. CSP-2 path_consistency).
        code = (
            'def path_consistency(csp, domains):\n'
            '    """Apply path consistency."""\n'
            '    # A COMPLETER\n'
            '    # Pour chaque paire (Xi, Xj) ...\n'
            '    pass\n'
            'print("Exercice 2 : implementer path_consistency")\n'
        )
        assert is_stub_code(code) is True

    def test_print_exercice_a_completer(self):
        assert is_stub_code('print("Exercice a completer")') is True

    def test_return_none(self):
        assert is_stub_code("return None") is True

    def test_todo_comment(self):
        assert is_stub_code("# TODO: implement") is True

    def test_console_writeline_french(self):
        assert is_stub_code('Console.WriteLine("Exercice a completer")') is True

    def test_real_code_not_stub(self):
        code = "def solve(x):\n    return x ** 2 + 3 * x + 1\nresult = solve(42)"
        assert is_stub_code(code) is False

    def test_empty_is_stub(self):
        assert is_stub_code("") is True

    def test_whitespace_only_is_stub(self):
        assert is_stub_code("   \n  \n  ") is True

    def test_single_import_plus_pass(self):
        assert is_stub_code("import numpy as np\npass") is True

    def test_two_code_lines_not_stub(self):
        code = "x = compute(data)\ny = transform(x)"
        assert is_stub_code(code) is False

    def test_import_only_is_stub(self):
        assert is_stub_code("import pandas as pd") is True

    def test_comment_only_is_stub(self):
        assert is_stub_code("# just a comment\n# another") is True

    def test_csharp_pass_is_stub(self):
        # C# comments start with //
        assert is_stub_code("// TODO\nreturn null;") is True

    def test_csharp_multiline_todo_stub(self):
        # Regression: a richly-scaffolded C# exercise stub (TODO + Etapes +
        # default return + display call) has many code lines, so the
        # `len(code_lines) <= 1` shortcut does NOT apply. Before recognizing
        # `// TODO` as a stub marker, these were systematically false-positive
        # as HIGH leaks across the .NET Interactive notebooks (GameTheory etc.).
        code = (
            "// Exercice 1 (a completer) : voisinage de swap\n"
            "// TODO etudiant : implémenter ExploreSwapNeighbors\n"
            "// Etape 1 : iterer sur swaps. Etape 2 : calculer les voisins.\n"
            "public List<(OrdinalGame, string, int)> ExploreSwapNeighbors(OrdinalGame g)\n"
            "{\n"
            "    // TODO etudiant\n"
            "    return new List<(OrdinalGame, string, int)>();\n"
            "}\n"
            'display("Exercice 1 : stub a completer.");'
        )
        assert is_stub_code(code) is True


# ---------------------------------------------------------------------------
# EXERCISE_HEADER_RE
# ---------------------------------------------------------------------------

class TestExerciseHeaderRe:
    def test_french_exercice(self):
        m = EXERCISE_HEADER_RE.search("## Exercice 1 : Tri")
        assert m is not None
        assert m.group(1) == "1"
        assert "Tri" in m.group(2)

    def test_exercice_no_number(self):
        m = EXERCISE_HEADER_RE.search("### Exercice")
        assert m is not None

    def test_english_exercise(self):
        m = EXERCISE_HEADER_RE.search("# Exercise 3: Sorting")
        assert m is not None
        assert m.group(1) == "3"

    def test_with_dot_separator(self):
        m = EXERCISE_HEADER_RE.search("## 2. Exercice")
        assert m is not None

    def test_no_match_regular_heading(self):
        assert EXERCISE_HEADER_RE.search("## Introduction") is None

    def test_no_match_example(self):
        assert EXERCISE_HEADER_RE.search("## Exemple guide") is None

    def test_h3_exercice(self):
        m = EXERCISE_HEADER_RE.search("### Exercice 5")
        assert m is not None
        assert m.group(1) == "5"


# ---------------------------------------------------------------------------
# SOUMIS_PAR_RE
# ---------------------------------------------------------------------------

class TestSoumisParRe:
    def test_french(self):
        assert SOUMIS_PAR_RE.search("Solution soumis par Jean") is not None

    def test_english(self):
        assert SOUMIS_PAR_RE.search("submitted by Alice") is not None

    def test_no_match(self):
        assert SOUMIS_PAR_RE.search("Random text") is None


# ---------------------------------------------------------------------------
# SOLUTION_MARKER_RE
# ---------------------------------------------------------------------------

class TestSolutionMarkerRe:
    def test_solution(self):
        assert SOLUTION_MARKER_RE.search("# Solution") is not None

    def test_reponse(self):
        assert SOLUTION_MARKER_RE.search("## Reponse") is not None

    def test_resultat(self):
        assert SOLUTION_MARKER_RE.search("Resultat:") is not None

    def test_no_match(self):
        assert SOLUTION_MARKER_RE.search("Code here") is None


# ---------------------------------------------------------------------------
# scan_notebook
# ---------------------------------------------------------------------------

class TestScanNotebook:
    def test_clean_stub_exercise(self, tmp_path):
        nb_path = _write_nb(tmp_path / "clean.ipynb", [
            _md("## Exercice 1 : Tri"),
            _code("pass"),
        ])
        findings = scan_notebook(str(nb_path))
        assert len(findings) == 0

    def test_solution_leak_high(self, tmp_path):
        nb_path = _write_nb(tmp_path / "leak.ipynb", [
            _md("## Exercice 1 : Tri"),
            _code("# Solution\ndef quicksort(arr):\n    if len(arr) <= 1:\n        return arr\n    pivot = arr[0]\n    left = [x for x in arr[1:] if x <= pivot]\n    right = [x for x in arr[1:] if x > pivot]\n    return quicksort(left) + [pivot] + quicksort(right)\nresult = quicksort(data)\nprint(result)"),
        ])
        findings = scan_notebook(str(nb_path))
        assert any(f["severity"] == "HIGH" for f in findings)

    def test_soumis_par_leak(self, tmp_path):
        nb_path = _write_nb(tmp_path / "soumis.ipynb", [
            _md("## Exercice 2 soumis par Alice"),
            _code("x = complex_calc(data)\ny = transform(x)\nresult = finalize(y)"),
        ])
        findings = scan_notebook(str(nb_path))
        assert any(f["severity"] == "HIGH" for f in findings)
        assert any("soumis par" in f["message"] for f in findings)

    def test_soumis_par_with_stub_ok(self, tmp_path):
        nb_path = _write_nb(tmp_path / "ok.ipynb", [
            _md("## Exercice 2 soumis par Alice"),
            _code("pass"),
        ])
        findings = scan_notebook(str(nb_path))
        assert len(findings) == 0

    def test_duplicate_exercise_number(self, tmp_path):
        nb_path = _write_nb(tmp_path / "dup.ipynb", [
            _md("## Exercice 1 : First"),
            _code("pass"),
            _md("## Exercice 1 : Second"),
            _code("pass"),
        ])
        findings = scan_notebook(str(nb_path))
        assert any(f["severity"] == "MEDIUM" for f in findings)

    def test_no_exercises_clean(self, tmp_path):
        nb_path = _write_nb(tmp_path / "none.ipynb", [
            _md("# Title"),
            _code("x = 1"),
            _md("## Conclusion"),
        ])
        findings = scan_notebook(str(nb_path))
        assert len(findings) == 0

    def test_invalid_json(self, tmp_path):
        bad = tmp_path / "bad.ipynb"
        bad.write_text("{invalid json!!!", encoding="utf-8")
        findings = scan_notebook(str(bad))
        assert any(f["severity"] == "ERROR" for f in findings)

    def test_code_cell_gap(self, tmp_path):
        """Next code cell within 3 cells after exercise header with >8 lines."""
        nb_path = _write_nb(tmp_path / "gap.ipynb", [
            _md("## Exercice 1"),
            _md("Some instructions"),
            _md("More instructions"),
            _code("def solve():\n    data = load()\n    x = preprocess(data)\n    y = model(x)\n    z = postprocess(y)\n    result = validate(z)\n    return result\noutput = solve()\nprint(output)"),
        ])
        findings = scan_notebook(str(nb_path))
        assert any(f["severity"] == "HIGH" for f in findings)

    def test_code_cell_too_far(self, tmp_path):
        """Next code cell beyond 3 cells is not checked."""
        nb_path = _write_nb(tmp_path / "far.ipynb", [
            _md("## Exercice 1"),
            _md("A"),
            _md("B"),
            _md("C"),
            _code("def solve():\n    return complex_thing(data)\nresult = solve()"),
        ])
        findings = scan_notebook(str(nb_path))
        assert len(findings) == 0

    def test_exercise_no_number(self, tmp_path):
        nb_path = _write_nb(tmp_path / "nonum.ipynb", [
            _md("## Exercice"),
            _code("x = full_solution(data)\ny = process(x)\nresult = y"),
        ])
        findings = scan_notebook(str(nb_path))
        # No soumis par, but has solution marker or >8 lines
        assert any(f["severity"] == "HIGH" for f in findings)


# ---------------------------------------------------------------------------
# discover_notebooks
# ---------------------------------------------------------------------------

class TestDiscoverNotebooks:
    def test_finds_notebooks(self, tmp_path):
        (tmp_path / "a.ipynb").write_text("{}", encoding="utf-8")
        (tmp_path / "b.ipynb").write_text("{}", encoding="utf-8")
        result = discover_notebooks(str(tmp_path))
        assert len(result) == 2

    def test_excludes_checkpoints(self, tmp_path):
        (tmp_path / ".ipynb_checkpoints").mkdir()
        (tmp_path / ".ipynb_checkpoints" / "hidden.ipynb").write_text("{}", encoding="utf-8")
        (tmp_path / "visible.ipynb").write_text("{}", encoding="utf-8")
        result = discover_notebooks(str(tmp_path))
        assert len(result) == 1

    def test_excludes_output_files(self, tmp_path):
        (tmp_path / "nb.ipynb").write_text("{}", encoding="utf-8")
        (tmp_path / "nb_output.ipynb").write_text("{}", encoding="utf-8")
        result = discover_notebooks(str(tmp_path))
        assert len(result) == 1

    def test_excludes_output_dir(self, tmp_path):
        (tmp_path / "_output").mkdir()
        (tmp_path / "_output" / "exec.ipynb").write_text("{}", encoding="utf-8")
        (tmp_path / "real.ipynb").write_text("{}", encoding="utf-8")
        result = discover_notebooks(str(tmp_path))
        assert len(result) == 1

    def test_empty_dir(self, tmp_path):
        result = discover_notebooks(str(tmp_path))
        assert result == []

    def test_nested_dirs(self, tmp_path):
        sub = tmp_path / "sub" / "deep"
        sub.mkdir(parents=True)
        (sub / "nb.ipynb").write_text("{}", encoding="utf-8")
        result = discover_notebooks(str(tmp_path))
        assert len(result) == 1

    def test_sorted_output(self, tmp_path):
        (tmp_path / "z.ipynb").write_text("{}", encoding="utf-8")
        (tmp_path / "a.ipynb").write_text("{}", encoding="utf-8")
        result = discover_notebooks(str(tmp_path))
        assert result[0].endswith("a.ipynb")
        assert result[1].endswith("z.ipynb")

    def test_non_ipynb_ignored(self, tmp_path):
        (tmp_path / "readme.md").write_text("hello", encoding="utf-8")
        (tmp_path / "script.py").write_text("pass", encoding="utf-8")
        result = discover_notebooks(str(tmp_path))
        assert result == []


# ---------------------------------------------------------------------------
# STUB_PATTERNS constants
# ---------------------------------------------------------------------------

class TestStubPatterns:
    def test_patterns_exist(self):
        assert len(STUB_PATTERNS) > 0

    def test_patterns_are_valid_regex(self):
        for pattern in STUB_PATTERNS:
            assert re.compile(pattern) is not None


# ---------------------------------------------------------------------------
# Worked-example attribution (closest-preceding-header-wins, precision fix)
# ---------------------------------------------------------------------------

# A non-stub code body (>8 lines, no stub markers) so the detector would flag it
# as a HIGH leak if it were under an Exercice header.
_SOLUTION_BODY = "\n".join(
    [
        "def solve(x):",
        "    # Solution complete",
        "    a = x + 1",
        "    b = a * 2",
        "    c = b - 3",
        "    d = c ** 2",
        "    e = d % 7",
        "    f = e // 2",
        "    g = f + x",
        "    return g",
    ]
)


class TestClosestPrecedingHeaderIsExample:
    def _cells(self, *specs):
        cells = []
        for ct, src in specs:
            cells.append({"cell_type": ct, "source": [src]})
        return cells

    def test_example_header_is_true(self):
        cells = self._cells(("markdown", "### Exemple guide : demo"), ("code", _SOLUTION_BODY))
        assert closest_preceding_header_is_example(cells, 1) is True

    def test_exercise_header_is_false(self):
        cells = self._cells(("markdown", "### Exercice 4 : a faire"), ("code", _SOLUTION_BODY))
        assert closest_preceding_header_is_example(cells, 1) is False

    def test_no_header_is_false(self):
        cells = self._cells(("markdown", "Just some prose, no header."), ("code", _SOLUTION_BODY))
        assert closest_preceding_header_is_example(cells, 1) is False

    def test_intervening_example_header_wins_over_section(self):
        # "## 10. Exercices" section header, then "### Exemple guide" sub-header,
        # then code: the code belongs to the worked example, NOT the section.
        cells = self._cells(
            ("markdown", "## 10. Exercices\n\nQuelques exercices."),
            ("markdown", "### Exemple guide : cas resolu"),
            ("code", _SOLUTION_BODY),
        )
        assert closest_preceding_header_is_example(cells, 2) is True

    def test_multi_header_single_cell_last_line_wins(self):
        # One markdown cell holding BOTH a section header and a closer example
        # sub-header (the Lean-11 case). The LAST header line wins.
        cells = self._cells(
            ("markdown", "## 8. Exercices\n\nIntro.\n\n### Exemple guide 1 : demo"),
            ("code", _SOLUTION_BODY),
        )
        assert closest_preceding_header_is_example(cells, 1) is True

    def test_prose_between_code_and_header_still_finds_it(self):
        # A prose-only markdown cell between the example header and the code does
        # not break attribution: scan keeps going back to the example header.
        cells = self._cells(
            ("markdown", "### Exemple guide : demo"),
            ("markdown", "Un paragraphe explicatif sans header."),
            ("code", _SOLUTION_BODY),
        )
        assert closest_preceding_header_is_example(cells, 2) is True


class TestWorkedExampleFalsePositiveSuppression:
    def test_worked_example_under_exercises_section_not_flagged(self, tmp_path):
        # The measured false positive: a complete code cell under a "## Exercices"
        # section header whose immediate sub-header is "### Exemple guide".
        nb = _write_nb(
            tmp_path / "nb.ipynb",
            [
                _md("## 10. Exercices\n\nSection intro."),
                _md("### Exemple guide : cas resolu\n\nOn montre..."),
                _code(_SOLUTION_BODY),
            ],
        )
        findings = scan_notebook(str(nb))
        assert not any(f.get("severity") == "HIGH" for f in findings)

    def test_real_exercise_still_flagged(self, tmp_path):
        # True positive preserved: code cell directly under "### Exercice N".
        nb = _write_nb(
            tmp_path / "nb.ipynb",
            [
                _md("### Exercice 3 : a completer\n\nImplementez..."),
                _code(_SOLUTION_BODY),
            ],
        )
        findings = scan_notebook(str(nb))
        highs = [f for f in findings if f.get("severity") == "HIGH"]
        assert len(highs) == 1
        assert highs[0]["cell_index"] == 1

