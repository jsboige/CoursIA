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
