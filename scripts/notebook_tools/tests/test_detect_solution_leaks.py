"""Tests for detect_solution_leaks.py — solution leak detection in notebooks."""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).parent.parent))
from detect_solution_leaks import (
    is_stub_code,
    scan_notebook,
)


def _nb(cells: list[dict]) -> dict:
    """Build a minimal notebook dict."""
    return {
        "cells": cells,
        "metadata": {
            "kernelspec": {"display_name": "Python 3", "name": "python3"},
        },
        "nbformat": 4,
        "nbformat_minor": 5,
    }


def _code(source: str) -> dict:
    """Build a code cell."""
    lines = source.split("\n")
    elements = [line + "\n" for line in lines[:-1]] + [lines[-1]]
    return {
        "cell_type": "code",
        "source": elements,
        "execution_count": 1,
        "outputs": [],
        "metadata": {},
    }


def _md(source: str) -> dict:
    """Build a markdown cell."""
    lines = source.split("\n")
    elements = [line + "\n" for line in lines[:-1]] + [lines[-1]]
    return {
        "cell_type": "markdown",
        "source": elements,
        "metadata": {},
    }


def _write_nb(tmp_path: Path, name: str, nb: dict) -> str:
    """Write a notebook to disk and return the path string."""
    p = tmp_path / name
    p.write_text(json.dumps(nb), encoding="utf-8")
    return str(p)


# --- is_stub_code ---


class TestIsStubCode:
    def test_pass_is_stub(self):
        assert is_stub_code("pass") is True

    def test_print_exercice_a_completer_is_stub(self):
        assert is_stub_code('print("Exercice a completer")') is True

    def test_print_exercices_a_completer_is_stub(self):
        assert is_stub_code('print("Exercices a completer")') is True

    def test_return_none_is_stub(self):
        assert is_stub_code("return None") is True

    def test_todo_comment_is_stub(self):
        assert is_stub_code("# TODO: implementer la solution") is True

    def test_empty_source_is_stub(self):
        assert is_stub_code("") is True

    def test_comment_only_is_stub(self):
        assert is_stub_code("# Just a comment\n# Another comment") is True

    def test_import_only_is_stub(self):
        assert is_stub_code("import numpy as np") is True

    def test_import_plus_one_line_is_stub(self):
        assert is_stub_code("import numpy as np\nresult = None") is True

    def test_complete_code_is_not_stub(self):
        source = "x = 10\ny = 20\nprint(x + y)\nresult = x * y"
        assert is_stub_code(source) is False

    def test_real_function_is_not_stub(self):
        source = "def solve(data):\n    return [x**2 for x in data]"
        assert is_stub_code(source) is False

    def test_multiline_solution_is_not_stub(self):
        source = "a = 1\nb = 2\nc = a + b\nprint(c)\nreturn c"
        assert is_stub_code(source) is False

    def test_console_writeline_stub(self):
        assert is_stub_code('Console.WriteLine("Exercice a completer")') is True

    def test_csharp_comment_only_is_stub(self):
        assert is_stub_code("// TODO: implement\n// Another comment") is True


# --- scan_notebook ---


class TestScanNotebookClean:
    """No leaks in properly structured notebooks."""

    def test_exercise_with_stub(self, tmp_path):
        nb = _nb([
            _md("## Exercice 1\nResoudre le probleme."),
            _code("pass"),
        ])
        path = _write_nb(tmp_path, "clean.ipynb", nb)
        findings = scan_notebook(path)
        assert findings == []

    def test_exercise_with_todo(self, tmp_path):
        nb = _nb([
            _md("## Exercice 2\nCalculer X."),
            _code("# TODO: votre code ici\npass"),
        ])
        path = _write_nb(tmp_path, "clean.ipynb", nb)
        findings = scan_notebook(path)
        assert findings == []

    def test_exercise_with_return_none(self, tmp_path):
        nb = _nb([
            _md("## Exercice 3\nImplementer f."),
            _code("def f(x):\n    return None  # TODO"),
        ])
        path = _write_nb(tmp_path, "clean.ipynb", nb)
        findings = scan_notebook(path)
        assert findings == []

    def test_example_with_complete_code_is_not_leak(self, tmp_path):
        """Exemple guide with complete code is NOT a leak."""
        nb = _nb([
            _md("## Exemple guide\nResolution complete."),
            _code("x = 10\ny = 20\nresult = x + y\nprint(result)"),
        ])
        path = _write_nb(tmp_path, "ok.ipynb", nb)
        findings = scan_notebook(path)
        assert all(f["severity"] != "HIGH" for f in findings)


class TestScanNotebookLeaks:
    """Detect solution leaks."""

    def test_exercise_with_long_complete_code_is_leak(self, tmp_path):
        """Code with >8 lines under Exercice header triggers HIGH."""
        nb = _nb([
            _md("## Exercice 1\nResoudre le probleme."),
            _code("x = 10\ny = 20\nz = 30\nresult = x + y + z\n"
                  "output = result * 2\nprint(output)\nreturn output\n# done\nfinal = True"),
        ])
        path = _write_nb(tmp_path, "leak.ipynb", nb)
        findings = scan_notebook(path)
        high = [f for f in findings if f["severity"] == "HIGH"]
        assert len(high) >= 1
        assert "Solution leak" in high[0]["message"]

    def test_exercise_with_short_complete_code_no_marker_not_leak(self, tmp_path):
        """Short code (<9 lines) without solution marker is NOT flagged.

        The detector only flags non-stub code under Exercice if it has
        >8 lines OR contains a solution marker. This is by design to
        avoid false positives on short helper cells.
        """
        nb = _nb([
            _md("## Exercice 1\nResoudre."),
            _code("x = 10\ny = 20\nresult = x + y"),
        ])
        path = _write_nb(tmp_path, "short.ipynb", nb)
        findings = scan_notebook(path)
        high = [f for f in findings if f["severity"] == "HIGH"]
        assert len(high) == 0

    def test_exercise_with_soumis_par_and_code_is_leak(self, tmp_path):
        nb = _nb([
            _md("## Exercice 5 — soumis par Jean\nMa solution."),
            _code("x = 42\nresult = x * 2\nprint(result)"),
        ])
        path = _write_nb(tmp_path, "soumis.ipynb", nb)
        findings = scan_notebook(path)
        high = [f for f in findings if f["severity"] == "HIGH"]
        assert len(high) >= 1
        assert "soumis par" in high[0]["message"]

    def test_exercise_with_solution_marker_is_leak(self, tmp_path):
        nb = _nb([
            _md("## Exercice 4\nCalculer."),
            _code("# Solution\nx = 10\ny = 20"),
        ])
        path = _write_nb(tmp_path, "marker.ipynb", nb)
        findings = scan_notebook(path)
        high = [f for f in findings if f["severity"] == "HIGH"]
        assert len(high) >= 1


class TestScanNotebookDuplicates:
    """Detect duplicate exercise numbering."""

    def test_duplicate_exercise_numbers(self, tmp_path):
        nb = _nb([
            _md("## Exercice 1\nPremier."),
            _code("pass"),
            _md("## Exercice 1\nSecond (duplicate)."),
            _code("pass"),
        ])
        path = _write_nb(tmp_path, "dup.ipynb", nb)
        findings = scan_notebook(path)
        medium = [f for f in findings if f["severity"] == "MEDIUM"]
        assert len(medium) >= 1
        assert "Duplicate" in medium[0]["message"]


class TestScanNotebookEdgeCases:
    """Edge cases and robustness."""

    def test_no_exercises_no_findings(self, tmp_path):
        nb = _nb([
            _md("# Title"),
            _code("x = 1"),
            _md("Some text"),
        ])
        path = _write_nb(tmp_path, "no_ex.ipynb", nb)
        findings = scan_notebook(path)
        assert findings == []

    def test_exercise_with_no_following_code(self, tmp_path):
        nb = _nb([
            _md("## Exercice 1\nEnonce."),
            _md("## Section suivante"),
        ])
        path = _write_nb(tmp_path, "no_code.ipynb", nb)
        findings = scan_notebook(path)
        assert findings == []

    def test_exercise_with_code_two_cells_away_checked(self, tmp_path):
        """Code cell within 3 cells of exercise header is checked."""
        nb = _nb([
            _md("## Exercice 1\nEnonce."),
            _md("Indice: utilisez la fonction f."),
            _code("# Solution complete\na = 10\nb = 20\nc = 30\nresult = a+b+c\n"
                  "output = result * 2\nprint(output)\nreturn output\nfinal = True"),
        ])
        path = _write_nb(tmp_path, "gap.ipynb", nb)
        findings = scan_notebook(path)
        high = [f for f in findings if f["severity"] == "HIGH"]
        # Has solution marker "# Solution" so should be flagged even if <9 lines
        assert len(high) >= 1

    def test_exercise_with_code_four_cells_away_not_checked(self, tmp_path):
        """Code cell beyond 3 cells of exercise header is NOT checked."""
        nb = _nb([
            _md("## Exercice 1\nEnonce."),
            _md("Indice 1."),
            _md("Indice 2."),
            _md("Indice 3."),
            _code("x = 10\ny = 20\nresult = x + y\nprint(result)"),
        ])
        path = _write_nb(tmp_path, "far.ipynb", nb)
        findings = scan_notebook(path)
        high = [f for f in findings if f["severity"] == "HIGH"]
        assert len(high) == 0

    def test_invalid_json_returns_error(self, tmp_path):
        p = tmp_path / "bad.ipynb"
        p.write_text("not valid json{{{", encoding="utf-8")
        findings = scan_notebook(str(p))
        assert any(f["severity"] == "ERROR" for f in findings)

    def test_exercise_numbered_with_dot(self, tmp_path):
        nb = _nb([
            _md("## 1. Exercice 3\nResoudre."),
            _code("pass"),
        ])
        path = _write_nb(tmp_path, "dot.ipynb", nb)
        findings = scan_notebook(path)
        # No leak since code is stub
        high = [f for f in findings if f["severity"] == "HIGH"]
        assert len(high) == 0

    def test_exercise_english_variant(self, tmp_path):
        nb = _nb([
            _md("## Exercise 1\nSolve the problem."),
            _code("pass"),
        ])
        path = _write_nb(tmp_path, "eng.ipynb", nb)
        findings = scan_notebook(path)
        # No leak since code is stub
        high = [f for f in findings if f["severity"] == "HIGH"]
        assert len(high) == 0
