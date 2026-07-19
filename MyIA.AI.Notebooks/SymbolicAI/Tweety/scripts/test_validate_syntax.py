"""Tests pour le module ``validate_syntax`` (syntax-validation des notebooks Tweety).

Run with: pytest Tweety/scripts/test_validate_syntax.py -v

Module couvert : ``Tweety/scripts/validate_syntax.py`` — validateur de syntaxe
Python (ast.parse) des cellules code des notebooks Tweety. 0 test Python avant
cette PR → garde-fou anti-régression. Le script distingue les cellules code des
markdown, gère la source en liste OU string, skip les cellules vides, truncate
la first-line à 60 chars, et fallback cell_id si absent.

Bug-hunt firsthand (po-2023 marco.py lesson : exercer, pas juste lire) :
0 bug fonctionnel forçable. La précédence de l'opérateur ternaire L87
(``a + b if cond else c``) est correcte ``(a+b) if cond else c``.
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent))

import validate_syntax as vs  # noqa: E402


# --- validate_python_syntax -------------------------------------------------

def test_validate_python_syntax_valid():
    assert vs.validate_python_syntax("x = 1\nprint(x)") == (True, "")


def test_validate_python_syntax_empty_string_is_valid():
    """ast.parse('') succeeds — empty cells are valid syntax."""
    assert vs.validate_python_syntax("") == (True, "")


def test_validate_python_syntax_whitespace_only_is_valid():
    assert vs.validate_python_syntax("   \n\t\n") == (True, "")


def test_validate_python_syntax_invalid_returns_line_and_msg():
    ok, msg = vs.validate_python_syntax("def f(:\n  pass")
    assert ok is False
    assert "Line 1" in msg


def test_validate_python_syntax_reports_correct_line_number():
    ok, msg = vs.validate_python_syntax("x = 1\ny = 2\nz = (")  # error on line 3
    assert ok is False
    assert "Line 3" in msg


def test_validate_python_syntax_complex_valid_program():
    code = (
        "import json\n"
        "def f(x):\n"
        "    return x * 2\n"
        "print(f(21))\n"
    )
    assert vs.validate_python_syntax(code) == (True, "")


# --- validate_notebook ------------------------------------------------------

def _write_nb(tmp_path: Path, name: str, cells: list) -> Path:
    p = tmp_path / name
    p.write_text(json.dumps({"cells": cells}), encoding="utf-8")
    return p


def test_validate_notebook_clean_returns_no_errors(tmp_path):
    p = _write_nb(tmp_path, "ok.ipynb", [
        {"cell_type": "code", "source": ["x = 1"]},
        {"cell_type": "markdown", "source": ["# title"]},
    ])
    assert vs.validate_notebook(p) == []


def test_validate_notebook_detects_syntax_error_in_code_cell(tmp_path):
    p = _write_nb(tmp_path, "bad.ipynb", [
        {"cell_type": "code", "source": ["def bad(:"], "id": "c0"},
    ])
    errs = vs.validate_notebook(p)
    assert len(errs) == 1
    assert errs[0]["cell_index"] == 0
    assert errs[0]["cell_id"] == "c0"
    assert "Line" in errs[0]["error"]


def test_validate_notebook_skips_markdown_cells(tmp_path):
    """Markdown cells must never be parsed as Python."""
    p = _write_nb(tmp_path, "md.ipynb", [
        {"cell_type": "markdown", "source": ["def f(:  # this is prose, not code"]},
    ])
    assert vs.validate_notebook(p) == []


def test_validate_notebook_skips_empty_code_cells(tmp_path):
    p = _write_nb(tmp_path, "empty.ipynb", [
        {"cell_type": "code", "source": ["   \n\t"]},
        {"cell_type": "code", "source": []},
    ])
    assert vs.validate_notebook(p) == []


def test_validate_notebook_accepts_source_as_string(tmp_path):
    """nbformat source may be a single string, not a list."""
    p = _write_nb(tmp_path, "str.ipynb", [
        {"cell_type": "code", "source": "def bad(:\n  pass"},
    ])
    errs = vs.validate_notebook(p)
    assert len(errs) == 1


def test_validate_notebook_cell_id_fallback_to_cell_index(tmp_path):
    """A code cell without an explicit id falls back to f'cell_{i}'."""
    p = _write_nb(tmp_path, "noid.ipynb", [
        {"cell_type": "code", "source": ["z = ("]},
    ])
    errs = vs.validate_notebook(p)
    assert errs[0]["cell_id"] == "cell_0"


def test_validate_notebook_first_line_truncation(tmp_path):
    """first_line is truncated to 60 chars + '...' when longer."""
    long_line = "x = " + "a" * 70  # 74 chars
    p = _write_nb(tmp_path, "long.ipynb", [
        {"cell_type": "code", "source": [long_line + "\nbad_syntax ("]},
    ])
    errs = vs.validate_notebook(p)
    fl = errs[0]["first_line"]
    assert fl.endswith("...")
    assert len(fl) == 63  # 60 + len("...")


def test_validate_notebook_first_line_not_truncated_under_60(tmp_path):
    short = "short bad syntax ("
    p = _write_nb(tmp_path, "short.ipynb", [
        {"cell_type": "code", "source": [short]},
    ])
    errs = vs.validate_notebook(p)
    assert errs[0]["first_line"] == short
    assert "..." not in errs[0]["first_line"]


def test_validate_notebook_missing_file_returns_error_dict(tmp_path):
    errs = vs.validate_notebook(tmp_path / "does_not_exist.ipynb")
    assert len(errs) == 1
    assert errs[0]["error"] == "File not found"
    assert errs[0]["notebook"] == "does_not_exist.ipynb"


def test_validate_notebook_invalid_json_returns_error(tmp_path):
    p = tmp_path / "broken.ipynb"
    p.write_text("{not valid json", encoding="utf-8")
    errs = vs.validate_notebook(p)
    assert len(errs) == 1
    assert "Invalid JSON" in errs[0]["error"]


def test_validate_notebook_multiple_errors_all_collected(tmp_path):
    p = _write_nb(tmp_path, "multi.ipynb", [
        {"cell_type": "code", "source": ["bad1 ("], "id": "a"},
        {"cell_type": "code", "source": ["x = 1"]},          # valid, skipped
        {"cell_type": "code", "source": ["bad2 ("], "id": "c"},
    ])
    errs = vs.validate_notebook(p)
    assert len(errs) == 2
    assert {e["cell_id"] for e in errs} == {"a", "c"}


def test_validate_notebook_no_cells_key_returns_empty(tmp_path):
    """A notebook dict without 'cells' is handled (empty iteration)."""
    p = tmp_path / "nocells.ipynb"
    p.write_text(json.dumps({"metadata": {}}), encoding="utf-8")
    assert vs.validate_notebook(p) == []


# --- TWEETY_NOTEBOOKS list sanity -------------------------------------------

def test_tweety_notebooks_list_nonempty_and_ipynb():
    assert len(vs.TWEETY_NOTEBOOKS) >= 1
    assert all(name.endswith(".ipynb") for name in vs.TWEETY_NOTEBOOKS)
