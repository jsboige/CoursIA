#!/usr/bin/env python3
"""
Tests for scripts/smartcontracts/validate_sc_notebooks.py

Covers pure functions: source_text, is_nav_cell, has_exposed_solution,
make_source_list, and CellInfo/NotebookValidation dataclass construction.
No I/O, no filesystem, no Docker. Pure unit tests.

LIVE: called by SC validation pipeline + test_validate_sc_notebooks.py.
"""

import pytest
import sys
from pathlib import Path

# Add smartcontracts to sys.path
_sc_dir = str(Path(__file__).resolve().parent.parent / "smartcontracts")
if _sc_dir not in sys.path:
    sys.path.insert(0, _sc_dir)

from validate_sc_notebooks import (
    source_text,
    is_nav_cell,
    has_exposed_solution,
    make_source_list,
    CellInfo,
    NotebookValidation,
    Colors,
)


# ─── source_text ──────────────────────────────────────────────────────


class TestSourceText:
    def test_string_source(self):
        cell = {"source": "print('hello')"}
        assert source_text(cell) == "print('hello')"

    def test_list_source(self):
        cell = {"source": ["line1\n", "line2\n", "line3"]}
        assert source_text(cell) == "line1\nline2\nline3"

    def test_empty_string_source(self):
        cell = {"source": ""}
        assert source_text(cell) == ""

    def test_empty_list_source(self):
        cell = {"source": []}
        assert source_text(cell) == ""

    def test_missing_source(self):
        cell = {}
        assert source_text(cell) == ""

    def test_single_line_list(self):
        cell = {"source": ["only line"]}
        assert source_text(cell) == "only line"

    def test_multiline_list_no_trailing_newline(self):
        cell = {"source": ["a\n", "b\n", "c"]}
        assert source_text(cell) == "a\nb\nc"

    def test_multiline_list_with_trailing_newline(self):
        cell = {"source": ["a\n", "b\n", "c\n"]}
        assert source_text(cell) == "a\nb\nc\n"


# ─── is_nav_cell ──────────────────────────────────────────────────────


class TestIsNavCell:
    def test_prev_link(self):
        assert is_nav_cell("[<< Setup Foundry](SC-1-Setup-Foundry.ipynb)") is True

    def test_next_link(self):
        assert is_nav_cell("[Setup Web3py >>](SC-2-Setup-Web3py.ipynb)") is True

    def test_both_links(self):
        text = "[<< Setup Foundry](SC-1.ipynb) | [Setup Web3py >>](SC-2.ipynb)"
        assert is_nav_cell(text) is True

    def test_plain_text(self):
        assert is_nav_cell("This is a regular markdown cell") is False

    def test_empty_string(self):
        assert is_nav_cell("") is False

    def test_code_cell(self):
        assert is_nav_cell("print('hello world')") is False

    def test_link_without_arrows(self):
        assert is_nav_cell("[Click here](other.ipynb)") is False

    def test_arrows_without_link(self):
        """Arrows as plain text, not in markdown link syntax."""
        assert is_nav_cell("<< previous | next >>") is False


# ─── has_exposed_solution ─────────────────────────────────────────────


class TestHasExposedSolution:
    def test_todo_excluded(self):
        code = "result = None  # TODO etudiant: implement"
        assert has_exposed_solution(code) is False

    def test_not_implemented_excluded(self):
        code = "raise NotImplementedError('Exercice a completer')"
        assert has_exposed_solution(code) is False

    def test_votre_code_excluded(self):
        code = "# Votre code ici\npass"
        assert has_exposed_solution(code) is False

    def test_solidity_string_excluded(self):
        code = "contract_code = '''pragma solidity ^0.8.0;'''"
        assert has_exposed_solution(code) is False

    def test_solidity_double_quote_string_excluded(self):
        code = 'contract_code = """pragma solidity ^0.8.0;"""'
        assert has_exposed_solution(code) is False

    def test_complete_test_function_detected(self):
        code = """
function test_transfer() public {
    token.transfer(addr2, 100);
    assertEq(token.balanceOf(addr2), 100);
}
"""
        assert has_exposed_solution(code) is True

    def test_plain_code_not_detected(self):
        code = "x = 5\ny = 10\nprint(x + y)"
        assert has_exposed_solution(code) is False

    def test_empty_code(self):
        assert has_exposed_solution("") is False

    def test_todo_with_assert(self):
        """TODO takes priority over assertEq."""
        code = "// TODO: implement\ntoken.transfer(addr2, 100);\nassertEq(token.balanceOf(addr2), 100);"
        assert has_exposed_solution(code) is False


# ─── make_source_list ─────────────────────────────────────────────────


class TestMakeSourceList:
    def test_single_line(self):
        result = make_source_list("hello")
        assert result == ["hello"]

    def test_multiline(self):
        result = make_source_list("line1\nline2\nline3")
        assert result == ["line1\n", "line2\n", "line3"]

    def test_trailing_newline(self):
        result = make_source_list("line1\nline2\n")
        assert result == ["line1\n", "line2\n"]

    def test_empty_string(self):
        result = make_source_list("")
        assert result == []

    def test_only_newlines(self):
        result = make_source_list("\n\n")
        assert result == ["\n", "\n"]

    def test_preserves_content(self):
        text = "print('hello')\n# comment\nx = 42"
        result = make_source_list(text)
        assert "".join(result) == text

    def test_roundtrip(self):
        """Joining make_source_list output reproduces original text."""
        original = "line a\nline b\nline c"
        result = make_source_list(original)
        assert "".join(result) == original


# ─── Dataclasses ───────────────────────────────────────────────────────


class TestCellInfo:
    def test_construction(self):
        info = CellInfo(
            index=0,
            cell_type="code",
            cell_id="abc123",
            source_len=50,
            has_output=True,
            is_exercise=False,
            is_nav=False,
            source_format="list",
            first_line="print('hello')"
        )
        assert info.index == 0
        assert info.cell_type == "code"
        assert info.source_len == 50
        assert info.has_output is True

    def test_defaults(self):
        """CellInfo has no defaults - all required."""
        info = CellInfo(
            index=1, cell_type="markdown", cell_id="def",
            source_len=10, has_output=False, is_exercise=False,
            is_nav=False, source_format="string", first_line="# Title"
        )
        assert info.index == 1


class TestNotebookValidation:
    def test_construction(self):
        val = NotebookValidation(
            name="SC-0-Cypherpunk-Origins",
            path="/path/to/notebook.ipynb",
            profile="standalone"
        )
        assert val.name == "SC-0-Cypherpunk-Origins"
        assert val.profile == "standalone"
        assert val.errors == []
        assert val.warnings == []

    def test_errors_append(self):
        val = NotebookValidation(name="test", path="/t.ipynb", profile="standalone")
        val.errors.append("Something wrong")
        assert len(val.errors) == 1

    def test_warnings_append(self):
        val = NotebookValidation(name="test", path="/t.ipynb", profile="standalone")
        val.warnings.append("Minor issue")
        assert len(val.warnings) == 1


# ─── Colors ────────────────────────────────────────────────────────────


class TestColors:
    def test_disable(self):
        originals = {attr: getattr(Colors, attr)
                     for attr in ['GREEN', 'RED', 'YELLOW', 'BLUE', 'CYAN', 'BOLD', 'END']}
        Colors.disable()
        for attr in ['GREEN', 'RED', 'YELLOW', 'BLUE', 'CYAN', 'BOLD', 'END']:
            assert getattr(Colors, attr) == ""
        # Restore all
        for attr, val in originals.items():
            setattr(Colors, attr, val)

    def test_colors_have_values(self):
        assert Colors.GREEN != ""
        assert Colors.RED != ""
        assert Colors.END != ""


# ─── Cross-invariants ─────────────────────────────────────────────────


class TestCrossInvariants:
    def test_source_text_roundtrip_with_make_source_list(self):
        """source_text(make_source_list(x)) should reproduce x for list cells."""
        original = "line1\nline2\nline3"
        source_list = make_source_list(original)
        cell = {"source": source_list}
        assert source_text(cell) == original

    def test_nav_detection_with_source_text(self):
        """is_nav_cell works on output of source_text."""
        cell = {"source": ["[<< Prev](prev.ipynb) | [Next >>](next.ipynb)"]}
        text = source_text(cell)
        assert is_nav_cell(text) is True

    def test_exercise_cell_not_exposed(self):
        """Exercise stub cell should not be flagged as exposed solution."""
        cell = {
            "source": [
                "# Exercice : implementer la fonction\n",
                "result = None  # TODO etudiant\n",
                "print('Exercice a completer')"
            ]
        }
        text = source_text(cell)
        assert has_exposed_solution(text) is False
