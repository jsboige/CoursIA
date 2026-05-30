"""Tests for scripts/smartcontracts/validate_sc_notebooks.py — SC notebook validator.

Tests focus on pure functions: source_text, is_nav_cell, has_exposed_solution,
make_source_list, get_executable_cells, validate_notebook — covering validation
logic, dataclass defaults, edge cases.
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "smartcontracts"))
from validate_sc_notebooks import (
    CellInfo,
    Colors,
    NotebookValidation,
    get_executable_cells,
    has_exposed_solution,
    is_nav_cell,
    make_source_list,
    source_text,
    validate_notebook,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _code(source: str | list, cell_id: str = "cell-0") -> dict:
    """Build a code cell dict."""
    return {
        "cell_type": "code",
        "source": source,
        "id": cell_id,
        "outputs": [],
        "execution_count": 1,
    }


def _md(source: str | list, cell_id: str = "cell-md") -> dict:
    """Build a markdown cell dict."""
    return {
        "cell_type": "markdown",
        "source": source,
        "id": cell_id,
        "metadata": {},
    }


def _write_nb(path: Path, cells: list[dict], metadata: dict | None = None) -> Path:
    """Write a minimal notebook file for testing."""
    path.parent.mkdir(parents=True, exist_ok=True)
    nb = {"cells": cells, "metadata": metadata or {}, "nbformat": 4, "nbformat_minor": 5}
    path.write_text(json.dumps(nb), encoding="utf-8")
    return path


# ---------------------------------------------------------------------------
# source_text
# ---------------------------------------------------------------------------

class TestSourceText:
    """Tests for cell source extraction."""

    def test_string_source(self):
        cell = {"source": "hello\nworld"}
        assert source_text(cell) == "hello\nworld"

    def test_list_source(self):
        cell = {"source": ["hello\n", "world"]}
        assert source_text(cell) == "hello\nworld"

    def test_empty_string(self):
        cell = {"source": ""}
        assert source_text(cell) == ""

    def test_empty_list(self):
        cell = {"source": []}
        assert source_text(cell) == ""

    def test_missing_source(self):
        cell = {}
        assert source_text(cell) == ""

    def test_list_with_trailing_newline(self):
        cell = {"source": ["line1\n", "line2\n", ""]}
        assert source_text(cell) == "line1\nline2\n"

    def test_single_element_list(self):
        cell = {"source": ["single line"]}
        assert source_text(cell) == "single line"


# ---------------------------------------------------------------------------
# is_nav_cell
# ---------------------------------------------------------------------------

class TestIsNavCell:
    """Tests for navigation cell detection."""

    def test_back_link(self):
        assert is_nav_cell("Previous [<< SC-4]") is True

    def test_forward_link(self):
        assert is_nav_cell("[SC-6 >>] Next") is True

    def test_both_links(self):
        assert is_nav_cell("[<< SC-4] | [SC-6 >>]") is True

    def test_no_links(self):
        assert is_nav_cell("# Solidity Basics") is False

    def test_empty_text(self):
        assert is_nav_cell("") is False

    def test_partial_match_no_brackets(self):
        assert is_nav_cell(">> end") is False

    def test_backward_link_only_arrows(self):
        assert is_nav_cell("<< SC-4") is False


# ---------------------------------------------------------------------------
# has_exposed_solution
# ---------------------------------------------------------------------------

class TestHasExposedSolution:
    """Tests for exposed solution detection in code cells."""

    def test_todo_not_exposed(self):
        assert has_exposed_solution("x = compute()  # TODO") is False

    def test_not_implemented_not_exposed(self):
        assert has_exposed_solution("raise NotImplementedError") is False

    def test_votre_code_not_exposed(self):
        assert has_exposed_solution("# Votre code ici") is False

    def test_triple_quote_not_exposed(self):
        code = 'contract_code = """pragma solidity ^0.8.0;"""'
        assert has_exposed_solution(code) is False

    def test_triple_quote_single(self):
        code = "contract_code = '''pragma solidity ^0.8.0;'''"
        assert has_exposed_solution(code) is False

    def test_plain_code_not_exposed(self):
        """Plain code without test function patterns is not flagged."""
        assert has_exposed_solution("x = 1 + 2") is False

    def test_test_function_with_assert(self):
        """Test function with assertEq pattern IS exposed."""
        code = "function test_transfer() {\n    assertEq(balance, 100);\n}"
        assert has_exposed_solution(code) is True

    def test_empty_text(self):
        assert has_exposed_solution("") is False


# ---------------------------------------------------------------------------
# make_source_list
# ---------------------------------------------------------------------------

class TestMakeSourceList:
    """Tests for STRING → LIST source conversion."""

    def test_multiline(self):
        result = make_source_list("line1\nline2\nline3")
        assert result == ["line1\n", "line2\n", "line3"]

    def test_single_line(self):
        result = make_source_list("only line")
        assert result == ["only line"]

    def test_empty_string(self):
        result = make_source_list("")
        assert result == []

    def test_trailing_newline(self):
        """Trailing empty line after \\n is dropped (elif line: filter)."""
        result = make_source_list("a\nb\n")
        assert result == ["a\n", "b\n"]

    def test_preserves_content(self):
        code = "from web3 import Web3\nw3 = Web3()"
        result = make_source_list(code)
        assert result[0] == "from web3 import Web3\n"
        assert result[1] == "w3 = Web3()"


# ---------------------------------------------------------------------------
# get_executable_cells
# ---------------------------------------------------------------------------

class TestGetExecutableCells:
    """Tests for executable cell filtering."""

    def test_basic_executable(self, tmp_path):
        nb_path = _write_nb(tmp_path / "test.ipynb", [
            _md("# Title"),
            _code("x = 1 + 2"),
        ])
        cells = get_executable_cells(nb_path, "standalone", False)
        assert len(cells) == 1
        assert cells[0][1].strip() == "x = 1 + 2"

    def test_skip_exercise_todo(self, tmp_path):
        nb_path = _write_nb(tmp_path / "test.ipynb", [
            _code("result = None  # TODO: implement"),
        ])
        cells = get_executable_cells(nb_path, "standalone", False)
        assert len(cells) == 0

    def test_skip_exercise_not_implemented(self, tmp_path):
        nb_path = _write_nb(tmp_path / "test.ipynb", [
            _code("raise NotImplementedError"),
        ])
        cells = get_executable_cells(nb_path, "standalone", False)
        assert len(cells) == 0

    def test_skip_pip_install(self, tmp_path):
        nb_path = _write_nb(tmp_path / "test.ipynb", [
            _code("!pip install web3"),
        ])
        cells = get_executable_cells(nb_path, "standalone", False)
        assert len(cells) == 0

    def test_skip_markdown(self, tmp_path):
        nb_path = _write_nb(tmp_path / "test.ipynb", [
            _md("# Section"),
        ])
        cells = get_executable_cells(nb_path, "standalone", False)
        assert len(cells) == 0

    def test_skip_empty_code(self, tmp_path):
        nb_path = _write_nb(tmp_path / "test.ipynb", [
            _code(""),
        ])
        cells = get_executable_cells(nb_path, "standalone", False)
        assert len(cells) == 0

    def test_anvil_without_service(self, tmp_path):
        """Anvil profile cells requiring web3 are skipped when anvil unavailable."""
        nb_path = _write_nb(tmp_path / "test.ipynb", [
            _code("w3.eth.get_balance(account)"),
        ])
        cells = get_executable_cells(nb_path, "anvil", False)
        assert len(cells) == 0

    def test_anvil_with_service(self, tmp_path):
        """Anvil profile cells included when service is available."""
        nb_path = _write_nb(tmp_path / "test.ipynb", [
            _code("w3.eth.get_balance(account)"),
        ])
        cells = get_executable_cells(nb_path, "anvil", True)
        assert len(cells) == 1

    def test_anvil_skip_web3_provider(self, tmp_path):
        nb_path = _write_nb(tmp_path / "test.ipynb", [
            _code("Web3.HTTPProvider('http://127.0.0.1:8545')"),
        ])
        cells = get_executable_cells(nb_path, "anvil", False)
        assert len(cells) == 0

    def test_anvil_skip_compile_deploy(self, tmp_path):
        nb_path = _write_nb(tmp_path / "test.ipynb", [
            _code("compile_and_deploy(contract_source)"),
        ])
        cells = get_executable_cells(nb_path, "anvil", False)
        assert len(cells) == 0

    def test_mixed_cells(self, tmp_path):
        nb_path = _write_nb(tmp_path / "test.ipynb", [
            _md("# Title"),
            _code("x = 1"),
            _code("raise NotImplementedError"),
            _code("y = 2"),
            _code("!pip install foo"),
        ])
        cells = get_executable_cells(nb_path, "standalone", False)
        assert len(cells) == 2

    def test_cell_index_correct(self, tmp_path):
        nb_path = _write_nb(tmp_path / "test.ipynb", [
            _md("# Title"),
            _code("x = 1"),
            _code("y = 2"),
        ])
        cells = get_executable_cells(nb_path, "standalone", False)
        assert cells[0][0] == 1  # index of first code cell
        assert cells[1][0] == 2  # index of second code cell


# ---------------------------------------------------------------------------
# validate_notebook
# ---------------------------------------------------------------------------

class TestValidateNotebook:
    """Tests for notebook structural validation."""

    def test_valid_notebook(self, tmp_path):
        """Well-structured notebook with title, nav, objectives."""
        nb_dir = tmp_path / "SC-Test"
        nb_dir.mkdir()
        nb_path = _write_nb(nb_dir / "SC-99-Test.ipynb", [
            _md("# SC-99 Test Notebook\n[<< SC-98] | [SC-100 >>]"),
            _md("## Objectifs d'apprentissage\nDurée: 30 minutes\nPrérequis: Python"),
            _code("print('hello')"),
            _md("[<< SC-98] | [SC-100 >>]"),
        ])
        v = validate_notebook(str(nb_dir), "SC-99-Test", "standalone")
        assert v.exists is True
        assert v.has_title is True
        assert v.has_navigation_header is True
        assert v.has_navigation_footer is True
        assert v.has_objectives is True
        assert v.has_duration is True
        assert v.has_prerequisites is True
        assert v.cell_count == 4
        assert v.code_cells == 1
        assert v.markdown_cells == 3

    def test_missing_notebook(self, tmp_path):
        v = validate_notebook(str(tmp_path / "nonexistent"), "SC-Missing", "standalone")
        assert v.exists is False
        assert "not found" in v.errors[0].lower()

    def test_invalid_json(self, tmp_path):
        nb_dir = tmp_path / "bad"
        nb_dir.mkdir()
        bad = nb_dir / "SC-Bad.ipynb"
        bad.write_text("not json{{{", encoding="utf-8")
        v = validate_notebook(str(nb_dir), "SC-Bad", "standalone")
        assert v.exists is True
        assert any("json" in e.lower() for e in v.errors)

    def test_no_cells(self, tmp_path):
        nb_dir = tmp_path / "empty"
        nb_dir.mkdir()
        _write_nb(nb_dir / "SC-Empty.ipynb", [])
        v = validate_notebook(str(nb_dir), "SC-Empty", "standalone")
        assert "no cells" in v.errors[0].lower()

    def test_string_format_cells_flagged(self, tmp_path):
        """Cells with STRING source are flagged as errors."""
        nb_dir = tmp_path / "str"
        nb_dir.mkdir()
        _write_nb(nb_dir / "SC-String.ipynb", [
            {"cell_type": "markdown", "source": "# SC-String Test", "id": "m1"},
            {"cell_type": "code", "source": "x = 1\ny = 2", "id": "c1"},
        ])
        v = validate_notebook(str(nb_dir), "SC-String", "standalone")
        # Both markdown and code cells with STRING source are counted
        assert v.string_format_cells == 2
        assert any("STRING" in e for e in v.errors)

    def test_missing_title(self, tmp_path):
        nb_dir = tmp_path / "notitle"
        nb_dir.mkdir()
        _write_nb(nb_dir / "SC-NoTitle.ipynb", [
            _md("Just some text"),
        ])
        v = validate_notebook(str(nb_dir), "SC-NoTitle", "standalone")
        assert v.has_title is False
        assert any("title" in e.lower() for e in v.errors)

    def test_empty_cells_warning(self, tmp_path):
        nb_dir = tmp_path / "empty_cells"
        nb_dir.mkdir()
        _write_nb(nb_dir / "SC-EmptyCells.ipynb", [
            _md("# SC-Test"),
            _md(""),
        ])
        v = validate_notebook(str(nb_dir), "SC-EmptyCells", "standalone")
        assert v.empty_cells == 1
        assert any("empty" in w.lower() for w in v.warnings)

    def test_exercise_cells_counted(self, tmp_path):
        nb_dir = tmp_path / "exercises"
        nb_dir.mkdir()
        _write_nb(nb_dir / "SC-Ex.ipynb", [
            _md("# SC-Test"),
            _code("result = None  # TODO"),
        ])
        v = validate_notebook(str(nb_dir), "SC-Ex", "standalone")
        assert v.exercise_cells == 1

    def test_anvil_missing_web3(self, tmp_path):
        """Anvil notebook without web3 setup triggers an error."""
        nb_dir = tmp_path / "anvil"
        nb_dir.mkdir()
        _write_nb(nb_dir / "SC-Anvil.ipynb", [
            _md("# SC-Test"),
            _code("print('no web3 here')"),
        ])
        v = validate_notebook(str(nb_dir), "SC-Anvil", "anvil")
        assert v.has_web3_setup is False
        assert any("web3" in e.lower() for e in v.errors)

    def test_anvil_with_web3(self, tmp_path):
        nb_dir = tmp_path / "anvil_ok"
        nb_dir.mkdir()
        _write_nb(nb_dir / "SC-OK.ipynb", [
            _md("# SC-Test"),
            _code("from web3 import Web3\nw3 = Web3()"),
        ])
        v = validate_notebook(str(nb_dir), "SC-OK", "anvil")
        assert v.has_web3_setup is True

    def test_consecutive_code_warning(self, tmp_path):
        """More than 2 consecutive code cells triggers a warning (threshold > 2)."""
        nb_dir = tmp_path / "consec"
        nb_dir.mkdir()
        _write_nb(nb_dir / "SC-Consec.ipynb", [
            _md("# SC-Test"),
            _code("a = 1"),
            _code("b = 2"),
            _code("c = 3"),
            _code("d = 4"),
        ])
        v = validate_notebook(str(nb_dir), "SC-Consec", "standalone")
        # 4 consecutive code cells → counter max = 3 (pairs: 2→3→4)
        assert v.consecutive_code_cells == 3
        assert any("consecutive" in w.lower() for w in v.warnings)

    def test_no_navigation_header_warning(self, tmp_path):
        nb_dir = tmp_path / "no_nav"
        nb_dir.mkdir()
        _write_nb(nb_dir / "SC-Nav.ipynb", [
            _md("# SC-Test"),
        ])
        v = validate_notebook(str(nb_dir), "SC-Nav", "standalone")
        assert v.has_navigation_header is False
        assert any("header" in w.lower() for w in v.warnings)

    def test_no_navigation_footer_warning(self, tmp_path):
        nb_dir = tmp_path / "no_footer"
        nb_dir.mkdir()
        _write_nb(nb_dir / "SC-Footer.ipynb", [
            _md("# SC-Test\n[<< SC-1]"),
            _code("x = 1"),
            _code("y = 2"),
            _md("Some closing text without navigation"),
        ])
        v = validate_notebook(str(nb_dir), "SC-Footer", "standalone")
        assert v.has_navigation_header is True
        assert v.has_navigation_footer is False

    def test_profile_stored(self, tmp_path):
        nb_dir = tmp_path / "profile"
        nb_dir.mkdir()
        _write_nb(nb_dir / "SC-Prof.ipynb", [_md("# SC-Test")])
        v = validate_notebook(str(nb_dir), "SC-Prof", "foundry")
        assert v.profile == "foundry"


# ---------------------------------------------------------------------------
# Dataclasses
# ---------------------------------------------------------------------------

class TestDataclasses:
    """Tests for dataclass defaults."""

    def test_notebook_validation_defaults(self):
        v = NotebookValidation(name="test", path="/path/test.ipynb", profile="standalone")
        assert v.exists is True
        assert v.cell_count == 0
        assert v.code_cells == 0
        assert v.errors == []
        assert v.warnings == []
        assert v.deps_available == {}

    def test_cell_info_creation(self):
        ci = CellInfo(
            index=5, cell_type="code", cell_id="c5",
            source_len=42, has_output=True, is_exercise=False,
            is_nav=False, source_format="list", first_line="x = 1",
        )
        assert ci.index == 5
        assert ci.has_output is True
        assert ci.source_format == "list"


# ---------------------------------------------------------------------------
# Colors
# ---------------------------------------------------------------------------

class TestColors:
    """Tests for ANSI color helper."""

    def test_disable(self):
        original = Colors.GREEN
        Colors.disable()
        assert Colors.GREEN == ""
        assert Colors.RED == ""
        # Restore
        Colors.GREEN = original
        Colors.RED = '\033[91m'
        Colors.YELLOW = '\033[93m'
        Colors.BLUE = '\033[94m'
        Colors.CYAN = '\033[96m'
        Colors.BOLD = '\033[1m'
        Colors.END = '\033[0m'
