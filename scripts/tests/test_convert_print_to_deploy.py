"""Tests for ``scripts/smartcontracts/convert_print_to_deploy.py`` (pure functions).

``convert_print_to_deploy.py`` is a **one-shot migration script** that rewrites
``print(CONTRACT)`` cells in the Solidity notebooks into ``compile_and_deploy()``
calls. It has **no ``__main__`` guard** and runs a notebook I/O loop on hardcoded
absolute paths at **module import time** — so naively importing it would trigger
file I/O on paths that don't exist outside the original migration run.

These tests target the **3 pure functions** (``source_text``, ``make_source_list``,
``transform_print_cell``) by loading them via AST surgery that keeps only the
``FunctionDef`` + ``Import`` nodes and skips the module-level notebook loop. This
is a standard pattern for testing one-shot scripts that have import-time side
effects (isolate the pure logic from the side-effecting driver).

The module was a **0-test orphan** (0 importers, 0 tests on origin/main) — these
tests lock the contract-detection + print→deploy transform behavior.

Run with: pytest scripts/tests/test_convert_print_to_deploy.py -v
"""

import ast
import sys
from pathlib import Path

import pytest

# Load ONLY the pure functions (skip the module-level notebook I/O loop).
_MODULE_PATH = Path(__file__).resolve().parent.parent / "smartcontracts" / "convert_print_to_deploy.py"
_source = _MODULE_PATH.read_text(encoding="utf-8")
_tree = ast.parse(_source)
# Keep top-level FunctionDef + imports; drop the module-level `notebooks` loop
# and the SC_BASE constant (functions reference neither at call time — they take
# `cell` as argument).
_kept = [n for n in _tree.body if isinstance(n, (ast.FunctionDef, ast.Import, ast.ImportFrom))]
_mod = ast.Module(body=_kept, type_ignores=[])
_ns = {}
exec(compile(_mod, str(_MODULE_PATH), "exec"), _ns)

source_text = _ns["source_text"]
make_source_list = _ns["make_source_list"]
transform_print_cell = _ns["transform_print_cell"]


# --------------------------------------------------------------------------- #
#  source_text                                                                 #
# --------------------------------------------------------------------------- #

class TestSourceText:
    """source_text : cell source (list ou string) -> string unique."""

    def test_list_source_joined(self):
        cell = {"source": ["line1\n", "line2\n", "line3"]}
        assert source_text(cell) == "line1\nline2\nline3"

    def test_string_source_passthrough(self):
        cell = {"source": "already a string\n"}
        assert source_text(cell) == "already a string\n"

    def test_missing_source_key_defaults_empty(self):
        assert source_text({}) == ""

    def test_empty_list_source(self):
        assert source_text({"source": []}) == ""

    def test_empty_string_source(self):
        assert source_text({"source": ""}) == ""


# --------------------------------------------------------------------------- #
#  make_source_list                                                            #
# --------------------------------------------------------------------------- #

class TestMakeSourceList:
    """make_source_list : string -> list format notebook source (newline-trailing)."""

    def test_single_line_no_trailing_newline(self):
        # 1 line, no trailing \n -> ["line"] (no newline appended).
        assert make_source_list("line") == ["line"]

    def test_single_line_with_trailing_newline(self):
        # "line\n" splits into ["line", ""]; first gets \n, last empty dropped.
        assert make_source_list("line\n") == ["line\n"]

    def test_multi_line_trailing_newlines(self):
        result = make_source_list("a\nb\nc\n")
        assert result == ["a\n", "b\n", "c\n"]

    def test_multi_line_no_trailing_newline(self):
        result = make_source_list("a\nb\nc")
        assert result == ["a\n", "b\n", "c"]

    def test_empty_string(self):
        assert make_source_list("") == []

    def test_roundtrip_with_source_text(self):
        # source_text(make_source_list(text)) == text (roundtrip property).
        text = "line1\nline2\nline3"
        assert source_text({"source": make_source_list(text)}) == text


# --------------------------------------------------------------------------- #
#  transform_print_cell                                                        #
# --------------------------------------------------------------------------- #

class TestTransformPrintCell:
    """transform_print_cell : detecte CONTRACT+print, remplace par compile_and_deploy."""

    def _cell(self, source):
        """Build a code cell with source as a single string (list-form internally)."""
        return {"cell_type": "code", "source": source}

    def test_transforms_simple_contract(self):
        cell = self._cell(
            "CONTRACT = '''pragma solidity ^0.8.0;\ncontract Foo {}'''\n"
            "print(CONTRACT)\n"
        )
        result, transformed = transform_print_cell(cell)
        assert transformed is True
        out = "".join(result["source"]) if isinstance(result["source"], list) else result["source"]
        # print(CONTRACT) removed.
        assert "print(CONTRACT)" not in out
        # compile_and_deploy added with the contract var.
        assert "compile_and_deploy(w3, CONTRACT, deployer)" in out
        # Contract name lowercased as instance.
        assert "foo, receipt = compile_and_deploy" in out

    def test_constructor_params_commented_out(self):
        # Constructor with params -> deploy line is COMMENTED (args to adjust).
        cell = self._cell(
            "C = '''pragma solidity ^0.8.0;\n"
            "contract Token { constructor(uint256 supply) {} }'''\n"
            "print(C)\n"
        )
        result, transformed = transform_print_cell(cell)
        assert transformed is True
        out = "".join(result["source"]) if isinstance(result["source"], list) else result["source"]
        assert "# Deployer" in out
        # The deploy line is commented (constructor params need manual args).
        assert "# token, receipt = compile_and_deploy(w3, C, deployer)" in out

    def test_empty_constructor_not_commented(self):
        # Constructor with empty params () -> NOT treated as params -> active deploy.
        cell = self._cell(
            "C = '''pragma solidity ^0.8.0;\n"
            "contract Bare { constructor() {} }'''\n"
            "print(C)\n"
        )
        result, transformed = transform_print_cell(cell)
        assert transformed is True
        out = "".join(result["source"]) if isinstance(result["source"], list) else result["source"]
        # Empty constructor -> active (uncommented) deploy line.
        assert "bare, receipt = compile_and_deploy(w3, C, deployer)" in out
        assert "# bare, receipt" not in out

    def test_no_pragma_not_transformed(self):
        cell = self._cell("x = 1\nprint(x)\n")
        result, transformed = transform_print_cell(cell)
        assert transformed is False
        # Cell returned unchanged.
        assert result["source"] == "x = 1\nprint(x)\n"

    def test_no_print_not_transformed(self):
        cell = self._cell("CONTRACT = '''pragma solidity ^0.8.0; contract Foo {}'''\n")
        result, transformed = transform_print_cell(cell)
        assert transformed is False

    def test_no_triple_quote_var_not_transformed(self):
        # pragma + print but no triple-quote contract var assignment -> skip.
        cell = self._cell("pragma solidity in a comment\nprint('hi')\n")
        result, transformed = transform_print_cell(cell)
        assert transformed is False

    def test_contract_name_fallback_unknown(self):
        # pragma + triple-quote + print but no `contract Name` keyword -> "Unknown".
        cell = self._cell(
            "X = '''pragma solidity ^0.8.0; interface IFoo {}'''\n"
            "print(X)\n"
        )
        result, transformed = transform_print_cell(cell)
        assert transformed is True
        out = "".join(result["source"]) if isinstance(result["source"], list) else result["source"]
        # No `contract` keyword -> instance_name = "unknown".
        assert "unknown, receipt = compile_and_deploy" in out

    def test_result_source_is_list_format(self):
        # The transformed cell source must be a LIST (notebook format), not str.
        cell = self._cell(
            "CONTRACT = '''pragma solidity ^0.8.0; contract Foo {}'''\n"
            "print(CONTRACT)\n"
        )
        result, _ = transform_print_cell(cell)
        assert isinstance(result["source"], list)
        # Every element except the last ends with \n (notebook convention).
        for line in result["source"][:-1]:
            assert line.endswith("\n")

    def test_print_lines_all_removed(self):
        # Multiple print lines in the cell -> all removed.
        cell = self._cell(
            "CONTRACT = '''pragma solidity ^0.8.0; contract Foo {}'''\n"
            "print('deploying')\n"
            "print(CONTRACT)\n"
            "print('done')\n"
        )
        result, transformed = transform_print_cell(cell)
        assert transformed is True
        out = "".join(result["source"]) if isinstance(result["source"], list) else result["source"]
        assert "print('deploying')" not in out
        assert "print(CONTRACT)" not in out
        assert "print('done')" not in out

    def test_original_cell_mutated_in_place(self):
        # transform_print_cell mutates the passed cell dict (returns same object).
        cell = self._cell(
            "CONTRACT = '''pragma solidity ^0.8.0; contract Foo {}'''\n"
            "print(CONTRACT)\n"
        )
        result, transformed = transform_print_cell(cell)
        assert transformed is True
        # Same object (mutated in place).
        assert result is cell
        # Source now a list.
        assert isinstance(cell["source"], list)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
