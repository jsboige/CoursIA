#!/usr/bin/env python3
"""Tests for scripts/smartcontracts/update_sc_navigation.py.

Covers the five pure navigation helpers (relative_path, make_nav_line,
make_source_list, is_nav_cell, source_text) plus NOTEBOOKS/SHORT_NAMES data
integrity and a smoke test of update_notebook_nav() via tmp_path.

Import note: the module runs a top-level processing loop (`# Process all
notebooks`, line 226) on import that opens/rewrites 27 SmartContracts
notebooks from a hardcoded SC_BASE. To test the REAL function source without
triggering that side-effecting loop, we exec only the function-defining
prefix of the source (everything before `# Process all notebooks`). This
keeps NOTEBOOKS / SHORT_NAMES data + all six functions; only the loop is
dropped. Honest (real function code) and hermetic (no file I/O at import).

Executable both ways:
    py scripts/smartcontracts/tests/test_update_sc_navigation.py
    npx pytest scripts/smartcontracts/tests/test_update_sc_navigation.py
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
SRC_PATH = HERE.parent / "update_sc_navigation.py"

# Exec the function-defining prefix of the real source (drop the top-level
# processing loop) into a namespace.
_full = SRC_PATH.read_text(encoding="utf-8")
_prefix = _full.split("# Process all notebooks")[0]
_ns: dict = {}
exec(compile(_prefix, str(SRC_PATH), "exec"), _ns)

NOTEBOOKS = _ns["NOTEBOOKS"]
SHORT_NAMES = _ns["SHORT_NAMES"]
relative_path = _ns["relative_path"]
make_nav_line = _ns["make_nav_line"]
make_source_list = _ns["make_source_list"]
is_nav_cell = _ns["is_nav_cell"]
source_text = _ns["source_text"]
update_notebook_nav = _ns["update_notebook_nav"]


# ---------------------------------------------------------------------------
# relative_path
# ---------------------------------------------------------------------------

def test_relative_path_same_dir():
    assert relative_path("00-Foundations", "00-Foundations", "SC-0-Cypherpunk-Origins") == "SC-0-Cypherpunk-Origins.ipynb"


def test_relative_path_cross_dir():
    assert relative_path("01-Solidity-Foundation", "00-Foundations", "SC-0-Cypherpunk-Origins") == "../00-Foundations/SC-0-Cypherpunk-Origins.ipynb"


# ---------------------------------------------------------------------------
# make_nav_line -- boundary conditions
# ---------------------------------------------------------------------------

def test_nav_line_first_only_next():
    line = make_nav_line(0)
    assert "<<" not in line          # no prev at index 0
    assert ">>" in line
    # the next notebook is SC-1-Setup-Foundry -> "Setup Foundry"
    assert "Setup Foundry" in line


def test_nav_line_last_only_prev():
    line = make_nav_line(len(NOTEBOOKS) - 1)
    assert ">>" not in line          # no next at last index
    assert "<<" in line
    # the prev notebook is SC-25-Mainnet-Deploy -> "Mainnet Deploy"
    assert "Mainnet Deploy" in line


def test_nav_line_middle_has_both():
    line = make_nav_line(5)
    assert "<<" in line
    assert ">>" in line
    assert " | " in line             # joined by pipe


def test_nav_line_separator_is_pipe():
    line = make_nav_line(10)
    # exactly one " | " separator between prev and next
    assert line.count(" | ") == 1


def test_nav_line_prev_link_uses_relative_path():
    line = make_nav_line(1)
    # idx 1 prev is idx 0 (same 00-Foundations dir) -> relative "SC-0-....ipynb"
    assert "](SC-0-Cypherpunk-Origins.ipynb)" in line


# ---------------------------------------------------------------------------
# make_source_list
# ---------------------------------------------------------------------------

def test_make_source_list_two_lines_no_trailing_nl():
    assert make_source_list("a\nb") == ["a\n", "b"]


def test_make_source_list_trailing_nl():
    assert make_source_list("a\nb\n") == ["a\n", "b\n"]


def test_make_source_list_empty():
    assert make_source_list("") == []


def test_make_source_list_single_line():
    assert make_source_list("only") == ["only"]


def test_make_source_list_only_newlines():
    # "a\n\n" -> ["a\n", "\n"]  (two lines, last is empty but has its own \n)
    assert make_source_list("a\n\n") == ["a\n", "\n"]


# ---------------------------------------------------------------------------
# is_nav_cell
# ---------------------------------------------------------------------------

def _md(source):
    return {"cell_type": "markdown", "source": [source] if isinstance(source, str) else source}


def test_is_nav_cell_prev_link():
    assert is_nav_cell(_md("[<< Prev](path.ipynb)")) is True


def test_is_nav_cell_next_link():
    assert is_nav_cell(_md("[Next >>](path.ipynb)")) is True


def test_is_nav_cell_both():
    assert is_nav_cell(_md("[<< Prev](a.ipynb) | [Next >>](b.ipynb)")) is True


def test_is_nav_cell_plain_markdown():
    assert is_nav_cell(_md("Just some prose, no links here")) is False


def test_is_nav_cell_code_cell_rejected():
    cell = {"cell_type": "code", "source": ["[<< Prev](x.ipynb)"]}
    assert is_nav_cell(cell) is False


def test_is_nav_cell_accepts_text_arg():
    """is_nav_cell takes an optional pre-extracted text to avoid re-extraction."""
    assert is_nav_cell({"cell_type": "markdown"}, text="[Next >>](p.ipynb)") is True
    assert is_nav_cell({"cell_type": "markdown"}, text="no links") is False


# ---------------------------------------------------------------------------
# source_text
# ---------------------------------------------------------------------------

def test_source_text_str():
    assert source_text({"source": "hello"}) == "hello"


def test_source_text_list():
    assert source_text({"source": ["ab", "cd"]}) == "abcd"


def test_source_text_missing():
    assert source_text({}) == ""


# ---------------------------------------------------------------------------
# NOTEBOOKS / SHORT_NAMES data integrity
# ---------------------------------------------------------------------------

def test_every_notebook_has_short_name():
    for _dir, name in NOTEBOOKS:
        assert name in SHORT_NAMES, name


def test_notebooks_unique():
    names = [n for _, n in NOTEBOOKS]
    assert len(names) == len(set(names))


def test_make_nav_line_valid_for_every_index():
    """Smoke: make_nav_line must not raise for any valid index, and every line
    references exactly one or two notebooks (boundary or middle)."""
    for idx in range(len(NOTEBOOKS)):
        line = make_nav_line(idx)
        assert isinstance(line, str) and line
        # count of link targets
        n_links = line.count("](")
        assert n_links in (1, 2)


# ---------------------------------------------------------------------------
# update_notebook_nav -- smoke via tmp_path (takes nb_path explicitly)
# ---------------------------------------------------------------------------

def _write_nb(path: Path, cells: list[dict]) -> Path:
    nb = {"cells": cells, "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
    path.write_text(json.dumps(nb), encoding="utf-8")
    return path


def test_update_nav_adds_header_nav_when_absent(tmp_path):
    """For a notebook with no nav, update_notebook_nav adds the nav line into
    the header cell (cell[0], after the title heading) rather than appending a
    footer -- because the footer scan (last 3 cells) overlaps cell[0] and
    detects the just-inserted header nav. Observed behavior, asserted here."""
    nb_path = _write_nb(tmp_path / "nb.ipynb", [_md("# SC-X Title"), _md("body")])
    nav = make_nav_line(5)
    modified = update_notebook_nav(nb_path, nav, "SC-X")
    assert modified is True
    nb = json.loads(nb_path.read_text(encoding="utf-8"))
    header = "".join(nb["cells"][0]["source"])
    assert header.startswith("# SC-X Title")   # title preserved
    assert nav in header                        # nav inserted after title
    assert is_nav_cell(nb["cells"][0]) is True


def test_update_nav_replaces_existing_header_nav(tmp_path):
    nb_path = _write_nb(tmp_path / "nb.ipynb", [
        _md("[<< Old Prev](old.ipynb) | [Old Next >>](old.ipynb)"),
        _md("body"),
    ])
    nav = make_nav_line(5)
    modified = update_notebook_nav(nb_path, nav, "SC-X")
    assert modified is True
    nb = json.loads(nb_path.read_text(encoding="utf-8"))
    assert "".join(nb["cells"][0]["source"]) == nav
