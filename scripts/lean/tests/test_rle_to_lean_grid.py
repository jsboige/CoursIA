#!/usr/bin/env python3
"""Tests for rle_to_lean_grid.py (#19989, Part of #17465).

Dual-mode: runnable directly (``python scripts/lean/tests/test_rle_to_lean_grid.py``)
or under pytest (auto-collected by scripts-tests.yml on any ``scripts/**`` change).

Locks the contract of the RLE->Grid converter:
  - parse the Golly RLE body (``b``/``o``/``$``/``!`` + count runs);
  - ignore ``#`` comments and the ``x = ..., y = ..., rule = ...`` header;
  - normalize the bounding-box corner to (0, 0), rows sorted;
  - reject unknown characters, missing header, body overflowing the header
    (a truncated or corrupt pattern must never yield a plausible grid);
  - emit a Lean ``def name : Grid := [...]`` literal (no trailing comma).
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

SCRIPT = Path(__file__).resolve().parent.parent / "rle_to_lean_grid.py"
sys.path.insert(0, str(SCRIPT.parent))

from rle_to_lean_grid import RleError, emit_lean, normalize, parse_rle  # noqa: E402


def _rle(body: str, header: str = "x = 5, y = 5, rule = B3/S23") -> str:
    return f"#C comment\n{header}\n{body}\n"


def test_glider_parse_and_normalize():
    width, height, cells = parse_rle(_rle("3bo$2bo$3o!"))
    assert (width, height) == (5, 5)
    assert sorted(cells) == [(0, 2), (1, 2), (2, 1), (2, 2), (3, 0)]


def test_normalize_shifts_corner_to_origin():
    assert normalize([(5, 7), (6, 7), (6, 8)]) == [(0, 0), (1, 0), (1, 1)]


def test_multiline_body_and_row_runs():
    # glider ecrit sur plusieurs lignes, avec un ``2$`` (une ligne vide)
    _, _, cells = parse_rle(_rle("3bo$2bo2$3o!"))
    assert sorted(cells) == [(0, 3), (1, 3), (2, 1), (2, 3), (3, 0)]


def test_unknown_character_is_rle_error():
    with pytest.raises(RleError):
        parse_rle(_rle("3bo$2bx$3o!"))


def test_missing_header_is_rle_error():
    with pytest.raises(RleError):
        parse_rle("3bo$2bo$3o!")


def test_body_overflowing_header_is_rle_error():
    with pytest.raises(RleError):
        parse_rle(_rle("6o!", header="x = 5, y = 5, rule = B3/S23"))


def test_emit_lean_literal_shape():
    lean = emit_lean("unitcellInitial", [(0, 0), (1, 0), (1, 1)], per_line=2)
    assert lean.startswith("def unitcellInitial : Grid := [")
    assert "(0, 0), (1, 0)," in lean
    assert lean.rstrip().endswith("]")
    assert "],]" not in lean  # pas de virgule pendante sur le dernier chunk


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))
