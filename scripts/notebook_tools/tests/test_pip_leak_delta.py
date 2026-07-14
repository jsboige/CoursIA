#!/usr/bin/env python3
"""Tests for pip_leak_delta (HIGH delta guard, See #6314).

Covers:
    * count_high / high_by_file classification wiring.
    * delta == 0  -> exit 0 (inherited leaks tolerated).
    * delta < 0  -> exit 0 (PR fixes leaks, encouraged).
    * delta > 0  -> exit 1 + stderr names the newly-leaking file.
    * malformed JSON -> exit 2.

Run:
    pytest scripts/notebook_tools/tests/test_pip_leak_delta.py
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

SCRIPT_DIR = Path(__file__).resolve().parent.parent  # scripts/notebook_tools/
sys.path.insert(0, str(SCRIPT_DIR))

import pip_leak_delta  # noqa: E402


def _audit(nb_specs):
    """Build a minimal audit-JSON document from (file, [classification,...])."""
    return [
        {
            "file": f,
            "total_cells": 5,
            "code_cells": 5,
            "occurrences": [
                {"cell_index": i, "classification": cls, "source_preview": "..."}
                for i, cls in enumerate(classes)
            ],
        }
        for f, classes in nb_specs
    ]


# --- pure helpers -----------------------------------------------------------

def test_count_high_only_counts_unconditional():
    doc = _audit(
        [
            ("a.ipynb", ["UNCONDITIONAL_BASH", "CONDITIONAL_TRY", "NON_BASH"]),
            ("b.ipynb", ["UNCONDITIONAL_SYS", "UNCONDITIONAL_BASH"]),
            ("c.ipynb", ["CONDITIONAL_TRY", "NON_BASH"]),
        ]
    )
    assert pip_leak_delta.count_high(doc) == 3


def test_high_by_file_groups_cells():
    doc = _audit([("a.ipynb", ["UNCONDITIONAL_BASH", "UNCONDITIONAL_SYS", "NON_BASH"])])
    by = pip_leak_delta.high_by_file(doc)
    assert by == {"a.ipynb": [0, 1]}


# --- CLI exit codes ---------------------------------------------------------

def _run(tmp_path, base_doc, head_doc):
    base = tmp_path / "base.json"
    head = tmp_path / "head.json"
    base.write_text(json.dumps(base_doc), encoding="utf-8")
    head.write_text(json.dumps(head_doc), encoding="utf-8")
    return pip_leak_delta.main([str(base), str(head)])


def test_delta_zero_exit_0_inherited_tolerated(capsys, tmp_path):
    doc = _audit([("leak.ipynb", ["UNCONDITIONAL_BASH"])])
    rc = _run(tmp_path, doc, doc)
    out = capsys.readouterr().out
    assert rc == 0
    assert "delta=+0" in out
    assert "tolerated" in out


def test_delta_negative_exit_0_fix_encouraged(capsys, tmp_path):
    base = _audit([("a.ipynb", ["UNCONDITIONAL_BASH"]), ("b.ipynb", ["UNCONDITIONAL_BASH"])])
    head = _audit([("a.ipynb", ["UNCONDITIONAL_BASH"])])  # b fixed
    rc = _run(tmp_path, base, head)
    out = capsys.readouterr().out
    assert rc == 0
    assert "delta=-1" in out


def test_delta_positive_exit_1_names_new_file(capsys, tmp_path):
    base = _audit([("a.ipynb", ["UNCONDITIONAL_BASH"])])
    head = _audit(
        [
            ("a.ipynb", ["UNCONDITIONAL_BASH"]),  # inherited, unchanged
            ("new.ipynb", ["UNCONDITIONAL_BASH"]),  # NEW leak introduced
        ]
    )
    rc = _run(tmp_path, base, head)
    captured = capsys.readouterr()
    assert rc == 1
    assert "delta=+1" in captured.out
    assert "new.ipynb" in captured.err


def test_worsened_existing_file_exit_1(capsys, tmp_path):
    base = _audit([("a.ipynb", ["UNCONDITIONAL_BASH"])])
    head = _audit([("a.ipynb", ["UNCONDITIONAL_BASH", "UNCONDITIONAL_SYS"])])
    rc = _run(tmp_path, base, head)
    assert rc == 1
    assert "a.ipynb" in capsys.readouterr().err


def test_malformed_json_exit_2(tmp_path):
    base = tmp_path / "base.json"
    head = tmp_path / "head.json"
    base.write_text("{not json", encoding="utf-8")
    head.write_text("[]", encoding="utf-8")
    rc = pip_leak_delta.main([str(base), str(head)])
    assert rc == 2
