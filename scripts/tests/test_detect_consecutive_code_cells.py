#!/usr/bin/env python3
"""Unit tests for detect_consecutive_code_cells.py -- the adjacency organ (#12797).

The rule (#12797, decision user 2026-08-24): a run of >=2 consecutive code cells
(no markdown in between) is an opportunity for an intermediate markdown cell, or
otherwise a merge pattern. The detector is ADVISORY: it always exits 0, the
signal is the label the workflow poses.

Run:
    python -m pytest scripts/tests/test_detect_consecutive_code_cells.py
"""
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "notebook_tools"))

import detect_consecutive_code_cells as dcc  # noqa: E402


def _nb(cell_types):
    """Build an nbformat-shaped dict from a sequence of cell_type strings."""
    return {
        "cells": [{"cell_type": t, "source": "x", "outputs": [], "execution_count": 1}
                  for t in cell_types]
    }


def _write(path: Path, data: dict) -> Path:
    path.write_text(json.dumps(data), encoding="utf-8")
    return path


# ---- pure functions: _consecutive_runs / _measure ----------------------------

def test_runs_detects_maximal_block():
    runs = dcc._consecutive_runs(_nb(["code", "code", "markdown", "code"]))
    assert [(r.start, r.length) for r in runs] == [(0, 2), (3, 1)]


def test_runs_no_code():
    assert dcc._consecutive_runs(_nb(["markdown", "markdown"])) == []


def test_measure_single_run_at_floor():
    # run of exactly CONSECUTIVE_MIN qualifies.
    max_run, n_qual, n_code = dcc._measure(_nb(["markdown", "code", "code"]))
    assert (max_run, n_qual, n_code) == (2, 1, 2)


def test_measure_run_below_floor_does_not_qualify():
    max_run, n_qual, n_code = dcc._measure(_nb(["code", "markdown"]))
    assert (max_run, n_qual, n_code) == (1, 0, 1)


def test_measure_long_run_counts_once():
    max_run, n_qual, n_code = dcc._measure(_nb(["code", "code", "code", "code"]))
    assert (max_run, n_qual, n_code) == (4, 1, 4)


def test_measure_zero_code_cells_is_ok_not_unmeasured():
    # Unlike density, no code cell is NOT unmeasured here: there is no division
    # by zero, a notebook of only markdown has no adjacency defect.
    max_run, n_qual, n_code = dcc._measure(_nb(["markdown"]))
    assert (max_run, n_qual, n_code) == (0, 0, 0)


# ---- check_paths: validation of the classification exemption ----------------

def test_consecutive_detected(tmp_path):
    p = _write(tmp_path / "a.ipynb", _nb(["code", "code", "markdown"]))
    result = dcc.check_paths([p])
    assert len(result.consecutive) == 1
    v = result.consecutive[0]
    assert v.status == "consecutive" and v.max_run == 2 and v.runs == 1


def test_ok_when_no_run(tmp_path):
    p = _write(tmp_path / "a.ipynb", _nb(["code", "markdown", "code"]))
    result = dcc.check_paths([p])
    assert len(result.ok) == 1 and result.ok[0].status == "ok"


def test_setup_exempt(tmp_path):
    p = _write(tmp_path / "00-1-Setup.ipynb", _nb(["code", "code", "code"]))
    result = dcc.check_paths([p])
    assert len(result.exempt) == 1 and result.exempt[0].kind == "setup"


def test_out_of_corpus_folder_exempt(tmp_path):
    # A stem with the "template" marker is classified out-of-corpus (template
    # kind); classify_notebook keys off path markers, not off /tmp location.
    p = _write(tmp_path / "exercise-template.ipynb", _nb(["code", "code"]))
    result = dcc.check_paths([p])
    assert len(result.exempt) == 1 and result.exempt[0].kind == "template"


def test_unmeasured_on_corrupt_json(tmp_path):
    p = tmp_path / "broken.ipynb"
    p.write_text("{not valid json", encoding="utf-8")
    result = dcc.check_paths([p])
    assert len(result.unmeasured) == 1 and "cannot parse" in result.unmeasured[0].detail


# ---- payload shape -----------------------------------------------------------

def test_payload_shape_exposed(tmp_path):
    good = _write(tmp_path / "good.ipynb", _nb(["code", "markdown", "code"]))
    bad = _write(tmp_path / "bad.ipynb", _nb(["code", "code"]))
    result = dcc.check_paths([good, bad])
    payload = result.as_payload()
    assert payload["summary"]["judged"] == 2
    assert payload["summary"]["consecutive"] == 1
    assert payload["labels"]["consecutive"]["name"] == dcc.LABEL_NAME
    assert payload["summary"]["unmeasured"] == 0
