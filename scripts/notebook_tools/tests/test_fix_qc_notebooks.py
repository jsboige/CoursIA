"""Tests for scripts/notebook_tools/fix_qc_notebooks.py — QC notebook fixers.

The module applies targeted string-rewrite fixes to QuantConnect notebooks
(ML-XGBoost, RL-Portfolio, etc.) that had broken under partial-asset data.
The fix_* functions are one-shot transformations, BUT they are re-invoked
whenever a QC notebook is regenerated and loses its guard — so the matching
and rewrite logic carries real regression value.

Coverage:
- _set_source: pure helper — splits source into nbformat lines, clears outputs/execution_count
- _indent: pure helper — indents non-blank lines, preserves blank lines (subtle)
- fix_ml_xgboost: integration — detects target cells by string markers, applies
  guards, counts fixed cells, writes notebook, returns count; no-op when markers absent

The module imports only stdlib (json, sys, os) at top level — hermetic.
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from fix_qc_notebooks import _set_source, _indent, fix_ml_xgboost


# ---------------------------------------------------------------------------
# _set_source
# ---------------------------------------------------------------------------

def test_set_source_splits_multiline_into_nbformat_lines():
    cell = {}
    _set_source(cell, "a\nb\nc")
    # nbformat convention: each line except the last carries a trailing newline
    assert cell["source"] == ["a\n", "b\n", "c"]


def test_set_source_single_line_no_trailing_newline():
    cell = {}
    _set_source(cell, "only line")
    assert cell["source"] == ["only line"]


def test_set_source_clears_outputs():
    cell = {"outputs": [{"data": "stale"}]}
    _set_source(cell, "x")
    assert cell["outputs"] == []


def test_set_source_resets_execution_count():
    cell = {"execution_count": 7}
    _set_source(cell, "x")
    assert cell["execution_count"] is None


def test_set_source_empty_string():
    cell = {}
    _set_source(cell, "")
    assert cell["source"] == [""]


def test_set_source_preserves_trailing_newline_as_separate_line_pair():
    # "a\n" splits to ["a\n", ""] — trailing newline yields a final empty element
    cell = {}
    _set_source(cell, "a\n")
    assert cell["source"] == ["a\n", ""]


# ---------------------------------------------------------------------------
# _indent
# ---------------------------------------------------------------------------

def test_indent_indents_all_nonblank_lines():
    assert _indent("a\nb", 2) == "  a\n  b"


def test_indent_preserves_blank_lines_unindented():
    # Subtle contract: blank lines are NOT indented (avoids trailing whitespace)
    result = _indent("a\n\nb", 2)
    assert result == "  a\n\n  b"


def test_indent_zero_spaces_is_identity_for_nonblank():
    assert _indent("a\nb", 0) == "a\nb"


def test_indent_empty_string():
    assert _indent("", 4) == ""


def test_indent_single_line():
    assert _indent("hello", 3) == "   hello"


def test_indent_only_blank_lines():
    assert _indent("\n\n", 2) == "\n\n"


def test_indent_four_spaces():
    assert _indent("x", 4) == "    x"


def test_indent_mixed_blank_and_content():
    src = "line1\n\nline2\n\n\nline3"
    result = _indent(src, 2)
    assert result == "  line1\n\n  line2\n\n\n  line3"


# ---------------------------------------------------------------------------
# fix_ml_xgboost — integration with notebook fixtures
# ---------------------------------------------------------------------------

def _make_notebook(cells_src: list[str]) -> dict:
    """Build a minimal valid notebook with code cells from source strings."""
    return {
        "cells": [
            {
                "cell_type": "code",
                "execution_count": None,
                "metadata": {},
                "outputs": [],
                "source": [src],
            }
            for src in cells_src
        ],
        "metadata": {"kernelspec": {"name": "python3", "display_name": "Python 3"}},
        "nbformat": 4,
        "nbformat_minor": 5,
    }


def _write_nb(tmp_path: Path, nb: dict) -> Path:
    p = tmp_path / "test_quantbook.ipynb"
    p.write_text(json.dumps(nb), encoding="utf-8")
    return p


def test_fix_ml_xgboost_noop_when_markers_absent(tmp_path):
    """A notebook without the target markers is unchanged; returns 0."""
    nb = _make_notebook(["import pandas as pd\nprint('hello')"])
    p = _write_nb(tmp_path, nb)
    fixed = fix_ml_xgboost(str(p))
    assert fixed == 0
    # Notebook content unchanged
    result = json.loads(p.read_text(encoding="utf-8"))
    assert result["cells"][0]["source"] == ["import pandas as pd\nprint('hello')"]


def test_fix_ml_xgboost_detects_data_load_cell(tmp_path):
    """The data-load cell with both markers triggers a fix (fixed >= 1)."""
    marker_src = (
        "# Top 15 actions tech\ncloses = history\n"
        'print(f"Données: {closes.shape[0]} jours, {closes.shape[1]} actifs")\n'
        "closes.head()"
    )
    nb = _make_notebook([marker_src])
    p = _write_nb(tmp_path, nb)
    fixed = fix_ml_xgboost(str(p))
    assert fixed >= 1
    result = json.loads(p.read_text(encoding="utf-8"))
    # The guard (ticker filtering) was injected
    modified_src = "".join(result["cells"][0]["source"])
    assert "available_tickers" in modified_src or "Filter tickers" in modified_src


def test_ml_xgboost_marker_without_replace_target_no_fix(tmp_path):
    """Markers present but the replaceable print absent => no change for that cell."""
    # Has the detection markers but NOT the exact replace target string
    src = "# Top 15 actions tech\ncloses = history\nprint('something else entirely')"
    nb = _make_notebook([src])
    p = _write_nb(tmp_path, nb)
    fixed = fix_ml_xgboost(str(p))
    assert fixed == 0


def test_fix_ml_xgboost_only_one_marker_insufficient(tmp_path):
    """A single marker (Top 15) without 'closes = history' does not trigger."""
    src = "# Top 15 actions tech\nprint('no closes assignment here')"
    nb = _make_notebook([src])
    p = _write_nb(tmp_path, nb)
    fixed = fix_ml_xgboost(str(p))
    assert fixed == 0


def test_fix_ml_xgboost_writes_valid_notebook(tmp_path):
    """After fixing, the written file is valid JSON with nbformat 4."""
    marker_src = (
        "# Top 15 actions tech\ncloses = history\n"
        'print(f"Données: {closes.shape[0]} jours, {closes.shape[1]} actifs")\n'
        "closes.head()"
    )
    nb = _make_notebook([marker_src])
    p = _write_nb(tmp_path, nb)
    fix_ml_xgboost(str(p))
    result = json.loads(p.read_text(encoding="utf-8"))
    assert result["nbformat"] == 4
    assert "cells" in result


def test_fix_ml_xgboost_clears_outputs_on_modified_cell(tmp_path):
    """A cell that gets fixed has its outputs/execution_count reset via _set_source."""
    # Build a cell WITH stale outputs + the markers + replace target
    cell = {
        "cell_type": "code",
        "execution_count": 5,
        "metadata": {},
        "outputs": [{"output_type": "stream", "text": "stale"}],
        "source": [
            "# Top 15 actions tech\ncloses = history\n"
            'print(f"Données: {closes.shape[0]} jours, {closes.shape[1]} actifs")\n'
            "closes.head()"
        ],
    }
    nb = {"cells": [cell], "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
    p = _write_nb(tmp_path, nb)
    fix_ml_xgboost(str(p))
    result = json.loads(p.read_text(encoding="utf-8"))
    assert result["cells"][0]["outputs"] == []
    assert result["cells"][0]["execution_count"] is None


def test_fix_ml_xgboost_idempotent_second_run_no_additional_fix(tmp_path):
    """Re-running the fixer on an already-fixed notebook does not double-fix."""
    marker_src = (
        "# Top 15 actions tech\ncloses = history\n"
        'print(f"Données: {closes.shape[0]} jours, {closes.shape[1]} actifs")\n'
        "closes.head()"
    )
    nb = _make_notebook([marker_src])
    p = _write_nb(tmp_path, nb)
    first = fix_ml_xgboost(str(p))
    second = fix_ml_xgboost(str(p))
    assert first >= 1
    # Second run: the replace target is gone, so no further fix
    assert second == 0


def test_fix_ml_xgboost_multiple_cells_counted(tmp_path):
    """Multiple distinct target cells each increment the fixed counter."""
    data_load = (
        "# Top 15 actions tech\ncloses = history\n"
        'print(f"Données: {closes.shape[0]} jours, {closes.shape[1]} actifs")\n'
        "closes.head()"
    )
    feature_cell = (
        "def calculate_xgb_features(closes, volumes, highs, lows):\n"
        "    pass\n"
        "features = calculate_xgb_features(closes, volumes, highs, lows)\n"
        "# Calculer les features\nfeatures = calculate_xgb_features(closes, volumes, highs, lows)"
    )
    nb = _make_notebook([data_load, feature_cell])
    p = _write_nb(tmp_path, nb)
    fixed = fix_ml_xgboost(str(p))
    assert fixed >= 2
