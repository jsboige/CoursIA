"""Tests for scripts/notebook_tools/cell_order_ci.py — per-PR regression gate.

The gate fails only on a *regression* (a HIGH finding in head that was not in
base). Pre-existing findings do not block; a new notebook (no base) must be clean.
"""

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from cell_order_ci import regressions, high_signatures, main  # noqa: E402


def _md(source: str) -> dict:
    return {"cell_type": "markdown", "source": [source]}


def _write(path: Path, cells: list[dict]) -> Path:
    nb = {"cells": cells, "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
    path.write_text(json.dumps(nb), encoding="utf-8")
    return path


# A notebook with a genuine backwards section jump (## 2 after ## 3).
_BAD = [_md("## 2. A"), _md("## 3. B"), _md("## 2. oops")]
# A clean notebook.
_CLEAN = [_md("## 1. A"), _md("## 2. B"), _md("## 3. C")]


class TestHighSignatures:
    def test_none_base_is_empty(self):
        assert high_signatures("NONE") == set()
        assert high_signatures(None) == set()

    def test_missing_path_is_empty(self, tmp_path):
        assert high_signatures(str(tmp_path / "absent.ipynb")) == set()

    def test_clean_has_no_high(self, tmp_path):
        p = _write(tmp_path / "c.ipynb", _CLEAN)
        assert high_signatures(str(p)) == set()

    def test_bad_has_high(self, tmp_path):
        p = _write(tmp_path / "b.ipynb", _BAD)
        sigs = high_signatures(str(p))
        assert any(cat == "SECTION_ORDER" for cat, _ in sigs)


class TestRegressions:
    def test_new_clean_notebook_no_regression(self, tmp_path):
        head = _write(tmp_path / "h.ipynb", _CLEAN)
        assert regressions("NONE", str(head)) == []

    def test_new_bad_notebook_is_regression(self, tmp_path):
        head = _write(tmp_path / "h.ipynb", _BAD)
        assert len(regressions("NONE", str(head))) >= 1

    def test_preexisting_high_does_not_block(self, tmp_path):
        # Same HIGH finding in base and head -> not a regression.
        base = _write(tmp_path / "base.ipynb", _BAD)
        head = _write(tmp_path / "head.ipynb", _BAD)
        assert regressions(str(base), str(head)) == []

    def test_new_high_introduced_is_regression(self, tmp_path):
        base = _write(tmp_path / "base.ipynb", _CLEAN)
        head = _write(tmp_path / "head.ipynb", _BAD)
        assert len(regressions(str(base), str(head))) >= 1

    def test_fixing_high_is_not_regression(self, tmp_path):
        base = _write(tmp_path / "base.ipynb", _BAD)
        head = _write(tmp_path / "head.ipynb", _CLEAN)
        assert regressions(str(base), str(head)) == []

    def test_malformed_head_is_graceful(self, tmp_path):
        base = _write(tmp_path / "base.ipynb", _CLEAN)
        head = tmp_path / "head.ipynb"
        head.write_text("{not json", encoding="utf-8")
        assert regressions(str(base), str(head)) == []


class TestMainExitCodes:
    def test_exit_zero_on_clean(self, tmp_path):
        head = _write(tmp_path / "h.ipynb", _CLEAN)
        assert main(["--base", "NONE", "--head", str(head)]) == 0

    def test_exit_one_on_regression(self, tmp_path):
        head = _write(tmp_path / "h.ipynb", _BAD)
        assert main(["--base", "NONE", "--head", str(head)]) == 1
