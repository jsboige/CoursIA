#!/usr/bin/env python3
"""Tests for the H.3 null-exec pre-commit hook (notebook_tools/check_null_exec.py).

Adapted from the CoursIA-2 lane sub-grain (#9894) to the canonical
implementation in #9895: that impl reuses the ``validate_pr_notebooks.py``
predicates (lean / QC Cloud / PII carve-outs) and exposes positional files
(how pre-commit passes them) plus ``--all`` / ``--check`` / ``--explain`` /
``--verbose``. These tests drive it the way pre-commit does -- with positional
notebook paths -- and assert its actual messages.

Covers:
  - clean notebook (executed cells) -> exit 0
  - one H.3 violation (execution_count=null + outputs=[]) -> exit 1
  - comment-only / empty code cell skipped (NOT a violation)
  - PII carve-out (metadata.pii_no_output=true) absorbs null+empty cells
  - a cell with null count BUT outputs present is out of H.3 scope -> exit 0
  - unparseable notebook reported (cannot parse) -> exit 1
  - mixed clean + violation across two files -> exit 1
  - --explain prints the rule summary -> exit 0
  - --verbose emits a per-notebook OK/FAIL line -> exit 1, both tags present

Run:
    python -m pytest scripts/tests/test_check_null_exec.py -v
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

# Script under test (scripts/notebook_tools/check_null_exec.py).
SCRIPT = Path(__file__).resolve().parent.parent / "notebook_tools" / "check_null_exec.py"


def _mk_nb(tmp_path: Path, name: str, cells: list[dict], metadata: dict | None = None) -> Path:
    p = tmp_path / name
    payload = {"cells": cells, "metadata": metadata or {}}
    p.write_text(json.dumps(payload), encoding="utf-8")
    return p


def _code_cell(source: str, execution_count=None, outputs=None) -> dict:
    return {
        "cell_type": "code",
        "source": source,
        "metadata": {},
        "execution_count": execution_count,
        "outputs": outputs if outputs is not None else [],
    }


def _md_cell(source: str) -> dict:
    return {"cell_type": "markdown", "source": source, "metadata": {}}


def _run(*extra: str) -> subprocess.CompletedProcess:
    return subprocess.run(
        [sys.executable, str(SCRIPT), *extra],
        capture_output=True,
        text=True,
    )


# --- the strict H.3 rule ---


def test_clean_notebook(tmp_path: Path):
    nb = _mk_nb(
        tmp_path,
        "ok.ipynb",
        [
            _md_cell("# title"),
            _code_cell("x = 1", execution_count=1, outputs=[{"text": "ok"}]),
            _code_cell("y = 2", execution_count=2, outputs=[{"text": "ok"}]),
        ],
    )
    res = _run(str(nb))
    assert res.returncode == 0, f"unexpected fail: {res.stderr}"


def test_h3_violation(tmp_path: Path):
    nb = _mk_nb(
        tmp_path,
        "bad.ipynb",
        [_code_cell("x = 1", execution_count=None, outputs=[])],
    )
    res = _run(str(nb))
    assert res.returncode == 1
    # Canonical message (#9895): "N un-executed cell(s) refused".
    assert "un-executed cell(s)" in res.stderr
    assert "execution_count=null + outputs=[]" in res.stderr


def test_mixed_clean_and_violation(tmp_path: Path):
    ok = _mk_nb(tmp_path, "ok.ipynb", [_code_cell("x = 1", execution_count=1, outputs=[{"t": 1}])])
    bad = _mk_nb(tmp_path, "bad.ipynb", [_code_cell("y = 2", execution_count=None, outputs=[])])
    res = _run(str(ok), str(bad))
    assert res.returncode == 1
    assert "1 un-executed cell(s)" in res.stderr


# --- the carve-outs / tolerances ---


def test_comment_only_cell_skipped(tmp_path: Path):
    """A code cell whose source is only comments is not executable -> skipped."""
    nb = _mk_nb(
        tmp_path,
        "comments.ipynb",
        [
            _code_cell("# TODO: explanation only", execution_count=None, outputs=[]),
            _code_cell("// C# comment-only", execution_count=None, outputs=[]),
            _code_cell("x = 1", execution_count=1, outputs=[{"text": "ok"}]),
        ],
    )
    res = _run(str(nb))
    assert res.returncode == 0, f"comment-only cells must be skipped: {res.stderr}"


def test_empty_code_cell_skipped(tmp_path: Path):
    """An empty source code cell is not executable -> skipped."""
    nb = _mk_nb(
        tmp_path,
        "empty.ipynb",
        [_code_cell("", execution_count=None, outputs=[])],
    )
    res = _run(str(nb))
    assert res.returncode == 0, f"empty cell must be skipped: {res.stderr}"


def test_pii_carve_out_absorbs_violations(tmp_path: Path):
    """metadata.pii_no_output=true: empty outputs are the compliant state."""
    nb = _mk_nb(
        tmp_path,
        "pii.ipynb",
        [
            _code_cell("x = 1", execution_count=None, outputs=[]),
            _code_cell("y = 2", execution_count=None, outputs=[]),
        ],
        metadata={"pii_no_output": True},
    )
    res = _run(str(nb))
    assert res.returncode == 0, f"PII carve-out must absorb: {res.stderr}"


def test_violation_with_outputs_is_not_flagged(tmp_path: Path):
    """execution_count=null BUT outputs != [] is OUT OF H.3 SCOPE.

    H.3 mandates BOTH conditions (null count AND empty outputs). A cell with
    cleared outputs on a real run is unusual but distinct from null-exec.
    """
    nb = _mk_nb(
        tmp_path,
        "weird.ipynb",
        [_code_cell("x = 1", execution_count=None, outputs=[{"text": "ok"}])],
    )
    res = _run(str(nb))
    assert res.returncode == 0, f"outputs-present must be out of scope: {res.stderr}"


def test_dotnet_comment_cell_skipped(tmp_path: Path):
    """C#/.NET-Interactive-shaped comment cell is skipped; a real cell must run."""
    nb = _mk_nb(
        tmp_path,
        "csharp.ipynb",
        [
            _code_cell("// TODO: real C# later", execution_count=None, outputs=[]),
            _code_cell('Console.WriteLine("ok");', execution_count=1, outputs=[{"text": "ok"}]),
        ],
    )
    res = _run(str(nb))
    assert res.returncode == 0, f"dotnet comment cell must be skipped: {res.stderr}"


# --- operational robustness ---


def test_parse_error_reported(tmp_path: Path):
    """A non-JSON notebook is reported (cannot parse), refusing the commit."""
    nb = tmp_path / "broken.ipynb"
    nb.write_text("not-a-json", encoding="utf-8")
    res = _run(str(nb))
    assert res.returncode == 1
    assert "cannot parse" in res.stderr


def test_no_targets_is_clean():
    """No files passed -> exit 0 (pre-commit with no staged notebooks)."""
    res = _run()
    assert res.returncode == 0


# --- CLI ergonomics ---


def test_explain_prints_rule(tmp_path: Path):
    res = _run("--explain")
    assert res.returncode == 0
    assert "H.3" in res.stdout


def test_verbose_emits_per_notebook(tmp_path: Path):
    ok = _mk_nb(tmp_path, "ok.ipynb", [_code_cell("x = 1", execution_count=1, outputs=[{"t": 1}])])
    bad = _mk_nb(tmp_path, "bad.ipynb", [_code_cell("y = 2", execution_count=None, outputs=[])])
    res = _run("--verbose", str(ok), str(bad))
    assert res.returncode == 1, f"unexpected pass: {res.stderr}"
    assert "OK" in res.stderr and "FAIL" in res.stderr, (
        f"expected OK + FAIL on stderr, got: {res.stderr}"
    )


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))
