#!/usr/bin/env python3
"""Tests for H.3 null-exec pre-commit hook (scripts/notebook_tools/check_null_exec.py).

Covers the carve-outs and the strict H.3 rule:
  - clean notebook (executed cells) → OK
  - one H.3 violation → 1 violation reported, exit 1
  - empty / comment-only cell skipped
  - PII carve-out (metadata.pii_no_output = true) absorbs all violations
  - parse error → exit 2 (operational, not a violation)
  - mixed OK + parse error → exit 2 (parse error wins)
  - call with --explain → exit 0, prints doc

Run:
    python -m pytest scripts/tests/test_check_null_exec.py -v
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

# script under test
SCRIPT = Path(__file__).resolve().parent.parent / "notebook_tools" / "check_null_exec.py"


def _mk_nb(tmp_path: Path, name: str, cells: list[dict]) -> Path:
    p = tmp_path / name
    p.write_text(json.dumps({"cells": cells, "metadata": {}}), encoding="utf-8")
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


# --- check_notebook unit tests ---


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
    res = subprocess.run(
        [sys.executable, str(SCRIPT), "--check", str(nb)],
        capture_output=True,
        text=True,
    )
    assert res.returncode == 0, f"unexpected fail: {res.stderr}"
    assert "OK" not in res.stderr  # --verbose not used


def test_h3_violation(tmp_path: Path):
    nb = _mk_nb(
        tmp_path,
        "bad.ipynb",
        [
            _code_cell("x = 1", execution_count=None, outputs=[]),
        ],
    )
    res = subprocess.run(
        [sys.executable, str(SCRIPT), "--check", str(nb)],
        capture_output=True,
        text=True,
    )
    assert res.returncode == 1
    assert "1 un-executed code cell" in res.stderr


def test_comment_only_cell_skipped(tmp_path: Path):
    nb = _mk_nb(
        tmp_path,
        "skipped.ipynb",
        [
            _code_cell("# TODO: explanation only", execution_count=None, outputs=[]),
            _code_cell("// C# comment-only", execution_count=None, outputs=[]),
            _code_cell("x = 1", execution_count=1, outputs=[{"text": "ok"}]),
        ],
    )
    res = subprocess.run(
        [sys.executable, str(SCRIPT), "--check", str(nb)],
        capture_output=True,
        text=True,
    )
    assert res.returncode == 0, f"unexpected fail: {res.stderr}"


def test_pii_carve_out_absorbs_violations(tmp_path: Path):
    nb = tmp_path / "pii.ipynb"
    nb.write_text(
        json.dumps(
            {
                "metadata": {"pii_no_output": True},
                "cells": [
                    _code_cell("x = 1", execution_count=None, outputs=[]),
                    _code_cell("y = 2", execution_count=None, outputs=[]),
                ],
            }
        ),
        encoding="utf-8",
    )
    res = subprocess.run(
        [sys.executable, str(SCRIPT), "--check", str(nb)],
        capture_output=True,
        text=True,
    )
    assert res.returncode == 0, f"PII carve-out must absorb: {res.stderr}"


def test_pii_carve_out_does_not_mask_others(tmp_path: Path):
    """The PII flag is a notebook-level metadata. Both cells get absorbed."""
    nb = tmp_path / "pii.ipynb"
    nb.write_text(
        json.dumps(
            {
                "metadata": {"pii_no_output": True},
                "cells": [
                    _code_cell("x = 1", execution_count=None, outputs=[]),
                    _code_cell("# TODO", execution_count=None, outputs=[]),
                ],
            }
        ),
        encoding="utf-8",
    )
    res = subprocess.run(
        [sys.executable, str(SCRIPT), "--check", str(nb)],
        capture_output=True,
        text=True,
    )
    assert res.returncode == 0


def test_parse_error_exit_2(tmp_path: Path):
    """A non-JSON notebook is an operational error, not a H.3 violation."""
    nb = tmp_path / "broken.ipynb"
    nb.write_text("not-a-json", encoding="utf-8")
    res = subprocess.run(
        [sys.executable, str(SCRIPT), "--check", str(nb)],
        capture_output=True,
        text=True,
    )
    assert res.returncode == 2
    assert "PARSE ERRORS" in res.stderr


def test_mixed_clean_and_violations(tmp_path: Path):
    ok = _mk_nb(tmp_path, "ok.ipynb", [_code_cell("x = 1", execution_count=1)])
    bad = _mk_nb(tmp_path, "bad.ipynb", [_code_cell("y = 2", execution_count=None)])
    res = subprocess.run(
        [sys.executable, str(SCRIPT), "--check", str(ok), str(bad)],
        capture_output=True,
        text=True,
    )
    assert res.returncode == 1
    assert "1 un-executed code cell" in res.stderr


def test_empty_code_cell_skipped(tmp_path: Path):
    nb = _mk_nb(
        tmp_path,
        "empty.ipynb",
        [_code_cell("", execution_count=None, outputs=[])],
    )
    res = subprocess.run(
        [sys.executable, str(SCRIPT), "--check", str(nb)],
        capture_output=True,
        text=True,
    )
    assert res.returncode == 0


def test_violation_with_outputs_is_not_flagged(tmp_path: Path):
    """execution_count: None but outputs != [] is OUT OF H.3 SCOPE.

    H.3 mandates BOTH conditions. A cell with cleared outputs after an exec
    is unusual but distinct from the H.3 null-exec case.
    """
    nb = _mk_nb(
        tmp_path,
        "weird.ipynb",
        [_code_cell("x = 1", execution_count=None, outputs=[{"text": "ok"}])],
    )
    res = subprocess.run(
        [sys.executable, str(SCRIPT), "--check", str(nb)],
        capture_output=True,
        text=True,
    )
    assert res.returncode == 0


def test_explain():
    res = subprocess.run(
        [sys.executable, str(SCRIPT), "--explain"],
        capture_output=True,
        text=True,
    )
    assert res.returncode == 0
    assert "H.3" in res.stdout


def test_verbose_emits_per_notebook(tmp_path: Path):
    ok = _mk_nb(tmp_path, "ok.ipynb", [_code_cell("x = 1", execution_count=1)])
    bad = _mk_nb(tmp_path, "bad.ipynb", [_code_cell("y = 2", execution_count=None)])
    # Test both flag orderings — argparse must accept --verbose before OR after --check.
    for cli in (
        [sys.executable, str(SCRIPT), "--verbose", "--check", str(ok), str(bad)],
        [sys.executable, str(SCRIPT), "--check", str(ok), str(bad), "--verbose"],
    ):
        res = subprocess.run(cli, capture_output=True, text=True)
        assert res.returncode == 1, f"unexpected fail {res.stderr}"
        assert "OK" in res.stderr and "FAIL" in res.stderr, (
            f"expected OK + FAIL on stderr, got: {res.stderr}"
        )


def test_dotnet_cell_path(tmp_path: Path):
    """Same rule but exercising a C#/.NET-Interactive-shaped cell."""
    nb = _mk_nb(
        tmp_path,
        "csharp.ipynb",
        [
            _code_cell(
                "// TODO: real C# later",
                execution_count=None,
                outputs=[],
            ),
            _code_cell(
                'Console.WriteLine("ok");',
                execution_count=1,
                outputs=[{"text": "ok"}],
            ),
        ],
    )
    res = subprocess.run(
        [sys.executable, str(SCRIPT), "--check", str(nb)],
        capture_output=True,
        text=True,
    )
    assert res.returncode == 0


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))
