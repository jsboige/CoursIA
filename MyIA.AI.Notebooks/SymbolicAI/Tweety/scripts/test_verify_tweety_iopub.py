# -*- coding: utf-8 -*-
"""Regression tests for verify_all_tweety.execute_cell_by_cell.

Pins the IOPub-drain fix: after the cwd setup (`os.chdir`), the kernel emits
status:busy then status:idle on the IOPub channel. get_shell_msg() only drains
the SHELL reply, leaving those two messages queued. The first cell's collection
loop then reads the stale status:idle and breaks immediately, silently dropping
cell 0's real output (which lands in cell 1's loop).

Before the fix this test FAILED firsthand:
    cell0 preview=''            (its 'HELLO_FROM_CELL_0' was lost)
    cell1 preview='HELLO_FROM_CELL_0\\n'   (cell 0's orphaned output)

After the fix each cell captures its OWN output.

These tests spin a real python3 kernel via jupyter_client (available on every
worker per rule F). They are skipped, not failed, if jupyter_client is absent.
"""

from __future__ import annotations

import json
import os
import pathlib
import sys
import tempfile

import pytest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

try:
    import jupyter_client  # noqa: F401
    HAS_JUPYTER = True
except Exception:
    HAS_JUPYTER = False

from verify_all_tweety import execute_cell_by_cell  # noqa: E402

pytestmark = pytest.mark.skipif(not HAS_JUPYTER,
                                reason="jupyter_client not installed")


def _write_notebook(sources: list) -> pathlib.Path:
    """Write a minimal notebook with the given code-cell sources, return path."""
    nb = {
        "cells": [
            {
                "cell_type": "code",
                "source": [s] if isinstance(s, str) else s,
                "outputs": [],
                "execution_count": None,
                "metadata": {},
            }
            for s in sources
        ],
        "metadata": {
            "kernelspec": {
                "name": "python3", "display_name": "Python 3", "language": "python",
            }
        },
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    f = tempfile.NamedTemporaryFile(
        mode="w", suffix=".ipynb", delete=False, encoding="utf-8"
    )
    json.dump(nb, f)
    f.close()
    return pathlib.Path(f.name)


def test_first_cell_captures_own_output():
    """cell 0's print output must be captured by cell 0, not shifted to cell 1.

    Regression pin for the IOPub-drain bug: before the fix, cell 0's loop broke
    on the cwd setup's stale status:idle, so cell 0 preview was empty and cell 1
    inherited cell 0's output.
    """
    nbpath = _write_notebook([
        'print("HELLO_FROM_CELL_0")',
        'print("WORLD_FROM_CELL_1")',
    ])
    try:
        results = execute_cell_by_cell(nbpath, timeout=30, verbose=False)
    finally:
        os.unlink(nbpath)

    code_results = [r for r in results if r.cell_type == "code"]
    assert len(code_results) >= 2, f"expected >=2 code results, got {results}"

    cell0, cell1 = code_results[0], code_results[1]
    # The bug: cell0 preview was '' and cell1 captured 'HELLO_FROM_CELL_0'.
    assert cell0.output_preview is not None
    assert "HELLO_FROM_CELL_0" in cell0.output_preview, (
        f"cell 0 lost its output (bug): cell0={cell0.output_preview!r} "
        f"cell1={cell1.output_preview!r}"
    )
    assert "WORLD_FROM_CELL_1" in cell1.output_preview, (
        f"cell 1 lost its output: cell1={cell1.output_preview!r}"
    )
