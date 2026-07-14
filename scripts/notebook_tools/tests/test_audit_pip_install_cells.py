#!/usr/bin/env python3
"""Tests for audit_pip_install_cells.

Covers:
    * UNCONDITIONAL_BASH : bare ``!pip install`` outside any try/except.
    * UNCONDITIONAL_SYS  : ``!{sys.executable} -m pip install`` (IPython form).
    * CONDITIONAL_TRY    : ``!pip install`` inside ``try/except ImportError``.
    * NON_BASH           : ``pip install`` mention in a docstring / string.
    * Multi-cell scan    : ``scan_notebook`` reports only matching cells.
    * iter_notebooks     : ``_output.ipynb`` / ``_executed.ipynb`` excluded.

Run:
    pytest scripts/notebook_tools/tests/test_audit_pip_install_cells.py
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

# Make the script importable from the tests dir.
SCRIPT_DIR = (
    Path(__file__).resolve().parent.parent  # scripts/notebook_tools/tests/../
)
sys.path.insert(0, str(SCRIPT_DIR))

from audit_pip_install_cells import (  # noqa: E402
    _classify_cell,
    _iter_notebooks,
    scan_notebook,
)


# --- classification --------------------------------------------------------

def test_unconditional_bash_pip_install():
    src = "import numpy\n!pip install pandas\nimport pandas as pd\n"
    assert _classify_cell(src) == "UNCONDITIONAL_BASH"


def test_unconditional_sys_pip_install():
    src = (
        "import sys\n"
        "!{sys.executable} -m pip install python-constraint\n"
        "from constraint import Problem\n"
    )
    assert _classify_cell(src) == "UNCONDITIONAL_SYS"


def test_conditional_try_pip_install():
    src = (
        "try:\n"
        "    from rich import print\n"
        "except ImportError:\n"
        "    !pip install rich\n"
        "    from rich import print\n"
    )
    assert _classify_cell(src) == "CONDITIONAL_TRY"


def test_non_bash_mention_in_string():
    src = (
        "# To reproduce this offline:\n"
        "#   $ pip install pandas\n"
        "import pandas as pd\n"
    )
    assert _classify_cell(src) == "NON_BASH"


def test_non_bash_mention_in_docstring():
    src = (
        '"""\n'
        "Helper module. Install with `pip install foo` to use the API.\n"
        '"""\n'
    )
    assert _classify_cell(src) == "NON_BASH"


def test_ipython_magic_pip_install():
    src = "%pip install torch\nimport torch\n"
    assert _classify_cell(src) == "UNCONDITIONAL_BASH"


def test_python_qualified_pip_install():
    src = "! python -m pip install requests\nimport requests\n"
    assert _classify_cell(src) == "UNCONDITIONAL_BASH"


def test_no_pip_install_at_all():
    src = "import pandas as pd\nprint(pd.__version__)\n"
    assert _classify_cell(src) == "NON_BASH"


# --- scan_notebook ---------------------------------------------------------

def _write_nb(tmp_path: Path, cells: list[dict]) -> Path:
    nb = {
        "cells": cells,
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    path = tmp_path / "test.ipynb"
    path.write_text(json.dumps(nb), encoding="utf-8")
    return path


def test_scan_notebook_counts_only_code_cells_with_pip(tmp_path: Path):
    cells = [
        {"cell_type": "markdown", "source": ["# Use `pip install foo`\n"], "metadata": {}, "outputs": []},
        {"cell_type": "code", "source": ["import pandas as pd\n"], "metadata": {}, "outputs": [], "execution_count": 1},
        {"cell_type": "code", "source": ["!pip install pandas\n"], "metadata": {}, "outputs": [], "execution_count": 2},
        {"cell_type": "code", "source": ["import sys\ntry:\n    from rich import print\nexcept ImportError:\n    !pip install rich\n    from rich import print\n"], "metadata": {}, "outputs": [], "execution_count": 3},
        {"cell_type": "code", "source": ["print('done')\n"], "metadata": {}, "outputs": [], "execution_count": 4},
    ]
    path = _write_nb(tmp_path, cells)
    report = scan_notebook(path)
    assert report["total_cells"] == 5
    assert report["code_cells"] == 4
    assert len(report["occurrences"]) == 2  # cells 2 and 3
    classifications = {occ["cell_index"]: occ["classification"] for occ in report["occurrences"]}
    assert classifications[2] == "UNCONDITIONAL_BASH"
    assert classifications[3] == "CONDITIONAL_TRY"


def test_scan_notebook_no_occurrences(tmp_path: Path):
    cells = [
        {"cell_type": "code", "source": ["print('hello')\n"], "metadata": {}, "outputs": [], "execution_count": 1},
    ]
    path = _write_nb(tmp_path, cells)
    report = scan_notebook(path)
    assert report["occurrences"] == []


def test_iter_notebooks_excludes_papermill_artifacts(tmp_path: Path):
    # Create 3 files: source, _output, _executed
    (tmp_path / "real.ipynb").write_text("{}", encoding="utf-8")
    papermill_out = tmp_path / "_output"
    papermill_out.mkdir()
    (papermill_out / "real_output.ipynb").write_text("{}", encoding="utf-8")
    papermill_exec = tmp_path / "_executed"
    papermill_exec.mkdir()
    (papermill_exec / "real_executed.ipynb").write_text("{}", encoding="utf-8")
    paths = sorted(p.name for p in _iter_notebooks(tmp_path))
    assert paths == ["real.ipynb"]


# --- end-to-end CLI ---

def test_cli_check_exits_1_on_unconditional(tmp_path: Path, monkeypatch, capsys):
    """End-to-end: a repo with one HIGH-severity cell triggers --check exit 1."""
    nb_dir = tmp_path / "MyIA.AI.Notebooks"
    nb_dir.mkdir()
    nb = {
        "cells": [
            {"cell_type": "code", "source": ["!pip install pandas\n"], "metadata": {}, "outputs": [], "execution_count": 1},
        ],
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    (nb_dir / "leaky.ipynb").write_text(json.dumps(nb), encoding="utf-8")

    monkeypatch.chdir(tmp_path)
    monkeypatch.setattr(sys, "argv", ["audit_pip_install_cells.py", "--scan-all", "--check"])
    from audit_pip_install_cells import main
    exit_code = main()
    captured = capsys.readouterr()

    assert exit_code == 1
    assert "UNCONDITIONAL_BASH" in captured.out


def test_cli_check_exits_0_on_clean_repo(tmp_path: Path, monkeypatch, capsys):
    """End-to-end: a clean repo triggers --check exit 0."""
    nb_dir = tmp_path / "MyIA.AI.Notebooks"
    nb_dir.mkdir()
    nb = {
        "cells": [
            {"cell_type": "code", "source": ["print('hello')\n"], "metadata": {}, "outputs": [], "execution_count": 1},
        ],
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    (nb_dir / "clean.ipynb").write_text(json.dumps(nb), encoding="utf-8")

    monkeypatch.chdir(tmp_path)
    monkeypatch.setattr(sys, "argv", ["audit_pip_install_cells.py", "--scan-all", "--check"])
    from audit_pip_install_cells import main
    exit_code = main()
    captured = capsys.readouterr()
    assert exit_code == 0
    assert "No `!pip install` occurrences found" in captured.out