"""Tests for scripts/notebook_tools/generate_16e.py — GT-16e notebook generator.

The module builds a Lean 4 kernel notebook procedurally (top-level md()/lean4()
cell appends + a final write). Importing it has side effects (it writes to
sys.argv[1]), so:

- Unit tests extract md()/lean4() via AST and exec them in an isolated namespace
  (no top-level side effects).
- Integration tests run the script as a subprocess (real generator, regle F) and
  validate the emitted .ipynb (nbformat, kernel, cell structure, determinism).
"""

import ast
import json
import subprocess
import sys
from pathlib import Path

import pytest

GEN = Path(__file__).resolve().parent.parent / "generate_16e.py"
assert GEN.exists(), f"generator not found at {GEN}"


# ---------------------------------------------------------------------------
# Helpers — isolate md()/lean4() without triggering module top-level side effects
# ---------------------------------------------------------------------------

def _load_helpers():
    """Compile only the md() and lean4() FunctionDefs into an isolated namespace.

    generate_16e.py executes notebook construction at import time and writes to
    sys.argv[1]; importing it directly would create files. Instead we parse the
    AST, extract the two helper functions, and exec them with a fresh `cells`
    list. This tests the real source of md()/lean4() without side effects.
    """
    tree = ast.parse(GEN.read_text(encoding="utf-8"))
    ns = {"cells": []}
    for node in tree.body:
        if isinstance(node, ast.FunctionDef) and node.name in ("md", "lean4"):
            mod = ast.Module(body=[node], type_ignores=[])
            exec(compile(mod, str(GEN), "exec"), ns)
    return ns


# ---------------------------------------------------------------------------
# Unit tests — md() / lean4() cell constructors
# ---------------------------------------------------------------------------

def test_md_builds_markdown_cell_structure():
    ns = _load_helpers()
    ns["md"]("# Title", "cell-1")
    cell = ns["cells"][-1]
    assert cell["cell_type"] == "markdown"
    assert cell["id"] == "cell-1"
    assert cell["metadata"] == {}
    assert cell["source"] == ["# Title"]


def test_md_appends_one_cell_per_call():
    ns = _load_helpers()
    assert ns["cells"] == []
    ns["md"]("a", "c1")
    ns["md"]("b", "c2")
    assert len(ns["cells"]) == 2
    assert [c["id"] for c in ns["cells"]] == ["c1", "c2"]


def test_lean4_builds_code_cell_structure():
    ns = _load_helpers()
    ns["lean4"]("#check 1", "code-1")
    cell = ns["cells"][-1]
    assert cell["cell_type"] == "code"
    assert cell["id"] == "code-1"
    assert cell["execution_count"] is None
    assert cell["language"] == "lean4"
    assert cell["metadata"] == {}
    assert cell["outputs"] == []
    assert cell["source"] == ["#check 1"]


def test_lean4_cells_start_unexecuted():
    """Generated code cells are stubs pending kernel execution (execution_count None)."""
    ns = _load_helpers()
    for i in range(3):
        ns["lean4"](f"example {i}", f"k{i}")
    for cell in ns["cells"]:
        assert cell["execution_count"] is None
        assert cell["outputs"] == []


def test_md_and_lean4_share_global_cells_in_order():
    """Both helpers append to the same module-level cells list, preserving order."""
    ns = _load_helpers()
    ns["md"]("intro", "m1")
    ns["lean4"]("code", "k1")
    ns["md"]("outro", "m2")
    assert [c["id"] for c in ns["cells"]] == ["m1", "k1", "m2"]
    assert [c["cell_type"] for c in ns["cells"]] == ["markdown", "code", "markdown"]


# ---------------------------------------------------------------------------
# Integration tests — run the real generator (subprocess, regle F)
# ---------------------------------------------------------------------------

def _run_generator(out_path: Path):
    """Run generate_16e.py writing to out_path; return the parsed notebook dict."""
    proc = subprocess.run(
        [sys.executable, str(GEN), str(out_path)],
        capture_output=True, text=True, cwd=str(out_path.parent),
    )
    assert proc.returncode == 0, f"generator failed:\nSTDOUT:{proc.stdout}\nSTDERR:{proc.stderr}"
    assert out_path.exists(), f"output notebook not written to {out_path}"
    return json.loads(out_path.read_text(encoding="utf-8"))


def test_generator_emits_valid_nbformat4_notebook(tmp_path):
    nb = _run_generator(tmp_path / "out.ipynb")
    assert nb["nbformat"] == 4
    assert nb["nbformat_minor"] == 5
    assert isinstance(nb["cells"], list)


def test_generator_sets_lean4_wsl_kernel(tmp_path):
    nb = _run_generator(tmp_path / "out.ipynb")
    ks = nb["metadata"]["kernelspec"]
    assert ks["name"] == "lean4-wsl"
    assert ks["language"] == "lean4"
    li = nb["metadata"]["language_info"]
    assert li["name"] == "lean4"


def test_generator_emits_both_markdown_and_code_cells(tmp_path):
    nb = _run_generator(tmp_path / "out.ipynb")
    types = {c["cell_type"] for c in nb["cells"]}
    assert "markdown" in types
    assert "code" in types
    # Substantial tour notebook (24 cells per generator)
    assert len(nb["cells"]) >= 20


def test_generator_code_cells_carry_lean4_language(tmp_path):
    nb = _run_generator(tmp_path / "out.ipynb")
    code_cells = [c for c in nb["cells"] if c["cell_type"] == "code"]
    assert len(code_cells) >= 1
    for c in code_cells:
        assert c.get("language") == "lean4"
        assert c.get("execution_count") is None
        assert c.get("outputs") == []


def test_generator_every_cell_has_required_fields(tmp_path):
    nb = _run_generator(tmp_path / "out.ipynb")
    for i, c in enumerate(nb["cells"]):
        assert "cell_type" in c, f"cell {i} missing cell_type"
        assert "id" in c, f"cell {i} missing id"
        assert "source" in c, f"cell {i} missing source"
        assert "metadata" in c, f"cell {i} missing metadata"
        assert isinstance(c["source"], list)


def test_generator_is_deterministic_byte_stable(tmp_path):
    """Running the generator twice yields byte-identical output."""
    out1 = tmp_path / "first.ipynb"
    out2 = tmp_path / "second.ipynb"
    _run_generator(out1)
    _run_generator(out2)
    assert out1.read_bytes() == out2.read_bytes(), "generator output not byte-stable"


def test_generator_output_reloads_as_valid_json(tmp_path):
    out = tmp_path / "out.ipynb"
    _run_generator(out)
    # Re-load to confirm no trailing garbage / valid JSON round-trip
    data = json.loads(out.read_text(encoding="utf-8"))
    assert data["nbformat"] == 4
