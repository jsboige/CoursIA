"""Tests for scripts/notebook_tools/flatten_import_notebook.py

Tests the pure transform (flatten_notebook, has_import_directive) on synthetic
notebooks written to tmp_path. No I/O on production notebooks, no kernel
execution (the .net-csharp headless exec is verified firsthand in the PR body,
not re-run per test).
"""

import json
import sys
from pathlib import Path

import pytest

_tools_dir = str(Path(__file__).resolve().parent.parent)
if _tools_dir not in sys.path:
    sys.path.insert(0, _tools_dir)

import nbformat

from flatten_import_notebook import (
    IMPORT_RE,
    flatten_notebook,
    has_import_directive,
)


def _write_nb(path: Path, cells: list[dict], kernel: str = "python3") -> Path:
    nb = {
        "cells": cells,
        "metadata": {"kernelspec": {"name": kernel, "display_name": kernel, "language": kernel}},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    path.write_text(json.dumps(nb), encoding="utf-8")
    return path


def _code(source: str) -> dict:
    return {"cell_type": "code", "source": [source], "metadata": {}, "execution_count": None, "outputs": []}


def _md(source: str) -> dict:
    return {"cell_type": "markdown", "source": [source], "metadata": {}}


# ---------------------------------------------------------------------------
# IMPORT_RE + has_import_directive
# ---------------------------------------------------------------------------

class TestImportDetection:
    def test_import_re_matches_notebook_target(self):
        m = IMPORT_RE.search("#!import Sudoku-0-Environment-Csharp.ipynb")
        assert m is not None
        assert m.group(1) == "Sudoku-0-Environment-Csharp.ipynb"

    def test_import_re_ignores_non_ipynb_magic(self):
        # Other magic commands (#!csharp, #!time, %%) are NOT #!import targets.
        assert IMPORT_RE.search("#!csharp") is None
        assert IMPORT_RE.search("#!time") is None
        assert IMPORT_RE.search("%matplotlib inline") is None

    def test_import_re_matches_relative_subdir_path(self):
        m = IMPORT_RE.search("#!import ../Helpers/Env.ipynb")
        assert m.group(1) == "../Helpers/Env.ipynb"

    def test_has_import_directive_true(self, tmp_path):
        nb = _write_nb(tmp_path / "a.ipynb", [_code("#!import env.ipynb"), _code("var x = 1;")])
        loaded = nbformat.read(nb, as_version=4)
        assert has_import_directive(loaded) is True

    def test_has_import_directive_false(self, tmp_path):
        nb = _write_nb(tmp_path / "a.ipynb", [_code("var x = 1;")])
        loaded = nbformat.read(nb, as_version=4)
        assert has_import_directive(loaded) is False


# ---------------------------------------------------------------------------
# flatten_notebook
# ---------------------------------------------------------------------------

class TestFlatten:
    def test_inlines_imported_cells_at_import_site(self, tmp_path):
        """The #!import cell is REPLACED by the imported notebook's cells, in
        order, at the same position -- so the importing notebook's own cells
        run AFTER the helpers they depend on.
        """
        env = _write_nb(tmp_path / "env.ipynb", [
            _md("# Env"),
            _code("class Helper { }"),
            _code("# Helper defini"),
        ])
        main = _write_nb(tmp_path / "main.ipynb", [
            _md("# Main"),
            _code("#!import env.ipynb"),
            _code("var h = new Helper();"),
        ])
        flat = flatten_notebook(main)
        kinds = [c.cell_type for c in flat.cells]
        sources = ["".join(c.source) for c in flat.cells]
        # env's 3 cells replace the single #!import cell -> 1(md) + 3(env) + 1(code) = 5
        assert len(flat.cells) == 5
        assert "class Helper { }" in sources
        assert "# Helper defini" in sources
        # the importing notebook's dependent cell runs AFTER the helpers
        assert sources.index("class Helper { }") < sources.index("var h = new Helper();")
        # no residual #!import
        assert all("#!import" not in s for s in sources)

    def test_recursive_chained_imports(self, tmp_path):
        """A -> B -> C: flattening A inlines B which inlines C (transitive)."""
        _write_nb(tmp_path / "c.ipynb", [_code("class C { }")])
        _write_nb(tmp_path / "b.ipynb", [_code("#!import c.ipynb"), _code("class B { }")])
        a = _write_nb(tmp_path / "a.ipynb", [_code("#!import b.ipynb"), _code("class A { }")])
        flat = flatten_notebook(a)
        sources = ["".join(c.source) for c in flat.cells]
        joined = "\n".join(sources)
        assert "class C { }" in joined and "class B { }" in joined and "class A { }" in joined
        assert all("#!import" not in s for s in sources)

    def test_cycle_safe(self, tmp_path):
        """A -> B -> A must not infinite-recurse; the second A is skipped
        (already on the import chain)."""
        _write_nb(tmp_path / "a.ipynb", [_code("#!import b.ipynb"), _code("class A { }")])
        _write_nb(tmp_path / "b.ipynb", [_code("#!import a.ipynb"), _code("class B { }")])
        flat = flatten_notebook(tmp_path / "a.ipynb")
        # terminates and produces some flattened output (B inlined; second A skipped)
        sources = ["".join(c.source) for c in flat.cells]
        assert "class A { }" in sources
        assert "class B { }" in sources

    def test_missing_import_target_left_verbatim(self, tmp_path):
        """A #!import pointing at a non-existent file is kept AS-IS so the
        failure surfaces as a normal CellExecutionError on execute (not a
        silent drop of the directive).
        """
        main = _write_nb(tmp_path / "main.ipynb", [
            _code("#!import does-not-exist.ipynb"),
            _code("var x = 1;"),
        ])
        flat = flatten_notebook(main)
        sources = ["".join(c.source) for c in flat.cells]
        assert any("#!import does-not-exist.ipynb" in s for s in sources)

    def test_no_import_returns_notebook_unchanged(self, tmp_path):
        """A notebook with no #!import flattens to itself (no-op)."""
        main = _write_nb(tmp_path / "main.ipynb", [_md("# T"), _code("var x = 1;")])
        flat = flatten_notebook(main)
        assert len(flat.cells) == len(nbformat.read(main, as_version=4).cells)

    def test_preserves_importing_notebook_metadata(self, tmp_path):
        """The flattened notebook keeps the IMPORTING notebook's kernelspec
        (not the imported helper's) -- it runs as the same kernel/language.
        """
        _write_nb(tmp_path / "env.ipynb", [_code("class Helper {}")], kernel="python3")
        main = _write_nb(tmp_path / "main.ipynb", [_code("#!import env.ipynb")], kernel=".net-csharp")
        flat = flatten_notebook(main)
        assert flat.metadata["kernelspec"]["name"] == ".net-csharp"
