"""Unit tests for scripts/extract_notebook_content.py (SymbolicAI README helper).

The module is a standalone script (run via `__main__`) that scans SymbolicAI
notebooks and emits a README report + markdown tables. It was a **test orphan**:
imported by nothing (grep repo-wide = 0 `.py` importers), exercised only when a
human ran it for README regeneration. This suite pins the pure parsing logic
(`extract_cell_preview`, `analyze_notebook`, `scan_directory`) and the two
formatters' shape, so behavior is locked regardless of README re-runs.

No network, no kernel, no heavy deps — just `json` + `pathlib`. Each notebook
fixture is written to a tmp file so `analyze_notebook`/`scan_directory` exercise
real file I/O.
"""
import json
import sys
from pathlib import Path

# Make the script importable as a module (it lives in scripts/, tests in scripts/tests/).
_SCRIPTS = Path(__file__).resolve().parent.parent
if str(_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(_SCRIPTS))

import extract_notebook_content as enc  # noqa: E402


# --- helpers ----------------------------------------------------------------

def _nb(cells, kernel="Python 3"):
    """Build a minimal ipynb dict with the given cells."""
    return {
        "cells": cells,
        "metadata": {"kernelspec": {"display_name": kernel}},
    }


def _write_nb(tmp_path: Path, name: str, cells, kernel="Python 3"):
    """Write a notebook dict to <tmp_path>/<name> and return its path."""
    p = tmp_path / name
    p.write_text(json.dumps(_nb(cells, kernel)), encoding="utf-8")
    return p


# --- extract_cell_preview ---------------------------------------------------

def test_preview_list_source_joins_lines():
    cell = {"source": ["import json\n", "x = 1\n", "print(x)\n"]}
    out = enc.extract_cell_preview(cell)
    assert out == "import json x = 1 print(x)"


def test_preview_str_source_splits_on_newline():
    cell = {"source": "a = 1\nb = 2\nc = 3"}
    assert enc.extract_cell_preview(cell) == "a = 1 b = 2 c = 3"


def test_preview_respects_max_lines():
    cell = {"source": ["line1\n", "line2\n", "line3\n", "line4\n"]}
    out = enc.extract_cell_preview(cell, max_lines=2)
    assert "line3" not in out
    assert out == "line1 line2"


def test_preview_truncates_to_max_chars():
    cell = {"source": ["abcdefghij\n", "klmnopqrst\n"]}
    out = enc.extract_cell_preview(cell, max_chars=10)
    assert len(out) <= 10
    assert out == "abcdefghij"


def test_preview_skips_shebang_magic_lines():
    """Lines starting with `#!` (.NET magics) are stripped from the preview."""
    cell = {"source": ["#!whoami\n", "real code\n"]}
    assert enc.extract_cell_preview(cell) == "real code"


def test_preview_skips_blank_lines():
    cell = {"source": ["\n", "  \n", "kept\n"]}
    assert enc.extract_cell_preview(cell) == "kept"


def test_preview_empty_cell():
    assert enc.extract_cell_preview({"source": []}) == ""
    assert enc.extract_cell_preview({}) == ""


# --- analyze_notebook -------------------------------------------------------

def test_analyze_extracts_title_from_first_h1(tmp_path):
    p = _write_nb(tmp_path, "n.ipynb", [
        {"cell_type": "markdown", "source": ["# Mon Titre\n"]},
        {"cell_type": "code", "source": ["x = 1\n"]},
    ])
    info = enc.analyze_notebook(p)
    assert info["title"] == "Mon Titre"
    assert info["total_cells"] == 2
    assert info["markdown_cells"] == 1
    assert info["code_cells"] == 1


def test_analyze_kernel_display_name(tmp_path):
    p = _write_nb(tmp_path, "n.ipynb", [], kernel=".NET (C#)")
    assert enc.analyze_notebook(p)["kernel"] == ".NET (C#)"


def test_analyze_default_kernel_when_missing(tmp_path):
    p = tmp_path / "n.ipynb"
    p.write_text(json.dumps({"cells": [], "metadata": {}}), encoding="utf-8")
    assert enc.analyze_notebook(p)["kernel"] == "Unknown"


def test_analyze_extracts_sections_and_subsections(tmp_path):
    p = _write_nb(tmp_path, "n.ipynb", [
        {"cell_type": "markdown", "source": ["# T\n", "\n", "## Section A\n", "### Sub 1\n", "### Sub 2\n"]},
        {"cell_type": "markdown", "source": ["## Section B\n"]},
    ])
    info = enc.analyze_notebook(p)
    assert info["sections"] == ["Section A", "Section B"]
    assert info["subsections"] == ["Sub 1", "Sub 2"]


def test_analyze_title_none_when_no_h1(tmp_path):
    p = _write_nb(tmp_path, "n.ipynb", [
        {"cell_type": "markdown", "source": ["## Not a title\n"]},
    ])
    assert enc.analyze_notebook(p)["title"] is None


def test_analyze_returns_error_on_missing_file(tmp_path):
    info = enc.analyze_notebook(tmp_path / "does_not_exist.ipynb")
    assert "error" in info
    assert isinstance(info["error"], str)


def test_analyze_returns_error_on_invalid_json(tmp_path):
    p = tmp_path / "broken.ipynb"
    p.write_text("{not valid json", encoding="utf-8")
    info = enc.analyze_notebook(p)
    assert "error" in info


def test_analyze_subsections_capped_at_20(tmp_path):
    cells = [{"cell_type": "markdown", "source":
              ["# T\n"] + [f"### Sub {i}\n" for i in range(30)]}]
    p = _write_nb(tmp_path, "n.ipynb", cells)
    assert len(enc.analyze_notebook(p)["subsections"]) == 20


# --- scan_directory ---------------------------------------------------------

def test_scan_finds_notebooks(tmp_path):
    base = tmp_path / "base"
    base.mkdir()
    _write_nb(base, "a.ipynb", [{"cell_type": "markdown", "source": ["# A\n"]}])
    sub = base / "sub"
    sub.mkdir()
    _write_nb(sub, "b.ipynb", [{"cell_type": "markdown", "source": ["# B\n"]}])
    nbs = enc.scan_directory(base)
    names = sorted(n["name"] for n in nbs)
    assert names == ["a", "b"]


def test_scan_skips_ipynb_checkpoints(tmp_path):
    base = tmp_path / "base"
    base.mkdir()
    _write_nb(base, "real.ipynb", [{"cell_type": "markdown", "source": ["# R\n"]}])
    cp = base / ".ipynb_checkpoints"
    cp.mkdir()
    _write_nb(cp, "cached.ipynb", [{"cell_type": "markdown", "source": ["# C\n"]}])
    names = [n["name"] for n in enc.scan_directory(base)]
    assert names == ["real"]


def test_scan_excludes_legacy_subtree(tmp_path):
    """A subtree whose path contains 'archive' is skipped by scan_directory.

    NOTE: the test name deliberately avoids the substring 'archive' — pytest's
    tmp_path embeds the test function name, and the module's filter is
    `'archive' in str(path).lower()`, so a name containing 'archive' would
    suppress every fixture (including the intentional 'live' notebook).
    """
    base = tmp_path / "base"
    base.mkdir()
    _write_nb(base, "live.ipynb", [{"cell_type": "markdown", "source": ["# L\n"]}])
    arch = base / "Archive"
    arch.mkdir()
    _write_nb(arch, "old.ipynb", [{"cell_type": "markdown", "source": ["# O\n"]}])
    names = [n["name"] for n in enc.scan_directory(base)]
    assert names == ["live"]


def test_scan_relative_path_and_directory(tmp_path):
    base = tmp_path / "base"
    sub = base / "group"
    sub.mkdir(parents=True)
    _write_nb(sub, "deep.ipynb", [{"cell_type": "markdown", "source": ["# D\n"]}])
    nbs = enc.scan_directory(base)
    n = nbs[0]
    assert n["relative_path"].replace("\\", "/") == "group/deep.ipynb"
    assert n["directory"] in ("group", str(Path("group")))


def test_scan_root_directory_label(tmp_path):
    base = tmp_path / "base"
    base.mkdir()
    _write_nb(base, "top.ipynb", [{"cell_type": "markdown", "source": ["# T\n"]}])
    assert enc.scan_directory(base)[0]["directory"] == "root"


# --- formatters (shape, not stdout content) ---------------------------------

def test_generate_report_handles_empty(capsys):
    enc.generate_report([])
    captured = capsys.readouterr()
    assert "Total: 0 notebooks" in captured.out


def test_generate_report_groups_by_directory(capsys, tmp_path):
    nbs = [
        {"name": "a", "directory": "g1", "kernel": "K", "title": "A",
         "total_cells": 1, "markdown_cells": 1, "code_cells": 0,
         "sections": [], "subsections": []},
        {"name": "b", "directory": "g2", "kernel": "K", "title": "B",
         "total_cells": 2, "markdown_cells": 1, "code_cells": 1,
         "sections": ["S"], "subsections": []},
    ]
    enc.generate_report(nbs)
    out = capsys.readouterr().out
    assert "G1" in out and "G2" in out


def test_generate_markdown_table_emits_header(capsys):
    # generate_markdown_table prints the table header once per directory group,
    # so a non-empty list (one directory) is required for the header to appear.
    enc.generate_markdown_table([
        {"name": "foo", "directory": "g", "total_cells": 1, "sections": []},
    ])
    out = capsys.readouterr().out
    assert "| Notebook | Cellules | Sections principales |" in out


def test_generate_markdown_table_row(capsys):
    enc.generate_markdown_table([
        {"name": "foo", "directory": "g", "total_cells": 5, "sections": ["A", "B", "C"]},
    ])
    out = capsys.readouterr().out
    assert "| foo | 5 |" in out
