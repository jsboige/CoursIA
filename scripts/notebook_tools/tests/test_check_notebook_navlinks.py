"""Tests for scripts/notebook_tools/check_notebook_navlinks.py — notebook navlink checker.

Validates:
- Detects broken relative .ipynb navlinks (0 false negatives)
- Accepts valid relative navlinks (0 false positives)
- Skips HTTP links
- Resolves relative to the source notebook's directory (not repo root)
- --strict exit code semantics
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import check_notebook_navlinks as cnn


def _make_nb(*cells):
    """Build a minimal notebook from (cell_type, source_lines) tuples."""
    return {
        "cells": [
            {"cell_type": ct, "source": src if isinstance(src, list) else [src], "metadata": {}, "outputs": [] if ct == "code" else None}
            for ct, src in cells
        ],
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }


@pytest.fixture
def nb_tree(tmp_path: Path):
    """Create a fake notebook family: Search-1 exists, Search-2 exists in a subdir,
    Search-3 does NOT exist (broken target)."""
    nb_good = tmp_path / "Search-1-Real.ipynb"
    nb_subdir = tmp_path / "Sub" / "Search-2-Real.ipynb"
    nb_missing_target = tmp_path / "Search-9-Real.ipynb"  # the source with broken links
    for p in (nb_good, nb_subdir, nb_missing_target):
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(json.dumps(_make_nb(("markdown", "# title"))), encoding="utf-8")

    # Notebook in tmp_path root: links to existing (same dir), existing (subdir), missing, http
    src = tmp_path / "Src.ipynb"
    src.write_text(json.dumps(_make_nb(
        ("markdown", "**Nav**: [next](Search-1-Real.ipynb) | "
                     "[sub](Sub/Search-2-Real.ipynb) | "
                     "[broken](Search-999-Missing.ipynb) | "
                     "[web](https://example.com/x.ipynb)"),
    )), encoding="utf-8")
    return tmp_path


def test_detects_broken_navlink(nb_tree, monkeypatch):
    monkeypatch.setattr(cnn, "REPO_ROOT", nb_tree)
    broken = cnn.scan([nb_tree])
    targets = {b.target for b in broken}
    assert "Search-999-Missing.ipynb" in targets, "must detect the missing target"


def test_accepts_valid_navlinks(nb_tree, monkeypatch):
    monkeypatch.setattr(cnn, "REPO_ROOT", nb_tree)
    broken = cnn.scan([nb_tree])
    targets = {b.target for b in broken}
    assert "Search-1-Real.ipynb" not in targets, "same-dir valid link must NOT be flagged"
    assert "Sub/Search-2-Real.ipynb" not in targets, "subdir valid link must NOT be flagged"


def test_skips_http_links(nb_tree, monkeypatch):
    monkeypatch.setattr(cnn, "REPO_ROOT", nb_tree)
    broken = cnn.scan([nb_tree])
    targets = {b.target for b in broken}
    assert not any(t.startswith("http") for t in targets), "HTTP links must be skipped"


def test_only_one_broken(nb_tree, monkeypatch):
    monkeypatch.setattr(cnn, "REPO_ROOT", nb_tree)
    broken = cnn.scan([nb_tree])
    assert len(broken) == 1, f"expected exactly 1 broken navlink, got {len(broken)}"


def test_strict_exit_code(nb_tree, monkeypatch):
    monkeypatch.setattr(cnn, "REPO_ROOT", nb_tree)
    # With a broken link present, --strict must exit 1
    assert cnn.main([str(nb_tree), "--strict", "--quiet"]) == 1


def test_strict_clean_exit_code(nb_tree, monkeypatch):
    monkeypatch.setattr(cnn, "REPO_ROOT", nb_tree)
    # Scanning only the notebook with no broken link (the good one's dir has no broken refs)
    clean = nb_tree / "Clean.ipynb"
    clean.write_text(json.dumps(_make_nb(("markdown", "[ok](Search-1-Real.ipynb)"))), encoding="utf-8")
    assert cnn.main([str(clean), "--strict", "--quiet"]) == 0


def test_report_format_empty(monkeypatch):
    assert cnn.format_report([], quiet=False) == "OK: 0 broken notebook navlink(s)."
    assert cnn.format_report([], quiet=True) == ""


def test_resolves_relative_to_notebook_dir(nb_tree, monkeypatch):
    """A navlink in Sub/Search-2-Real.ipynb pointing to ../Search-1-Real.ipynb must resolve."""
    monkeypatch.setattr(cnn, "REPO_ROOT", nb_tree)
    sub_nb = nb_tree / "Sub" / "Search-2-Real.ipynb"
    sub_nb.write_text(json.dumps(_make_nb(
        ("markdown", "[parent](../Search-1-Real.ipynb) | [broken-sib](Search-888.ipynb)"),
    )), encoding="utf-8")
    broken = cnn.scan([nb_tree / "Sub"])
    targets = {b.target for b in broken}
    assert "../Search-1-Real.ipynb" not in targets, "relative ../ must resolve to parent dir"
    assert "Search-888.ipynb" in targets
