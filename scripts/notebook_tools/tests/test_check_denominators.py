"""Tests for check_denominators.py (#8050).

Verifies phantom detection (the blocking signal), structural-gap tolerance,
and the forensic-only categorization — using a synthetic mini-tree so the tests
do not depend on the full repo state.
"""
import importlib.util
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
MODULE_PATH = HERE.parent / "check_denominators.py"


def _load_module():
    spec = importlib.util.spec_from_file_location("check_denominators", MODULE_PATH)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def _make_notebook(path: Path, *, executed: bool = True) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    ec = 1 if executed else None
    nb = {
        "cells": [
            {"cell_type": "code", "execution_count": ec, "outputs": [], "source": []}
        ],
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    path.write_text(json.dumps(nb), encoding="utf-8")


def _make_catalogue(repo_root: Path, entries: list[str]) -> None:
    data = [{"path": p, "serie": p.split("/")[0]} for p in entries]
    (repo_root / "COURSE_CATALOG.generated.json").write_text(
        json.dumps(data), encoding="utf-8"
    )


def test_clean_catalogue_no_phantom(tmp_path):
    """A catalogue whose every entry exists on disk -> exit 0."""
    mod = _load_module()
    root = tmp_path / "MyIA.AI.Notebooks"
    _make_notebook(root / "GenAI" / "NB-1.ipynb")
    _make_notebook(root / "Search" / "S-1.ipynb")
    # NB-2 in a _archive dir -> forensic-excluded, not a phantom
    _make_notebook(root / "Search" / "_archives" / "old.ipynb")
    _make_catalogue(tmp_path, ["GenAI/NB-1.ipynb", "Search/S-1.ipynb"])

    forensic = mod.build_forensic_set(root, _load_forensic_is_excluded())
    catalogue = mod.read_catalogue(tmp_path)
    assert "Search/_archives/old.ipynb" not in forensic  # forensic excludes _archives
    catalogue_only = sorted(catalogue - forensic)
    phantoms = [p for p in catalogue_only if not (root / p).exists()]
    assert phantoms == []


def test_phantom_detected(tmp_path, capsys):
    """A catalogue entry whose file is missing on disk -> phantom -> exit 1."""
    mod = _load_module()
    root = tmp_path / "MyIA.AI.Notebooks"
    _make_notebook(root / "GenAI" / "NB-1.ipynb")
    # catalogue references a notebook that does NOT exist on disk
    _make_catalogue(
        tmp_path, ["GenAI/NB-1.ipynb", "IIT/Phantom-Does-Not-Exist.ipynb"]
    )

    rc = mod.main.__wrapped__ if hasattr(mod.main, "__wrapped__") else None
    # call main via argv override
    sys.argv = ["check_denominators.py", "--root", str(root), "--repo-root", str(tmp_path)]
    rc = mod.main()
    captured = capsys.readouterr()
    assert rc == 1, "phantom catalogue entry must fail the check"
    assert "ICT" not in captured.err  # synthetic tree, but ensure FAIL surfaced
    assert "Phantom-Does-Not-Exist.ipynb" in captured.out


def test_structural_gap_is_non_blocking(tmp_path, capsys):
    """forensic > catalogue (research/twins/examples) is healthy -> exit 0."""
    mod = _load_module()
    root = tmp_path / "MyIA.AI.Notebooks"
    _make_notebook(root / "QuantConnect" / "research" / "r1.ipynb")  # forensic-only
    _make_notebook(root / "QuantConnect" / "NB-1-Csharp.ipynb")  # twin, forensic-only
    _make_notebook(root / "GenAI" / "NB-1.ipynb")  # catalogued
    _make_catalogue(tmp_path, ["GenAI/NB-1.ipynb"])  # only the primary

    sys.argv = ["check_denominators.py", "--root", str(root), "--repo-root", str(tmp_path)]
    rc = mod.main()
    captured = capsys.readouterr()
    assert rc == 0, "structural forensic/catalogue gap must NOT block"
    assert "forensic-only" in captured.out


def test_categorize_buckets():
    """forensic-only notebooks are bucketed by their non-catalogue reason."""
    mod = _load_module()
    paths = [
        "QuantConnect/research/r1.ipynb",
        "QuantConnect/projects/p1.ipynb",
        "GenAI/Image/examples/eg.ipynb",
        "GameTheory/GT-1-Csharp.ipynb",
        "GradeBook.ipynb",
        "Search/_archives/old.ipynb",
        "GameTheory/GT-weird.ipynb",
    ]
    buckets = mod.categorize_forensic_only(paths)
    assert buckets.get("qc research/project") == 2
    assert buckets.get("examples") == 1
    assert buckets.get("twin (C#/Lean/Python variant)") == 1
    assert buckets.get("tool (GradeBook)") == 1
    assert buckets.get("archive") == 1
    assert buckets.get("other (GameTheory)") == 1


def _load_forensic_is_excluded():
    """Load forensic_scan.is_excluded for parity tests."""
    spec = importlib.util.spec_from_file_location(
        "forensic_scan", HERE.parent / "forensic_scan.py"
    )
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m.is_excluded
