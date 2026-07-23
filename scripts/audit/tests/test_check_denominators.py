"""Tests for scripts/audit/check_denominators.py (#8050 phantom-detection follow-up).

Covers the two divergence classes:
  - DRIFT   : notebook on disk/forensic but missing from the catalogue.
  - PHANTOM : catalogue entry pointing to a file absent from disk (catalogue bug,
    e.g. a '-executed' suffix residue). Distinct from drift; the most actionable
    signal because the catalog-cron does not always self-heal it.

Uses a synthetic mini-tree so the tests do not depend on the live repo state.
"""
import importlib.util
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
CHECK_PATH = HERE.parent / "check_denominators.py"


def _load_check():
    spec = importlib.util.spec_from_file_location("check_denominators", CHECK_PATH)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def _notebook(path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(
            {
                "cells": [
                    {
                        "cell_type": "code",
                        "execution_count": 1,
                        "outputs": [],
                        "source": [],
                    }
                ],
                "metadata": {},
                "nbformat": 4,
                "nbformat_minor": 5,
            }
        ),
        encoding="utf-8",
    )


def _catalog(repo_root: Path, entries: list[str]) -> None:
    (repo_root / "COURSE_CATALOG.generated.json").write_text(
        json.dumps([{"path": p, "serie": p.split("/")[0]} for p in entries]),
        encoding="utf-8",
    )


def _run(tmp_path, catalog_entries, extra_on_disk=()):
    """Build a synthetic tree + catalog, return the check module + computed sets."""
    mod = _load_check()
    root = tmp_path / "MyIA.AI.Notebooks"
    for rel in catalog_entries:
        _notebook(root / rel)
    for rel in extra_on_disk:
        _notebook(root / rel)
    _catalog(tmp_path, catalog_entries)
    return mod, root


def test_phantom_detected_as_exit1(tmp_path, capsys, monkeypatch):
    """A catalogue entry whose file is missing on disk -> phantom -> exit 1 in --strict."""
    mod, root = _run(
        tmp_path,
        ["IIT/Real.ipynb", "IIT/Phantom-Does-Not-Exist.ipynb"],
    )
    # Phantom-Does-Not-Exist.ipynb is in the catalogue but NOT created on disk
    (root / "IIT" / "Phantom-Does-Not-Exist.ipynb").unlink()

    monkeypatch.setattr(
        sys, "argv",
        ["check_denominators.py", "--root", str(root),
         "--catalog", str(tmp_path / "COURSE_CATALOG.generated.json"), "--strict"],
    )
    rc = mod.main()
    out = capsys.readouterr().out
    assert rc == 1, "phantom catalogue entry must fail the check in --strict"
    assert "Phantom-Does-Not-Exist.ipynb" in out
    assert "PHANTOM" in out


def test_phantom_in_report_json(tmp_path, capsys, monkeypatch):
    """The JSON report carries phantom_paths separately from drift_paths."""
    mod, root = _run(
        tmp_path,
        ["GenAI/NB-1.ipynb", "Search/Ghost.ipynb"],  # Ghost.ipynb phantom
    )
    (root / "Search" / "Ghost.ipynb").unlink()
    json_out = tmp_path / "report.json"
    monkeypatch.setattr(
        sys, "argv",
        ["check_denominators.py", "--root", str(root),
         "--catalog", str(tmp_path / "COURSE_CATALOG.generated.json"),
         "--json-out", str(json_out)],
    )
    mod.main()
    report = json.loads(json_out.read_text(encoding="utf-8"))
    assert report["phantom_count"] == 1
    assert "Search/Ghost.ipynb" in report["phantom_paths"]
    assert "Search/Ghost.ipynb" not in report["drift_paths"]


def test_no_phantom_exit0(tmp_path, monkeypatch):
    """A catalogue whose every entry exists on disk -> no phantom -> exit 0 (no drift either)."""
    mod, root = _run(tmp_path, ["GenAI/NB-1.ipynb", "Search/NB-2.ipynb"])
    monkeypatch.setattr(
        sys, "argv",
        ["check_denominators.py", "--root", str(root),
         "--catalog", str(tmp_path / "COURSE_CATALOG.generated.json"), "--strict"],
    )
    rc = mod.main()
    assert rc == 0, "clean tree (no drift, no phantom) must pass --strict"


def test_drift_and_phantom_independent(tmp_path, capsys, monkeypatch):
    """Drift (notebook missing from catalogue) and phantom (catalogue -> missing file)
    are independent signals: a tree can have both, neither, or one without the other."""
    mod, root = _run(
        tmp_path,
        ["GenAI/Cataloged.ipynb", "IIT/Phantom.ipynb"],  # Phantom.ipynb absent from disk
        extra_on_disk=["ML/Drifted.ipynb"],  # on disk + forensic, but NOT in catalogue -> drift
    )
    (root / "IIT" / "Phantom.ipynb").unlink()  # make it a phantom
    monkeypatch.setattr(
        sys, "argv",
        ["check_denominators.py", "--root", str(root),
         "--catalog", str(tmp_path / "COURSE_CATALOG.generated.json"), "--strict"],
    )
    rc = mod.main()
    out = capsys.readouterr().out
    assert rc == 1
    assert "Phantom.ipynb" in out  # phantom surfaced
    # Drifted.ipynb is excluded from catalogue by CATALOG_EXCLUDE_PEDAGOGICAL? No -> it's drift
    assert "ML/Drifted.ipynb" in out or "DRIFT" in out


def test_executed_suffix_phantom_pattern(tmp_path, capsys, monkeypatch):
    """Regression for the real-world ICT-15c case: a '-executed' suffix residue
    where the real file exists without the suffix and the catalogue lists BOTH."""
    mod, root = _run(
        tmp_path,
        [
            "IIT/ICT-15c-Real.ipynb",            # real file, on disk
            "IIT/ICT-15c-Real-executed.ipynb",   # phantom: in catalogue, NOT on disk
        ],
    )
    # Only create the real file on disk; the -executed one stays phantom
    (root / "IIT" / "ICT-15c-Real-executed.ipynb").unlink()
    monkeypatch.setattr(
        sys, "argv",
        ["check_denominators.py", "--root", str(root),
         "--catalog", str(tmp_path / "COURSE_CATALOG.generated.json"), "--strict"],
    )
    rc = mod.main()
    out = capsys.readouterr().out
    assert rc == 1
    assert "ICT-15c-Real-executed.ipynb" in out
    assert "ICT-15c-Real.ipynb" not in out.split("PHANTOM")[1]  # real file not flagged as phantom
