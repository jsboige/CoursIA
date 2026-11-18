"""Tests for the CI half of the pure-rename family (#24068).

The pre-commit half is covered by ``test_staged_pure_rename_skip.py``. This
file covers the two CI surfaces of the same defect class, where the checkout
IS the head and there is no index to read:

  - ``check_encoding_corruption --base REF`` (fast-lane registry TRANCHE35):
    counts the double-encoding artifacts on the ADDED lines of the notebooks
    changed since REF;
  - ``check_cell_source_parses --pr-diff BASE HEAD``: scans the whole
    notebook of every changed file.

Both were measured as blind to a pure move: the pathspec carrying only the
DESTINATION breaks git's rename pairing, so the destination looks like a
brand-new file and every line counts as added -- the inherited artifact (or
the inherited parse error) is re-reported on a gesture that introduced
nothing. The issue text assumed the CI half was already correct; the
measurement contradicts it, so it is fixed here too.

Each test carries its CONTROL POSITIVE: the same defect on a file that is
NOT a pure rename must still be refused. Without it, the skip would be a
blanket silence.
"""

from __future__ import annotations

import importlib.util
import json
import subprocess
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(REPO_ROOT / "scripts"))
# notebook_tools/ is not a package: its scripts import each other by bare
# name, so the folder itself must be on sys.path for a by-path load.
sys.path.insert(0, str(REPO_ROOT / "scripts" / "notebook_tools"))
sys.path.insert(0, str(REPO_ROOT / "scripts" / "audit"))

import git_index_renames  # noqa: E402


def _load(module_name: str):
    """Load a notebook_tools script by path (notebook_tools/ is not a package)."""
    path = REPO_ROOT / "scripts" / "notebook_tools" / f"{module_name}.py"
    spec = importlib.util.spec_from_file_location(module_name, str(path))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _git(repo: Path, *args: str) -> str:
    out = subprocess.run(["git", *args], cwd=repo, check=True,
                         capture_output=True, encoding="utf-8",
                         errors="replace")
    return out.stdout.strip()


def _nb(cells: list[tuple[str, str]]) -> dict:
    return {
        "cells": [
            {"cell_type": t, "source": s.splitlines(keepends=True),
             "outputs": [], "metadata": {}, "execution_count": None}
            for t, s in cells
        ],
        "metadata": {"kernelspec": {"name": "python3"}},
        "nbformat": 4,
        "nbformat_minor": 5,
    }


def _write_nb(path: Path, nb: dict) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(nb, ensure_ascii=False, indent=1),
                    encoding="utf-8")
    return path


def _new_repo(tmp_path: Path) -> Path:
    repo = tmp_path / "repo"
    repo.mkdir()
    _git(repo, "init", "-q", ".")
    _git(repo, "config", "user.email", "t@t.t")
    _git(repo, "config", "user.name", "t")
    return repo


# A corrupted markdown cell: the double-encoding family the detector hunts.
CORRUPT = "mÃ©taheuristique â€” plateau"
# A code cell that does not compile.
BROKEN = "def f(:\n    pass\n"


@pytest.fixture
def pinned_probe(monkeypatch):
    """Anchor the shared probe on the repository under test.

    The probe runs git from the process' current directory (git's own
    convention), so the test must move there: a revision that belongs to
    the fixture repository, asked of the checkout under test, is not an
    error but a **lazy fetch** on a partial clone -- a network round trip
    per call, which is how a unit test ends up hanging for minutes.
    """
    def _pin(repo: Path):
        monkeypatch.setattr(git_index_renames, "REPO_ROOT", repo)
        monkeypatch.chdir(repo)
    return _pin


# ---------------------------------------------------------------------------
# check_encoding_corruption --base (CI)
# ---------------------------------------------------------------------------

def test_encoding_corruption_base_ignores_pure_rename(tmp_path, monkeypatch,
                                                       pinned_probe, capsys):
    """A notebook that was only MOVED adds no line: no artifact to report."""
    mod = _load("check_encoding_corruption")
    repo = _new_repo(tmp_path)
    _write_nb(repo / "old.ipynb", _nb([("markdown", CORRUPT)]))
    _git(repo, "add", "-A")
    _git(repo, "commit", "-qm", "init")
    base = _git(repo, "rev-parse", "HEAD")
    _git(repo, "mv", "old.ipynb", "new.ipynb")
    _git(repo, "commit", "-qm", "rename pur")

    pinned_probe(repo)
    monkeypatch.chdir(repo)
    assert mod.main(["--base", base]) == 0
    err = capsys.readouterr().err
    assert "pure rename(s) ignored" in err
    assert "#24068" in err


def test_encoding_corruption_base_still_fails_on_added_notebook(
        tmp_path, monkeypatch, pinned_probe):
    """CONTROL POSITIVE: a notebook ADDED since the base, carrying a
    corrupted line, must still be refused."""
    mod = _load("check_encoding_corruption")
    repo = _new_repo(tmp_path)
    _write_nb(repo / "keep.txt", "rien")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-qm", "init")
    base = _git(repo, "rev-parse", "HEAD")
    _write_nb(repo / "added.ipynb", _nb([("markdown", CORRUPT)]))
    _git(repo, "add", "-A")
    _git(repo, "commit", "-qm", "ajout")

    pinned_probe(repo)
    monkeypatch.chdir(repo)
    assert mod.main(["--base", base]) == 1


def test_encoding_corruption_base_still_fails_on_modified_notebook(
        tmp_path, monkeypatch, pinned_probe):
    """CONTROL POSITIVE, second form: an EXISTING notebook whose added line
    carries the artifact must still be refused."""
    mod = _load("check_encoding_corruption")
    repo = _new_repo(tmp_path)
    _write_nb(repo / "kept.ipynb", _nb([("markdown", "propre")]))
    _git(repo, "add", "-A")
    _git(repo, "commit", "-qm", "init")
    base = _git(repo, "rev-parse", "HEAD")
    _write_nb(repo / "kept.ipynb", _nb([("markdown", "propre"),
                                        ("markdown", CORRUPT)]))
    _git(repo, "commit", "-qam", "retouche")

    pinned_probe(repo)
    monkeypatch.chdir(repo)
    assert mod.main(["--base", base]) == 1


def test_encoding_corruption_base_reports_only_new_artifact_on_rename(
        tmp_path, monkeypatch, pinned_probe):
    """A rename WITH edits: the inherited artifact is not re-reported, the
    newly added one is (the delta form, #24066 applied to the CI half)."""
    mod = _load("check_encoding_corruption")
    repo = _new_repo(tmp_path)
    _write_nb(repo / "old.ipynb", _nb([("markdown", CORRUPT),
                                        ("markdown", "ligne de contexte")]))
    _git(repo, "add", "-A")
    _git(repo, "commit", "-qm", "init")
    base = _git(repo, "rev-parse", "HEAD")
    _git(repo, "mv", "old.ipynb", "new.ipynb")
    _write_nb(repo / "new.ipynb", _nb([("markdown", CORRUPT),
                                        ("markdown", "ligne de contexte"),
                                        ("markdown", "ligne ajoutee propre")]))
    _git(repo, "commit", "-qam", "rename + retouche")

    pinned_probe(repo)
    monkeypatch.chdir(repo)
    assert mod.main(["--base", base]) == 0


def test_encoding_corruption_base_reports_new_artifact_on_rename(
        tmp_path, monkeypatch, pinned_probe):
    """Same rename WITH edits, but the ADDED line carries the artifact: the
    guard must still refuse (the delta is not an amnesty)."""
    mod = _load("check_encoding_corruption")
    repo = _new_repo(tmp_path)
    _write_nb(repo / "old.ipynb", _nb([("markdown", "ligne de contexte")]))
    _git(repo, "add", "-A")
    _git(repo, "commit", "-qm", "init")
    base = _git(repo, "rev-parse", "HEAD")
    _git(repo, "mv", "old.ipynb", "new.ipynb")
    _write_nb(repo / "new.ipynb", _nb([("markdown", "ligne de contexte"),
                                        ("markdown", CORRUPT)]))
    _git(repo, "commit", "-qam", "rename + retouche")

    pinned_probe(repo)
    monkeypatch.chdir(repo)
    assert mod.main(["--base", base]) == 1


# ---------------------------------------------------------------------------
# check_cell_source_parses --pr-diff (CI)
# ---------------------------------------------------------------------------

def test_cell_source_parses_pr_diff_ignores_pure_rename(tmp_path, monkeypatch,
                                                         pinned_probe, capsys):
    """A notebook that was only MOVED keeps its cells: no new parse error."""
    mod = _load("check_cell_source_parses")
    repo = _new_repo(tmp_path)
    _write_nb(repo / "old.ipynb", _nb([("code", BROKEN)]))
    _git(repo, "add", "-A")
    _git(repo, "commit", "-qm", "init")
    base = _git(repo, "rev-parse", "HEAD")
    _git(repo, "mv", "old.ipynb", "new.ipynb")
    _git(repo, "commit", "-qm", "rename pur")

    pinned_probe(repo)
    monkeypatch.chdir(repo)
    monkeypatch.setattr(mod, "REPO_ROOT", repo)
    monkeypatch.setattr(sys, "argv", ["check_cell_source_parses.py",
                                      "--pr-diff", base, "HEAD"])
    assert mod.main() == 0
    err = capsys.readouterr().err
    assert "pure rename(s) ignored" in err
    assert "#24068" in err


def test_cell_source_parses_pr_diff_still_fails_on_added_notebook(
        tmp_path, monkeypatch, pinned_probe):
    """CONTROL POSITIVE: a notebook ADDED since the base with a cell that
    does not compile must still be refused."""
    mod = _load("check_cell_source_parses")
    repo = _new_repo(tmp_path)
    _write_nb(repo / "keep.txt", "rien")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-qm", "init")
    base = _git(repo, "rev-parse", "HEAD")
    _write_nb(repo / "added.ipynb", _nb([("code", BROKEN)]))
    _git(repo, "add", "-A")
    _git(repo, "commit", "-qm", "ajout")

    pinned_probe(repo)
    monkeypatch.chdir(repo)
    monkeypatch.setattr(mod, "REPO_ROOT", repo)
    monkeypatch.setattr(sys, "argv", ["check_cell_source_parses.py",
                                      "--pr-diff", base, "HEAD"])
    assert mod.main() == 1


def test_cell_source_parses_pr_diff_still_fails_on_rename_with_edits(
        tmp_path, monkeypatch, pinned_probe):
    """CONTROL POSITIVE, second form: a rename WITH edits is a real change --
    the notebook stays in the target and its broken cell is reported."""
    mod = _load("check_cell_source_parses")
    repo = _new_repo(tmp_path)
    _write_nb(repo / "old.ipynb", _nb([("code", "x = 1")]))
    _git(repo, "add", "-A")
    _git(repo, "commit", "-qm", "init")
    base = _git(repo, "rev-parse", "HEAD")
    _git(repo, "mv", "old.ipynb", "new.ipynb")
    _write_nb(repo / "new.ipynb", _nb([("code", "x = 1"),
                                        ("code", BROKEN)]))
    _git(repo, "commit", "-qam", "rename + retouche")

    pinned_probe(repo)
    monkeypatch.chdir(repo)
    monkeypatch.setattr(mod, "REPO_ROOT", repo)
    monkeypatch.setattr(sys, "argv", ["check_cell_source_parses.py",
                                      "--pr-diff", base, "HEAD"])
    assert mod.main() == 1


# ---------------------------------------------------------------------------
# The range probe itself
# ---------------------------------------------------------------------------

def test_range_probe_reads_the_score_verbatim(tmp_path, pinned_probe):
    """The CI-side probe reports the same shape as the index one."""
    repo = _new_repo(tmp_path)
    _write_nb(repo / "old.ipynb", _nb([("markdown", "a")]))
    _git(repo, "add", "-A")
    _git(repo, "commit", "-qm", "init")
    base = _git(repo, "rev-parse", "HEAD")
    _git(repo, "mv", "old.ipynb", "new.ipynb")
    _git(repo, "commit", "-qm", "rename pur")

    pinned_probe(repo)
    renames = git_index_renames.renames_between(base)
    assert renames == {"new.ipynb": ("old.ipynb", "100")}
    assert git_index_renames.pure_renames_between(base) == {"new.ipynb"}


def test_range_probe_without_git_is_empty(monkeypatch):
    monkeypatch.setattr(git_index_renames, "git_out", lambda *a: None)
    assert git_index_renames.renames_between("main") == {}
    assert git_index_renames.pure_renames_between("main") == set()
