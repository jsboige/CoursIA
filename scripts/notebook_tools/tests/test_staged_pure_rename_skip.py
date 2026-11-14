"""Tests for the shared pure-rename skip applied to the four path-keyed
defect hooks (#24068, volet « autres hooks » of #24039).

The defect class: pre-commit hands these hooks the staged filenames
(``pass_filenames: true``) and none of them knew a file can merely be
*MOVED*. A consolidation-by-move (the #23553 case) re-passed each moved
notebook in front of the predicates, so a moved-but-untouched notebook that
already carried a defect came out red -- on a gesture that did not introduce
it -- and the only visible way out was ``SKIP=``, i.e. disabling the guard.

What each test asserts, per the issue's acceptance criteria:

  1. the pure rename is IGNORED by the hook (no finding);
  2. the CONTROL POSITIVE holds: the same defect in a file that is NOT a
     pure rename still makes the hook fail. Without (2), the skip would be
     a blanket silence -- the failure mode the issue names explicitly.

The probe itself lives in ``scripts/audit/git_index_renames.py``; these tests
patch its ``git_out`` (the single source both probes read) rather than
patching each hook, so the wiring is exercised end to end.
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
# name (check_null_exec -> validate_pr_notebooks), so the folder itself must
# be on sys.path for a by-path load to resolve those.
sys.path.insert(0, str(REPO_ROOT / "scripts" / "notebook_tools"))
sys.path.insert(0, str(REPO_ROOT / "scripts" / "audit"))

import git_index_renames  # noqa: E402


def _load(module_name: str):
    """Load a notebook_tools script by path (notebook_tools/ is not a package).

    Same rationale as the sibling test files: a direct path-based load keeps
    the import unambiguous under both local pytest and CI's --import-mode
    importlib.
    """
    path = REPO_ROOT / "scripts" / "notebook_tools" / f"{module_name}.py"
    spec = importlib.util.spec_from_file_location(module_name, str(path))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _staged(*pairs: str) -> str:
    """Build a ``git diff --cached --name-status -z`` payload.

    Each pair is ``<status>\\0<old>\\0<new>`` (status carries the score
    verbatim: R100, R087, ...).
    """
    return "".join(p + "\0" for p in pairs)


@pytest.fixture(autouse=True)
def _hermetic_probe(monkeypatch):
    """Pin the probe to "no rename" by default: a unit test must not read the
    contributor's staging area, which would make the suite depend on
    whatever happens to be ``git add``-ed at the time it runs."""
    monkeypatch.setattr(git_index_renames, "git_out", lambda *a: "")


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
    path.write_text(json.dumps(nb, ensure_ascii=False), encoding="utf-8")
    return path


# ---------------------------------------------------------------------------
# The shared probe itself
# ---------------------------------------------------------------------------

def test_probe_reads_the_score_verbatim(monkeypatch):
    payload = _staged("R100", "old/a.py", "new/a.py",
                      "R087", "old/b.py", "new/b.py",
                      "M", "plain.py")
    monkeypatch.setattr(git_index_renames, "git_out", lambda *a: payload)
    assert git_index_renames.staged_pure_renames() == {"new/a.py"}
    assert git_index_renames.staged_renames_with_old() == {
        "new/a.py": "old/a.py",
        "new/b.py": "old/b.py",
    }


def test_probe_without_git_is_empty(monkeypatch):
    monkeypatch.setattr(git_index_renames, "git_out", lambda *a: None)
    assert git_index_renames.staged_pure_renames() == set()
    assert git_index_renames.staged_renames_with_old() == {}


def test_skip_pure_renames_normalises_windows_separators(monkeypatch):
    """pre-commit hands Windows paths with backslashes; git reports forward
    slashes. The comparison must survive the difference."""
    payload = _staged("R100", "old/dir/x.ipynb", "new/dir/x.ipynb")
    monkeypatch.setattr(git_index_renames, "git_out", lambda *a: payload)
    kept, skipped = git_index_renames.skip_pure_renames(
        ["new\\dir\\x.ipynb", "other.ipynb"])
    assert skipped == ["new\\dir\\x.ipynb"]
    assert kept == ["other.ipynb"]


# ---------------------------------------------------------------------------
# Hook 1/4 -- check_null_exec (H.3)
# ---------------------------------------------------------------------------

def test_null_exec_ignores_pure_rename(tmp_path, monkeypatch, capsys):
    mod = _load("check_null_exec")
    nb = _write_nb(tmp_path / "moved.ipynb", _nb([("code", "x = 1")]))
    payload = _staged("R100", "old/moved.ipynb", nb.as_posix())
    monkeypatch.setattr(git_index_renames, "git_out", lambda *a: payload)
    assert mod.main([str(nb)]) == 0
    out = capsys.readouterr()
    assert "pure rename(s) ignored" in out.err
    assert "#24068" in out.err


def test_null_exec_still_fails_on_non_rename(tmp_path, monkeypatch):
    """CONTROL POSITIVE: the same defect in a file that is not a pure rename
    must still be refused."""
    mod = _load("check_null_exec")
    nb = _write_nb(tmp_path / "stayed.ipynb", _nb([("code", "x = 1")]))
    payload = _staged("R100", "old/other.ipynb", "somewhere/other.ipynb")
    monkeypatch.setattr(git_index_renames, "git_out", lambda *a: payload)
    assert mod.main([str(nb)]) == 1


# ---------------------------------------------------------------------------
# Hook 2/4 -- check_cell_source_parses
# ---------------------------------------------------------------------------

def test_cell_source_parses_ignores_pure_rename(tmp_path, monkeypatch, capsys):
    mod = _load("check_cell_source_parses")
    broken = "def f(:\n    pass\n"  # does not compile
    nb = _write_nb(tmp_path / "moved.ipynb", _nb([("code", broken)]))
    payload = _staged("R100", "old/moved.ipynb", nb.as_posix())
    monkeypatch.setattr(git_index_renames, "git_out", lambda *a: payload)
    monkeypatch.setattr(sys, "argv", ["check_cell_source_parses.py", str(nb)])
    assert mod.main() == 0
    err = capsys.readouterr().err
    assert "pure rename(s) ignored" in err
    assert "#24068" in err


def test_cell_source_parses_still_fails_on_non_rename(tmp_path, monkeypatch):
    """CONTROL POSITIVE."""
    mod = _load("check_cell_source_parses")
    broken = "def f(:\n    pass\n"
    nb = _write_nb(tmp_path / "stayed.ipynb", _nb([("code", broken)]))
    payload = _staged("R100", "old/other.ipynb", "somewhere/other.ipynb")
    monkeypatch.setattr(git_index_renames, "git_out", lambda *a: payload)
    monkeypatch.setattr(sys, "argv", ["check_cell_source_parses.py", str(nb)])
    assert mod.main() == 1


# ---------------------------------------------------------------------------
# Hook 3/4 -- check_encoding_corruption
# ---------------------------------------------------------------------------

def test_encoding_corruption_ignores_pure_rename(tmp_path, monkeypatch, capsys):
    mod = _load("check_encoding_corruption")
    nb = _write_nb(tmp_path / "moved.ipynb",
                   _nb([("markdown", "mÃ©taheuristique â€” plateau")]))
    payload = _staged("R100", "old/moved.ipynb", nb.as_posix())
    monkeypatch.setattr(git_index_renames, "git_out", lambda *a: payload)
    assert mod.main([str(nb)]) == 0
    err = capsys.readouterr().err
    assert "pure rename(s) ignored" in err
    assert "#24068" in err


def test_encoding_corruption_still_fails_on_non_rename(tmp_path, monkeypatch):
    """CONTROL POSITIVE."""
    mod = _load("check_encoding_corruption")
    nb = _write_nb(tmp_path / "stayed.ipynb",
                   _nb([("markdown", "mÃ©taheuristique â€” plateau")]))
    payload = _staged("R100", "old/other.ipynb", "somewhere/other.ipynb")
    monkeypatch.setattr(git_index_renames, "git_out", lambda *a: payload)
    assert mod.main([str(nb)]) == 1


# ---------------------------------------------------------------------------
# Hook 4/4 -- check_knots_extracts
# ---------------------------------------------------------------------------

def test_knots_extracts_ignores_pure_rename(tmp_path, monkeypatch, capsys):
    mod = _load("check_knots_extracts")
    stale = "from `knot_lean/Knots/DoesNotExist.lean` import x"
    nb = _write_nb(tmp_path / "moved.ipynb", _nb([("markdown", stale)]))
    payload = _staged("R100", "old/moved.ipynb", nb.as_posix())
    monkeypatch.setattr(git_index_renames, "git_out", lambda *a: payload)
    # The default --path-filter targets Lean/KNOTS/; the moved notebook must
    # match it for the skip to be the thing under test.
    assert mod.main([str(nb), "--path-filter", ""]) == 0
    err = capsys.readouterr().err
    assert "pure rename(s) ignored" in err
    assert "#24068" in err


def test_knots_extracts_still_fails_on_non_rename(tmp_path, monkeypatch):
    """CONTROL POSITIVE."""
    mod = _load("check_knots_extracts")
    stale = "from `knot_lean/Knots/DoesNotExist.lean` import x"
    nb = _write_nb(tmp_path / "stayed.ipynb", _nb([("markdown", stale)]))
    payload = _staged("R100", "old/other.ipynb", "somewhere/other.ipynb")
    monkeypatch.setattr(git_index_renames, "git_out", lambda *a: payload)
    assert mod.main([str(nb), "--path-filter", ""]) == 1


# ---------------------------------------------------------------------------
# The probe is reachable from every hook (the wiring, not the behaviour)
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("module_name", [
    "check_null_exec",
    "check_cell_source_parses",
    "check_encoding_corruption",
    "check_knots_extracts",
])
def test_hook_imports_the_shared_probe(module_name):
    """Every hook of the family must read the SAME probe -- four copies of
    the parser would drift, which is the failure the issue names when it
    asks for mutualisation."""
    mod = _load(module_name)
    assert hasattr(mod, "skip_pure_renames"), (
        f"{module_name} does not use the shared rename probe")
    assert mod.skip_pure_renames is git_index_renames.skip_pure_renames


def test_hook_scripts_stay_importable_under_python39():
    """The py39 hook-import guard follows the import closure of every
    ``entry:`` script. The new shared module is in that closure for four
    hooks, so it must carry the future-import the guard requires."""
    src = (REPO_ROOT / "scripts" / "audit" / "git_index_renames.py").read_text(
        encoding="utf-8")
    assert "from __future__ import annotations" in src


# ---------------------------------------------------------------------------
# Un git qui ne repond pas comme git (mesure #25032 en CI)
# ---------------------------------------------------------------------------

def test_a_misbehaving_git_cannot_break_the_probe(monkeypatch):
    """Une reponse de `rev-parse` qui n'est pas un repertoire ne doit JAMAIS
    devenir un chemin.

    Mesure (CI Linux, #25032) : la sonde `git_out` etant remplacee par un
    payload `--name-status -z` (il contient des NUL), `repo_root()` le
    transformait en chemin ; `Path(...).resolve()` levait alors
    `ValueError: embedded null byte` et la garde TOMBAIT au lieu de scanner.
    Le meme test passait sur Windows (l'appel systeme y tolere le NUL) :
    un vert local qui ne prouve rien (cf. le controle positif ci-dessous)."""
    payload = _staged("R100", "old/a.py", "new/a.py")
    monkeypatch.setattr(git_index_renames, "git_out", lambda *a: payload)
    monkeypatch.setattr(git_index_renames, "_TOPLEVEL", {})

    root = git_index_renames.repo_root()          # ne doit pas lever
    assert root == git_index_renames.REPO_ROOT, (
        "une reponse inutilisable doit se replier sur la racine du module")
    assert git_index_renames.staged_pure_renames() == {"new/a.py"}
    kept, skipped = git_index_renames.skip_pure_renames(["new/a.py"])
    assert skipped == ["new/a.py"]
    assert kept == []


def test_a_misbehaving_git_does_not_poison_the_root_cache(monkeypatch):
    """Le CACHE de racine est memorise par repertoire courant : une racine
    inutilisable memorisee pollue tous les appelants suivants du meme
    repertoire (mesure : un test pre-existant de `check_encoding_corruption`,
    qui n'a rien a voir avec la sonde, echouait sur la racine polluee)."""
    payload = _staged("R100", "old/a.py", "new/a.py")
    monkeypatch.setattr(git_index_renames, "git_out", lambda *a: payload)
    monkeypatch.setattr(git_index_renames, "_TOPLEVEL", {})
    git_index_renames.repo_root()

    # git redevient correct : la racine doit redevenir la vraie racine.
    monkeypatch.setattr(git_index_renames, "git_out", lambda *a: "")
    monkeypatch.setattr(git_index_renames, "_TOPLEVEL", {})
    root = git_index_renames.repo_root()
    assert root == git_index_renames.REPO_ROOT
    assert (root / "scripts").is_dir()


def test_the_comparison_key_is_the_same_on_every_platform():
    """La CLE de comparaison doit etre identique sur les deux plateformes.

    Sur Windows, `Path.as_posix()` convertit les antislashs ; sur POSIX, un
    antislash est un caractere legal de nom de fichier et la conversion n'a
    jamais lieu -- les memes appels produisaient donc deux cles differentes,
    et le skip ne mordait que sur la machine Windows (vert local, rouge en
    CI). La conversion est desormais explicite."""
    key = git_index_renames.repo_relative("dossier\\sous\\fichier.ipynb")
    assert key == "dossier/sous/fichier.ipynb"
    assert git_index_renames.repo_relative("dossier/sous/fichier.ipynb") == key
