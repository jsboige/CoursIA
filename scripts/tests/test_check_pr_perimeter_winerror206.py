#!/usr/bin/env python3
"""#28843: un perimetre large ne fait plus tomber la mesure du perimetre.

Sur Windows, ``CreateProcess`` borne la ligne de commande a 32 767 caracteres et
``Popen`` leve ``OSError`` (WinError 206) **avant** tout code de retour : la
liste des chemins d'une PR de renommage (508 chemins = 46 718 caracteres
mesures) rendait ``_classify_carried`` injouable, alors que sa docstring promet
un repli sur toute panne d'instrument.

Ces tests figent les deux moities de la reparation : le decoupage respecte le
budget et fait l'union, et l'``OSError`` rend le repli documente au lieu d'un
traceback. Les tests sont hermetiques : ``sys.platform`` et ``subprocess.run``
sont posees par monkeypatch, donc ils passent aussi bien sur Windows que sur la
CI ubuntu.
"""

import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import check_pr_perimeter as cpp  # noqa: E402

PREFIX = ["git", "diff", "--name-only", "-z"]
PREFIX_LEN = len(PREFIX) + 3  # + base_ref, head, "--"


class _FakeProc:
    """Sortie minimale d'un ``subprocess.run`` substitue."""

    def __init__(self, stdout: bytes = b"", returncode: int = 0) -> None:
        self.stdout = stdout
        self.returncode = returncode


def _long_paths(n: int, width: int = 110) -> list[str]:
    return [
        f"MyIA.AI.Notebooks/Serie/Sous-serie/{i:03d}-" + "x" * width + ".ipynb"
        for i in range(n)
    ]


def _nul(paths: list[str]) -> bytes:
    return b"\0".join(p.encode("utf-8") for p in paths) + (b"\0" if paths else b"")


def test_chunk_pathspecs_splits_under_budget_and_preserves_order():
    paths = _long_paths(40)
    budget = 2_000
    chunks = cpp._chunk_pathspecs("origin/main", "deadbeef", paths, budget)

    assert len(chunks) > 1, "un budget serre doit produire plusieurs tranches"
    assert [p for chunk in chunks for p in chunk] == paths, "union et ordre preserves"
    prefix = PREFIX + ["origin/main", "deadbeef", "--"]
    for chunk in chunks:
        assert len(subprocess.list2cmdline(prefix + chunk)) <= budget


def test_chunk_budget_below_one_line_makes_one_path_per_chunk():
    """Controle a reponse connue : le decoupage s'ancre sur la longueur mesuree."""
    paths = _long_paths(5)
    chunks = cpp._chunk_pathspecs("origin/main", "deadbeef", paths, 1)
    assert chunks == [[p] for p in paths]


def test_changed_paths_unions_all_chunks(monkeypatch):
    paths = _long_paths(30)
    calls: list[list[str]] = []

    def fake_run(argv, capture_output=True, **kwargs):
        chunk = list(argv[PREFIX_LEN:])
        calls.append(chunk)
        return _FakeProc(stdout=_nul(chunk))

    monkeypatch.setattr(cpp.subprocess, "run", fake_run)
    monkeypatch.setattr(cpp.sys, "platform", "win32")
    monkeypatch.setattr(cpp, "_PATHSPEC_BUDGET_WINDOWS", 2_000)

    changed = cpp._changed_paths("origin/main", "head", paths)

    assert changed == set(paths), "l'union des tranches doit rendre tous les chemins"
    assert len(calls) > 1, "la liste longue doit avoir ete decoupee"
    assert [p for chunk in calls for p in chunk] == paths


def test_changed_paths_returns_none_on_oserror(monkeypatch):
    """WinError 206 est leve avant tout code de retour : pas de `returncode` a lire."""

    def boom(*args, **kwargs):
        raise OSError(206, "Nom de fichier ou extension trop long")

    monkeypatch.setattr(cpp.subprocess, "run", boom)
    monkeypatch.setattr(cpp.sys, "platform", "win32")

    assert cpp._changed_paths("origin/main", "head", ["a.ipynb"]) is None


def test_changed_paths_returns_none_on_git_error(monkeypatch):
    monkeypatch.setattr(cpp.subprocess, "run", lambda *a, **k: _FakeProc(b"", 129))
    assert cpp._changed_paths("origin/main", "head", ["a.ipynb"]) is None


def test_classify_carried_partitions_own_and_carried(monkeypatch):
    files = [{"path": "a.ipynb"}, {"path": "b.ipynb"}, {"path": "c.ipynb"}]
    monkeypatch.setattr(cpp, "_resolve_base_pair", lambda pr: ("headsha", "origin/main"))
    monkeypatch.setattr(cpp, "_base_age_hours", lambda base, head: 12)
    monkeypatch.setattr(
        cpp.subprocess, "run", lambda *a, **k: _FakeProc(stdout=_nul(["a.ipynb", "c.ipynb"]))
    )
    monkeypatch.setattr(cpp.sys, "platform", "win32")

    note = cpp._classify_carried(1, files)

    assert [f["path"] for f in note.propres] == ["a.ipynb", "c.ipynb"]
    assert [f["path"] for f in note.charries] == ["b.ipynb"]
    assert note.base_age_hours == 12


def test_classify_carried_falls_back_on_oserror(monkeypatch):
    """Le repli promis par la docstring : aucun fichier n'est exclu a tort."""
    files = [{"path": "a.ipynb"}, {"path": "b.ipynb"}]
    monkeypatch.setattr(cpp, "_resolve_base_pair", lambda pr: ("headsha", "origin/main"))

    def boom(*args, **kwargs):
        raise OSError(206, "Nom de fichier ou extension trop long")

    monkeypatch.setattr(cpp.subprocess, "run", boom)
    monkeypatch.setattr(cpp.sys, "platform", "win32")

    note = cpp._classify_carried(1, files)

    assert note.propres == files
    assert note.charries == []
    assert note.base_age_hours is None
