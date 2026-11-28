"""Les organes de carnets doivent lire des chemins REELS, pas des chemins cites.

`git` *cite* les chemins non ASCII quand `core.quotePath` vaut `true` (le
defaut) : `Créateur de mail personnalisé.ipynb` sort `Cr\\303\\251ateur de
mail personnalis\\303\\251.ipynb`, entoure de guillemets. Ce chemin n'existe
pas sur le disque, et les organes qui le consomment se trompent :

- `check_cell_id_invalid_ratchet.py` levait `Invalid argument` a la lecture et
  rendait exit 2 « mesure impossible » (#28632) ;
- `check_papermill_ratchet.py` annoncait `ADDED` sur un carnet que la PR ne
  faisait que modifier (#28632) ;
- `check_exec_ratchet.py`, `check_execution_signature.py`,
  `check_cell_source_parses.py`, `check_latex_control_chars.py` et
  `check_activity_leak.py` ecartaient le carnet en silence -- un **faux
  vert**, la panne la plus dangereuse.

Le correctif est deja dans le depot (`check_notebook_navlinks.py`,
`check_notebook_nav_chain.py`) : `-c core.quotePath=false`.

Ces tests pient le contrat sur un vrai depot git miniature (nom accentue
reel) et verifient l'invariant mecanique sur toute la famille d'organes.
"""
import ast
import json
import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import check_cell_id_invalid_ratchet as cell_id_gate
import check_exec_ratchet as exec_gate
import check_papermill_ratchet as pm_gate

ORGANS_DIR = Path(__file__).resolve().parent.parent
ACCENTED = "Créateur de mail personnalisé.ipynb"


def git_ok(repo, *args):
    return subprocess.run(["git", *args], cwd=repo, check=True,
                          capture_output=True, encoding="utf-8")


@pytest.fixture
def repo(tmp_path):
    subprocess.run(["git", "init", "-q"], cwd=tmp_path, check=True,
                   capture_output=True)
    git_ok(tmp_path, "config", "user.email", "t@t")
    git_ok(tmp_path, "config", "user.name", "t")
    git_ok(tmp_path, "config", "core.autocrlf", "false")
    return tmp_path


def commit(repo, msg):
    git_ok(repo, "add", "-A")
    git_ok(repo, "commit", "-m", msg)
    return subprocess.run(["git", "rev-parse", "HEAD"], cwd=repo,
                          check=True, capture_output=True,
                          encoding="utf-8").stdout.strip()


def write_nb(repo, rel, outputs):
    path = repo / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    nb = {"cells": [{"cell_type": "code", "execution_count": 1,
                     "source": "print(1)", "outputs": outputs,
                     "metadata": {}}],
          "metadata": {"papermill": {"input_path": rel, "output_path": rel,
                                      "start_time": "2026-08-16T10:00:00",
                                      "end_time": "2026-08-16T10:01:00",
                                      "duration": 60.0, "exception": False}},
          "nbformat": 4, "nbformat_minor": 5}
    path.write_text(json.dumps(nb), encoding="utf-8")


OUT1 = [{"output_type": "stream", "name": "stdout", "text": "hello"}]
OUT2 = [{"output_type": "stream", "name": "stdout", "text": "world"}]


class TestAccentedPathIsReadForReal:
    """Le chemin cite ne doit jamais atteindre le disque ni le rapport."""

    def test_cell_id_ratchet_lists_the_real_accented_path(self, repo):
        write_nb(repo, ACCENTED, OUT1)
        base = commit(repo, "base")
        write_nb(repo, ACCENTED, OUT2)
        commit(repo, "head")
        monkey = pytest.MonkeyPatch()
        monkey.chdir(repo)
        try:
            paths = cell_id_gate.changed_notebooks(base)
        finally:
            monkey.undo()
        assert paths == [ACCENTED]

    def test_cell_id_ratchet_measures_instead_of_exiting_2(self, repo):
        """Le defaut mesuré : `Invalid argument` -> exit 2 « impossible »."""
        write_nb(repo, ACCENTED, OUT1)
        base = commit(repo, "base")
        write_nb(repo, ACCENTED, OUT2)
        commit(repo, "head")
        monkey = pytest.MonkeyPatch()
        monkey.chdir(repo)
        try:
            rc = cell_id_gate.main([base])
        finally:
            monkey.undo()
        assert rc == 0

    def test_papermill_ratchet_does_not_report_ADDED(self, repo):
        """Un carnet MODIFIE ne doit pas passer pour un carnet AJOUTE."""
        write_nb(repo, ACCENTED, OUT1)
        base = commit(repo, "base")
        write_nb(repo, ACCENTED, OUT2)
        commit(repo, "head")
        recs = pm_gate.ratchet(base, cwd=repo)
        assert [r["notebook"] for r in recs] == [ACCENTED]
        assert recs[0]["verdict"] != "ADDED"

    def test_exec_ratchet_lists_the_real_accented_path(self, repo):
        write_nb(repo, ACCENTED, OUT1)
        base = commit(repo, "base")
        write_nb(repo, ACCENTED, OUT2)
        commit(repo, "head")
        assert exec_gate.changed_notebooks(base, cwd=repo) == [ACCENTED]


# --------------------------------------------------------------------------
# Invariant mecanique : tout `git` qui EMET des chemins doit desactiver le
# citement -- soit par `-z` (sortie brute), soit par `core.quotePath=false`.
# --------------------------------------------------------------------------

PATH_EMITTING_ARGS = ("--name-only", "--name-status")


def _string_elements(node):
    """Elements string litteraux d'une liste (hors Starred)."""
    out = []
    for elt in getattr(node, "elts", []):
        if isinstance(elt, ast.Constant) and isinstance(elt.value, str):
            out.append(elt.value)
    return out


def _strings_of(node):
    """Chaines litterales d'un argument (Constante ou liste)."""
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        return [node.value]
    return _string_elements(node)


def _git_lists(tree):
    """Listes Python dont le premier element est la chaine "git"."""
    for node in ast.walk(tree):
        if isinstance(node, ast.List) and _string_elements(node)[:1] == ["git"]:
            yield node


def _helper_git_list(tree, helper_name):
    """Le List du corps d'un helper `def helper(*args)` qui lance git."""
    for node in ast.walk(tree):
        if isinstance(node, ast.FunctionDef) and node.name == helper_name:
            for sub in ast.walk(node):
                if isinstance(sub, ast.List) and _string_elements(sub)[:1] == ["git"]:
                    return sub
    return None


def _helper_calls_emitting_paths(tree, helper_name):
    """Appels `helper(..., "--name-only", ...)`."""
    hits = []
    for node in ast.walk(tree):
        if (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
                and node.func.id == helper_name):
            strings = []
            for arg in node.args:
                strings.extend(_strings_of(arg))
            if any(s in PATH_EMITTING_ARGS for s in strings):
                hits.append(node)
    return hits


def _safe(elements):
    # La cle de config git est insensible a la casse : `core.quotepath=false`
    # vaut `core.quotePath=false`.
    return "-z" in elements or any(
        e.strip().lower() == "core.quotepath=false" for e in elements)


@pytest.mark.parametrize("path", sorted(ORGANS_DIR.glob("*.py")),
                         ids=lambda p: p.name)
def test_path_emitting_git_calls_disable_path_quoting(path):
    """Aucun `git` qui emet des chemins ne doit citer les chemins non ASCII."""
    tree = ast.parse(path.read_text(encoding="utf-8"))
    offenders = []
    for lst in _git_lists(tree):
        elements = _string_elements(lst)
        if any(a in elements for a in PATH_EMITTING_ARGS) and not _safe(elements):
            offenders.append(f"liste littérale ligne {lst.lineno}")
    # helper `git(*args)` : le drapeau doit etre dans le List du helper
    helper = _helper_git_list(tree, "git")
    if helper is not None and _helper_calls_emitting_paths(tree, "git"):
        if not _safe(_string_elements(helper)):
            offenders.append("helper git() sans core.quotePath=false")
    assert not offenders, f"{path.name} : {offenders}"
