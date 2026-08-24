"""Tests du cablage du strip metadata.papermill par executeur (#12722).

Un test PAR EXECUTEUR : le defaut etait un correctif pose sur une moitie du
mecanisme (dotnet_executor seul, #11146) et jamais grepe sur ses jumeaux —
11 PRs bloquees par le ratchet STALE_BLOCK (#11155) au 2026-08-24. Un test
unique sur le module partage ne prouverait pas le CABLAGE, et c'est le
cablage qui manquait.

Chaque test ecrit un notebook factice portant un bloc ``metadata.papermill``
perime, le passe au point d'ecriture DE L'EXECUTEUR, et verifie que le bloc
a disparu apres ecriture. Avant le fix, chaque test echoue (le bloc survit).

Les executeurs kernel (dotnet_executor, exec_single_cell) sont testes par
subprocess reel sur kernel python3 — le parametre kernel est generique, pas
besoin de .NET. Les executeurs exigeant une infra non disponible en CI
(exec_dotnet_persist : kernel .NET ; execute_qcpy_docker : Docker/quantbook)
sont testes sur leur point d'ecriture extrait, ``_save_executed``.
"""

import json
import subprocess
import sys
from pathlib import Path

import pytest

TOOLS = Path(__file__).resolve().parent.parent / "notebook_tools"
sys.path.insert(0, str(TOOLS))

STALE_BLOCK = {
    "default_parameters": {},
    "duration": 9.28,
    "end_time": "2026-05-31T22:55:02.293900+00:00",
    "environment_variables": {},
    "exception": None,
    "start_time": "2026-05-31T22:54:53.016187+00:00",
    "version": "2.6.0",
}


def _write_fake_nb(path: Path) -> Path:
    nb = {
        "cells": [
            {"cell_type": "code", "id": "c0", "metadata": {},
             "execution_count": None, "outputs": [],
             "source": "1 + 1"},
        ],
        "metadata": {
            "kernelspec": {"display_name": "Python 3", "language": "python",
                           "name": "python3"},
            "language_info": {"name": "python"},
            "papermill": dict(STALE_BLOCK),
        },
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    path.write_text(json.dumps(nb, indent=1, ensure_ascii=False) + "\n",
                    encoding="utf-8")
    return path


def _papermill_block_of(path: Path):
    nb = json.loads(path.read_text(encoding="utf-8"))
    return nb.get("metadata", {}).get("papermill")


# --- notebook_helpers : executeur de kernel generique (2 points d'ecriture) ---

def test_notebook_helpers_save_strips_stale_block(tmp_path):
    from notebook_helpers import NotebookHelper
    p = _write_fake_nb(tmp_path / "nb.ipynb")
    helper = NotebookHelper(str(p))
    helper.notebook["cells"][0]["execution_count"] = 1
    helper.save()
    assert _papermill_block_of(p) is None, (
        "NotebookHelper.save() doit retirer le bloc perime : les sorties "
        "fraiches decrivent CE run, pas la passe papermill du 2026-05-31")


def test_notebook_helpers_write_notebook_strips_stale_block(tmp_path):
    from notebook_helpers import write_notebook
    p = _write_fake_nb(tmp_path / "nb.ipynb")
    nb = json.loads(p.read_text(encoding="utf-8"))
    write_notebook(str(p), nb)
    assert _papermill_block_of(p) is None


# --- exec_dotnet_persist : point d'ecriture extrait (kernel .NET requis sinon) ---

def test_exec_dotnet_persist_save_executed_strips_stale_block(tmp_path):
    from exec_dotnet_persist import _save_executed
    p = _write_fake_nb(tmp_path / "nb.ipynb")
    nb = json.loads(p.read_text(encoding="utf-8"))
    _save_executed(nb, p)
    assert _papermill_block_of(p) is None


# --- execute_qcpy_docker : point d'ecriture extrait (Docker requis sinon) ---

def test_execute_qcpy_docker_save_executed_strips_stale_block(tmp_path):
    pytest.importorskip("websocket")
    from execute_qcpy_docker import _save_executed
    p = _write_fake_nb(tmp_path / "nb.ipynb")
    nb = json.loads(p.read_text(encoding="utf-8"))
    _save_executed(nb, p)
    assert _papermill_block_of(p) is None


# --- executeurs kernel generiques : subprocess reel sur kernel python3 ---------

def _run_subprocess(script: str, args: list, tmp_path: Path):
    p = _write_fake_nb(tmp_path / "nb.ipynb")
    r = subprocess.run(
        [sys.executable, str(TOOLS / script), str(p), *args],
        capture_output=True, text=True, timeout=180, cwd=str(TOOLS),
        encoding="utf-8", errors="replace")
    assert r.returncode == 0, f"{script} stderr:\n{r.stderr[-800:]}"
    assert _papermill_block_of(p) is None, (
        f"{script} reecrit le notebook sans retirer le bloc papermill perime")


def test_dotnet_executor_subprocess_strips_stale_block(tmp_path):
    _run_subprocess("dotnet_executor.py", ["--kernel", "python3",
                                           "--timeout", "60"], tmp_path)


def test_exec_single_cell_subprocess_strips_stale_block(tmp_path):
    _run_subprocess("exec_single_cell.py", ["--index", "0",
                                            "--timeout", "60"], tmp_path)
