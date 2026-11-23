#!/usr/bin/env python3
"""Tests de la pagination de la liste des fichiers d'une PR (#27684).

``gh pr view --json files`` plafonne a **100** fichiers : au-dela, la vue est
tronquee sans le dire. Le controle de perimetre de ``merge_ready`` est
fail-closed, donc la troncature rendait la PR non mergeable au lieu de
signaler un fichier hors perimetre. L'organe lit desormais le REST pagine
``/pulls/{n}/files``.

Aucun acces reseau : un runner script e rend les pages une par une.
"""
from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
MERGE_READY_PATH = HERE.parent / "coordination" / "merge_ready.py"
_spec = importlib.util.spec_from_file_location("merge_ready_pagination_under_test",
                                              MERGE_READY_PATH)
mr = importlib.util.module_from_spec(_spec)
sys.modules["merge_ready_pagination_under_test"] = mr
_spec.loader.exec_module(mr)


class RunnerFaux:
    """Runner qui repond aux pages ``/pulls/{n}/files`` script ees."""

    def __init__(self, pages: dict[int, list[list[dict]]] | None = None,
                 rc: int = 0, stdout_brut: str | None = None):
        self.pages = pages or {}
        self.rc = rc
        self.stdout_brut = stdout_brut
        self.calls: list[list[str]] = []

    def run(self, cmd: list[str], env: dict | None = None) -> mr.RunResult:
        self.calls.append(list(cmd))
        if self.stdout_brut is not None:
            return mr.RunResult(self.rc, self.stdout_brut, "")
        if self.rc != 0:
            return mr.RunResult(self.rc, "", "gh failed")
        pr = int(cmd[2].split("/pulls/")[1].split("/")[0])
        page = int(cmd[2].rsplit("page=", 1)[1].split("&")[0])
        pages = self.pages.get(pr, [])
        payload = pages[page - 1] if 0 < page <= len(pages) else []
        return mr.RunResult(0, json.dumps(payload), "")

    def sleep(self, seconds: float) -> None:
        return None


def _vue(nb_fichiers: int, changes: int | None = None) -> dict:
    return {
        "files": [{"path": f"src/f{i}.py"} for i in range(nb_fichiers)],
        "changedFiles": changes if changes is not None else nb_fichiers,
    }


def test_vue_complete_ne_appelle_pas_le_rest():
    runner = RunnerFaux()
    fichiers = mr.fetch_pr_files(runner, 123, _vue(10), {})
    assert fichiers == [{"path": f"src/f{i}.py"} for i in range(10)]
    assert runner.calls == []


def test_vue_tronquee_complete_le_rest_par_pages():
    # 146 fichiers : la vue en montre 100, le REST en rend 146 en 2 pages.
    runner = RunnerFaux(
        pages={
            123: [
                [{"filename": f"src/f{i}.py"} for i in range(100)],
                [{"filename": f"src/f{i}.py"} for i in range(100, 146)],
            ]
        }
    )
    fichiers = mr.fetch_pr_files(runner, 123, _vue(100, changes=146), {})
    assert fichiers is not None
    assert len(fichiers) == 146
    assert fichiers[0] == {"path": "src/f0.py"}
    assert fichiers[-1] == {"path": "src/f145.py"}
    # Le REST nomme `filename` ; la vue nomme `path` : la forme rendue est
    # celle de la vue, pour que les consommateurs ne changent pas.
    assert all(set(row) == {"path"} for row in fichiers)
    assert len(runner.calls) == 2
    assert "per_page=100" in runner.calls[0][2]


def test_lecture_illisible_rend_none():
    runner = RunnerFaux(rc=1)
    assert mr.fetch_pr_files(runner, 123, _vue(100, changes=150), {}) is None


def test_stdout_non_json_rend_none():
    runner = RunnerFaux(stdout_brut="pas du json", rc=0)
    assert mr.fetch_pr_files(runner, 123, _vue(100, changes=150), {}) is None


def test_reponse_non_liste_rend_none():
    runner = RunnerFaux(stdout_brut=json.dumps({"message": "rate limit"}), rc=0)
    assert mr.fetch_pr_files(runner, 123, _vue(100, changes=150), {}) is None


def test_page_vide_arrete_la_pagination():
    runner = RunnerFaux(pages={123: [[{"filename": "src/a.py"}]]})
    fichiers = mr.fetch_pr_files(runner, 123, _vue(1, changes=150), {})
    assert fichiers == [{"path": "src/a.py"}]
    assert len(runner.calls) == 1


def test_ligne_rest_sans_nom_de_fichier_rend_none():
    # Reserve 1 de NanoClaw (#27749) : une ligne REST sans `filename` ni
    # `path` ne doit pas produire `{"path": ""}` — un chemin vide ne matche
    # aucune exclusion de perimetre, la garde le lirait comme « hors
    # harnais ». Fail-closed : la ligne est illisible, la liste entiere
    # l'est aussi.
    runner = RunnerFaux(
        pages={123: [[{"filename": "src/a.py"}, {"sha": "abc123"}]]}
    )
    assert mr.fetch_pr_files(runner, 123, _vue(100, changes=150), {}) is None


def test_ligne_rest_au_chemin_vide_rend_none():
    runner = RunnerFaux(pages={123: [[{"filename": "src/a.py"}, {"filename": "  "}]]})
    assert mr.fetch_pr_files(runner, 123, _vue(100, changes=150), {}) is None


def test_ligne_rest_au_champ_path_non_chaine_rend_none():
    runner = RunnerFaux(pages={123: [[{"filename": "src/a.py"}, {"filename": 42}]]})
    assert mr.fetch_pr_files(runner, 123, _vue(100, changes=150), {}) is None
