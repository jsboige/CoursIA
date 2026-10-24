"""Tests de `scripts/ci/filter_pr_introduced_notebooks.py` (#22298).

Ce que le fichier prouve
------------------------
  1. Un carnet qu'aucun commit **propre a la PR** ne touche est retire de la
     liste -- c'est le defaut qui a produit trois faux `MD_REWRITE` sur
     #21650, ou la base du stack etait en retard de 521 commits et le diff
     rendait 287 carnets pour un seul fichier reellement ecrit.
  2. **Controle positif** : un carnet que la PR a reellement ecrit reste dans
     la liste. Un filtre qui eteindrait le gate passerait le point 1 et
     echouerait ici.
  3. **Un commit de merge n'apporte aucun chemin** : integrer `main` dans sa
     branche ne fait pas de la PR l'auteur de ce que `main` a ecrit.
  4. **Fail-open** : ensemble indeterminable (ref illisible, aucun commit
     propre) -> rien n'est retire ; le gate garde son comportement d'origine.
  5. Le filtre est **transparent** : `parse_rows` puis `render_rows` rendent
     la sortie `--name-status` d'origine, renommages `R<score>` compris.
  6. La ligne `D` traverse le filtre : la sauter est le role du workflow.
  7. **Bout en bout sur un vrai depot git, mecanisme de #21650 reproduit** :
     une branche empilee dont la base ignore ce que `main` a gagne depuis le
     fork rend deux carnets ; le filtre n'en garde qu'un et nomme l'autre.

Run: python -m pytest scripts/ci/tests/test_filter_pr_introduced_notebooks.py -q
"""
from __future__ import annotations

import importlib.util
import io
import subprocess
import sys
from pathlib import Path

import pytest

MODULE_PATH = Path(__file__).resolve().parents[1] / "filter_pr_introduced_notebooks.py"
_spec = importlib.util.spec_from_file_location("filter_pr_introduced_notebooks", MODULE_PATH)
assert _spec and _spec.loader
fpin = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(fpin)


# --------------------------------------------------------------------------
# 1, 2, 4, 6 -- verdicts, sur un ensemble injecte (aucun git, aucun reseau)
# --------------------------------------------------------------------------

def test_not_owned_is_dropped():
    row = ("M", "never-written.ipynb", "never-written.ipynb")
    kept, dropped = fpin.filter_rows([row], {"a.ipynb"})
    assert kept == []
    assert [reason for _, reason in dropped] == ["aucun commit de la PR ne le touche"]


def test_owned_is_kept():
    """Controle positif : la PR a vraiment ecrit ce carnet."""
    row = ("M", "a.ipynb", "a.ipynb")
    kept, dropped = fpin.filter_rows([row], {"a.ipynb"})
    assert kept == [row]
    assert dropped == []


def test_unknown_ownership_is_fail_open():
    """Ensemble indeterminable : le gate garde son comportement d'origine."""
    rows = [("M", "a.ipynb", "a.ipynb"), ("A", "b.ipynb", "b.ipynb")]
    kept, dropped = fpin.filter_rows(rows, None)
    assert kept == rows
    assert dropped == []


def test_deleted_row_traverses():
    row = ("D", "gone.ipynb", "gone.ipynb")
    kept, dropped = fpin.filter_rows([row], set())
    assert kept == [row]
    assert dropped == []


def test_rename_is_judged_on_the_new_path():
    row = ("R100", "old.ipynb", "new.ipynb")
    kept, _ = fpin.filter_rows([row], {"new.ipynb"})
    assert kept == [row]
    kept, dropped = fpin.filter_rows([row], {"old.ipynb"})
    assert kept == [] and len(dropped) == 1


# --------------------------------------------------------------------------
# 5 -- transparence du format
# --------------------------------------------------------------------------

def test_parse_and_render_roundtrip():
    text = "M\tplain.ipynb\nR100\told.ipynb\tnew.ipynb\nA\tcreated.ipynb\nD\tgone.ipynb"
    rows = fpin.parse_rows(text)
    assert rows == [
        ("M", "plain.ipynb", "plain.ipynb"),
        ("R100", "old.ipynb", "new.ipynb"),
        ("A", "created.ipynb", "created.ipynb"),
        ("D", "gone.ipynb", "gone.ipynb"),
    ]
    assert fpin.render_rows(rows) == text


def test_parse_rows_ignores_blank_and_truncated_lines():
    assert fpin.parse_rows("\n\nM\n") == []


# --------------------------------------------------------------------------
# 3 & 7 -- bout en bout : mecanisme #21650 reproduit dans un vrai depot git
# --------------------------------------------------------------------------

def _git(repo: Path, *args: str) -> str:
    proc = subprocess.run(
        [
            "git",
            "-c", "user.email=ci@example.invalid",
            "-c", "user.name=CI",
            "-c", "commit.gpgsign=false",
            *args,
        ],
        cwd=repo,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        check=True,
    )
    return proc.stdout.strip()


def _write(repo: Path, name: str, payload: str) -> None:
    (repo / name).write_text(payload, encoding="utf-8")


@pytest.fixture()
def stacked_repo(tmp_path: Path) -> Path:
    """Reproduit une PR empilee dont la base ignore ce que `main` a gagne.

    - `A` sur `main` : les deux carnets sont a v1 ; `stale-base` pointe `A` ;
    - la branche PR part de `A` et ecrit `touched.ipynb` (v2) ;
    - `main` avance et ecrit `untouched.ipynb` (v2) **et** `merged-only.ipynb` ;
    - la branche fusionne `main` : sa tete porte les trois, mais la base du
      stack (`A`) n'en a aucun -- exactement #21650, ou `main` avait 521
      commits d'avance et le diff contre la base rendait 287 carnets.
    """
    _git(tmp_path, "init", "-b", "main", "--quiet")
    _write(tmp_path, "touched.ipynb", '{"cells": [], "v": 1}\n')
    _write(tmp_path, "untouched.ipynb", '{"cells": [], "v": 1}\n')
    _git(tmp_path, "add", ".")
    _git(tmp_path, "commit", "-m", "A", "--quiet")
    _git(tmp_path, "branch", "stale-base")

    _git(tmp_path, "checkout", "-b", "feature", "--quiet")
    _write(tmp_path, "touched.ipynb", '{"cells": [1], "v": 1}\n')
    _git(tmp_path, "commit", "-am", "branch writes one notebook", "--quiet")

    _git(tmp_path, "checkout", "main", "--quiet")
    _write(tmp_path, "untouched.ipynb", '{"cells": [1], "v": 1}\n')
    _write(tmp_path, "merged-only.ipynb", '{"cells": [], "v": 1}\n')
    _git(tmp_path, "add", ".")
    _git(tmp_path, "commit", "-m", "main moves on", "--quiet")

    _git(tmp_path, "checkout", "feature", "--quiet")
    _git(tmp_path, "merge", "main", "--no-edit", "--quiet")
    return tmp_path


def test_owned_paths_ignore_merge_commits(stacked_repo, monkeypatch):
    """Point 3 : le merge de `main` n'apporte aucun chemin a la PR."""
    monkeypatch.chdir(stacked_repo)
    owned = fpin.pr_owned_paths("stale-base", "HEAD", "main")
    assert owned == {"touched.ipynb"}, owned


def test_stale_base_diff_lists_three_but_filter_keeps_one(stacked_repo, monkeypatch, capsys):
    monkeypatch.chdir(stacked_repo)
    diff = _git(stacked_repo, "diff", "--name-status", "-M", "stale-base...HEAD")
    listed = {line.split("\t")[1] for line in diff.splitlines() if line.strip()}
    assert listed == {"touched.ipynb", "untouched.ipynb", "merged-only.ipynb"}, listed

    monkeypatch.setattr(sys, "stdin", io.StringIO(diff + "\n"))
    assert (
        fpin.main(
            ["--base", "stale-base", "--main-ref", "main", "--head-ref", "HEAD", "--stats"]
        )
        == 0
    )

    out, err = capsys.readouterr()
    lines = [line for line in out.splitlines() if line.strip()]
    assert len(lines) == 1, lines
    assert lines[0].endswith("touched.ipynb")
    assert "1 carnet(s) conserve(s)" in err
    assert "2 retire(s)" in err
    assert "untouched.ipynb (M) : aucun commit de la PR ne le touche" in err
    assert "merged-only.ipynb" in err
    assert "::notice" in err


def test_unreadable_base_is_fail_open(stacked_repo, monkeypatch, capsys):
    """Point 4 : une base illisible ne retire rien."""
    monkeypatch.chdir(stacked_repo)
    diff = _git(stacked_repo, "diff", "--name-status", "-M", "stale-base...HEAD")
    monkeypatch.setattr(sys, "stdin", io.StringIO(diff + "\n"))
    fpin.main(["--base", "refs/heads/inexistante", "--main-ref", "main", "--stats"])
    out, err = capsys.readouterr()
    assert len([line for line in out.splitlines() if line.strip()]) == 3
    assert "indeterminable" in err
