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
  3. **Un merge qui ne fait que transporter n'apporte aucun chemin** :
     integrer `main` dans sa branche ne fait pas de la PR l'auteur de ce que
     `main` a ecrit.
  3bis. **Un merge qui ecrit, si** : une resolution de conflit -- ou une
     edition faite pendant le merge -- n'existe chez aucun parent, donc elle
     appartient a la PR. Faux negatif releve par l'adjoint sur #22302 : avec
     `rev-list --no-merges`, le carnet resolu disparaissait de la liste et le
     gate ne l'auditait pas.
  4. **Fail-open** : ensemble indeterminable (ref illisible, aucun commit
     propre) -> rien n'est retire ; le gate garde son comportement d'origine.
  5. Le filtre est **transparent** : `parse_rows` puis `render_rows` rendent
     la sortie `--name-status` d'origine, renommages `R<score>` compris.
  6. La ligne `D` traverse le filtre : la sauter est le role du workflow.
  7. **Bout en bout sur un vrai depot git, mecanisme de #21650 reproduit** :
     une branche empilee dont la base ignore ce que `main` a gagne depuis le
     fork rend deux carnets ; le filtre n'en garde qu'un et nomme l'autre.
  8. **La jambe shell ne verdit pas sur un plantage de l'organe** : le
     fail-open ne couvre que la fonction -- un filtre qui crashe doit rougir
     le gate, sinon son stdout vide se lit « aucun carnet » et le gate est
     eteint en silence (releve par Hermes sur #22302).

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


def test_merge_qui_transporte_seulement_n_apporte_aucun_chemin(stacked_repo, monkeypatch):
    """Point 3 : le merge de `main` n'apporte aucun chemin a la PR."""
    monkeypatch.chdir(stacked_repo)
    # Le merge est bien dans l'historique propre a la PR : c'est son
    # differentiel qui ne lui attribue rien, pas son exclusion.
    history = _git(stacked_repo, "rev-list", "--parents", "stale-base..HEAD", "--not", "main")
    assert any(len(line.split()) > 2 for line in history.splitlines()), history
    owned = fpin.pr_owned_paths("stale-base", "HEAD", "main")
    assert owned == {"touched.ipynb"}, owned


@pytest.fixture()
def resolved_merge_repo(tmp_path: Path) -> Path:
    """PR empilee dont le **merge** ecrit un carnet que la branche n'a jamais touche.

    Scenario exact rapporte par l'adjoint sur #22302 :
    - `stale-base` porte `nb.ipynb` v1 et `other.py` ;
    - la branche ne touche que `other.py` ;
    - `main` avance et reecrit `nb.ipynb` (v2) ;
    - la branche fusionne `main` **et, pendant le merge, reecrit `nb.ipynb`** (v3).

    `nb.ipynb` n'existe chez aucun parent sous sa forme finale : c'est la PR
    qui l'a ecrit. `diff stale-base...HEAD` le liste, et un filtre qui l'ecarte
    n'audite pas un carnet que la PR a reellement modifie. Un commit ordinaire
    de la branche ne le touche jamais -- c'est bien le cas ou `--no-merges`
    faisait disparaitre le carnet.
    """
    _git(tmp_path, "init", "-b", "main", "--quiet")
    _write(tmp_path, "nb.ipynb", '{"v": 1, "a": 0}\n')
    _write(tmp_path, "other.py", "x1\n")
    _git(tmp_path, "add", ".")
    _git(tmp_path, "commit", "-m", "A", "--quiet")
    _git(tmp_path, "branch", "stale-base")

    _git(tmp_path, "checkout", "-b", "feature", "--quiet")
    _write(tmp_path, "other.py", "x2\n")
    _git(tmp_path, "commit", "-am", "la branche ne touche pas nb.ipynb", "--quiet")

    _git(tmp_path, "checkout", "main", "--quiet")
    _write(tmp_path, "nb.ipynb", '{"v": 2, "main": 1}\n')
    _git(tmp_path, "commit", "-am", "main reecrit nb.ipynb", "--quiet")

    _git(tmp_path, "checkout", "feature", "--quiet")
    # `--no-commit` : la fusion s'arrete avant de conclure, pour que l'ecriture
    # faite pendant le merge entre DANS le commit de merge (et non dans un
    # commit ordinaire, qui rendrait le cas indiscernable).
    _git(tmp_path, "merge", "main", "--no-edit", "--no-commit", "--quiet")
    _write(tmp_path, "nb.ipynb", '{"v": 3, "resolved": 1}\n')
    _git(tmp_path, "add", ".")
    _git(tmp_path, "commit", "-m", "merge main (ecriture pendant le merge)", "--quiet")
    return tmp_path


def test_ecriture_pendant_le_merge_est_attribuee_a_la_pr(resolved_merge_repo, monkeypatch):
    """3bis : le carnet ecrit par le merge reste dans la liste du gate.

    Avec `rev-list --no-merges`, `owned` valait `{other.py}` et `nb.ipynb`
    etait retire -- un carnet que la PR a ecrit n'etait jamais audite.
    """
    monkeypatch.chdir(resolved_merge_repo)
    # Le seul commit ordinaire de la branche ne touche pas nb.ipynb : c'est
    # bien du merge que vient l'attribution, pas d'un commit de branche.
    plain = _git(resolved_merge_repo, "rev-list", "--no-merges", "stale-base..HEAD", "--not", "main").split()
    assert len(plain) == 1, plain
    touched = _git(
        resolved_merge_repo, "diff-tree", "--no-commit-id", "-r", "-M",
        "--name-status", "--root", plain[0],
    )
    assert "nb.ipynb" not in touched, touched
    owned = fpin.pr_owned_paths("stale-base", "HEAD", "main")
    assert owned == {"other.py", "nb.ipynb"}, owned


def test_differentiel_et_filtre_du_merge_bout_en_bout(resolved_merge_repo, monkeypatch, capsys):
    """Le gate garde les deux carnets listes, y compris celui ecrit par le merge."""
    monkeypatch.chdir(resolved_merge_repo)
    diff = _git(resolved_merge_repo, "diff", "--name-status", "-M", "stale-base...HEAD")
    listed = {line.split("\t")[-1] for line in diff.splitlines() if line.strip()}
    assert listed == {"nb.ipynb", "other.py"}, listed

    monkeypatch.setattr(sys, "stdin", io.StringIO(diff + "\n"))
    assert fpin.main(
        ["--base", "stale-base", "--main-ref", "main", "--head-ref", "HEAD", "--stats"]
    ) == 0

    out, err = capsys.readouterr()
    lines = [line for line in out.splitlines() if line.strip()]
    assert len(lines) == 2, lines
    assert "0 retire(s)" in err, err
    assert "2 carnet(s) conserve(s)" in err, err


def test_merge_sans_ecriture_n_est_pas_lu_comme_une_ecriture(stacked_repo, monkeypatch):
    """Controle negatif : sans ecriture de merge, l'ensemble reste inchange.

    Le fixture `stacked_repo` fusionne `main` **sans rien editer** pendant le
    merge : l'intersection des differentiels est vide, donc `untouched.ipynb`
    et `merged-only.ipynb` restent hors de `owned`.
    """
    monkeypatch.chdir(stacked_repo)
    owned = fpin.pr_owned_paths("stale-base", "HEAD", "main")
    assert "untouched.ipynb" not in owned
    assert "merged-only.ipynb" not in owned


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


# --------------------------------------------------------------------------
# 8 -- la jambe shell ne verdit pas sur un plantage de l'organe
# --------------------------------------------------------------------------

WORKFLOW = Path(__file__).resolve().parents[3] / ".github/workflows/enrich-quality-gate.yml"


def test_jambe_shell_ne_verdit_pas_vert_sur_un_plantage_de_l_organe():
    """Point 8 : un organe qui crashe rougit le gate, il ne le vertit pas.

    Le contrat fail-open ne couvre que la FONCTION : un ensemble indeterminable
    ne retire rien. Un organe absent ou casse (script deplace, import qui leve,
    argparse qui refuse un argument) n'est pas « indeterminable » -- son stdout
    est vide, et la branche `-z` qui suit conclurait « No notebooks changed —
    clean » avec `exit 0`. Le gate serait alors eteint en silence sur toutes les
    PRs a carnets, l'inverse du contrat revendique (releve par Hermes sur
    #22302).

    Ce test garde la forme du cablage, pas son intention : il exige, dans le
    meme fichier, l'appel garde par `if !` et l'echec explicite qui le suit.
    Retirer la garde rougit ; la deplacer hors du bloc de l'appel aussi.
    """
    workflow = WORKFLOW.read_text(encoding="utf-8")
    call_line = next(
        (i for i, line in enumerate(workflow.splitlines())
         if "filter_pr_introduced_notebooks.py" in line and "python " in line),
        None,
    )
    assert call_line is not None, "l'appel de l'organe a disparu du workflow"
    lines = workflow.splitlines()
    # La garde doit etre la ligne de commande qui ENGLOBE l'appel : `if ! VAR=$(`.
    assert lines[call_line].lstrip().startswith("if ! STATUS=$("), lines[call_line]
    # ... et l'echec doit sortir en rouge, pas retomber sur la branche « clean ».
    tail = lines[call_line + 1:call_line + 5]
    assert any("exit 1" in line for line in tail), tail
    assert any("::error" in line for line in tail), tail
