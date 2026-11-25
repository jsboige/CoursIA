"""Tests de `scripts/notebook_tools/enrich_quality_delta.py` (#26973, ligne 2).

L'organe est teste **sans reseau** et **sans le depot** : les tests qui
exigent git construisent un petit depot jetable dans `tmp_path`.

Ce qui est verifie :

- la comparaison base-vs-head distingue « finding nouveau » de « finding deja
  present en base » (c'est le contrat du gate, et la raison d'etre de
  l'organe) ;
- l'organe **reutilise** les deux organes qu'il consomme au lieu de
  reecrire leur logique ;
- de bout en bout, sur un depot jetable : un lien casse ajoute par la PR
  rougit, un defaut preexistant ne rouge pas, un carnet supprime est saute,
  un carnet neuf sans base est compare, et le filtre « introduit par la PR »
  retire les carnets que `main` a touches sans la PR.
"""

from __future__ import annotations

import importlib.util
import json
import pathlib
import subprocess
import sys

import pytest

_MODULE_PATH = (
    pathlib.Path(__file__).resolve().parents[1] / "enrich_quality_delta.py"
)


def _load_module():
    spec = importlib.util.spec_from_file_location("enrich_quality_delta", _MODULE_PATH)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    sys.modules["enrich_quality_delta"] = module
    spec.loader.exec_module(module)
    return module


eqd = _load_module()


# ---------------------------------------------------------------------------
# helpers : un petit carnet, un petit depot
# ---------------------------------------------------------------------------

def _notebook(link: str, extra_cell: bool = False) -> str:
    """Carnet minimal contenant un lien markdown relatif.

    `extra_cell` ajoute une cellule markdown : elle sert a rendre le contenu
    REELLEMENT different entre la base et la tete (un commit identique ne
    serait pas commite) -- et a garder un JSON VALIDE, sans quoi le
    detecteur rendrait une erreur au lieu de findings (un test qui passe
    alors qu'il ne verifie rien).
    """
    cells = [
        {
            "cell_type": "markdown",
            "metadata": {},
            "source": ["Un lien vers [cible]({})\n".format(link)],
        }
    ]
    if extra_cell:
        cells.append(
            {
                "cell_type": "markdown",
                "metadata": {},
                "source": ["Une ligne de plus.\n"],
            }
        )
    return json.dumps(
        {
            "cells": cells,
            "metadata": {},
            "nbformat": 4,
            "nbformat_minor": 5,
        }
    )


def _git(repo: pathlib.Path, *args: str) -> str:
    proc = subprocess.run(
        ["git", "-C", str(repo), *args],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        check=True,
    )
    return proc.stdout


def _init_repo(repo: pathlib.Path) -> None:
    repo.mkdir(parents=True, exist_ok=True)
    _git(repo, "init", "-b", "main")
    _git(repo, "config", "user.email", "test@example.invalid")
    _git(repo, "config", "user.name", "Test")
    _git(repo, "config", "commit.gpgsign", "false")


def _write_notebook(repo: pathlib.Path, name: str, link: str) -> pathlib.Path:
    target = repo / "MyIA.AI.Notebooks" / "Serie" / name
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(_notebook(link), encoding="utf-8")
    return target


def _write_resolved_target(repo: pathlib.Path) -> None:
    """Cree la cible que pointe le lien « cible.md » (lien RESOLU)."""
    target = repo / "MyIA.AI.Notebooks" / "Serie" / "cible.md"
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text("cible resolue\n", encoding="utf-8")


def _args(repo: pathlib.Path, base_ref: str = "HEAD~1", head_ref: str = "HEAD",
          main_ref: str = "HEAD~1"):
    import argparse

    return argparse.Namespace(
        base_ref=base_ref,
        head_ref=head_ref,
        main_ref=main_ref,
        repo_root=str(repo),
        pr_body_file="",
    )


# ---------------------------------------------------------------------------
# la comparaison elle-meme
# ---------------------------------------------------------------------------

def test_le_selftest_de_l_organe_passe():
    assert eqd.self_test() == 0


def test_des_findings_identiques_en_base_et_en_tete_ne_sont_pas_nouveaux(tmp_path):
    base = tmp_path / "base.ipynb"
    head = tmp_path / "head.ipynb"
    base.write_text(_notebook("cible.md"), encoding="utf-8")
    head.write_text(_notebook("cible.md"), encoding="utf-8")
    assert eqd.enrich_quality_ci.regressions(str(base), str(head), tmp_path) == []


def test_un_lien_casse_ajoute_par_la_tete_est_une_regression(tmp_path):
    base = tmp_path / "base.ipynb"
    head = tmp_path / "head.ipynb"
    base.write_text(_notebook("cible.md"), encoding="utf-8")
    head.write_text(_notebook("absente.md"), encoding="utf-8")
    findings = eqd.enrich_quality_ci.regressions(str(base), str(head), tmp_path)
    assert findings
    assert any(category == "HREF_MISSING" for category, _ in findings)


def test_un_defaut_deja_present_en_base_ne_bloque_pas(tmp_path):
    base = tmp_path / "base.ipynb"
    head = tmp_path / "head.ipynb"
    base.write_text(_notebook("absente.md"), encoding="utf-8")
    head.write_text(_notebook("absente.md"), encoding="utf-8")
    assert eqd.enrich_quality_ci.regressions(str(base), str(head), tmp_path) == []


# ---------------------------------------------------------------------------
# l'organe consomme les deux organes, il ne les reecrit pas
# ---------------------------------------------------------------------------

def test_l_organe_appelle_les_deux_organes_consommes():
    source = _MODULE_PATH.read_text(encoding="utf-8")
    assert "enrich_quality_ci.main(" in source
    assert "pr_filter.filter_rows(" in source
    assert "pr_filter.pr_owned_paths(" in source


def test_l_organe_ne_reecrit_pas_la_comparaison():
    """La comparaison doit venir de l'organe d'origine, pas d'une copie."""
    source = _MODULE_PATH.read_text(encoding="utf-8")
    assert "def high_signatures" not in source
    assert "def scan_notebook" not in source
    assert "_identity(" not in source


def test_le_body_de_pr_est_transmis_a_la_comparaison(monkeypatch):
    """Sans le canal du body, une reecriture ANNONCEE (#17744) serait vue
    comme une regression : le marqueur doit donc atteindre la comparaison."""
    captured = {}

    def fake_main(argv):
        captured["argv"] = list(argv)
        return 0

    monkeypatch.setattr(eqd.enrich_quality_ci, "main", fake_main)
    assert eqd.compare_one("NONE", "head.ipynb", pathlib.Path("."), "body.md") == 0
    assert "--pr-body-file" in captured["argv"]
    assert "body.md" in captured["argv"]


def test_sans_body_le_canal_nest_pas_transmis(monkeypatch):
    captured = {}

    def fake_main(argv):
        captured["argv"] = list(argv)
        return 0

    monkeypatch.setattr(eqd.enrich_quality_ci, "main", fake_main)
    assert eqd.compare_one("NONE", "head.ipynb", pathlib.Path(".")) == 0
    assert "--pr-body-file" not in captured["argv"]


# ---------------------------------------------------------------------------
# de bout en bout, sur un depot jetable
# ---------------------------------------------------------------------------

def test_un_lien_casse_ajoute_par_la_pr_rougit(tmp_path):
    repo = tmp_path / "repo"
    _init_repo(repo)
    _write_resolved_target(repo)
    _write_notebook(repo, "a.ipynb", "cible.md")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-m", "base")
    _write_notebook(repo, "a.ipynb", "absente.md")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-m", "PR")

    code, report = eqd.run(_args(repo))
    assert code == eqd.EXIT_REGRESSION
    assert "HREF_MISSING" in report or "regression" in report


def test_un_defaut_preexistant_ne_rouge_pas(tmp_path):
    repo = tmp_path / "repo"
    _init_repo(repo)
    _write_notebook(repo, "a.ipynb", "absente.md")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-m", "base")
    # Le contenu change (sinon le commit est vide) mais le defaut, lui, reste.
    (repo / "MyIA.AI.Notebooks" / "Serie" / "a.ipynb").write_text(
        _notebook("absente.md", extra_cell=True), encoding="utf-8")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-m", "PR")

    code, _ = eqd.run(_args(repo))
    assert code == eqd.EXIT_OK


def test_un_carnet_supprime_par_la_pr_est_saute(tmp_path):
    repo = tmp_path / "repo"
    _init_repo(repo)
    _write_resolved_target(repo)
    _write_notebook(repo, "a.ipynb", "cible.md")
    _write_notebook(repo, "b.ipynb", "cible.md")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-m", "base")
    _git(repo, "rm", "-q", "MyIA.AI.Notebooks/Serie/b.ipynb")
    _git(repo, "commit", "-m", "PR")

    code, report = eqd.run(_args(repo))
    assert code == eqd.EXIT_OK
    assert "b.ipynb" not in report


def test_un_carnet_neuf_sans_base_est_complique_comme_neuf(tmp_path):
    repo = tmp_path / "repo"
    _init_repo(repo)
    _write_resolved_target(repo)
    _write_notebook(repo, "a.ipynb", "cible.md")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-m", "base")
    _write_notebook(repo, "neuf.ipynb", "absente.md")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-m", "PR")

    code, _ = eqd.run(_args(repo))
    assert code == eqd.EXIT_REGRESSION


def test_le_filtre_pr_introduit_retire_un_carnet_touche_par_main_seulement(tmp_path):
    """Un carnet que `main` a touche, et que la PR ne touche pas, est retire.

    Cas de la PR empilee : la branche de la PR a recu `main` par un MERGE,
    donc le diff contre la base porte aussi ce que le merge a seulement
    transporte. Sans le filtre « introduit par la PR », les findings de
    `main` seraient attribues a la PR (mesure #21650 : 287 carnets pour un
    fichier). Le filtre retire le carnet transporte et garde celui que la PR
    a ecrit.
    """
    repo = tmp_path / "repo"
    _init_repo(repo)
    _write_resolved_target(repo)
    _write_notebook(repo, "a.ipynb", "cible.md")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-m", "base")
    fork = _git(repo, "rev-parse", "HEAD").strip()

    # `main` avance : il casse le lien de a.ipynb.
    _write_notebook(repo, "a.ipynb", "absente.md")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-m", "main casse le lien")

    # La PR part du fork, RECOIT main (merge : elle transporte la casse),
    # puis ecrit b.ipynb -- qui est, lui, propre.
    _git(repo, "checkout", "-b", "feature", fork)
    _git(repo, "merge", "--no-edit", "main")
    _write_notebook(repo, "b.ipynb", "cible.md")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-m", "PR")

    code, report = eqd.run(
        _args(repo, base_ref=fork, head_ref="HEAD", main_ref="main"))
    # a.ipynb est casse par `main`, pas par la PR : il doit etre retire.
    assert code == eqd.EXIT_OK
    assert "a.ipynb" in report  # le motif du retrait est trace


def test_une_diff_illisible_est_une_erreur_d_usage(tmp_path):
    repo = tmp_path / "repo"
    _init_repo(repo)
    code, report = eqd.run(_args(repo, base_ref="ref-inexistante"))
    assert code == eqd.EXIT_USAGE
    assert "diff illisible" in report


def test_un_repo_vide_ne_produit_pas_de_regression(tmp_path):
    repo = tmp_path / "repo"
    _init_repo(repo)
    _write_resolved_target(repo)
    _write_notebook(repo, "a.ipynb", "cible.md")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-m", "base")

    code, report = eqd.run(_args(repo, base_ref="HEAD", head_ref="HEAD"))
    assert code == eqd.EXIT_OK


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(pytest.main([__file__, "-v"]))
