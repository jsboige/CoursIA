#!/usr/bin/env python3
"""Tests de l'organe d'inventaire de la ferme de worktrees.

Ce que ces tests tiennent :
1. l'attribution de lane lit le tag `Grain:` du body et **rien d'autre** ;
2. un body sans tag ne donne **aucune** lane (pas de deduction) ;
3. le parseur de `git worktree list --porcelain` rend chemin, branche et
   detachement ;
4. `.lane-owner` est lu quand il existe, ignore quand il n'existe pas ;
5. le census compte les worktrees de la ferme et laisse `unattributed` quand
   l'attribution est indisponible (`--no-gh`).

Run : python -m pytest scripts/audit/tests/test_census_worktree_farm.py
"""
from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import census_worktree_farm  # noqa: E402
from census_worktree_farm import (  # noqa: E402
    census,
    dir_size,
    fetch_prs,
    gh_slug,
    is_recyclable,
    lane_from_body,
    parse_worktree_list,
    pr_status_for,
    read_lane_owner,
)


def test_lane_from_body_lit_le_tag_grain():
    body = ("Grain: MED/notebook-python — lane myia-ai-01:CoursIA-2 — "
            "prev: MED/training #27402\n\nCorps de PR.")
    assert lane_from_body(body) == "myia-ai-01:CoursIA-2"


def test_lane_from_body_ignore_un_body_sans_tag():
    assert lane_from_body("Une PR qui ne porte pas de tag de grain.") is None
    assert lane_from_body("") is None


def test_lane_from_body_ne_confond_pas_les_deux_lanes():
    """Le tag nomme UNE lane : celle du porteur. Une mention d'une autre lane
    dans le corps ne doit pas la prendre."""
    body = ("Grain: MED/guard — lane myia-po-2025:CoursIA-2 — prev: MED/guard #1\n"
            "\nSuite a la demande de myia-ai-01:CoursIA (coordinateur).")
    assert lane_from_body(body) == "myia-po-2025:CoursIA-2"


def test_lane_from_body_est_ancree_sur_la_premiere_ligne():
    """La lecture est ancree sur la premiere ligne non vide : une citation de
    lane en tete de corps, avant le tag, ne donne rien."""
    body = ("Sur la demande de myia-ai-01:CoursIA (coordinateur).\n"
            "Grain: MED/guard — lane myia-po-2025:CoursIA-2 — prev: MED/guard #1\n")
    assert lane_from_body(body) is None


def test_parse_worktree_list_rend_chemin_branche_et_detachement():
    text = ("worktree D:/wt/a\n"
            "HEAD abc123\n"
            "branch refs/heads/feature/x\n\n"
            "worktree D:/wt/b\n"
            "HEAD def456\n"
            "detached\n")
    entries = parse_worktree_list(text)
    assert len(entries) == 2
    assert entries[0]["path"] == "D:/wt/a"
    assert entries[0]["branch"] == "feature/x"
    assert entries[1].get("detached") is True
    assert "branch" not in entries[1]


def test_read_lane_owner(tmp_path):
    assert read_lane_owner(str(tmp_path)) is None
    (tmp_path / ".lane-owner").write_text(
        "myia-ai-01:CoursIA-2\n", encoding="utf-8")
    assert read_lane_owner(str(tmp_path)) == "myia-ai-01:CoursIA-2"


def test_dir_size_compte_les_fichiers(tmp_path):
    (tmp_path / "a.txt").write_text("x" * 10, encoding="utf-8")
    (tmp_path / "sub").mkdir()
    (tmp_path / "sub" / "b.txt").write_text("y" * 5, encoding="utf-8")
    assert dir_size(str(tmp_path)) == 15


def test_census_compte_les_worktrees_sans_attribution(tmp_path):
    """Un worktree sans PR reste `unattributed` : l'inventaire ne devine pas."""
    repo = tmp_path / "repo"
    farm = tmp_path / "wt"
    farm.mkdir()
    repo.mkdir()
    env = dict(os.environ, GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@t",
               GIT_COMMITTER_NAME="t", GIT_COMMITTER_EMAIL="t@t")
    subprocess.run(["git", "init", "-q", "-b", "main", str(repo)], check=True,
                   env=env)
    (repo / "f.txt").write_text("x", encoding="utf-8")
    subprocess.run(["git", "-C", str(repo), "add", "f.txt"], check=True, env=env)
    subprocess.run(["git", "-C", str(repo), "commit", "-qm", "init"], check=True,
                   env=env)
    subprocess.run(["git", "-C", str(repo), "worktree", "add", "-q",
                    str(farm / "wt1"), "-b", "feature/x"], check=True, env=env)
    report = census(str(farm), str(repo), use_gh=False)
    assert report["count"] == 1
    assert report["rows"][0]["name"] == "wt1"
    assert report["rows"][0]["branch"] == "feature/x"
    assert report["rows"][0]["lane"] is None
    assert "(unattributed)" in report["by_lane"]


def test_census_exclut_le_clone_principal(tmp_path):
    """Le clone principal ne fait pas partie de la ferme : il est exclu."""
    repo = tmp_path / "repo"
    farm = tmp_path / "wt"
    farm.mkdir()
    repo.mkdir()
    env = dict(os.environ, GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@t",
               GIT_COMMITTER_NAME="t", GIT_COMMITTER_EMAIL="t@t")
    subprocess.run(["git", "init", "-q", "-b", "main", str(repo)], check=True,
                   env=env)
    (repo / "f.txt").write_text("x", encoding="utf-8")
    subprocess.run(["git", "-C", str(repo), "add", "f.txt"], check=True, env=env)
    subprocess.run(["git", "-C", str(repo), "commit", "-qm", "init"], check=True,
                   env=env)
    subprocess.run(["git", "-C", str(repo), "worktree", "add", "-q",
                    str(farm / "wt1"), "-b", "feature/x"], check=True, env=env)
    report = census(str(farm), str(repo), use_gh=False)
    assert all(row["path"] != str(repo) for row in report["rows"])


def test_gh_slug_lit_le_remote(tmp_path):
    """Le slug GitHub vient du remote origin, pas du chemin local."""
    repo = tmp_path / "repo"
    repo.mkdir()
    env = dict(os.environ, GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@t",
               GIT_COMMITTER_NAME="t", GIT_COMMITTER_EMAIL="t@t")
    subprocess.run(["git", "init", "-q", "-b", "main", str(repo)], check=True,
                   env=env)
    assert gh_slug(str(repo)) is None
    subprocess.run(["git", "-C", str(repo), "remote", "add", "origin",
                    "https://github.com/jsboige/CoursIA.git"], check=True, env=env)
    assert gh_slug(str(repo)) == "jsboige/CoursIA"
    subprocess.run(["git", "-C", str(repo), "remote", "set-url", "origin",
                    "git@github.com:jsboige/CoursIA.git"], check=True, env=env)
    assert gh_slug(str(repo)) == "jsboige/CoursIA"


def test_pr_status_for_distingue_hors_index_d_aucune_pr():
    """Ask 2 #28685 : un index Borne ne lit pas une branche absente comme
    « sans PR » — c'est un etat distinct (`hors_index`), pas un zero verifie.
    Un index COMPLET (sous le plafond) peut, lui, affirmer `aucune_pr`."""
    assert pr_status_for({"state": "OPEN"}, True) == "vue"
    assert pr_status_for(None, True) == "hors_index"
    assert pr_status_for(None, False) == "aucune_pr"
    assert pr_status_for({"state": "MERGED"}, False) == "vue"


def test_pr_fermee_hors_index_nest_pas_lue_sans_pr():
    """Cas minimum #28685 : PR hors de l'index borne -> `hors_index`, jamais
    « aucune PR » (le faux zero de l'organe)."""
    assert pr_status_for(None, truncated=True) == "hors_index"
    assert pr_status_for(None, truncated=True) != "aucune_pr"


def test_is_recyclable_pr_fermee_propre_preserve():
    """Les trois conditions tiennent a la fois -> recyclable."""
    pr = {"state": "MERGED"}
    state = {"modified": 0, "untracked": 0, "ahead": 0}
    assert is_recyclable(pr, state) is True


def test_is_recyclable_arbre_sale_pas_recyclable():
    """Cas minimum #28685 : PR fermee mais arbre sale (contenu non committe)
    -> pas recyclable. La PR fermee seule n'est pas un verdict de
    retirabilite (ask 3)."""
    pr = {"state": "MERGED"}
    assert is_recyclable(pr, {"modified": 1, "untracked": 0, "ahead": 0}) is False
    assert is_recyclable(pr, {"modified": 0, "untracked": 1, "ahead": 0}) is False


def test_is_recyclable_head_non_preserve_pas_retirable():
    """Cas minimum #28685 : PR fermee, arbre propre, mais HEAD au-dela de
    origin/<br> (commits non pousses) -> pas retirable. `ahead` inconnu
    (None, ex. HEAD detache) est non preserve (fail-safe)."""
    pr = {"state": "CLOSED"}
    assert is_recyclable(pr, {"modified": 0, "untracked": 0, "ahead": 2}) is False
    assert is_recyclable(pr, {"modified": 0, "untracked": 0, "ahead": None}) is False


def test_is_recyclable_pr_open_nest_pas_recyclable():
    """Sans PR fermee, aucun recyclage : PR ouverte ou absente."""
    state = {"modified": 0, "untracked": 0, "ahead": 0}
    assert is_recyclable({"state": "OPEN"}, state) is False
    assert is_recyclable(None, state) is False


def _fake_gh(prs):
    """Fabrique un objet de sortie `gh pr list` porte de la liste donnee."""
    class R:
        returncode = 0
        stdout = json.dumps(prs)
        stderr = ""
    return R()


def _pr(n, br, state):
    return {"number": n, "headRefName": br, "state": state, "body": "",
            "title": "", "mergedAt": None}


def test_fetch_prs_signale_la_troncature_au_plafond(monkeypatch):
    """Le nombre de PRs remises ATTEIGNANT `limit` -> `tronque=True`. C'est ce
    drapeau qui interdit de lire une branche absente comme « sans PR »."""
    monkeypatch.setattr(
        census_worktree_farm.subprocess, "run",
        lambda cmd, **kw: _fake_gh([_pr(1, "b1", "OPEN"),
                                    _pr(2, "b2", "MERGED"),
                                    _pr(3, "b3", "OPEN")]))
    index, err, truncated = fetch_prs("jsboige/CoursIA", limit=3)
    assert err is None
    assert truncated is True
    assert set(index) == {"b1", "b2", "b3"}


def test_fetch_prs_complet_sous_le_plafond(monkeypatch):
    """Sous le plafond, l'index est complet -> `tronque=False` : on peut
    affirmer `aucune_pr` pour une branche absente."""
    monkeypatch.setattr(
        census_worktree_farm.subprocess, "run",
        lambda cmd, **kw: _fake_gh([_pr(1, "b1", "OPEN")]))
    index, err, truncated = fetch_prs("jsboige/CoursIA", limit=600)
    assert err is None
    assert truncated is False
    assert set(index) == {"b1"}


def test_fetch_prs_gh_indisponible_pas_tronque(monkeypatch):
    """`gh` absent -> index vide + erreur, et PAS tronque (pas de faux
    `hors_index` sur un echec de mesure)."""
    def boom(cmd, **kw):
        raise OSError("gh not found")
    monkeypatch.setattr(census_worktree_farm.subprocess, "run", boom)
    index, err, truncated = fetch_prs("jsboige/CoursIA", limit=600)
    assert index == {}
    assert err is not None
    assert truncated is False


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-q"]))
