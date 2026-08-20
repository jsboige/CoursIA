#!/usr/bin/env python3
"""Detection d'orphelin par squash dans `--update` (#11919).

Le bug fondateur : sur main, le `python_sha` (git blob SHA legacy) enregistre
sur Probas-13 Crowdsourcing etait un blob orphelin par le squash de #11878.
Le contenu du notebook etait intact, mais le blob SHA n'etait pas ancre sur
main. Consequence pratique :
  - `--verify-recorded-sha` detectait MISMATCH (recorded=bd40c841e143 vs
    calculated=efce50915b82) ;
  - `--update` simultanement refusait comme no-op (content_sha identiques =
    _shas_match True = faux audit).

Deux sous-commandes du meme outil, sur la meme paire, au meme instant :
l'une dit « incoherent », l'autre dit « rien a faire ».

Le fix : sur un no-op detecte, comparer les git blob SHA du recorded contre
le HEAD. Si au moins un diverge, c'est un orphelin par squash -> ce n'est
PAS un no-op, le rebaseline doit corriger les git blob SHA.

Run:
    pytest scripts/notebook_tools/tests/test_check_twin_parity_squash_orphan.py
"""
from __future__ import annotations

import hashlib
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import check_twin_parity as ctp  # noqa: E402


# --- helpers -----------------------------------------------------------------

def _git_repo(tmp_path: Path) -> Path:
    """Un mini-depot git pret a committer des notebooks."""
    repo = tmp_path / "repo"
    repo.mkdir()
    for args in (("init", "-q"), ("config", "user.email", "t@t"),
                 ("config", "user.name", "t")):
        subprocess.run(["git", *args], cwd=repo, check=True, capture_output=True)
    return repo


def _nb(source: list[str] | None = None) -> dict:
    return {
        "cells": [{
            "cell_type": "markdown",
            "source": source if source is not None else ["# Title\n"],
            "metadata": {},
        }],
        "metadata": {"kernelspec": {"name": "python3"}},
        "nbformat": 4,
        "nbformat_minor": 5,
    }


def _commit(repo: Path, rel: str, nb: dict, msg: str) -> None:
    p = repo / rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(nb), encoding="utf-8")
    subprocess.run(["git", "add", "-A"], cwd=repo, check=True, capture_output=True)
    subprocess.run(["git", "commit", "-qm", msg], cwd=repo,
                   check=True, capture_output=True)


def _squash_replace_blob(repo: Path, rel: str, new_content: bytes) -> str:
    """Simule un squash-merge qui re-hashe le blob sans changer le contenu.

    Truc : on commit un blob DIFFERENT (meme contenu textuel apres json.dumps)
    qu'on rebascule ensuite. Le SHA change, le contenu non. C'est le scenario
    fondateur : un agent re-commit en deux etapes distinctes, le SHA git blob
    final n'est pas celui de l'attestation d'origine, alors que le contenu
    est identique.

    Retourne le NOUVEAU blob SHA.
    """
    # 1. Re-commit avec un padding metadata (le contenu didactique reste
    #    identique : `_nb(source=...)` produit un notebook stable cote `cells`).
    #    On usa de `_commit` normal pour poser un SHAsuch que le git blob SHA
    #    change : modifier la date ou ajouter un champ metadata distinct.
    #    Ici on ajoute une clef metadata differente (kernelspec.display_name
    #    change) : le content_sha (metadata-immune) reste identique, mais le
    #    git blob SHA change.
    p = repo / rel
    nb = json.loads(p.read_text(encoding="utf-8"))
    nb["metadata"]["kernelspec"]["display_name"] = "Python 3 (squash)"
    p.write_text(json.dumps(nb), encoding="utf-8")
    subprocess.run(["git", "add", "-A"], cwd=repo, check=True, capture_output=True)
    subprocess.run(["git", "commit", "-qm", "squash repr"], cwd=repo,
                   check=True, capture_output=True)
    return ctp._git_blob_sha(repo, rel)


def _make_pair_yaml_with_content_sha(
    pairs_dir: Path, name: str, py_rel: str, cs_rel: str,
    py_sha: str, cs_sha: str, py_content: str, cs_content: str,
) -> None:
    """Ecrit une entree registry file-per-entry (cf #8542) avec content_sha."""
    entry = pairs_dir / f"{name}.yaml"
    entry.write_text(
        f"name: {name}\n"
        f"family: Search\n"
        f"python: {py_rel}\n"
        f"csharp: {cs_rel}\n"
        f"parity_level: full\n"
        f"last_audit:\n"
        f"  date: 2026-08-19\n"
        f"  by: myia-po-2026:CoursIA-2\n"
        f"  python_sha: {py_sha}\n"
        f"  csharp_sha: {cs_sha}\n"
        f"  content_python_sha: {py_content}\n"
        f"  content_csharp_sha: {cs_content}\n",
        encoding="utf-8",
    )


# --- 1. Reproducer du defaut #11919 ----------------------------------------

def test_squash_orphan_mismatch_then_noop_defect(tmp_path):
    """Defaut fondateur : MISMATCH cote --verify-recorded-sha MAIS no-op cote --update.

    Ce test echoue AVANT le fix appliqué dans update_pair ; il passe apres.
    """
    repo = _git_repo(tmp_path)
    py_rel = "py/nb.ipynb"
    cs_rel = "cs/nb.ipynb"

    _commit(repo, py_rel, _nb(source=["# Title\n"]), "base py")
    _commit(repo, cs_rel, _nb(source=["// Title\n"]), "base cs")

    # SHAs AVANT le squash (recorded).
    py_blob_v1 = ctp._git_blob_sha(repo, py_rel)
    cs_blob_v1 = ctp._git_blob_sha(repo, cs_rel)
    py_content = ctp._content_sha(repo, py_rel)
    cs_content = ctp._content_sha(repo, cs_rel)
    assert py_blob_v1 and cs_blob_v1 and py_content and cs_content

    # Simuler un squash-merge : le contenu didactique reste le meme, mais le
    # blob SHA git change (sur le notebook python ; le csharp est laisse tel
    # quel pour ne declencher qu'un seul cote -- adapte au cas fondateur).
    new_py_blob = _squash_replace_blob(repo, py_rel, b"")
    assert new_py_blob != py_blob_v1, "le blob SHA aurait du changer"
    # content_sha dépend uniquement des cellules -> identiques avant/apres.
    assert ctp._content_sha(repo, py_rel) == py_content, (
        "le content_sha est cense etre inchange apres un squash sans modif "
        "pedagogique"
    )

    # Ecriture du registre avec les SHAs recorded (pre-squash).
    pairs_dir = repo / "twin_pairs.d"
    pairs_dir.mkdir()
    _make_pair_yaml_with_content_sha(
        pairs_dir, "Probas-13 Crowdsourcing", py_rel, cs_rel,
        py_blob_v1, cs_blob_v1, py_content, cs_content,
    )

    # 1. --verify-recorded-sha detecte MISMATCH sur python_sha (le recorded
    #    pointe sur l'ancien blob, calcule au HEAD trouve le nouveau).
    verify_rc = ctp.main([
        "--verify-recorded-sha", "--check", "--json",
        "--registry", str(pairs_dir),
        "--repo-root", str(repo),
    ])
    assert verify_rc == 1, (
        f"verify-recorded-sha --check aurait du rougir (MISMATCH), rc={verify_rc}"
    )

    # 2. --update refuse simultanement comme no-op (le bug) : on capture
    #    ce que retourne update_pair AVANT le fix (pour comparaison) puis
    #    on valide le bind --update ne refuse plus.
    pair = ctp.load_registry(pairs_dir)[0]
    audit, cur_py, is_noop = ctp.update_pair(repo, pair)
    assert audit["python_sha"] == new_py_blob, (
        "le rebaseline devrait calculer le git blob SHA du HEAD (post-squash)"
    )
    assert is_noop is False, (
        "un orphelin par squash devrait PAS etre un no-op : le contenu "
        "est identique mais le git blob SHA diverge, ce qui est precisement "
        "la classe de cas que le fix #11919 doit debloquer"
    )


# --- 2. Garde anti-regression : un vrai no-op reste un no-op ----------------

def test_real_noop_still_refused(tmp_path):
    """Re-implemente le gate no-op : un vrai no-op (content_sha + git blob
    SHAs tous identiques) DOIT rester refuse.
    """
    repo = _git_repo(tmp_path)
    py_rel = "py/nb.ipynb"
    cs_rel = "cs/nb.ipynb"

    _commit(repo, py_rel, _nb(source=["# Title\n"]), "base py")
    _commit(repo, cs_rel, _nb(source=["// Title\n"]), "base cs")

    py_blob = ctp._git_blob_sha(repo, py_rel)
    cs_blob = ctp._git_blob_sha(repo, cs_rel)
    py_content = ctp._content_sha(repo, py_rel)
    cs_content = ctp._content_sha(repo, cs_rel)

    pairs_dir = repo / "twin_pairs.d"
    pairs_dir.mkdir()
    _make_pair_yaml_with_content_sha(
        pairs_dir, "Search-X", py_rel, cs_rel,
        py_blob, cs_blob, py_content, cs_content,
    )

    pair = ctp.load_registry(pairs_dir)[0]
    audit, cur_py, is_noop = ctp.update_pair(repo, pair)
    assert is_noop is True, (
        "vrai no-op (recorded == HEAD sur content_sha et git blob SHA) doit "
        "rester refuse (faux audit, design-gate #9399 critere 2)"
    )


# --- 3. Discrimination : un changement pedagogique n'est PAS un no-op -------

def test_real_content_change_is_not_noop(tmp_path):
    """Un changement de prose reelle -> content_sha diff -> no-op = False."""
    repo = _git_repo(tmp_path)
    py_rel = "py/nb.ipynb"
    cs_rel = "cs/nb.ipynb"

    _commit(repo, py_rel, _nb(source=["# Title\n"]), "base py")
    _commit(repo, cs_rel, _nb(source=["// Title\n"]), "base cs")

    py_blob_v1 = ctp._git_blob_sha(repo, py_rel)
    cs_blob_v1 = ctp._git_blob_sha(repo, cs_rel)
    py_content_v1 = ctp._content_sha(repo, py_rel)
    cs_content_v1 = ctp._content_sha(repo, cs_rel)

    # Après : changer la prose.
    _commit(repo, py_rel, _nb(source=["# Title modifié\n"]), "prose edit py")

    pairs_dir = repo / "twin_pairs.d"
    pairs_dir.mkdir()
    _make_pair_yaml_with_content_sha(
        pairs_dir, "Search-Y", py_rel, cs_rel,
        py_blob_v1, cs_blob_v1, py_content_v1, cs_content_v1,
    )

    pair = ctp.load_registry(pairs_dir)[0]
    audit, cur_py, is_noop = ctp.update_pair(repo, pair)
    assert is_noop is False, (
        "un changement de prose reelle -> content_sha diff -> doit "
        "rebbaseliner (pas un no-op)"
    )
    # Sanity : l'audit produit est bien le contenu courant.
    assert audit["content_python_sha"] != py_content_v1
