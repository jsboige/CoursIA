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

    Scenario fondateur #11919 : le recorded pointe sur un blob qui N'EST
    PLUS accessible depuis HEAD (orphelin par squash). On simule cela en :
      1. capturant le blob v1 (le recorded d'origine),
      2. creant une branche ephemere qui pose un blob v2 (meme contenu
         didactique, juste un champ metadata ajoute qui ne touche pas aux
         cellules -> content_sha reste identique, mais le git blob SHA change),
      3. detruisant cette branche + reflog expire + gc pour rendre le blob
         v2 inaccessible depuis HEAD.

    Apres : HEAD contient toujours le blob v1, mais le registre pointe sur
    le blob v2 (orphelin). Discrimination : `_blob_ancestor_in(HEAD, v2)
    == False` -> ce n'est PAS un no-op.

    Retourne le blob v2 (recorded sera v2, calcule sera v1).
    """
    blob_v1 = ctp._git_blob_sha(repo, rel)
    # Creer une branche ephemere qui pose un blob distinct.
    subprocess.run(["git", "checkout", "-q", "-b", "_ephemeral_orphan"],
                   cwd=repo, check=True, capture_output=True)
    # Modifier le notebook en ajoutant un champ metadata qui ne touche pas
    # aux cellules -> content_sha reste stable, mais git blob SHA change.
    p = repo / rel
    nb = json.loads(p.read_text(encoding="utf-8"))
    md = dict(nb.get("metadata", {}))
    md["_squash_orphan_marker"] = "v2-orphaned-on-purpose"
    nb["metadata"] = md
    p.write_text(json.dumps(nb), encoding="utf-8")
    subprocess.run(["git", "add", "-A"], cwd=repo, check=True, capture_output=True)
    subprocess.run(["git", "commit", "-qm", "ephemeral feat"], cwd=repo,
                   check=True, capture_output=True)
    blob_v2 = ctp._git_blob_sha(repo, rel)
    assert blob_v2 != blob_v1, "le blob SHA aurait du changer apres le commit ephemere"
    # Detruire la branche ephemere + reflog + gc pour rendre v2 orphelin.
    subprocess.run(["git", "checkout", "-q", "-"], cwd=repo,
                   check=True, capture_output=True)
    subprocess.run(["git", "branch", "-D", "_ephemeral_orphan"], cwd=repo,
                   check=True, capture_output=True)
    subprocess.run(["git", "reflog", "expire", "--expire=now", "--all"],
                   cwd=repo, check=True, capture_output=True)
    subprocess.run(["git", "gc", "--prune=now"], cwd=repo,
                   check=True, capture_output=True)
    # Verifier que v2 est bien orphelin depuis HEAD et v1 accessible.
    assert not ctp._blob_ancestor_in(repo, blob_v2), (
        f"le blob v2 {blob_v2[:12]} aurait du etre orphelin apres le gc, "
        f"mais `_blob_ancestor_in` le voit encore."
    )
    assert ctp._blob_ancestor_in(repo, blob_v1), (
        f"le blob v1 {blob_v1[:12]} aurait du rester accessible depuis HEAD"
    )
    return blob_v2


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
    # blob SHA git change. Apres la simulation, HEAD pointe toujours sur
    # py_blob_v1, mais le blob v2 (orphelin) est reference par le registre
    # recorded -- reproduisant le cas fondateur Probas-13 Crowdsourcing ou
    # le contenu est intact mais le git blob SHA enregistre pointe sur un
    # blob inaccessible.
    new_py_blob = _squash_replace_blob(repo, py_rel, b"")
    assert new_py_blob != py_blob_v1, "le blob SHA aurait du changer"
    # content_sha dépend uniquement des cellules -> identiques avant/apres.
    assert ctp._content_sha(repo, py_rel) == py_content, (
        "le content_sha est cense etre inchange apres un squash sans modif "
        "pedagogique"
    )
    # HEAD est reste sur v1 (la branche ephemere n'a pas ete fusionnee) :
    cur_py_at_HEAD = ctp._git_blob_sha(repo, py_rel)
    assert cur_py_at_HEAD == py_blob_v1, (
        f"HEAD aurait du rester sur v1 ({py_blob_v1[:12]}), "
        f"mais pointe sur {cur_py_at_HEAD[:12]}"
    )

    # Ecriture du registre : recorded pointe sur le blob ORPHELIN (v2), pas
    # sur HEAD (v1). C'est precisement le cas fondateur : le contenu est
    # identique, mais le git blob SHA enregistre n'est plus ancre d'aucun
    # commit accessible.
    pairs_dir = repo / "twin_pairs.d"
    pairs_dir.mkdir()
    _make_pair_yaml_with_content_sha(
        pairs_dir, "Probas-13 Crowdsourcing", py_rel, cs_rel,
        new_py_blob, cs_blob_v1, py_content, cs_content,
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
    # HEAD porte v1 (= py_blob_v1). Le recorded pointait sur v2 (orphelin).
    # Le rebaseline doit calculer cur_py = HEAD = v1 et lever is_noop=False
    # (le recorded v2 est orphelin -- le rebaseline ecrase le recorded avec
    # le SHA accessible, restaurant la coherence).
    assert cur_py == py_blob_v1, (
        f"update_pair aurait du calculer cur_py = HEAD = v1 "
        f"({py_blob_v1[:12]}), a obtenu {cur_py[:12]}"
    )
    assert audit["python_sha"] == py_blob_v1
    assert audit["content_python_sha"] == py_content, (
        "content_sha doit etre preserve par update_pair"
    )
    assert is_noop is False, (
        "un orphelin par squash devrait PAS etre un no-op : le contenu "
        "est identique mais le git blob SHA recorded est orphelin (v2), "
        "ce qui est precisement la classe de cas que le fix #11919 doit "
        "debloquer via reachability check (_blob_ancestor_in)"
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
