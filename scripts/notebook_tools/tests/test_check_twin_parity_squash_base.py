#!/usr/bin/env python3
"""Orphelin A VENIR par squash : la base du no-op est la branche, pas `main` (#28122).

Le no-op d'`--update` compare les `content_*_sha` (metadata-immunes). Quand la
seule difference est un tampon de metadata, l'ecriture est refusee -- c'est le
design-gate #9399 critere 2 (cas Sudoku-08/14 BDD), et c'est le comportement
voulu.

Mais la discrimination d'orphelin (`_blob_ancestor_in`) testait la
joignabilite du blob enregistre depuis **HEAD DE LA BRANCHE**. Sur une branche
destinee au squash, le blob enregistre peut etre encore joignable depuis HEAD
(il est pose par un commit de la branche) tout en n'etant **pas** dans `main` :
apres le squash, l'arbre de fusion portera le blob courant, pas celui
enregistre -- l'attestation decrit alors un blob que `main` n'a jamais eu.

Mesure (#28122, `metajeux-4-chemin-minimal-robinson-goforth`) : attestation
ecrite a `4a3a3975` (blob C# `909d8752`), puis commit `1185b9f4` qui ne retire
que des chemins papermill (metadata) -> blob `82e0c0c9`. `--update` repond
NO-OP : le contenu est intact, donc rien a re-attester. L'attestation
enregistree reste sur `909d8752`, que le squash ne livrera jamais a `main`.

Le correctif : un blob enregistre different du blob courant et **non
joignable depuis la base** (`origin/main`) est un orphelin a venir -> le
rebaseline doit ecrire. Le no-op metadata-only reste preserve quand le blob
enregistre est deja sur la base (Sudoku-08/14 BDD) : c'est le meme contenu, et
`main` porte deja ce blob.

Run:
    pytest scripts/notebook_tools/tests/test_check_twin_parity_squash_base.py
"""
from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

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


def _nb(source: list[str] | None = None, meta: dict | None = None) -> dict:
    metadata = {"kernelspec": {"name": "python3"}}
    if meta:
        metadata.update(meta)
    return {
        "cells": [{
            "cell_type": "markdown",
            "source": source if source is not None else ["# Title\n"],
            "metadata": {},
        }],
        "metadata": metadata,
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


def _git(repo: Path, *args: str) -> str:
    r = subprocess.run(["git", *args], cwd=repo, check=True, capture_output=True,
                       text=True, encoding="utf-8", errors="replace")
    return r.stdout.strip()


def _set_origin_main(repo: Path, sha: str) -> None:
    """Publie `refs/remotes/origin/main` (la base du squash) sur `sha`."""
    subprocess.run(["git", "update-ref", "refs/remotes/origin/main", sha],
                   cwd=repo, check=True, capture_output=True)


def _make_pair_yaml_with_content_sha(
    pairs_dir: Path, name: str, py_rel: str, cs_rel: str,
    py_sha: str, cs_sha: str, py_content: str, cs_content: str,
) -> None:
    """Ecrit une entree registry file-per-entry (cf #8542) avec content_sha."""
    entry = pairs_dir / f"{name}.yaml"
    entry.write_text(
        f"name: {name}\n"
        f"family: GameTheory\n"
        f"python: {py_rel}\n"
        f"csharp: {cs_rel}\n"
        f"parity_level: full\n"
        f"last_audit:\n"
        f"  date: 2026-11-22\n"
        f"  by: myia-po-2024:CoursIA-2\n"
        f"  python_sha: {py_sha}\n"
        f"  csharp_sha: {cs_sha}\n"
        f"  content_python_sha: {py_content}\n"
        f"  content_csharp_sha: {cs_content}\n",
        encoding="utf-8",
    )


def _base_repo(tmp_path: Path) -> tuple[Path, str, str, str, str]:
    """Depot de base : py et cs commites, `origin/main` pose dessus.

    Retourne (repo, py_rel, cs_rel, py_blob, cs_blob).
    """
    repo = _git_repo(tmp_path)
    py_rel = "py/nb.ipynb"
    cs_rel = "cs/nb.ipynb"
    _commit(repo, py_rel, _nb(), "base py")
    _commit(repo, cs_rel, _nb(), "base cs")
    _set_origin_main(repo, _git(repo, "rev-parse", "HEAD"))
    return repo, py_rel, cs_rel, ctp._git_blob_sha(repo, py_rel), \
        ctp._git_blob_sha(repo, cs_rel)


# --- 1. Attestation de branche + commit metadata-only -> le rebaseline ecrit ---

def test_attestation_de_branche_plus_drift_metadata_only_ecrit(tmp_path):
    """Le cas #28122 : l'attestation est un blob que `main` n'a jamais eu.

    Sur la branche, un commit metadata-only change le blob C# ; l'attestation
    enregistree pointe sur le blob d'avant ce commit (un blob de la branche,
    jamais de `main`). Le contenu est intact -> `_shas_match` dit no-op. Mais
    le blob enregistre n'est pas joignable depuis la base : apres le squash,
    `main` portera le blob courant, pas celui enregistre. Le rebaseline doit
    donc ecrire (is_noop = False).
    """
    repo, py_rel, cs_rel, py_blob, cs_blob_base = _base_repo(tmp_path)

    # Branche de travail : commit A (metadata-only) puis commit B (metadata-only).
    _git(repo, "checkout", "-q", "-b", "feature")
    _commit(repo, cs_rel, _nb(meta={"cost": {"usd": 0.01}}), "metadata A")
    cs_blob_A = ctp._git_blob_sha(repo, cs_rel)
    content = ctp._content_sha(repo, cs_rel)
    py_content = ctp._content_sha(repo, py_rel)
    _commit(repo, cs_rel, _nb(meta={"cost": {"usd": 0.02}}), "metadata B")
    cs_blob_B = ctp._git_blob_sha(repo, cs_rel)

    # Le contenu (cellules + outputs) n'a pas bouge : seul le metadata.
    assert content == ctp._content_sha(repo, cs_rel), (
        "le content_sha doit ignorer le metadata de niveau carnet"
    )
    assert cs_blob_A != cs_blob_base and cs_blob_B != cs_blob_A
    # Le blob de l'attestation (A) est joignable depuis HEAD (commit A est un
    # ancetre) : c'est precisement ce qui trompait la discrimination.
    assert ctp._blob_ancestor_in(repo, cs_blob_A), (
        "le blob A doit rester joignable depuis HEAD (c'est la branche, pas "
        "la base, qui le porte)"
    )
    assert not ctp._blob_ancestor_in(repo, cs_blob_A, "origin/main"), (
        "le blob A ne doit PAS etre joignable depuis origin/main : c'est un "
        "orphelin A VENIR (le squash ne le livrera jamais)"
    )

    pairs_dir = repo / "twin_pairs.d"
    pairs_dir.mkdir()
    _make_pair_yaml_with_content_sha(
        pairs_dir, "Metajeux-4-Chemin-Minimal", py_rel, cs_rel,
        py_blob, cs_blob_A, py_content, content,
    )

    pair = ctp.load_registry(pairs_dir)[0]
    audit, cur_py, is_noop = ctp.update_pair(repo, pair)
    assert is_noop is False, (
        "un blob enregistre qui n'est pas sur la base est un orphelin a venir : "
        "le rebaseline doit ecrire, pas refuser (#28122)"
    )
    assert audit["csharp_sha"] == cs_blob_B, (
        f"le rebaseline doit enregistrer le blob courant ({cs_blob_B[:12]}), "
        f"a obtenu {str(audit['csharp_sha'])[:12]}"
    )
    assert audit["content_csharp_sha"] == content, (
        "le content_sha doit rester preserve"
    )
    assert cur_py == py_blob


# --- 2. Le no-op metadata-only reste un no-op quand le blob est sur la base ---

def test_noop_metadata_only_preserve_si_le_blob_est_sur_la_base(tmp_path):
    """Design-gate #9399 critere 2 : le blob enregistre est deja sur `main`.

    Ici l'attestation porte le blob que `origin/main` porte deja (cas
    Sudoku-08/14 BDD). Le drift est metadata-only : le rebaseline doit rester
    refuse (faux audit), sinon chaque `--update` daterait une attestation
    identique.
    """
    repo, py_rel, cs_rel, py_blob, cs_blob_base = _base_repo(tmp_path)

    _git(repo, "checkout", "-q", "-b", "feature")
    _commit(repo, cs_rel, _nb(meta={"cost": {"usd": 0.01}}), "metadata only")
    cs_blob_now = ctp._git_blob_sha(repo, cs_rel)
    content = ctp._content_sha(repo, cs_rel)
    py_content = ctp._content_sha(repo, py_rel)

    assert cs_blob_now != cs_blob_base, "le blob SHA doit bouger"
    assert content == ctp._content_sha(repo, cs_rel)
    assert ctp._blob_ancestor_in(repo, cs_blob_base, "origin/main"), (
        "le blob enregistre est sur la base : il n'est pas un orphelin"
    )

    pairs_dir = repo / "twin_pairs.d"
    pairs_dir.mkdir()
    _make_pair_yaml_with_content_sha(
        pairs_dir, "Search-MetaOnly", py_rel, cs_rel,
        py_blob, cs_blob_base, py_content, content,
    )

    pair = ctp.load_registry(pairs_dir)[0]
    audit, _cur_py, is_noop = ctp.update_pair(repo, pair)
    assert is_noop is True, (
        "un drift metadata-only dont le blob enregistre est sur la base doit "
        "rester un no-op (design-gate #9399 critere 2)"
    )
    assert audit["content_csharp_sha"] == content
