#!/usr/bin/env python3
"""content_sha du registre de parite (#9399 volet c) — metadata-immune, prose-sensitive.

Avant #9399 volet (c), le gate comparait le **git blob SHA** du notebook entier.
Or un tampon `metadata.cost` seul (niveau carnet, jamais compile) deplace le blob
SHA -> DRIFT faux positif (les 2 Sudoku-8/14 BDD du 2026-08-04, ou seul le bloc
cost avait bouge). Pire, lancer `--update` apres un tel tampon ecrivait une entree
d'audit datee pour un changement NON pedagogique -> faux audit (ai-01 design-gate #9399).

Volet (c) ajoute un `content_*_sha` (SHA-256 du notebook **sans `nb["metadata"]`**),
enregistre a cote des `python_sha`/`csharp_sha` (anti-regression : les blob SHA
restent pour inspection). Le verdict DRIFT prefere le content_sha quand l'audit
l'enregistre ; retombe sur le blob pour les paires legacy (pre-content_sha).

Ces tests pincent le critere d'acceptation ai-01 :
  - un tampon metadata.cost SEUL sur un carnet enregistre ne produit AUCUN DRIFT ;
  - une correction de prose (cellule markdown) en produit toujours un.

Run:
    pytest scripts/notebook_tools/tests/test_check_twin_parity_content_sha.py
"""
from __future__ import annotations

import hashlib
import json
import os
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


def _commit(repo: Path, rel: str, nb: dict, msg: str) -> None:
    p = repo / rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(nb), encoding="utf-8")
    subprocess.run(["git", "add", "-A"], cwd=repo, check=True, capture_output=True)
    subprocess.run(["git", "commit", "-qm", msg], cwd=repo,
                   check=True, capture_output=True)


def _nb(source: list[str] | None = None, cost: float | None = None) -> dict:
    return {
        "cells": [{
            "cell_type": "markdown",
            "source": source if source is not None else ["# Title\n"],
            "metadata": {},
        }],
        "metadata": ({"cost": {"api_usd_est": cost}} if cost is not None
                     else {"kernelspec": {"name": "python3"}}),
        "nbformat": 4,
        "nbformat_minor": 5,
    }


# --- 1. _content_sha : metadata-immune + prose-sensitive ---------------------

def test_content_sha_ignores_notebook_level_metadata(tmp_path):
    repo = _git_repo(tmp_path)
    rel = "nb.ipynb"
    _commit(repo, rel, _nb(cost=0.0), "base")
    before = ctp._content_sha(repo, rel)
    _commit(repo, rel, _nb(cost=9.99), "cost stamp only")
    after = ctp._content_sha(repo, rel)
    assert before == after, (
        "un tampon metadata.cost seul ne doit PAS changer le content_sha "
        f"(before={before}, after={after})"
    )


def test_content_sha_detects_prose_change(tmp_path):
    repo = _git_repo(tmp_path)
    rel = "nb.ipynb"
    _commit(repo, rel, _nb(source=["# Title\n"]), "base")
    before = ctp._content_sha(repo, rel)
    _commit(repo, rel, _nb(source=["# Different Title\n"]), "prose edit")
    after = ctp._content_sha(repo, rel)
    assert before != after, (
        "une correction de prose DOIT changer le content_sha "
        "(critere d'acceptation ai-01 #9399)"
    )


def test_content_sha_is_sha256_hex_64():
    # shape contract : 64-char lowercase hex (distinct du git blob 40-hex)
    import re
    # pas de git ici : on construit le canonique a la main pour verifier la forme.
    nb = _nb(cost=1.0)
    stripped = {k: v for k, v in nb.items() if k != "metadata"}
    canon = json.dumps(stripped, sort_keys=True, ensure_ascii=False, separators=(",", ":"))
    sha = hashlib.sha256(canon.encode("utf-8")).hexdigest()
    assert re.fullmatch(r"[0-9a-f]{64}", sha)


# --- 2. _cmp_pair_shas : prefer content, fall back blob ----------------------

def test_cmp_pair_shas_prefers_content_when_recorded():
    d = {"python_sha": "blobP", "csharp_sha": "blobC",
         "content_python_sha": "cp", "content_csharp_sha": "cc"}
    assert ctp._cmp_pair_shas(d) == ("cp", "cc")


def test_cmp_pair_shas_falls_back_to_blob_for_legacy():
    d = {"python_sha": "blobP", "csharp_sha": "blobC"}  # no content_*_sha
    assert ctp._cmp_pair_shas(d) == ("blobP", "blobC")


# --- 3. _shas_match : metadata-only = no-op (pas de faux audit) -------------

def test_shas_match_metadata_only_change_is_noop():
    # l'ancien audit a enregistre content_sha ; une metadata-only change ne
    # doit PAS declencher un nouvel audit (faux audit, ai-01 design-gate).
    record = {"content_python_sha": "cp", "content_csharp_sha": "cc"}
    new_entry = {"python_sha": "newBlob",  # blob a change (metadata)
                 "csharp_sha": "blobC",
                 "content_python_sha": "cp",  # content inchange
                 "content_csharp_sha": "cc"}
    assert ctp._shas_match(record, new_entry) is True


def test_shas_match_prose_change_is_not_noop():
    record = {"content_python_sha": "cp", "content_csharp_sha": "cc"}
    new_entry = {"content_python_sha": "cp2",  # prose a change le content
                 "content_csharp_sha": "cc"}
    assert ctp._shas_match(record, new_entry) is False


def test_shas_match_legacy_blob_path_still_works():
    # paires legacy (pas de content_sha) : comparaison blob inchangee.
    record = {"python_sha": "blobP", "csharp_sha": "blobC"}
    new_entry = {"python_sha": "blobP", "csharp_sha": "blobC"}
    assert ctp._shas_match(record, new_entry) is True
