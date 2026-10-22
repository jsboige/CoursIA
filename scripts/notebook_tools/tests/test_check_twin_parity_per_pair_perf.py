#!/usr/bin/env python3
"""Le registre de base ne se charge qu'en partie en mode `--per-pair --pair` (#21972).

Avant ce fix, `--check --per-pair --base <ref> --pair <nom>` evalue bien une
seule paire, mais le registre du base-ref etait charge **en entier** : un
`git show` par fichier (2374 fichiers sous `twin_pairs.d/`), soit 3 min 27 s
pour une seule paire sur un poste Windows.

Le fix (#21972, voie « filtrer avant de lire ») : `_load_registry_at_ref`
recoit l'ensemble des noms selectionnes et ne fait `git show` que les fichiers
des paires visees. `names=None` (mode plein, sans selecteur) ne filtre rien.

Ces tests pinnent la garantie en **comptant les appels `git show`/`cat-file`** :
  - avec `--pair`, le chargement au base-ref est borne (pas integral) ;
  - sans selecteur, il reste integral (le mode plein du gate CI est inchange).

Run:
    pytest scripts/notebook_tools/tests/test_check_twin_parity_per_pair_perf.py
"""
from __future__ import annotations

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
    """Un mini-depot git pret a committer des notebooks + un registre."""
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


def _make_pair_yaml(pairs_dir: Path, name: str, py_rel: str, cs_rel: str,
                    py_sha: str, cs_sha: str) -> None:
    """Ecrit une entree registry file-per-entry (legacy, sans content_*_sha) :
    le check reste sur les git blob SHA, donc `check_pair` ne fait PAS de
    `git show` (pas de `_content_sha`) -- seuls les fichiers de registre sont
    lus au base-ref."""
    entry = pairs_dir / f"{ctp._slug(name)}.yaml"
    entry.write_text(
        f"name: {name}\n"
        f"family: Test\n"
        f"python: {py_rel}\n"
        f"csharp: {cs_rel}\n"
        f"parity_level: surface\n"
        f"last_audit:\n"
        f"  date: 2026-08-19\n"
        f"  by: myia-po-2023:CoursIA-2\n"
        f"  python_sha: {py_sha}\n"
        f"  csharp_sha: {cs_sha}\n",
        encoding="utf-8",
    )


def _build_repo(tmp_path: Path, n: int) -> tuple[Path, Path]:
    """Un depot avec `n` paires (notebooks + fichiers de registre) committees a
    HEAD, pour que le base-ref `HEAD` porte bien le registre."""
    repo = _git_repo(tmp_path)
    pairs_dir = repo / "twin_pairs.d"
    pairs_dir.mkdir()
    for i in range(n):
        py_rel = f"py/nb-{i:02d}.ipynb"
        cs_rel = f"cs/nb-{i:02d}.ipynb"
        _commit(repo, py_rel, _nb(source=[f"# Py {i}\n"]), f"base py {i}")
        _commit(repo, cs_rel, _nb(source=[f"// Cs {i}\n"]), f"base cs {i}")
    for i in range(n):
        name = f"Pair-{i:02d}"
        py_rel = f"py/nb-{i:02d}.ipynb"
        cs_rel = f"cs/nb-{i:02d}.ipynb"
        _make_pair_yaml(pairs_dir, name, py_rel, cs_rel,
                        ctp._git_blob_sha(repo, py_rel),
                        ctp._git_blob_sha(repo, cs_rel))
    subprocess.run(["git", "add", "-A"], cwd=repo, check=True, capture_output=True)
    subprocess.run(["git", "commit", "-qm", "registry"], cwd=repo,
                   check=True, capture_output=True)
    return repo, pairs_dir


def _counting_run_git(monkeypatch) -> dict:
    """Monkeypatch `_run_git` pour compter les appels `git show`/`cat-file`
    (le point d'etranglement de TOUS les appels git de l'organe)."""
    counts = {"show": 0, "cat-file": 0}
    real = ctp._run_git

    def wrapper(args, **kwargs):
        if len(args) >= 2:
            if args[1] == "show":
                counts["show"] += 1
            elif args[1] == "cat-file":
                counts["cat-file"] += 1
        return real(args, **kwargs)

    monkeypatch.setattr(ctp, "_run_git", wrapper)
    return counts


# --- 1. Avec --pair : le chargement au base-ref n'est PAS integral ------------


def test_per_pair_selector_reads_only_target_at_base(tmp_path, monkeypatch):
    """`--per-pair --base HEAD --pair <nom>` ne fait `git show` que la paire
    visee au base-ref, pas les N fichiers du registre. Rougit si le chargement
    redevient integral (#21972)."""
    n = 12
    repo, pairs_dir = _build_repo(tmp_path, n)
    counts = _counting_run_git(monkeypatch)

    rc = ctp.main([
        "--check", "--per-pair", "--base", "HEAD",
        "--pair", "Pair-00",
        "--registry", str(pairs_dir),
        "--repo-root", str(repo),
    ])
    # Un verdict a ete rendu (pas une erreur rc 2) : la paire a ete evaluee.
    assert rc in (0, 1)
    assert counts["show"] <= 3, (
        f"--per-pair --pair doit ne `git show` que la paire visee (+ ses audits) "
        f"au base-ref, pas les {n} fichiers du registre : {counts['show']} "
        f"`git show` observes (chargement integral re-introduit, #21972)"
    )


# --- 2. Sans selecteur : le mode plein du gate CI reste integral -------------


def test_per_pair_no_selector_still_reads_all(tmp_path, monkeypatch):
    """`--per-pair --base HEAD` (sans selecteur) charge TOUS les fichiers de
    registre au base-ref : le filtre #21972 ne doit PAS degrader le mode plein
    (acceptance : le verdict du mode plein est identique avant/apres)."""
    n = 12
    repo, pairs_dir = _build_repo(tmp_path, n)
    counts = _counting_run_git(monkeypatch)

    rc = ctp.main([
        "--check", "--per-pair", "--base", "HEAD",
        "--registry", str(pairs_dir),
        "--repo-root", str(repo),
    ])
    assert rc in (0, 1)
    assert counts["show"] >= n - 1, (
        f"le mode plein (sans selecteur) doit rester integral : "
        f"{counts['show']} `git show` pour {n} paires au base-ref"
    )


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))
