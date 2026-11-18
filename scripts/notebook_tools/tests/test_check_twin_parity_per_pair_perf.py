#!/usr/bin/env python3
"""Le registre de base ne se charge qu'en partie en mode `--per-pair --pair` (#21972).

Avant ce fix, `--check --per-pair --base <ref> --pair <nom>` evalue bien une
seule paire, mais le registre du base-ref etait charge **en entier** : un
`git show` par fichier (2374 fichiers sous `twin_pairs.d/`), soit 3 min 27 s
pour une seule paire sur un poste Windows.

Le fix (#21972, voie « filtrer avant de lire ») : `_load_registry_at_ref`
recoit l'ensemble des noms selectionnes et ne fait `git show` que les fichiers
des paires visees **et leurs fichiers d'audit**. `names=None` (mode plein, sans
selecteur) ne filtre rien.

Ces tests pinnent la garantie en **comptant les appels `git show`**, DECOMPOSES
en lectures de fichiers de **paire** (profondeur 1 sous le registre) et de
fichiers d'**audit** (profondeur 2, forme file-per-audit #14911) :

  - avec `--pair`, seule la paire visee est lue (1 fichier de registre) + TOUS
    ses fichiers d'audit — le compte est EXACT, pas un plafond arbitraire ;
  - sans selecteur, le mode plein du gate CI reste integral : 1 lecture par
    fichier de registre + 1 par fichier d'audit, pour TOUTES les paires.

La fixture porte des audits (une version antérieure du test en etait depourvue
: la borne `<= 3` ne mesurait que le cas sans audit et son commentaire « au
plus 2 audits » n'etait pas fonde, le chargeur lisant TOUS les audits de la
paire). Mesure de reference (reproduction independante, c2231) : 12 paires +
5 audits -> ciblé = 1 + 5 = 6 `git show`, plein = 12 + 5 = 17.

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
    """Ecrit une entree registry file-per-entry (profondeur 1, `twin_pairs.d/
    <slug>.yaml`). Le `last_audit:` inline est remplacé par les fichiers d'audit
    separes quand ceux-ci existent (`_load_registry_at_ref` fait
    `data["audits"] = audits; data.pop("last_audit")`) ; il reste ici comme
    baseline de SHAs."""
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


def _make_audit_files(pairs_dir: Path, name: str, count: int,
                      py_sha: str, cs_sha: str) -> None:
    """Ecrit `count` fichiers d'audit separes (forme file-per-audit #14911) sous
    `<registry>/<slug>/<idx>-<date>-<lane>.yaml` (profondeur 2). C'est cette
    profondeur que `_load_registry_at_ref` lit en `git show` distincts : c'est
    exactement le cas avec audits que le test doit couvrir. Les SHAs portent
    ceux du notebook committe pour que le verdict reste OK."""
    d = pairs_dir / ctp._slug(name)
    d.mkdir(parents=True, exist_ok=True)
    for i in range(count):
        day = f"{19 + i:02d}"
        (d / f"{i:04d}-2026-08-{day}-lane.yaml").write_text(
            f"date: 2026-08-{day}\n"
            f"by: myia-po-2023:CoursIA-2\n"
            f"python_sha: {py_sha}\n"
            f"csharp_sha: {cs_sha}\n",
            encoding="utf-8",
        )


def _build_repo(tmp_path: Path, n: int,
                audits: dict[str, int] | None = None) -> tuple[Path, Path]:
    """Un depot avec `n` paires (notebooks + fichiers de registre) committees a
    HEAD, pour que le base-ref `HEAD` porte bien le registre. `audits`
    (nom de paire -> nombre de fichiers d'audit separes) ajoute le cas avec
    audits pour les paires nommees."""
    audits = audits or {}
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
        py_sha = ctp._git_blob_sha(repo, py_rel)
        cs_sha = ctp._git_blob_sha(repo, cs_rel)
        _make_pair_yaml(pairs_dir, name, py_rel, cs_rel, py_sha, cs_sha)
        k = audits.get(name, 0)
        if k:
            _make_audit_files(pairs_dir, name, k, py_sha, cs_sha)
    subprocess.run(["git", "add", "-A"], cwd=repo, check=True, capture_output=True)
    subprocess.run(["git", "commit", "-qm", "registry"], cwd=repo,
                   check=True, capture_output=True)
    return repo, pairs_dir


def _counting_run_git(monkeypatch, reg_rel: str) -> dict:
    """Monkeypatch `_run_git` pour compter les `git show` du base-ref,
    DECOMPOSES en lectures de fichiers de PAIRE (profondeur 1 sous le registre)
    et d'AUDITS (profondeur 2) — la decomposition qui evite de masquer le cas
    avec audits derriere une borne arbitraire. `reg_rel` est le chemin du
    registre relatif a la racine du depot (`twin_pairs.d`)."""
    counts = {"pair": 0, "audit": 0, "other": 0, "cat-file": 0}
    prefix = reg_rel.rstrip("/") + "/"
    real = ctp._run_git

    def wrapper(args, **kwargs):
        if len(args) >= 3 and args[1] == "show":
            spec = args[2]
            path = spec.split(":", 1)[1] if ":" in spec else spec
            if path.startswith(prefix):
                segs = [s for s in path[len(prefix):].split("/") if s]
                counts[{1: "pair", 2: "audit"}.get(len(segs), "other")] += 1
            else:
                counts["other"] += 1
        elif len(args) >= 2 and args[1] == "cat-file":
            counts["cat-file"] += 1
        return real(args, **kwargs)

    monkeypatch.setattr(ctp, "_run_git", wrapper)
    return counts


# --- 1. Avec --pair : le chargement au base-ref n'est PAS integral ------------


def test_per_pair_selector_reads_only_target_at_base(tmp_path, monkeypatch):
    """`--per-pair --base HEAD --pair <nom>` ne fait `git show` au base-ref que
    le fichier de registre de la paire visee + TOUS ses fichiers d'audit, pas
    les N fichiers du registre. Rougit si le chargement redevient integral
    (#21972). Le compte est EXACT (1 lecture de paire + K lectures d'audit),
    pas un plafond arbitraire : le chargeur lit TOUS les audits de la paire."""
    n = 12
    k = 5  # fichiers d'audit de la paire ciblee
    repo, pairs_dir = _build_repo(tmp_path, n, audits={"Pair-00": k})
    reg_rel = pairs_dir.relative_to(repo).as_posix()
    counts = _counting_run_git(monkeypatch, reg_rel)

    rc = ctp.main([
        "--check", "--per-pair", "--base", "HEAD",
        "--pair", "Pair-00",
        "--registry", str(pairs_dir),
        "--repo-root", str(repo),
    ])
    assert rc in (0, 1)
    # 1 lecture de fichier de PAIRE : la paire visee seulement, pas les n.
    assert counts["pair"] == 1, (
        f"--per-pair --pair doit lire 1 fichier de registre (la paire visee), "
        f"pas les {n} du registre : {counts['pair']} lectures de paire "
        f"(chargement integral re-introduit, #21972)"
    )
    # TOUS les fichiers d'audit de la paire visee (pas un sous-ensemble).
    assert counts["audit"] == k, (
        f"--per-pair --pair doit lire les {k} fichiers d'audit de la paire "
        f"visee au base-ref, pas un sous-ensemble arbitraire : "
        f"{counts['audit']} lectures d'audit observees"
    )


# --- 2. Sans selecteur : le mode plein du gate CI reste integral -------------


def test_per_pair_no_selector_still_reads_all(tmp_path, monkeypatch):
    """`--per-pair --base HEAD` (sans selecteur) charge au base-ref TOUS les
    fichiers de registre + TOUS les fichiers d'audit : le filtre #21972 ne doit
    PAS degrader le mode plein (acceptance : le verdict du mode plein est
    identique avant/apres). La decomposition paire/audit est EXACTE : 1 `git
    show` par fichier de registre + 1 par fichier d'audit, pour TOUTES les
    paires (pas un seuil lache qui laisserait passer une lecture en moins)."""
    n = 12
    per = 2  # fichiers d'audit par paire
    audits = {f"Pair-{i:02d}": per for i in range(n)}
    repo, pairs_dir = _build_repo(tmp_path, n, audits=audits)
    reg_rel = pairs_dir.relative_to(repo).as_posix()
    counts = _counting_run_git(monkeypatch, reg_rel)

    rc = ctp.main([
        "--check", "--per-pair", "--base", "HEAD",
        "--registry", str(pairs_dir),
        "--repo-root", str(repo),
    ])
    assert rc in (0, 1)
    total_audits = per * n
    assert counts["pair"] == n, (
        f"le mode plein (sans selecteur) doit lire les {n} fichiers de registre "
        f"au base-ref : {counts['pair']} lectures de paire (attendu : {n})"
    )
    assert counts["audit"] == total_audits, (
        f"le mode plein doit lire les {total_audits} fichiers d'audit "
        f"(= {per} x {n} paires) : {counts['audit']} lectures d'audit "
        f"(attendu : {total_audits})"
    )


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))
