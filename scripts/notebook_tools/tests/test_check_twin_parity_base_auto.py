#!/usr/bin/env python3
"""La base du gate `--per-pair` se lit a l'execution, pas sur le main du jour (#22292).

En CI, `actions/checkout` extrait `refs/pull/N/merge` : un commit de fusion dont
le PREMIER parent est le `main` tel qu'il etait a l'evenement, le second etant la
tete de la PR. `origin/main`, lui, est refetch au demarrage du job. Sous famine
de runners, les deux divergent, et le verdict depend alors du **temps passe en
file** plutot que de ce que la PR fait.

La propriete pinnee ici, et elle seule : **un atterrissage sur `main` posterieur
au merge ref ne peut pas transformer le verdict d'une PR qui ne touche pas la
paire**. Deux bases sont comparees sur le MEME arbre de merge :

  - `--base origin/main` (comportement d'avant le fix) : la paire est OK au main
    du jour, DRIFT au merge ref -> `DRIFT_INTRODUCED`, donc un rouge bloquant sur
    une PR innocente ;
  - `--base auto` (le fix) : la paire est DRIFT des deux cotes -> le drift est
    `DRIFT_PRE_EXISTING`, qui ne fail pas le gate et releve de sa PR de
    rebaseline dediee (#8264).

Le test ne pretend pas rejouer la sequence exacte de l'incident #22218 : il
rejoue sa cause -- le verdict qui suit la file d'attente -- et echoue si on
revient a `origin/main`.

Run:
    pytest scripts/notebook_tools/tests/test_check_twin_parity_base_auto.py
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

def _git(repo: Path, *args: str) -> str:
    r = subprocess.run(["git", *args], cwd=repo, check=True, capture_output=True,
                       text=True, encoding="utf-8", errors="replace")
    return r.stdout.strip()


def _repo(tmp_path: Path) -> Path:
    repo = tmp_path / "repo"
    repo.mkdir()
    _git(repo, "init", "-q", "-b", "main")
    _git(repo, "config", "user.email", "t@t")
    _git(repo, "config", "user.name", "t")
    return repo


def _nb(text: str) -> dict:
    return {
        "cells": [{"cell_type": "markdown", "source": [text], "metadata": {}}],
        "metadata": {"kernelspec": {"name": "python3"}},
        "nbformat": 4,
        "nbformat_minor": 5,
    }


def _write(repo: Path, rel: str, payload: dict | str) -> None:
    p = repo / rel
    p.parent.mkdir(parents=True, exist_ok=True)
    if isinstance(payload, dict):
        p.write_text(json.dumps(payload), encoding="utf-8")
    else:
        p.write_text(payload, encoding="utf-8")


def _commit(repo: Path, msg: str) -> str:
    _git(repo, "add", "-A")
    _git(repo, "commit", "-qm", msg)
    return _git(repo, "rev-parse", "HEAD")


def _registry(pairs_dir: Path, py_sha: str, cs_sha: str) -> None:
    """Une entree de registre (file-per-entry, #8542) pour une paire unique."""
    pairs_dir.mkdir(parents=True, exist_ok=True)
    (pairs_dir / "pair-01.yaml").write_text(
        "name: Pair-01\n"
        "family: Test\n"
        "python: py/nb-01.ipynb\n"
        "csharp: cs/nb-01.ipynb\n"
        "parity_level: surface\n"
        "last_audit:\n"
        "  date: 2026-10-23\n"
        "  by: myia-ai-01:CoursIA\n"
        f"  python_sha: {py_sha}\n"
        f"  csharp_sha: {cs_sha}\n",
        encoding="utf-8",
    )


def _run_cli(repo: Path, base: str) -> dict:
    """Lance l'outil dans le mode exact du gate CI et rend le rapport JSON."""
    r = subprocess.run(
        [sys.executable, str(Path(ctp.__file__)), "--json", "--check",
         "--per-pair", "--base", base,
         "--repo-root", str(repo),
         "--registry", str(repo / "twin_pairs.d")],
        cwd=repo, capture_output=True, text=True,
        encoding="utf-8", errors="replace",
    )
    # rc 0 = gate vert, rc 1 = DRIFT_INTRODUCED. Tout autre code est une panne
    # d'outil et doit faire echouer le test plutot que se lire comme un verdict.
    assert r.returncode in (0, 1), f"rc inattendu {r.returncode}: {r.stderr}"
    assert r.stdout.lstrip().startswith("{"), f"stdout non-JSON: {r.stdout!r} / {r.stderr}"
    return json.loads(r.stdout)


def _merge_ref_repo(tmp_path: Path) -> tuple[Path, str]:
    """Un depot dont HEAD est un merge ref GitHub, avec un `main` qui a avance.

    Chronologie, calquee sur la fenetre d'attente en file :

      t1  main : notebooks v1, registre faux (SHA d'une version anterieure)
                 -> la paire est DRIFT : c'est le drift PRE-EXISTANT, celui
                 qu'une PR de rebaseline dediee doit traiter (#8264) ;
      PR  branchee sur t1, ne touche QUE `docs/note.md` (aucune paire) ;
      t2  main : `twin_pairs.d/pair-01.yaml` rebaseline sur les SHAs de v1
                 -> la paire est OK au main du jour ;
      M   merge ref : fusion de la PR dans **t1** (sujet au format GitHub),
                 construit AVANT t2 et jamais reconstruit.

    Rend (repo, sha de t2). HEAD est laisse sur M.
    """
    repo = _repo(tmp_path)
    pairs = repo / "twin_pairs.d"

    _write(repo, "py/nb-01.ipynb", _nb("# Py v1\n"))
    _write(repo, "cs/nb-01.ipynb", _nb("// Cs v1\n"))
    _write(repo, "docs/note.md", "v1\n")
    # SHA volontairement perime : la paire est en DRIFT des t1.
    _registry(pairs, "f" * 40, "f" * 40)
    t1 = _commit(repo, "t1")

    _git(repo, "checkout", "-q", "-b", "feature")
    _write(repo, "docs/note.md", "v1 + la PR\n")
    feature = _commit(repo, "PR: touche un fichier sans rapport")

    _git(repo, "checkout", "-q", "main")
    py_sha = ctp._git_blob_sha(repo, "py/nb-01.ipynb", "HEAD")
    cs_sha = ctp._git_blob_sha(repo, "cs/nb-01.ipynb", "HEAD")
    _registry(pairs, py_sha, cs_sha)
    t2 = _commit(repo, "rebaseline de la paire sur main")

    # Le merge ref : sujet exact du commit fabrique par GitHub.
    _git(repo, "checkout", "-q", "-B", "merge-ref", t1)
    _git(repo, "merge", "-q", "--no-ff", "feature", "-m",
         f"Merge {feature[:10]} into {t1[:10]}")

    # `origin/main` = le main du jour, refetch au demarrage du job.
    _git(repo, "update-ref", "refs/remotes/origin/main", t2)
    return repo, t2


# --- resolve_base_ref ---------------------------------------------------------

def test_auto_uses_first_parent_on_github_merge_commit(tmp_path):
    repo, _ = _merge_ref_repo(tmp_path)
    assert ctp.resolve_base_ref(repo, "auto") == "HEAD^1"


def test_auto_keeps_origin_main_off_a_merge_ref(tmp_path):
    repo = _repo(tmp_path)
    _write(repo, "a.txt", "a\n")
    _commit(repo, "linéaire")
    assert ctp.resolve_base_ref(repo, "auto") == "origin/main"


def test_auto_keeps_origin_main_on_a_non_github_merge(tmp_path):
    """Un commit de fusion pousse par l'auteur sur sa branche n'est pas un merge
    ref : son premier parent n'est pas le main du depot. On garde la base
    d'avant le fix plutot que d'en inventer une pire."""
    repo = _repo(tmp_path)
    _write(repo, "a.txt", "a\n")
    _commit(repo, "base")
    _git(repo, "checkout", "-q", "-b", "side")
    _write(repo, "b.txt", "b\n")
    _commit(repo, "side")
    _git(repo, "checkout", "-q", "main")
    _write(repo, "c.txt", "c\n")
    _commit(repo, "main")
    _git(repo, "merge", "-q", "--no-ff", "side", "-m", "fusion manuelle par l'auteur")
    assert ctp.resolve_base_ref(repo, "auto") == "origin/main"


def test_non_auto_base_is_returned_unchanged(tmp_path):
    repo = _repo(tmp_path)
    _write(repo, "a.txt", "a\n")
    _commit(repo, "base")
    assert ctp.resolve_base_ref(repo, "origin/main") == "origin/main"
    assert ctp.resolve_base_ref(repo, "HEAD~1") == "HEAD~1"


# --- propriete du gate --------------------------------------------------------

def test_main_advancing_after_the_merge_ref_does_not_red_an_innocent_pr(tmp_path):
    """Le coeur du fix : meme arbre, meme PR, deux bases, deux verdicts."""
    repo, _ = _merge_ref_repo(tmp_path)

    # Avant le fix : le main du jour est OK, le merge ref porte le drift
    # pre-existant -> l'outil impute ce drift a la PR.
    legacy = _run_cli(repo, "origin/main")
    assert legacy["base_ref"] == "origin/main"
    assert legacy["drift_introduced"] == 1, legacy["pairs"]
    assert legacy["pairs"][0]["verdict"] == "DRIFT_INTRODUCED"

    # Apres le fix : le drift est constate des deux cotes, il reste pre-existant
    # et releve de sa PR de rebaseline dediee (#8264).
    fixed = _run_cli(repo, "auto")
    assert fixed["base_ref"] == "HEAD^1"
    assert fixed["drift_introduced"] == 0, fixed["pairs"]
    assert fixed["drift_pre_existing"] == 1
    assert fixed["pairs"][0]["verdict"] == "DRIFT_PRE_EXISTING"
