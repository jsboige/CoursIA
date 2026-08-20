#!/usr/bin/env python3
"""Reparation squash-orphan sans --force (#11919) -- test end-to-end.

Incident fondateur (2026-08-20, Probas-13 Crowdsourcing) : le squash de #11878
a fait arriver sur main un notebook au contenu intact mais dont le blob SHA
atteste (bd40c841e143) n'y existe pas. Deux sous-commandes du meme outil, sur
la meme paire, au meme instant :

    --verify-recorded-sha  ->  MISMATCH (compare les blob SHA strictement)
    --update               ->  Refusees (no-op)  (le garde ne voyait que les
                               content SHA, identiques eux)

L'outil canonique de reparation considerait qu'il n'y avait rien a reparer
exactement quand il y avait quelque chose a reparer ; il fallait --force, qui
affiche alors l'avertissement « faux audit » -- trompeur, l'information
nouvelle (les blob SHAs frais) est bien reelle.

Depuis #11919 le garde no-op exige les DEUX grandeurs identiques (content ET
blob SHAs) : la reparation squash-orphan passe sans --force et sans
avertissement. Ces tests rejouent l'incident sur un mini-depot :

    1. --update ecrit SANS --force quand recorded_blob != calculated_blob a
       content SHA constant (acceptance 1) ;
    2. aucun avertissement « faux audit » dans ce cas -- il reste pour le vrai
       no-op force (acceptance 2) ;
    3. apres la reparation, --verify-recorded-sha dit OK : les deux
       sous-commandes ne peuvent plus rendre des verdicts opposes sur la meme
       paire (acceptance 4) ;
    4. le vrai no-op (tout identique) reste refuse sans --force et l'est avec
       --force + avertissement (non-regression du design-gate #9399).

Ce test ECHOUE sur le RED d'avant le fix (le update de la phase 1 etait
refuse : « 0 paire(s) mise(s) a jour » et le verify restait MISMATCH).

Run:
    pytest scripts/notebook_tools/tests/test_check_twin_parity_squash_orphan.py
"""
from __future__ import annotations

import io
import json
import os
import contextlib
import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import check_twin_parity as ctp  # noqa: E402


ORPHAN_BLOB = "deadbeef" * 5  # blob SHA fabrique (lettres = YAML string,
# pas int) : n'existera jamais dans l'historique du mini-depot


def _git_repo(tmp_path: Path) -> Path:
    repo = tmp_path / "repo"
    repo.mkdir()
    for args in (("init", "-q"), ("config", "user.email", "t@t"),
                 ("config", "user.name", "t")):
        subprocess.run(["git", *args], cwd=repo, check=True, capture_output=True)
    return repo


def _commit(repo: Path, rel: str, nb: dict, msg: str) -> str:
    p = repo / rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(nb, ensure_ascii=False), encoding="utf-8")
    subprocess.run(["git", "add", "-A"], cwd=repo, check=True, capture_output=True)
    subprocess.run(["git", "commit", "-qm", msg], cwd=repo,
                   check=True, capture_output=True)
    return ctp._git_blob_sha(repo, rel)


def _nb(title: str) -> dict:
    return {
        "cells": [{"cell_type": "markdown", "source": [f"# {title}\n"],
                   "metadata": {}}],
        "metadata": {"kernelspec": {"name": "python3"}},
        "nbformat": 4, "nbformat_minor": 5,
    }


def _write_registry(tmp_path: Path, repo: Path, orphan: bool) -> Path:
    """1 paire, registre mono-fichier (chemin legacy --registry <file.yaml>).

    L'audit enregistre les content SHAs REELS du carnet a HEAD mais un blob SHA
    soit orphelin (fabrique, cas squash) soit reel (cas no-op vrai).
    """
    py_sha = ctp._git_blob_sha(repo, "nb.py.ipynb")
    cs_sha = ctp._git_blob_sha(repo, "nb.cs.ipynb")
    cpy = ctp._content_sha(repo, "nb.py.ipynb")
    ccs = ctp._content_sha(repo, "nb.cs.ipynb")
    reg = tmp_path / "twin_pairs_test.yaml"
    rec_py = ORPHAN_BLOB if orphan else py_sha
    rec_cs = ORPHAN_BLOB if orphan else cs_sha
    reg.write_text(
        '- name: "Mini Pair"\n'
        '  family: Test/Mini\n'
        '  python: nb.py.ipynb\n'
        '  csharp: nb.cs.ipynb\n'
        '  parity_level: native-both\n'
        "  audits:\n"
        '    - date: "2026-08-19"\n'
        "      by: test\n"
        f"      python_sha: {rec_py}\n"
        f"      csharp_sha: {rec_cs}\n"
        f"      content_python_sha: {cpy}\n"
        f"      content_csharp_sha: {ccs}\n",
        encoding="utf-8",
    )
    return reg


def _run(argv: list[str]) -> tuple[int, str, str]:
    """main() in-process : capture (exit code, stdout, stderr)."""
    out, err = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
        rc = ctp.main(argv)
    return rc, out.getvalue(), err.getvalue()


@pytest.fixture()
def orphan_setup(tmp_path):
    repo = _git_repo(tmp_path)
    _commit(repo, "nb.py.ipynb", _nb("Python"), "py")
    _commit(repo, "nb.cs.ipynb", _nb("CSharp"), "cs")
    reg = _write_registry(tmp_path, repo, orphan=True)
    return repo, reg


def test_orphan_repaired_without_force_and_verdicts_agree(orphan_setup):
    """Acceptances 1 + 4 : le update ecrit sans --force, puis verify = OK."""
    repo, reg = orphan_setup

    # --check : sans lui le mode verify imprime le MISMATCH mais sort 0
    # (lecture humaine) ; le gate CI (#9399 volet b) passe --check.
    rc_v, _, _ = _run(["--registry", str(reg), "--repo-root", str(repo),
                       "--pair", "Mini Pair", "--verify-recorded-sha",
                       "--check"])
    assert rc_v != 0, "le blob orphelin doit d'abord etre un MISMATCH"

    rc_u, out_u, err_u = _run(["--registry", str(reg), "--repo-root", str(repo),
                               "--update", "--pair", "Mini Pair",
                               "--by", "test:orphan-repair"])
    assert rc_u == 0, err_u
    assert "1 paire(s) mise(s) a jour" in out_u + err_u
    assert "Refusees (no-op" not in err_u, (
        "le garde no-op ne doit plus refuser la reparation squash-orphan"
    )

    rc_v2, _, _ = _run(["--registry", str(reg), "--repo-root", str(repo),
                        "--pair", "Mini Pair", "--verify-recorded-sha",
                        "--check"])
    assert rc_v2 == 0, "apres reparation, verify-recorded-sha doit etre OK"


def test_orphan_repair_carries_no_faux_audit_warning(orphan_setup):
    """Acceptance 2 : pas d'avertissement « faux audit » sur la reparation."""
    repo, reg = orphan_setup
    rc, out, err = _run(["--registry", str(reg), "--repo-root", str(repo),
                         "--update", "--pair", "Mini Pair", "--by", "t"])
    assert rc == 0
    assert "faux audit" not in err.lower(), (
        "l'avertissement faux audit est reserve au vrai no-op force"
    )


def test_true_noop_still_refused_then_forced_with_warning(tmp_path):
    """Acceptance 2 (suite) : le VRAI no-op reste refuse ; --force ecrit et
    avertit (non-regression design-gate #9399 critere 2)."""
    repo = _git_repo(tmp_path)
    _commit(repo, "nb.py.ipynb", _nb("Python"), "py")
    _commit(repo, "nb.cs.ipynb", _nb("CSharp"), "cs")
    reg = _write_registry(tmp_path, repo, orphan=False)  # tout identique

    rc, out, err = _run(["--registry", str(reg), "--repo-root", str(repo),
                         "--update", "--pair", "Mini Pair", "--by", "t"])
    assert rc == 0
    assert "Refusees (no-op" in err
    assert "0 paire(s) mise(s) a jour" in out + err

    rcf, outf, errf = _run(["--registry", str(reg), "--repo-root", str(repo),
                            "--update", "--pair", "Mini Pair", "--by", "t",
                            "--force"])
    assert rcf == 0
    assert "faux audit" in errf.lower()
    assert "1 paire(s) mise(s) a jour" in outf + errf
