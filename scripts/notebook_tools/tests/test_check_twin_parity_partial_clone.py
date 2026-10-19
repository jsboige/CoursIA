#!/usr/bin/env python3
"""`_blob_ancestor_in` sur un clone partiel : aucun blob rapatrie.

Les workflows twin-parity font leur checkout avec `filter: blob:none`. Un
`git rev-list --objects` sans option y rapatrie un par un chaque blob absent
de l'historique : le 2026-10-14, 8 slots sur 10 sont restes bloques de 45 min
a 4 h dans ce seul appel. Le test reproduit un clone partiel et verifie que
la discrimination ancetre / orphelin reste juste sans aucun telechargement.

Run:
    pytest scripts/notebook_tools/tests/test_check_twin_parity_partial_clone.py
"""
from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import check_twin_parity as ctp  # noqa: E402


def _git(cwd: Path, *args: str) -> str:
    r = subprocess.run(["git", *args], cwd=cwd, check=True, capture_output=True,
                       text=True, encoding="utf-8")
    return r.stdout.strip()


def _packs(repo: Path) -> int:
    return len(list((repo / ".git" / "objects" / "pack").glob("*.pack")))


def _partial_clone(tmp_path: Path) -> tuple[Path, str, str]:
    """Depot source a deux commits, puis clone `blob:none` sans checkout."""
    src = tmp_path / "src"
    src.mkdir()
    _git(src, "init", "-q")
    for key, value in (("user.email", "t@t"), ("user.name", "t"),
                       ("uploadpack.allowFilter", "true"),
                       ("uploadpack.allowAnySHA1InWant", "true")):
        _git(src, "config", key, value)
    (src / "nb.ipynb").write_text("v1\n", encoding="utf-8")
    _git(src, "add", "nb.ipynb")
    _git(src, "commit", "-qm", "v1")
    blob_v1 = _git(src, "rev-parse", "HEAD:nb.ipynb")
    (src / "nb.ipynb").write_text("v2\n", encoding="utf-8")
    _git(src, "commit", "-qam", "v2")
    blob_v2 = _git(src, "rev-parse", "HEAD:nb.ipynb")

    clone = tmp_path / "clone"
    subprocess.run(["git", "clone", "-q", "--filter=blob:none", "--no-checkout",
                    src.as_uri(), str(clone)], check=True, capture_output=True)
    return clone, blob_v1, blob_v2


def test_historical_blob_reachable_without_fetch(tmp_path):
    clone, blob_v1, blob_v2 = _partial_clone(tmp_path)
    packs_before = _packs(clone)

    assert ctp._blob_ancestor_in(clone, blob_v1), "blob d'un commit ancetre non reconnu"
    assert ctp._blob_ancestor_in(clone, blob_v2), "blob du commit courant non reconnu"
    assert not ctp._blob_ancestor_in(clone, "0" * 40), "blob inconnu vu comme ancetre"

    assert _packs(clone) == packs_before, (
        "rev-list a rapatrie des blobs : le clone partiel se remplit a chaque appel")


def test_memo_follows_the_resolved_commit(tmp_path):
    """Le memo est indexe par commit resolu : un nouveau commit est relu."""
    clone, _, _ = _partial_clone(tmp_path)
    _git(clone, "config", "user.email", "t@t")
    _git(clone, "config", "user.name", "t")
    assert not ctp._blob_ancestor_in(clone, "0" * 40)

    (clone / "extra.txt").write_text("v3\n", encoding="utf-8")
    _git(clone, "add", "extra.txt")
    _git(clone, "commit", "-qm", "v3")
    blob_v3 = _git(clone, "rev-parse", "HEAD:extra.txt")

    assert ctp._blob_ancestor_in(clone, blob_v3), "memo perime apres un nouveau commit"
