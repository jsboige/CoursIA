#!/usr/bin/env python3
"""Mode --ci-strict du registre de parite (#9399 volet b).

Le gate par-PR (twin-parity.yml) ne rougit QUE le drift INTRODUIT par la PR
(cf L8264 precedent : #8282, #8289, #8322, #8372). Pour reperer un worker
qui a oublie `--update` apres une normalisation outillee, ou un SHA declare
a la main devenu faux, il faut un cron fleet-wide qui voit TOUT le drift.

Ces tests pincent les 2 cas du cron :
  - registre aligne sur working tree -> exit 0, breakdown 0 drift ;
  - registre desaligne sur working tree -> exit 1, breakdown contient
    une categorie de drift (drift_blob / drift_content).

Cas supplementaire : distinction erreur d'outil vs constat drift (cf
L948, c.1240) : un tool error (registre illisible, pas de depot git)
doit EXIT 2 (cf Exit codes docstring), pas etre confondu avec un
constat de drift rouge.

Run:
    pytest scripts/notebook_tools/tests/test_check_twin_parity_ci_sha.py
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
    """Un mini-depot git pret a committer des notebooks."""
    repo = tmp_path / "repo"
    repo.mkdir()
    for args in (("init", "-q"), ("config", "user.email", "t@t"),
                 ("config", "user.name", "t")):
        subprocess.run(["git", *args], cwd=repo, check=True, capture_output=True)
    return repo


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


def _commit(repo: Path, rel: str, nb: dict, msg: str) -> None:
    p = repo / rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(nb), encoding="utf-8")
    subprocess.run(["git", "add", "-A"], cwd=repo, check=True, capture_output=True)
    subprocess.run(["git", "commit", "-qm", msg], cwd=repo,
                   check=True, capture_output=True)


def _make_pair_yaml(pairs_dir: Path, name: str, py_rel: str, cs_rel: str,
                    py_sha: str, cs_sha: str) -> None:
    """Ecrit une entree registry file-per-entry (cf #8542)."""
    entry = pairs_dir / f"{name}.yaml"
    entry.write_text(
        f"name: {name}\n"
        f"family: Search\n"
        f"python: {py_rel}\n"
        f"csharp: {cs_rel}\n"
        f"parity_level: full\n"
        f"last_audit:\n"
        f"  date: 2026-08-05\n"
        f"  by: myia-po-2023:CoursIA-2\n"
        f"  python_sha: {py_sha}\n"
        f"  csharp_sha: {cs_sha}\n",
        encoding="utf-8",
    )


def _make_pair_yaml_with_content_sha(pairs_dir: Path, name: str, py_rel: str,
                                     cs_rel: str, py_sha: str, cs_sha: str,
                                     cpy: str, ccs: str) -> None:
    """Paire avec content_sha (volet c) en plus des blob SHA legacy."""
    entry = pairs_dir / f"{name}.yaml"
    entry.write_text(
        f"name: {name}\n"
        f"family: Search\n"
        f"python: {py_rel}\n"
        f"csharp: {cs_rel}\n"
        f"parity_level: full\n"
        f"last_audit:\n"
        f"  date: 2026-08-05\n"
        f"  by: myia-po-2023:CoursIA-2\n"
        f"  python_sha: {py_sha}\n"
        f"  csharp_sha: {cs_sha}\n"
        f"  content_python_sha: {cpy}\n"
        f"  content_csharp_sha: {ccs}\n",
        encoding="utf-8",
    )


# --- 1. cas MATCH (registre aligne) : exit 0 --------------------------------

def test_ci_strict_match_exit_zero(tmp_path):
    """Working tree aligne sur le registre -> CI gate vert, exit 0."""
    repo = _git_repo(tmp_path)
    py_rel = "py/nb.ipynb"
    cs_rel = "cs/nb.ipynb"

    _commit(repo, py_rel, _nb(source=["# Title\n"]), "base py")
    _commit(repo, cs_rel, _nb(source=["// Title\n"]), "base cs")
    py_blob = ctp._git_blob_sha(repo, py_rel)
    cs_blob = ctp._git_blob_sha(repo, cs_rel)

    pairs_dir = tmp_path / "twin_pairs.d"
    pairs_dir.mkdir()
    _make_pair_yaml(pairs_dir, "Search-A", py_rel, cs_rel, py_blob, cs_blob)

    rc = ctp.main([
        "--ci-strict", "--check", "--json",
        "--registry", str(pairs_dir),
        "--repo-root", str(repo),
    ])
    assert rc == 0, (
        f"working tree aligne sur registre devrait etre vert (exit 0), "
        f"rc={rc}"
    )


def test_ci_strict_match_breakdown_n_ok(tmp_path):
    """Breakdown : 1 paire legacy, content_sha absent -> categorie ok_legacy == 1."""
    repo = _git_repo(tmp_path)
    py_rel = "py/nb.ipynb"
    cs_rel = "cs/nb.ipynb"

    _commit(repo, py_rel, _nb(source=["# Title\n"]), "base py")
    _commit(repo, cs_rel, _nb(source=["// Title\n"]), "base cs")
    py_blob = ctp._git_blob_sha(repo, py_rel)
    cs_blob = ctp._git_blob_sha(repo, cs_rel)

    pairs_dir = tmp_path / "twin_pairs.d"
    pairs_dir.mkdir()
    _make_pair_yaml(pairs_dir, "Search-A", py_rel, cs_rel, py_blob, cs_blob)

    # Capture stdout JSON
    import io
    from contextlib import redirect_stdout
    buf = io.StringIO()
    with redirect_stdout(buf):
        rc = ctp.main([
            "--ci-strict", "--json",
            "--registry", str(pairs_dir),
            "--repo-root", str(repo),
        ])
    assert rc == 0
    out = json.loads(buf.getvalue())
    assert out["mode"] == "ci_strict"
    ci = out["ci_strict"]
    assert ci["n_ok_legacy"] == 1, (
        f"devrait avoir 1 ok_legacy (paire sans content_sha alignee), got {ci}"
    )
    assert ci["n_drift_blob"] == 0
    assert ci["n_drift_content"] == 0
    assert ci["n_no_audit"] == 0


def test_ci_strict_content_sha_match_exit_zero(tmp_path):
    """Paire avec content_sha enregistre et content_sha aligne -> vert (volet c)."""
    repo = _git_repo(tmp_path)
    py_rel = "py/nb.ipynb"
    cs_rel = "cs/nb.ipynb"

    _commit(repo, py_rel, _nb(source=["# Title\n"]), "base py")
    _commit(repo, cs_rel, _nb(source=["// Title\n"]), "base cs")
    py_blob = ctp._git_blob_sha(repo, py_rel)
    cs_blob = ctp._git_blob_sha(repo, cs_rel)
    py_content = ctp._content_sha(repo, py_rel)
    cs_content = ctp._content_sha(repo, cs_rel)

    pairs_dir = tmp_path / "twin_pairs.d"
    pairs_dir.mkdir()
    _make_pair_yaml_with_content_sha(
        pairs_dir, "Search-A", py_rel, cs_rel,
        py_blob, cs_blob, py_content, cs_content
    )

    rc = ctp.main([
        "--ci-strict", "--check", "--json",
        "--registry", str(pairs_dir),
        "--repo-root", str(repo),
    ])
    assert rc == 0, f"content_sha aligne devrait etre vert, rc={rc}"


# --- 2. cas MISMATCH (registre desaligne) : exit 1 ----------------------------

def test_ci_strict_legacy_blob_drift_exit_one(tmp_path):
    """Working tree modifie sans rebaseline -> exit 1, drift_blob > 0."""
    repo = _git_repo(tmp_path)
    py_rel = "py/nb.ipynb"
    cs_rel = "cs/nb.ipynb"

    _commit(repo, py_rel, _nb(source=["# Title\n"]), "base py")
    _commit(repo, cs_rel, _nb(source=["// Title\n"]), "base cs")
    # Capture SHAs AVANT la modification du working tree
    py_blob_v1 = ctp._git_blob_sha(repo, py_rel)
    cs_blob_v1 = ctp._git_blob_sha(repo, cs_rel)

    pairs_dir = tmp_path / "twin_pairs.d"
    pairs_dir.mkdir()
    _make_pair_yaml(pairs_dir, "Search-A", py_rel, cs_rel, py_blob_v1, cs_blob_v1)

    # Modifie le working tree (NON committe) -> l'index HEAD ne bouge pas,
    # mais on ecrit sur disque avec un contenu different -> _git_blob_sha
    # lit HEAD, donc on committe une nouvelle version et on re-lit.
    _commit(repo, py_rel, _nb(source=["# Title modifie\n"]), "edit py")
    py_blob_v2 = ctp._git_blob_sha(repo, py_rel)
    assert py_blob_v1 != py_blob_v2, "le SHA doit avoir bouge"

    # Le registre pointe encore sur v1, le HEAD est sur v2 -> drift
    rc = ctp.main([
        "--ci-strict", "--check", "--json",
        "--registry", str(pairs_dir),
        "--repo-root", str(repo),
    ])
    assert rc == 1, (
        f"registre desaligne (blob drift) devrait rougir (exit 1), rc={rc}"
    )


def test_ci_strict_legacy_blob_drift_breakdown(tmp_path):
    """Breakdown contient drift_blob > 0 quand blob SHA mismatch."""
    repo = _git_repo(tmp_path)
    py_rel = "py/nb.ipynb"
    cs_rel = "cs/nb.ipynb"

    _commit(repo, py_rel, _nb(source=["# Title\n"]), "base py")
    _commit(repo, cs_rel, _nb(source=["// Title\n"]), "base cs")
    py_blob_v1 = ctp._git_blob_sha(repo, py_rel)
    cs_blob_v1 = ctp._git_blob_sha(repo, cs_rel)

    pairs_dir = tmp_path / "twin_pairs.d"
    pairs_dir.mkdir()
    _make_pair_yaml(pairs_dir, "Search-A", py_rel, cs_rel, py_blob_v1, cs_blob_v1)

    _commit(repo, py_rel, _nb(source=["# Title modifie\n"]), "edit py")

    import io
    from contextlib import redirect_stdout
    buf = io.StringIO()
    with redirect_stdout(buf):
        rc = ctp.main([
            "--ci-strict", "--check", "--json",
            "--registry", str(pairs_dir),
            "--repo-root", str(repo),
        ])
    assert rc == 1
    out = json.loads(buf.getvalue())
    ci = out["ci_strict"]
    assert ci["n_drift_blob"] >= 1, (
        f"devrait avoir >=1 drift_blob (registre sur v1, HEAD sur v2), got {ci}"
    )
    assert ci["n_ok_legacy"] == 0


def test_ci_strict_content_sha_drift_breakdown(tmp_path):
    """Paire avec content_sha : content_sha mismatch -> drift_content > 0."""
    repo = _git_repo(tmp_path)
    py_rel = "py/nb.ipynb"
    cs_rel = "cs/nb.ipynb"

    _commit(repo, py_rel, _nb(source=["# Title\n"]), "base py")
    _commit(repo, cs_rel, _nb(source=["// Title\n"]), "base cs")
    py_blob_v1 = ctp._git_blob_sha(repo, py_rel)
    cs_blob_v1 = ctp._git_blob_sha(repo, cs_rel)
    py_content_v1 = ctp._content_sha(repo, py_rel)
    cs_content_v1 = ctp._content_sha(repo, cs_rel)

    pairs_dir = tmp_path / "twin_pairs.d"
    pairs_dir.mkdir()
    _make_pair_yaml_with_content_sha(
        pairs_dir, "Search-A", py_rel, cs_rel,
        py_blob_v1, cs_blob_v1, py_content_v1, cs_content_v1
    )

    # Modifie la PROSE (le content_sha doit bouger)
    _commit(repo, py_rel, _nb(source=["# Title modifie\n"]), "prose edit")

    import io
    from contextlib import redirect_stdout
    buf = io.StringIO()
    with redirect_stdout(buf):
        rc = ctp.main([
            "--ci-strict", "--check", "--json",
            "--registry", str(pairs_dir),
            "--repo-root", str(repo),
        ])
    assert rc == 1
    out = json.loads(buf.getvalue())
    ci = out["ci_strict"]
    assert ci["n_drift_content"] >= 1, (
        f"devrait avoir >=1 drift_content, got {ci}"
    )
    assert ci["n_ok_content"] == 0


# --- 3. distinction tool-error vs drift --------------------------------------

def test_ci_strict_no_git_repo_exits_nonzero(tmp_path):
    """Working tree PAS un depot git -> tool error, pas un drift finding.

    On documente la semantique d'exit ici : un tool error leve `SystemExit`
    (registre introuvable, pas un depot git) -- c'est DIFFERENT du drift
    finding qui retourne rc=1. Le workflow CI distingue les deux via
    l'absence de JSON parsable (cf .github/workflows/twin-parity-cron.yml).

    `pytest.raises(SystemExit)` valide la semantique : tool error ≠ drift.
    """
    with pytest.raises(SystemExit):
        ctp.main([
            "--ci-strict", "--check",
            "--registry", "/nonexistent/registre.yaml",
        ])