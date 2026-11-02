"""Twin-parity : le verdict doit dire QUEL jumeau a bouge (#23020).

Le statut d'une paire est un **agregat** des deux jumeaux : `check_pair` rend
`OK` / `DRIFT` / `MISSING` / `NUMBERING-DRIFT` pour la paire entiere, sans
dire quel cote est en cause. `_classify_per_pair` decidait sur ces deux
statuts seule -> `DRIFT_PRE_EXISTING` ne fail pas le gate.

Scenario reproduit (issue #23020) :

| etat | python | csharp | `check_pair` |
|---|---|---|---|
| base | blob courant `A' != A` -> DRIFT | blob courant `B` -> OK | DRIFT |
| HEAD (la PR modifie le jumeau C#) | `A' != A` -> DRIFT | `B' != B` -> DRIFT | DRIFT |

`DRIFT` -> `DRIFT` = `DRIFT_PRE_EXISTING` -> gate VERT, alors que la PR a
INTRODUIT le drift du cote C#. L'ensemble des jumeaux en drift au HEAD
(`{python, csharp}`) n'est pas inclus dans celui du base (`{python}`).

Le correctif compare **par jumeau** : `check_pair` expose `drift_sides`, et
`_classify_per_pair` ne rend `DRIFT_PRE_EXISTING` que si
`drift(HEAD) subset drift(BASE)` ; sinon `DRIFT_INTRODUCED`.

Aucun appel reseau : mini-depot git jetable (`tmp_path`), commits locaux.
"""
from __future__ import annotations

import importlib.util
import json
import subprocess
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
CHECK_PATH = REPO_ROOT / "scripts" / "notebook_tools" / "check_twin_parity.py"

spec = importlib.util.spec_from_file_location("check_twin_parity", CHECK_PATH)
mod = importlib.util.module_from_spec(spec)
sys.modules["check_twin_parity"] = mod
spec.loader.exec_module(mod)

PY_REL = "Notebooks/Serie-01/Twin-01-Python.ipynb"
CS_REL = "Notebooks/Serie-01/Twin-01-CSharp.ipynb"


# ---------------------------------------------------------------------------
# Seam pur : _classify_per_pair
# ---------------------------------------------------------------------------


def test_23020_scenario_de_l_issue_drift_csharp_introduit():
    # DRIFT -> DRIFT, mais le HEAD a un jumeau de PLUS en drift : la PR a
    # introduit le drift C#. Avant le correctif : DRIFT_PRE_EXISTING (gate
    # VERT). Attendu : DRIFT_INTRODUCED (gate ROUGE).
    verdict = mod._classify_per_pair("DRIFT", "DRIFT", {"python"}, {"python", "csharp"})
    assert verdict == "DRIFT_INTRODUCED"


def test_23020_non_regression_meme_ensemble_de_drift():
    # Drift identique des deux cotes -> reste PRE_EXISTING, le gate ne fail
    # pas (critere 4 de l'issue).
    verdict = mod._classify_per_pair("DRIFT", "DRIFT", {"python"}, {"python"})
    assert verdict == "DRIFT_PRE_EXISTING"


def test_23020_ensemble_drift_identique_vide():
    verdict = mod._classify_per_pair("DRIFT", "DRIFT", set(), set())
    assert verdict == "DRIFT_PRE_EXISTING"


def test_23020_sans_detail_par_cote_semantique_historique():
    # Sans les ensembles (appelant qui n'a pas le detail), la semantique
    # historique est conservee : DRIFT -> DRIFT = PRE_EXISTING.
    assert mod._classify_per_pair("DRIFT", "DRIFT") == "DRIFT_PRE_EXISTING"


def test_23020_paire_ajoutee_reste_introduite():
    # Paire absente du registre au base (base_status="MISSING") : pas d'etat
    # pre-existant, l'etat HEAD est ce que la PR introduit.
    assert mod._classify_per_pair("MISSING", "DRIFT", set(), {"csharp"}) == "DRIFT_INTRODUCED"
    assert mod._classify_per_pair("MISSING", "OK", set(), set()) == "OK"


def test_23020_base_ok_head_drift_reste_introduite():
    assert mod._classify_per_pair("OK", "DRIFT", set(), {"csharp"}) == "DRIFT_INTRODUCED"


def test_23020_drift_resolu_nest_pas_reclassifie():
    # Le jumeau remis en etat -> DRIFT_RESOLVED, jamais INTRODUCED (le drift
    # du HEAD est vide, donc sous-ensemble de celui du base).
    assert mod._classify_per_pair("DRIFT", "OK", {"python"}, set()) == "DRIFT_RESOLVED"


# ---------------------------------------------------------------------------
# Recette end-to-end : mini-depot git
# ---------------------------------------------------------------------------


def _git(repo: Path, *args: str) -> str:
    out = subprocess.run(
        ["git", *args], cwd=repo, capture_output=True, text=True,
        encoding="utf-8", errors="replace", check=True,
    )
    return out.stdout.strip()


def _blob_sha(repo: Path, rel: str) -> str:
    return _git(repo, "hash-object", rel)


def _write_pair_file(repo: Path, py_sha: str, cs_sha: str) -> Path:
    reg_dir = repo / "scripts" / "notebook_tools" / "twin_pairs.d"
    reg_dir.mkdir(parents=True, exist_ok=True)
    path = reg_dir / "twin-01.yaml"
    path.write_text(
        "name: Twin-01\n"
        "family: Serie/Test\n"
        "parity_level: full\n"
        f"python: {PY_REL}\n"
        f"csharp: {CS_REL}\n"
        "last_audit:\n"
        "  date: '2026-11-01'\n"
        "  by: lane-de-test\n"
        f"  python_sha: {py_sha}\n"
        f"  csharp_sha: {cs_sha}\n",
        encoding="utf-8",
    )
    return path


@pytest.fixture
def mini_repo(tmp_path: Path):
    """Mini-depot : une paire, un etat de base (python deja en drift) et un HEAD.

    - commit 1 : les deux carnets en v1 + l'attestation (sha de v1) ;
    - commit 2 (BASE) : le carnet PYTHON passe en v2 -> python drift, csharp OK ;
    - commit 3 (HEAD) : selon `touch_csharp`, le carnet C# passe en v2 aussi.
    """
    pytest.importorskip("yaml")
    repo = tmp_path / "repo"
    (repo / "Notebooks" / "Serie-01").mkdir(parents=True)
    py = repo / PY_REL
    cs = repo / CS_REL
    py.write_text('{"cells": [], "version": "v1"}\n', encoding="utf-8")
    cs.write_text('{"cells": [], "version": "v1"}\n', encoding="utf-8")
    py_sha = _blob_sha(repo, PY_REL)
    cs_sha = _blob_sha(repo, CS_REL)
    _write_pair_file(repo, py_sha, cs_sha)

    _git(repo, "init", "-q")
    _git(repo, "config", "user.email", "test@example.com")
    _git(repo, "config", "user.name", "Test")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "init")

    # BASE : le jumeau PYTHON bouge -> drift pre-existant sur python.
    py.write_text('{"cells": [], "version": "v2-python"}\n', encoding="utf-8")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "base: python drift")
    base_sha = _git(repo, "rev-parse", "HEAD")

    # HEAD : la PR touche le jumeau C#.
    cs.write_text('{"cells": [], "version": "v2-csharp"}\n', encoding="utf-8")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "head: la PR touche le csharp")

    return {"repo": repo, "base": base_sha}


def _run(repo: Path, base: str) -> tuple[int, dict]:
    proc = subprocess.run(
        [sys.executable, str(CHECK_PATH),
         "--registry", str(repo / "scripts" / "notebook_tools" / "twin_pairs.d"),
         "--repo-root", str(repo),
         "--per-pair", "--base", base, "--check", "--json"],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
    )
    return proc.returncode, json.loads(proc.stdout)


def test_23020_gate_rouge_et_nomme_le_jumeau(mini_repo):
    repo = mini_repo["repo"]
    rc, out = _run(repo, mini_repo["base"])
    assert rc == 1, out
    assert out["drift_introduced"] >= 1
    pair = out["pairs"][0]
    assert pair["verdict"] == "DRIFT_INTRODUCED"
    # Le message nomme LE jumeau en cause (critere 5).
    assert pair["introduced_twins"] == ["csharp"]
    assert pair["base_drift_sides"] == ["python"]
    assert pair["head_drift_sides"] == ["csharp", "python"]


def test_23020_non_regression_le_gate_ne_roughit_pas_sans_nouveau_drift(mini_repo):
    # Meme etat, mais la PR ne touche QUE le jumeau deja en drift (python) :
    # l'ensemble du HEAD est celui du base -> PRE_EXISTING, gate VERT.
    repo = mini_repo["repo"]
    cs = repo / CS_REL
    cs.write_text('{"cells": [], "version": "v1"}\n', encoding="utf-8")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "head: la PR ne touche que python")

    rc, out = _run(repo, mini_repo["base"])
    assert rc == 0, out
    assert out["drift_pre_existing"] == 1
    assert out["pairs"][0]["verdict"] == "DRIFT_PRE_EXISTING"
    assert out["pairs"][0]["introduced_twins"] == []
