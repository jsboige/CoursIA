#!/usr/bin/env python3
"""Une paire DEPLACEE par la branche base n'est pas une derive de la PR (#22920).

Defaut corrige
--------------
Le mode `--per-pair` compare le registre au base-ref (`git show`) au registre du
working tree. Quand `main` DEPLACE une paire (renommage, renumerotation) APRES
le fork de la branche de PR, le registre de la tete declare encore l'ANCIEN
chemin, celui du base declare le NOUVEAU : les chemins divergent entre refs.
`_classify_per_pair` ne recoit que deux STATUTS : ce cas lui est indiscernable
d'une vraie derive, et le gate prescrivait le rebaseline `--update --pair` --
un remede FAUX ici : il attesterait l'empreinte d'un chemin que main a deja
abandonne, et l'attestation REGRESSERAIT le registre au merge. Le remede correct
est `gh pr update-branch` (reprendre le deplacement, rejouer le travail et
l'attestation sur les nouveaux chemins).

Discriminant implemente
-----------------------
Decide EN AMONT de `_classify_per_pair` (qui reste pure, sa table 9-combos
valide), pour chaque paire presente aux DEUX refs :

  1. chemins declares divergents (python ou csharp) -- test pur, sans appel git ;
  2. sonde croisee : chemin du base absent de l'arbre de la tete, OU chemin de
     la tete absent du base (l'existence seule, via `_git_blob_sha`) ;
  3. orientation par le point de fork (merge-base) : le chemin de la tete
     existait au fork ET le chemin du base n'y existait pas.

La condition 3 est le discriminateur que la spec des seules sondes croisees ne
peut pas fournir : les scenarios « paire deplacee par main, branche en retard »
et « paire renommee par la PR » sont des images miroir EXACTES sur les arbres
base/tete (meme jeu d'observations : chemin du base present au base / absent de
la tete, chemin de la tete present a la tete / absent du base). Une sonde
ORIENTEE (ref anterieure aux deux) est necessaire pour dire de quel cote vient
le deplacement. Sans merge-base resolvable : pas de verdict STALE_BRANCH
(degradation vers le comportement existant).

Ce que ces tests pincent
------------------------
  1. paire deplacee par la branche base (la tete a en plus edite un carnet ->
     head_status DRIFT, le cas reel observe) -> STALE_BRANCH, compteur
     `stale_branch`=1, `drift_introduced`=0, chemins base/tete dans le rapport,
     remede `gh pr update-branch` et AUCUNE commande de rebaseline ;
  2. controle negatif -- suppression REELLE par la PR (chemins egaux, carnet
     absent au HEAD) -> reste DRIFT_INTRODUCED + head_status MISSING (lot
     « missing » de #22825, inchange) ;
  3. controle negatif -- vraie derive (chemins egaux, base OK / tete DRIFT) ->
     reste DRIFT_INTRODUCED ET la commande `--update --pair` est rendue ;
  4. controle negatif -- rename INTRODUIT par la PR (chemin de la tete absent
     du base ET du fork) -> PAS STALE_BRANCH (verdict OK apres re-attestation) ;
  5. le SNIPPET REEL du workflow execute sur un rapport mixte rend le rebaseline
     pour la paire en derive de contenu et `gh pr update-branch` pour la paire
     perimee, jamais l'inverse ;
  6. garde de cout : sans paire a chemins divergents, `git merge-base` n'est
     jamais appele ;
  7. garde de forme : la ligne de remediation STALE ne contient ni `--update`
     ni `--pair` (un rebaseline y serait un remede faux).

Run:
    pytest scripts/notebook_tools/tests/test_check_twin_parity_stale_branch.py -q
"""
from __future__ import annotations

import json
import os
import re
import subprocess
import sys
from pathlib import Path

import pytest

NOTEBOOK_TOOLS = Path(__file__).resolve().parents[1]
REPO_ROOT = NOTEBOOK_TOOLS.parents[1]
WORKFLOW = REPO_ROOT / ".github" / "workflows" / "twin-parity.yml"

sys.path.insert(0, str(NOTEBOOK_TOOLS))

import check_twin_parity as ctp  # noqa: E402
from check_twin_parity import (  # noqa: E402
    _pair_paths_diverge,
    _stale_remediation_line,
    render_introduced_remediation,
    split_stale_pairs,
)


# --- helpers : mini-depot git a DEUX branches (fork point / base / tete) ------

def _git(repo: Path, *args: str) -> subprocess.CompletedProcess:
    return subprocess.run(
        ["git", "-c", "user.name=test", "-c", "user.email=test@example.com", *args],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
        cwd=str(repo), check=True,
    )


def _nb(text: str) -> str:
    """Carnet minimal (seul le blob SHA compte pour le gate)."""
    return json.dumps({
        "cells": [{"cell_type": "markdown", "source": [text], "metadata": {}}],
        "metadata": {}, "nbformat": 4, "nbformat_minor": 5,
    })


def _write(repo: Path, rel: str, content: str) -> None:
    p = repo / rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(content, encoding="utf-8")


def _pair_entry(name: str, py: str, cs: str, repo: Path, ref: str = "HEAD") -> str:
    """Entree de registre attestant les blobs COURANTS des chemins donnes."""
    return (
        f"name: {name}\n"
        f"family: Fixture\n"
        f"python: {py}\n"
        f"csharp: {cs}\n"
        f"parity_level: surface\n"
        f"last_audit:\n"
        f"  date: 2026-10-27\n"
        f"  by: test-fixture\n"
        f"  python_sha: {ctp._git_blob_sha(repo, py, ref)}\n"
        f"  csharp_sha: {ctp._git_blob_sha(repo, cs, ref)}\n"
    )


PAIR_NAME = "Fixture-P10"
ENTRY_REL = f"twin_pairs.d/{ctp._slug(PAIR_NAME)}.yaml"
PY_10, CS_10 = "nb/py-10.ipynb", "nb/cs-10.ipynb"
PY_11, CS_11 = "nb/py-11.ipynb", "nb/cs-11.ipynb"
PY_12, CS_12 = "nb/py-12.ipynb", "nb/cs-12.ipynb"


def _forked_repo(tmp_path: Path, base_action, pr_action) -> tuple[Path, Path, str]:
    """C0 (fork point) : paire au chemin 10, attestee. Puis base et PR divergent.

    `base_action(repo)` tourne sur la branche base (main), `pr_action(repo)` sur
    la branche PR ; chacune commite. Retourne (repo, registre, base_sha) avec le
    working tree SUR la branche PR (ce que le gate evalue comme tete).
    """
    repo = tmp_path / "mini_repo"
    repo.mkdir()
    _git(repo, "init", "-q", "-b", "main")
    # C0a : les carnets d'abord -- l'attestation de C0b lit leurs blobs a HEAD.
    _write(repo, PY_10, _nb("# py dix"))
    _write(repo, CS_10, _nb("// cs dix"))
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "C0a carnets")
    # C0b : paire declaree au chemin 10, attestee sur les blobs 10.
    _write(repo, ENTRY_REL, _pair_entry(PAIR_NAME, PY_10, CS_10, repo))
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "C0b registre")
    # Branche PR au fork point, puis la base avance.
    _git(repo, "branch", "pr")
    base_action(repo)
    base_sha = _git(repo, "rev-parse", "HEAD").stdout.strip()
    # Tete : la branche PR avance de son cote (working tree = tete du gate).
    _git(repo, "checkout", "-q", "pr")
    pr_action(repo)
    return repo, repo / "twin_pairs.d", base_sha


def _run_per_pair(repo: Path, reg: Path, base_sha: str, capsys) -> tuple[dict, int]:
    rc = ctp.main([
        "--check", "--per-pair", "--base", base_sha,
        "--registry", str(reg), "--repo-root", str(repo), "--json",
    ])
    return json.loads(capsys.readouterr().out), rc


# --- 1. cas fondateur : paire deplacee par la BRANCHE BASE --------------------

def _base_moves_pair_to_11(repo: Path) -> None:
    """La branche base deplace la paire 10 -> 11 et re-atteste (move + rebaseline).
    Le move est committé AVANT l'attestation : `_pair_entry` lit les blobs a HEAD."""
    _git(repo, "mv", PY_10, PY_11)
    _git(repo, "mv", CS_10, CS_11)
    _git(repo, "commit", "-q", "-m", "main: deplace la paire 10 -> 11")
    _write(repo, ENTRY_REL, _pair_entry(PAIR_NAME, PY_11, CS_11, repo))
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "main: re-atteste sur les chemins 11")


def _pr_edits_old_notebook(repo: Path) -> None:
    """La PR travaille sur l'ANCIEN chemin (elle n'a pas le deplacement)."""
    _write(repo, PY_10, _nb("# py dix, edite par la PR"))
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "pr: edite py-10")


def test_pair_moved_on_base_is_stale_branch(tmp_path, capsys):
    """Le cas #22920 : head DRIFT (la PR a edite l'ancien chemin) mais la cause
    est le deplacement par la branche base -- pas une derive introduite par la PR."""
    repo, reg, base_sha = _forked_repo(tmp_path, _base_moves_pair_to_11,
                                       _pr_edits_old_notebook)
    data, rc = _run_per_pair(repo, reg, base_sha, capsys)

    assert rc == 1, "une paire STALE_BRANCH doit faire rougir le gate (action lane requise)"
    pair = data["pairs"][0]
    assert pair["verdict"] == "STALE_BRANCH", pair
    assert pair["head_status"] == "DRIFT"  # la PR a bien edite py-10...
    assert pair["base_status"] == "OK"
    assert data["stale_branch"] == 1
    assert data["drift_introduced"] == 0, (
        "une paire perimee ne doit JAMAIS compter dans drift_introduced (#22920)"
    )
    # Les chemins des deux refs sont dans le rapport : le remede est actionnable.
    assert pair["paths_head"] == {"python": PY_10, "csharp": CS_10}
    assert pair["paths_base"] == {"python": PY_11, "csharp": CS_11}


def test_stale_pair_gets_update_branch_never_a_rebaseline(tmp_path, capsys):
    """Remede : `gh pr update-branch` + rejouer sur les nouveaux chemins ; aucune
    commande de rebaseline ne doit etre generee pour une paire perimee."""
    repo, reg, base_sha = _forked_repo(tmp_path, _base_moves_pair_to_11,
                                       _pr_edits_old_notebook)
    data, _rc = _run_per_pair(repo, reg, base_sha, capsys)

    lines = render_introduced_remediation(data["pairs"])
    text = "\n".join(lines)
    assert "gh pr update-branch" in text
    assert "PERIMEE" in text
    # Les nouveaux chemins (ceux du base) sont nommes : la lane sait ou rejouer.
    assert PY_11 in text and CS_11 in text
    # Et surtout : AUCUNE commande de rebaseline pour cette paire.
    assert "--update" not in text
    assert "--pair" not in text
    # Le lot est bien separate de la commande generique (placeholder historique).
    assert "<nom exact de l entree>" not in text


def test_stale_branch_tag_in_text_output(tmp_path, capsys):
    """La sortie human-readable porte le verdict et le compteur dedie."""
    repo, reg, base_sha = _forked_repo(tmp_path, _base_moves_pair_to_11,
                                       _pr_edits_old_notebook)
    rc = ctp.main([
        "--check", "--per-pair", "--base", base_sha,
        "--registry", str(reg), "--repo-root", str(repo),
    ])
    out = capsys.readouterr().out
    assert rc == 1
    assert "[STALE-BRANCH] Fixture-P10" in out
    assert "STALE=1" in out


def test_stale_pair_with_clean_head_is_still_stale(tmp_path, capsys):
    """Variante OK/OK : meme sans edition de la PR, un registre de tete qui
    declare un chemin que le base a abandonne reste une branche perimee -- le
    gate actuel rendait OK/OK sans jamais signaler le deplacement."""
    repo, reg, base_sha = _forked_repo(
        tmp_path, _base_moves_pair_to_11, lambda repo: None)
    data, rc = _run_per_pair(repo, reg, base_sha, capsys)
    assert data["pairs"][0]["verdict"] == "STALE_BRANCH"
    assert data["stale_branch"] == 1
    assert rc == 1


# --- 2. controle negatif : suppression REELLE par la PR -----------------------

def test_real_deletion_stays_drift_introduced_missing(tmp_path, capsys):
    """Chemins egaux, carnet present au base et absent a la tete : le
    discriminant de divergence ne se declenche pas -- lot missing de #22825."""
    def pr_deletes(repo: Path) -> None:
        _git(repo, "rm", "-q", CS_10)
        _git(repo, "commit", "-q", "-m", "pr: supprime cs-10")

    repo, reg, base_sha = _forked_repo(tmp_path, lambda r: None, pr_deletes)
    data, rc = _run_per_pair(repo, reg, base_sha, capsys)

    pair = data["pairs"][0]
    assert pair["verdict"] == "DRIFT_INTRODUCED", pair
    assert pair["head_status"] == "MISSING"
    assert data["stale_branch"] == 0
    assert data["drift_introduced"] == 1
    assert rc == 1
    # Remede du lot missing (#22825), pas un remede de branche perimee.
    text = "\n".join(render_introduced_remediation(data["pairs"]))
    assert "[MISSING]" in text
    assert "gh pr update-branch" not in text


# --- 3. controle negatif : VRAIE derive de contenu ----------------------------

def test_real_content_drift_keeps_the_rebaseline_command(tmp_path, capsys):
    """Chemins egaux, base OK / tete DRIFT : derive introduite par la PR -- la
    commande `--update --pair` DOIT rester (comportement historique inchange)."""
    repo, reg, base_sha = _forked_repo(tmp_path, lambda r: None,
                                       _pr_edits_old_notebook)
    data, rc = _run_per_pair(repo, reg, base_sha, capsys)

    pair = data["pairs"][0]
    assert pair["verdict"] == "DRIFT_INTRODUCED", pair
    assert pair["head_status"] == "DRIFT"
    assert data["stale_branch"] == 0
    assert data["drift_introduced"] == 1
    assert rc == 1
    text = "\n".join(render_introduced_remediation(data["pairs"]))
    assert '--update --pair "Fixture-P10"' in text
    assert "gh pr update-branch" not in text


# --- 4. controle negatif : rename INTRODUIT par la PR -------------------------

def test_pr_introduced_rename_is_not_stale_branch(tmp_path, capsys):
    """La PR renomme 10 -> 12 et re-atteste : le nouveau chemin n'existe NI au
    base NI au point de fork -> le deplacement vient de la PR, pas de la base.
    Verdict OK (comportement per-pair existant), jamais STALE_BRANCH."""
    def pr_renames(repo: Path) -> None:
        _git(repo, "mv", PY_10, PY_12)
        _git(repo, "mv", CS_10, CS_12)
        _git(repo, "commit", "-q", "-m", "pr: renomme la paire 10 -> 12")
        _write(repo, ENTRY_REL, _pair_entry(PAIR_NAME, PY_12, CS_12, repo))
        _git(repo, "add", "-A")
        _git(repo, "commit", "-q", "-m", "pr: re-atteste sur les chemins 12")

    repo, reg, base_sha = _forked_repo(tmp_path, lambda r: None, pr_renames)
    data, rc = _run_per_pair(repo, reg, base_sha, capsys)

    pair = data["pairs"][0]
    assert pair["verdict"] != "STALE_BRANCH", pair
    assert pair["verdict"] == "OK"
    assert data["stale_branch"] == 0
    assert rc == 0, "un rename propre par la PR doit rester VERT"


# --- 5. le snippet REEL du workflow rend les deux remedes, chacun au bon lot --

def _stale_report_pair() -> dict:
    """Entree de rapport telle que produite par le mode --per-pair (STALE)."""
    return {
        "name": PAIR_NAME, "family": "Fixture", "parity_level": "surface",
        "base_ref": "deadbeef", "base_status": "OK", "head_status": "DRIFT",
        "verdict": "STALE_BRANCH", "base_details": [], "head_details": [],
        "paths_base": {"python": PY_11, "csharp": CS_11},
        "paths_head": {"python": PY_10, "csharp": CS_10},
    }


def _drift_report_pair() -> dict:
    return {
        "name": "Fixture-P20", "family": "Fixture", "parity_level": "surface",
        "base_ref": "deadbeef", "base_status": "OK", "head_status": "DRIFT",
        "verdict": "DRIFT_INTRODUCED", "base_details": [],
        "head_details": ["Python a drift : aaaaaaaa -> bbbbbbbb"],
    }


def _workflow_remediation_payload() -> str:
    """Extrait le code python de la ligne `CMDS=$(python -c "...")` du workflow
    (cf test_check_twin_parity_missing.py : le garde echoue si la ligne change
    de forme)."""
    text = WORKFLOW.read_text(encoding="utf-8")
    matches = re.findall(r'CMDS=\$\(python -c "([^"]*)"\)', text)
    assert matches, (
        "La ligne CMDS=$(python -c \"...\") est introuvable dans twin-parity.yml : "
        "le gate a change de forme, mettre ce test a jour AVANT de merger."
    )
    assert len(matches) == 1, f"Plusieurs lignes CMDS= trouvees ({len(matches)})."
    return matches[0]


def test_workflow_snippet_routes_each_pair_to_its_own_remedy(tmp_path):
    """Execute le python REEL du workflow sur un rapport derive + perimee : la
    paire en derive de contenu garde sa commande de rebaseline, la paire
    perimee recoit `gh pr update-branch` -- et jamais l'inverse."""
    payload = _workflow_remediation_payload()
    assert "render_introduced_remediation" in payload

    report = {
        "mode": "per_pair", "base_ref": "deadbeef", "total": 2,
        "ok": 0, "drift_introduced": 1, "drift_resolved": 0,
        "drift_pre_existing": 0, "stale_branch": 1,
        "pairs": [_drift_report_pair(), _stale_report_pair()],
    }
    (tmp_path / "twin_parity_report.json").write_text(
        json.dumps(report), encoding="utf-8")
    env = dict(os.environ)
    env["PYTHONPATH"] = os.pathsep.join(
        [str(NOTEBOOK_TOOLS), env.get("PYTHONPATH", "")]).strip(os.pathsep)
    proc = subprocess.run(
        [sys.executable, "-c", payload],
        cwd=tmp_path, env=env, capture_output=True, text=True,
        encoding="utf-8",
    )
    assert proc.returncode == 0, f"snippet du workflow en echec : {proc.stderr}"
    out = proc.stdout
    # La paire en derive de contenu garde la commande de rebaseline.
    assert '--update --pair "Fixture-P20"' in out
    # La paire perimee recoit le remede update-branch...
    assert "gh pr update-branch" in out
    assert "Fixture-P10" in out
    # ...et AUCUNE commande de rebaseline ne la vise.
    assert '--update --pair "Fixture-P10"' not in out


def test_workflow_reads_the_stale_branch_counter():
    """Garde statique : le bloc rouge du workflow lit `stale_branch` du rapport
    (sinon un rouge STALE seul afficherait « 0 paire(s) » et perdrait le remede)."""
    text = WORKFLOW.read_text(encoding="utf-8")
    assert "d.get('stale_branch',0)" in text


# --- 6. garde de cout : merge-base seulement si divergence --------------------

def test_merge_base_never_called_without_path_divergence(
        tmp_path, capsys, monkeypatch):
    """Un registre sans paire a chemins divergents ne paie NI merge-base NI
    sondes croisees : la garde `_pair_paths_diverge` est un test pur."""
    repo, reg, base_sha = _forked_repo(tmp_path, lambda r: None,
                                       _pr_edits_old_notebook)

    calls: list[list[str]] = []
    original = ctp._run_git

    def spy(args, **kwargs):
        calls.append(list(args))
        return original(args, **kwargs)

    monkeypatch.setattr(ctp, "_run_git", spy)
    _rc = ctp.main([
        "--check", "--per-pair", "--base", base_sha,
        "--registry", str(reg), "--repo-root", str(repo), "--json",
    ])
    capsys.readouterr()
    merge_base_calls = [c for c in calls if "merge-base" in c]
    assert merge_base_calls == [], (
        "git merge-base ne doit etre appele qu'en presence de chemins "
        f"divergents : {merge_base_calls}"
    )


# --- 7. garde de forme : la ligne STALE ne propose jamais un rebaseline -------

def test_stale_remediation_line_carries_no_rebaseline_tokens():
    """`--update` / `--pair` dans la ligne STALE seraient un remede FAUX : la
    ligne doit les eviter en toute circonstance (cf #22920)."""
    line = _stale_remediation_line(_stale_report_pair())
    assert "gh pr update-branch" in line
    assert "--update" not in line
    assert "--pair" not in line


def test_split_stale_pairs_selects_only_stale():
    """Le selecteur ne voit que le verdict STALE_BRANCH (jamais les autres)."""
    stale = _stale_report_pair()
    got = split_stale_pairs([_drift_report_pair(), stale])
    assert [p["name"] for p in got] == [PAIR_NAME]
    assert split_stale_pairs([]) == []


def test_pair_paths_diverge_is_pure_and_per_side():
    """Le test pur de divergence : cote par cote, insensible aux valeurs absentes."""
    assert _pair_paths_diverge({"python": "a", "csharp": "b"},
                               {"python": "a2", "csharp": "b"})
    assert _pair_paths_diverge({"python": "a", "csharp": "b"},
                               {"python": "a", "csharp": "b2"})
    assert not _pair_paths_diverge({"python": "a", "csharp": "b"},
                                   {"python": "a", "csharp": "b"})
    assert not _pair_paths_diverge({"python": "a", "csharp": None},
                                   {"python": "a", "csharp": None})
