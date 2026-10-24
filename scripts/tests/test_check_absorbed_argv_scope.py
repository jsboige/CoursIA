"""Tests de l'organe de bornage des gardes absorbés (check_absorbed_argv_scope).

Classe mesurée (#20303) : un garde absorbé dont l'argv a perdu l'argument qui
bornait l'analyse au diff rouge des PR sans rapport -- un finding né de la PR
d'AUTRUI suffit.

Les pieces pures (jetons, marqueurs, extraction des commandes) sont testees
ici. Les deux controles d'acceptance sont dans le rapport de PR :
  - POSITIF : un registre simule, dont un garde a perdu sa portee, rend
    SCOPE_LOST avec le nom du garde ;
  - NEGATIF : le registre reel rend SCOPE_OK (0 finding sur 29 gardes).
Le controle NEGATIF est rejoue ici quand la base est lisible, pour que la
derive soit vue par la CI et pas seulement par le rapport.
"""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

import pytest

CI_DIR = Path(__file__).resolve().parents[1] / "ci"
if str(CI_DIR) not in sys.path:
    sys.path.insert(0, str(CI_DIR))

import check_absorbed_argv_scope as cas  # noqa: E402
from fast_lane_registry import Guard  # noqa: E402


# --- jetons de bornage d'un argv -------------------------------------------

def test_jeton_explicite_est_un_bornage():
    assert cas.scope_tokens(
        ["python", "check.py", "--check", "--diff-base", "{base_ref}"]
    ) == ["--diff-base"]


def test_placeholder_paths_seul_est_un_bornage():
    """Le garde execute par fichier est borne aux fichiers de la PR."""
    assert cas.scope_tokens(["python", "check.py", "{changed_paths}"]) == [
        "{changed_paths}"
    ]


def test_placeholder_base_en_position_est_un_bornage():
    """Les cliquets « base vs PR » prennent la base en position : delta."""
    assert cas.scope_tokens(["python", "check.py", "{base_ref}"]) == ["{base_ref}"]


def test_placeholder_apres_un_jeton_nest_qu_un_bornage():
    """Apres `--base`, le placeholder n'en est que la VALEUR."""
    assert cas.scope_tokens(["python", "check.py", "--base", "{base_ref}"]) == [
        "--base"
    ]


def test_baseline_nest_pas_un_bornage():
    """Un fichier de baseline connu ne borne rien : c'est du bruit connu."""
    assert cas.scope_tokens(
        ["python", "check.py", "--check", "--baseline", "b.json"]
    ) == []


def test_argv_sans_bornage():
    assert cas.scope_tokens(["python", "check.py", "--check"]) == []


# --- marqueurs de bornage d'un workflow d'origine --------------------------

def test_marqueurs_du_workflow_dorigine():
    markers = cas.source_scope_markers([
        "git diff --name-only \"$BASE\"...HEAD > pr_files.txt",
        "python scripts/x.py --check --diff-files pr_files.txt",
    ])
    assert "--diff-files" in markers
    assert "pr_files.txt" in markers
    assert "git diff --name-only" in markers


def test_baseline_nest_pas_un_marqueur():
    """`--baseline` ne contient pas `--base ` (l'espace le distingue)."""
    assert cas.source_scope_markers(
        ["python scripts/x.py --check --baseline b.json"]
    ) == []


def test_run_commands_ignore_le_commentaire_yaml():
    """Un marqueur cite dans un commentaire YAML ne borne pas le workflow."""
    data = {
        "jobs": {
            "g": {
                "steps": [
                    {"run": "python scripts/x.py --check"},
                ],
            },
        },
    }
    assert cas.run_commands(data) == ["python scripts/x.py --check"]
    assert cas.source_scope_markers(cas.run_commands(data)) == []


def test_run_commands_ignore_les_commentaires_de_job():
    """Un commentaire YAML (hors bloc `run:`) ne borne pas le workflow."""
    data = {"jobs": {"g": {"steps": [{"run": "python scripts/x.py --check"}]}}}
    assert cas.source_scope_markers(cas.run_commands(data)) == []


# --- les deux invariants, sur un registre simule ---------------------------

def _garde(nom="g", argv=None, **kwargs):
    return Guard(
        name=nom,
        argv=argv or ["python", "check.py", "--check"],
        source="g.yml",
        paths=["a.py"],
        absorbed=True,
        **kwargs,
    )


def _source_borne():
    """Workflow d'origine qui borne l'analyse au diff (forme #20303)."""
    return {
        "jobs": {
            "g": {
                "steps": [
                    {"run": "git diff --name-only origin/main...HEAD > pr_files.txt"},
                    {"run": "python scripts/x.py --check --diff-files pr_files.txt"},
                ],
            },
        },
    }


def _simuler(monkeypatch, gardes, source=None, illisible=False):
    monkeypatch.setattr(cas, "all_guards", lambda: iter(gardes))
    monkeypatch.setattr(cas, "_load_yaml", lambda: object())
    if illisible:
        monkeypatch.setattr(cas, "_git_show", lambda base, rel: None)
    else:
        monkeypatch.setattr(cas, "_git_show", lambda base, rel: "text")
        monkeypatch.setattr(
            cas, "_parse_workflow", lambda text, yaml: source or {}
        )


def test_controle_positif_perte_de_portee(monkeypatch):
    """POSITIF : la source borne, l'argv non -> la portee est perdue."""
    _simuler(monkeypatch, [_garde()], source=_source_borne())
    problems, _skipped, stats, _evidence = cas.findings("origin/main")
    assert problems, "la perte de portee doit etre un finding"
    assert "portee a ete perdue" in problems[0]
    assert stats["checked"] == 1


def test_controle_negatif_portee_restauree(monkeypatch):
    """NEGATIF : la portee rendue (`--diff-base`) -> aucun finding."""
    _simuler(
        monkeypatch,
        [_garde(argv=["python", "check.py", "--check", "--diff-base", "{base_ref}"])],
        source=_source_borne(),
    )
    problems, _skipped, _stats, _evidence = cas.findings("origin/main")
    assert problems == []


def test_controle_positif_declaration_non_corroboree(monkeypatch):
    """POSITIF : `diff_bounded=True` sans jeton de bornage -> finding."""
    _simuler(monkeypatch, [_garde(diff_bounded=True)], source={})
    problems, _skipped, _stats, _evidence = cas.findings("origin/main")
    assert problems, "une declaration non corroboree doit etre un finding"
    assert "diff_bounded" in problems[0]


def test_garde_delta_est_borne_meme_sans_jeton(monkeypatch):
    """Un garde DELTA a trois temps annule par construction l'heritage."""
    _simuler(
        monkeypatch,
        [_garde(delta_argv=["python", "delta.py", "{base_json}", "{head_json}"])],
        source=_source_borne(),
    )
    problems, _skipped, _stats, _evidence = cas.findings("origin/main")
    assert problems == []


def test_source_illisible_est_un_finding(monkeypatch):
    """Fail-closed : un bornage non prouve est un finding, pas un ecart."""
    _simuler(monkeypatch, [_garde()], illisible=True)
    problems, _skipped, stats, _evidence = cas.findings("origin/main")
    assert problems and "illisible" in problems[0]
    assert stats["checked"] == 0


def test_source_non_borne_ne_produit_aucun_finding(monkeypatch):
    """Un garde global des deux cotes n'a rien perdu : pas de finding."""
    _simuler(monkeypatch, [_garde()], source={})
    problems, _skipped, _stats, _evidence = cas.findings("origin/main")
    assert problems == []


# --- controle sur le corpus reel -------------------------------------------

def _base_lisible():
    try:
        result = subprocess.run(
            ["git", "show", "origin/main:.github/workflows/notebook-nav-chain-guard.yml"],
            cwd=cas.ROOT, capture_output=True, text=True,
            encoding="utf-8", errors="replace", timeout=60,
        )
    except (OSError, subprocess.SubprocessError):
        return False
    return result.returncode == 0


@pytest.mark.skipif(not _base_lisible(), reason="origin/main illisible")
def test_corpus_reel_sans_portede_perdue():
    """NEGATIF : le registre reel ne perd aucune portee (mesure du jour).

    C'est le controle continu : un garde absorbé qui perd sa portee fait
    rougir ce test, sur chaque PR ou le registre change.
    """
    problems, _skipped, stats, _evidence = cas.findings("origin/main")
    assert problems == [], problems
    # Plancher de non-vacuite : le corpus mesure doit etre un corpus, pas
    # zero garde. 10 (et non 29) : une consolidation future du registre peut
    # faire baisser le compte sans que ce test doive rougir.
    assert stats["checked"] >= 10, stats


@pytest.mark.skipif(not _base_lisible(), reason="origin/main illisible")
def test_les_deux_cas_connus_ont_retrouve_leur_portee():
    """Les deux reparations mesurees (#20582, #21023) sont en place.

    C'est le temoin du correctif : si une porte disparait, ce test rougit
    AVANT que l'organe ne trouve un garde reellement borne.
    """
    evidence = {row["name"]: row for row in cas.findings("origin/main")[3]}
    presents = [nom for nom in ("check-nav-chain", "check-navlinks")
                if nom in evidence]
    assert presents, "aucun des deux cas connus n'est dans le corpus mesure"
    for nom in presents:
        assert evidence[nom]["argv_scope_tokens"], f"{nom} a perdu son jeton"
        assert evidence[nom]["diff_bounded"], f"{nom} a perdu sa declaration"
