"""Temoin permanent de la porte par fichier de #17417 T2-b (#23114).

La reserve de la review etait precise : les « 4 cas PASS » cites dans le body
de la PR avaient ete executes hors depot, donc l'organe n'avait aucun test
committe pour le garder. Ces tests fixent le CONTRAT de ``report_gating`` :

  {"#N": [chemins retenus tries]}   mesure faite, des fichiers sont tenus
  {}                                mesure faite, aucun fichier tenu
  None                              mesure impossible -> --apply refuse

``None`` couvre trois causes distinctes, chacune testee : gh absent, gh en
echec, et -- ajout de #23114 -- la **liste tronquee**. Cette derniere est la
plus dangereuse : une PR hors fenetre est indiscernable d'une PR inexistante,
donc un fichier qu'elle tient serait declare libre sans que rien ne le dise.

Le test porte sur la SEMANTIQUE, pas sur l'interface CLI : ``subprocess`` est
remplace dans le module, aucun appel reseau n'est fait.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path
from types import SimpleNamespace

import pytest

# Permettre l'import du module parent (scripts/notebook_tools/) sans setup
# site-packages -- le projet n'est pas installe en editable.
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import migrate_dsa_mlpython as migration  # noqa: E402

PLAN_A = "MyIA.AI.Notebooks/ML/DataScienceWithAgents/01/a.ipynb"
PLAN_B = "MyIA.AI.Notebooks/ML/DataScienceWithAgents/01/b.py"
HORS_PLAN = "MyIA.AI.Notebooks/ML/DataScienceWithAgents/autre/hors.ipynb"
CONCERNED = {PLAN_A, PLAN_B}


def _gh(prs, returncode=0, stderr=""):
    """Remplace ``subprocess`` dans le module : rend la sortie gh demandee."""

    def run(argv, **kwargs):  # signature volontairement large (capture_output, cwd...)
        assert argv[0] == "gh", f"seul gh est attendu, recu {argv[0]!r}"
        return SimpleNamespace(returncode=returncode, stdout=json.dumps(prs), stderr=stderr)

    return SimpleNamespace(run=run)


def _gh_absent():
    def run(argv, **kwargs):
        raise FileNotFoundError("gh")

    return SimpleNamespace(run=run)


def test_retient_l_intersection_par_pr_triee(monkeypatch):
    prs = [
        {"number": 101, "files": [{"path": PLAN_B}, {"path": PLAN_A}, {"path": HORS_PLAN}]},
        {"number": 102, "files": [{"path": PLAN_B}, {"path": PLAN_B}]},
    ]
    monkeypatch.setattr(migration, "subprocess", _gh(prs))

    gating = migration.report_gating(CONCERNED)

    assert gating == {"#101": [PLAN_A, PLAN_B], "#102": [PLAN_B]}
    # tri lexical et dedoublonnage : la PR 102 liste deux fois le meme fichier
    assert gating is not None
    assert gating["#101"] == sorted([PLAN_A, PLAN_B])
    assert len(gating["#102"]) == 1


def test_pr_hors_plan_ne_retient_rien(monkeypatch):
    """Temoin negatif : toucher le hub ne suffit pas, seule l'intersection compte."""
    prs = [{"number": 200, "files": [{"path": HORS_PLAN}]}]
    monkeypatch.setattr(migration, "subprocess", _gh(prs))

    assert migration.report_gating(CONCERNED) == {}


def test_aucune_pr_ouverte_rend_un_dict_vide(monkeypatch):
    monkeypatch.setattr(migration, "subprocess", _gh([]))

    assert migration.report_gating(CONCERNED) == {}


def test_gh_en_echec_rend_none(monkeypatch):
    monkeypatch.setattr(migration, "subprocess", _gh([], returncode=1, stderr="HTTP 502"))

    assert migration.report_gating(CONCERNED) is None


def test_gh_absent_rend_none(monkeypatch):
    monkeypatch.setattr(migration, "subprocess", _gh_absent())

    assert migration.report_gating(CONCERNED) is None


def test_liste_tronquee_rend_none(monkeypatch, capsys):
    """Atteindre la limite est une mesure PARTIELLE : elle se refuse, elle ne se tait pas."""
    monkeypatch.setattr(migration, "GH_PR_LIST_LIMIT", 2)
    prs = [{"number": n, "files": [{"path": PLAN_A}]} for n in (301, 302)]
    monkeypatch.setattr(migration, "subprocess", _gh(prs))

    assert migration.report_gating(CONCERNED) is None
    assert "TRONCATURE" in capsys.readouterr().out


def test_juste_sous_la_limite_reste_une_mesure(monkeypatch):
    """Le seuil ne doit pas refuser une lecture complete : 1 PR pour une limite de 2."""
    monkeypatch.setattr(migration, "GH_PR_LIST_LIMIT", 2)
    monkeypatch.setattr(migration, "subprocess", _gh([{"number": 400, "files": [{"path": PLAN_A}]}]))

    assert migration.report_gating(CONCERNED) == {"#400": [PLAN_A]}


def test_apply_refuse_une_mesure_impossible(monkeypatch, capsys):
    """Le fail-closed est ce qui protege le grand apply : None -> aucun git mv."""
    monkeypatch.setattr(migration, "report_gating", lambda concerned: None)
    monkeypatch.setattr(migration, "build_plan", lambda: ([], []))
    monkeypatch.setattr(migration, "check_plan", lambda plan: [])
    monkeypatch.setattr(migration, "build_replacements", lambda plan: [])
    monkeypatch.setattr(migration, "run_sweep", lambda reps: ({}, 0))

    assert migration.main(["--apply"]) == 1
    assert "REFUS" in capsys.readouterr().out


@pytest.mark.parametrize("value", [None, {}, {"#1": [PLAN_A]}])
def test_le_contrat_tient_sur_les_trois_formes(value):
    """Garde de forme : les trois retours attendus restent les seuls possibles."""
    assert value is None or isinstance(value, dict)
    if isinstance(value, dict):
        assert all(isinstance(k, str) and k.startswith("#") for k in value)
        assert all(isinstance(v, list) for v in value.values())
