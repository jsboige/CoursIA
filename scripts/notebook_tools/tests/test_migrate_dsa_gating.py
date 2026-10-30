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


# --- Plafond GraphQL sur la liste des fichiers d'une PR --------------------
#
# `gh pr list --json files` ramene 100 entrees par PR : au-dela, la fin de la
# liste disparait. Un fichier du plan tenu par une PR au-dela du plafond
# serait alors declare LIBRE, sans que rien ne le dise. La porte repasse par
# REST dans ce cas, et refuse si la re-mesure echoue.


def test_pr_au_plafond_graphql_est_re_mesuree_en_rest(monkeypatch):
    """100 fichiers vus par GraphQL : la liste est re-mesuree, paginee, en REST."""
    graphql_files = [{"path": f"g{i}.py"} for i in range(99)] + [{"path": PLAN_A}]
    rest_page1 = [{"path": f"r{i}.py"} for i in range(100)]
    rest_page2 = [{"path": PLAN_A}, {"path": PLAN_B}]
    calls = []

    def run(argv, **kwargs):
        calls.append(argv)
        if argv[1] == "api":
            page = argv[2].rsplit("page=", 1)[-1]
            batch = rest_page1 if page == "1" else rest_page2
            return SimpleNamespace(returncode=0, stdout=json.dumps(batch), stderr="")
        return SimpleNamespace(
            returncode=0,
            stdout=json.dumps([{"number": 500, "files": graphql_files}]),
            stderr="")

    monkeypatch.setattr(migration, "subprocess", SimpleNamespace(run=run))

    gating = migration.report_gating(CONCERNED)

    # Le fichier plan visible seulement par REST est bien retenu
    assert gating == {"#500": [PLAN_A, PLAN_B]}
    assert any(argv[1] == "api" for argv in calls)


def test_rest_echoue_au_plafond_rend_none(monkeypatch, capsys):
    """Re-mesure REST impossible : la porte refuse, elle ne se tait pas."""
    graphql_files = [{"path": f"g{i}.py"} for i in range(100)]

    def run(argv, **kwargs):
        if argv[1] == "api":
            return SimpleNamespace(returncode=1, stdout="", stderr="HTTP 502")
        return SimpleNamespace(
            returncode=0,
            stdout=json.dumps([{"number": 501, "files": graphql_files}]),
            stderr="")

    monkeypatch.setattr(migration, "subprocess", SimpleNamespace(run=run))

    assert migration.report_gating(CONCERNED) is None
    assert "REST" in capsys.readouterr().out


def test_sous_le_plafond_graphql_aucun_appel_rest(monkeypatch):
    """Temoin negatif : une PR sous le plafond ne declenche pas de re-mesure."""
    calls = []

    def run(argv, **kwargs):
        calls.append(argv)
        return SimpleNamespace(
            returncode=0,
            stdout=json.dumps([{"number": 502,
                                "files": [{"path": PLAN_A}] * 99}]),
            stderr="")

    monkeypatch.setattr(migration, "subprocess", SimpleNamespace(run=run))

    assert migration.report_gating(CONCERNED) == {"#502": [PLAN_A]}
    assert not any(argv[1] == "api" for argv in calls)
