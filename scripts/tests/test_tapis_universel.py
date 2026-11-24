"""Tests de la rotation UNIVERSELLE du tapis (`coordination/tapis_universel.py`).

Le chemin de selection se verifie sur ses trois garanties : la lecture est
LEGERE (metadonnees seules, jamais de corps ni de commentaires), la pagination
est COMPLETE (une liste partielle n'est jamais servie), et le budget global
est une borne de DUREE dont le depassement se dit. Puis la rotation elle-meme :
toutes les issues y passent, et une apparition n'y compte pas comme une visite.
Aucun test ne touche le reseau : `run` est un faux.
"""
import json
import subprocess
import sys
from datetime import UTC, datetime, timedelta
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from coordination import gh_bulk, gh_selection, tapis_marqueurs
from coordination import tapis_universel as tu

pytestmark = pytest.mark.usefixtures("forbid_shell_escape")

NOW = datetime(2026, 11, 18, 9, 0, tzinfo=UTC)
LANE = "myia-ai-01:CoursIA-2"


def _noeud(n: int, titre: str = "", cree: str = "2026-11-01T00:00:00Z",
           labels=()) -> dict:
    return {"number": n, "title": titre or f"Grain {n}", "createdAt": cree,
            "updatedAt": cree, "labels": {"nodes": [{"name": lab} for lab in labels]}}


def _page(nodes: list[dict], suivant: bool, curseur: str = "c") -> str:
    return json.dumps({"data": {"repository": {"issues": {
        "pageInfo": {"hasNextPage": suivant, "endCursor": curseur},
        "nodes": nodes}}}})


def _run_double_page(n1: int = 3, n2: int = 2):
    """Un faux `run` : deux pages de metadonnees, puis plus rien."""
    pages = [_page([_noeud(100 + k) for k in range(n1)], True),
             _page([_noeud(200 + k) for k in range(n2)], False)]
    appels: list[list[str]] = []

    def run(argv, timeout):
        appels.append(list(argv))
        return pages[len(appels) - 1] if len(appels) <= len(pages) else pages[-1]

    return run, appels


def test_la_selection_ne_lit_que_des_metadonnees():
    """La requete du chemin de selection ne demande ni corps ni commentaires."""
    run, appels = _run_double_page()
    metas, duree = gh_selection.lire_metadonnees_issues(run)
    assert len(metas) == 5
    assert duree >= 0
    requete = " ".join(appels[0])
    assert "body" not in requete and "comments" not in requete
    assert "number title createdAt updatedAt labels" in requete


def test_la_pagination_est_complete():
    """Toutes les pages sont lues : une liste partielle n'est jamais servie."""
    run, appels = _run_double_page(n1=3, n2=2)
    metas, _ = gh_selection.lire_metadonnees_issues(run)
    assert [m["number"] for m in metas] == [100, 101, 102, 200, 201]
    assert len(appels) == 2


def test_le_budget_global_erreur_explicite():
    """Un appel qui ne repond pas epuise le budget : l'erreur le nomme."""
    def run(argv, timeout):
        raise subprocess.TimeoutExpired(argv, timeout)

    with pytest.raises(gh_bulk.LectureIncomplete) as exc:
        gh_selection.lire_metadonnees_issues(run, budget_s=0.5)
    assert "budget global" in exc.value.cause


class _Horloge:
    """Une horloge simulee : elle n'avance que quand on le lui demande."""

    def __init__(self, pas: float = 0.0) -> None:
        self.t = 0.0
        self.pas = pas

    def __call__(self) -> float:
        return self.t

    def avancer(self, pas: float | None = None) -> None:
        self.t += self.pas if pas is None else pas


def test_le_rejeu_ne_redonne_pas_un_budget_neuf():
    """L'echeance est COMMUNE aux trois tailles de rejeu.

    Defect epingle : le budget etait calcule une fois par page, puis reutilise
    tel quel aux trois tailles — trois timeouts de 60 s pour un budget global
    de 60 s, soit 180 s de lecture possible.

    Contrat I6 (#28114) : le timeout d'un appel est le plus petit du PLAFOND
    de l'appel (15 s) et du temps RESTANT avant l'echeance. L'horloge
    avance ici de 20 s par appel, pour une echeance posee 25 s plus loin :
    le premier appel recoit 15 s (le plafond), le rejeu recoit 5 s (le
    RESTANT, recalcule), et la troisieme taille est refusee — l'echeance
    est atteinte, elle n'est pas repoussee.

    Le second timeout (5 s, et non 15 s) est l'observable qui porte
    l'invariant : sans recomputation du temps restant, le rejeu repartirait
    de zero et recoitrait le plafond.
    """
    horloge = _Horloge(pas=20.0)
    timeouts: list[int] = []

    def run(argv, timeout):
        timeouts.append(timeout)
        horloge.avancer()
        if len(timeouts) < 3:
            raise subprocess.TimeoutExpired(argv, timeout)
        return _page([_noeud(1)], False)

    with pytest.raises(gh_bulk.LectureIncomplete) as exc:
        gh_selection.lire_metadonnees_issues(run, budget_s=25.0, horloge=horloge)
    assert "budget global" in exc.value.cause
    assert timeouts == [15, 5], \
        f"le temps restant doit etre recalcule avant chaque rejeu : {timeouts}"


def test_une_reponse_arrivee_apres_l_echeance_est_incomplete():
    """Le controle se fait APRES la reponse finale : une lecture qui depasse
    sa borne est incomplete meme si la reponse est arrivee."""
    horloge = _Horloge()

    def run(argv, timeout):
        horloge.avancer(pas=70.0)  # l'appel depasse le budget de 60 s
        return _page([_noeud(1)], False)

    with pytest.raises(gh_bulk.LectureIncomplete) as exc:
        gh_selection.lire_metadonnees_issues(run, budget_s=60.0, horloge=horloge)
    assert "budget global" in exc.value.cause
    assert "depass" in exc.value.cause


def test_une_lecture_dans_la_borne_reste_conforme():
    """CONTROLE POSITIF : l'echeance ne doit rien casser quand la lecture
    tient dans le budget — deux pages, temps simule nul."""
    horloge = _Horloge()
    run, _appels = _run_double_page(n1=3, n2=2)
    metas, duree = gh_selection.lire_metadonnees_issues(run, budget_s=60.0,
                                                         horloge=horloge)
    assert [m["number"] for m in metas] == [100, 101, 102, 200, 201]
    assert duree == 0.0


def test_la_qualification_ne_lit_que_les_issues_nommees():
    """La lecture lourde ne porte que sur le grain pris en charge."""
    def run(argv, timeout):
        return json.dumps({"data": {"repository": {"i0": {
            "number": 7, "title": "Grain 7", "body": "Part of #3",
            "createdAt": "2026-11-01T00:00:00Z", "updatedAt": "2026-11-01T00:00:00Z",
            "labels": {"nodes": []},
            "comments": {"totalCount": 0, "nodes": []}}}}})

    lues = gh_selection.qualifier(run, numeros=[7])
    assert set(lues) == {7} and lues[7]["body"] == "Part of #3"


def test_une_apparition_ne_compte_pas_comme_une_visite():
    """« Une apparition ne compte pas comme travail reellement effectue » : les
    visites du niveau ne viennent que des commits qui citent l'issue."""
    metas = [_noeud(1), _noeud(2)]
    sans = tu.etats_leger(metas, {}, NOW)
    assert [e.visites for e in sans] == [0, 0]
    avec = tu.etats_leger(metas, {1: [{"sha": "a" * 12, "date": "2026-11-17T10:00:00Z",
                                       "sujet": "Fix: x"}]}, NOW)
    assert [e.visites for e in avec] == [1, 0]


def test_la_rotation_conserve_toutes_les_issues():
    """La rotation ne ecarte rien : le pool entier est classe, et sur des
    tours simules toutes les issues passent (pas de famine).

    La simulation mesure ce que fait un tour reel : le grain servi compte une
    VISITE (le travail reellement effectue), donc son niveau monte et il
    laisse la tete de niveau au suivant. Sans cette montee, la fenetre de
    tete (24) servirait toujours les memes issues -- ce n'est pas une famine
    du classement, c'est l'absence de travail."""
    metas = [gh_selection.metadonnee(_noeud(
        100 + k, cree=(NOW - timedelta(days=200 - 5 * k)).strftime(
            "%Y-%m-%dT%H:%M:%SZ"))) for k in range(60)]
    citations: dict[int, list[dict]] = {}
    vus: set[int] = set()
    for tour in range(12):
        etats_ = tu.etats_leger(metas, citations, NOW)
        file = tu.rotation_universelle(etats_, LANE, NOW, 8, graine=f"g{tour}")
        for e in file:
            vus.add(e.numero)
            citations.setdefault(e.numero, []).append(
                {"sha": f"{tour:040d}", "date": tapis_marqueurs._iso(NOW),
                 "sujet": "Fix: x"})
    assert len(vus) == 60, sorted(set(range(100, 160)) - vus)


def test_le_rapport_porte_l_etat_et_l_action():
    metas = [gh_selection.metadonnee(_noeud(
        1, titre="[EPIC] Racine #9", labels=["consolidation"])),
        gh_selection.metadonnee(_noeud(2))]
    etats_ = tu.etats_leger(metas, {}, NOW)
    file = tu.rotation_universelle(etats_, LANE, NOW, 8)
    r = tu.rapport(etats_, file, LANE, NOW, {"issues": 2, "secondes": 1.2})
    assert r["pool"] == 2 and len(r["grains"]) == 2
    for g in r["grains"]:
        assert "qualifier" in g["action"]
        assert g["priorite"]
    epic = next(g for g in r["grains"] if g["numero"] == 1)
    assert epic["consolidation"] is True
    assert "consolidation" in epic["action"]


def test_la_lecture_legique_est_plus_courte_que_la_lecture_lourde():
    """La lecture de selection ne transporte ni corps ni commentaires : elle est
    plus courte que la lecture complete, a nombre d'issues egal."""
    def run(argv, timeout):
        return _page([_noeud(100 + k) for k in range(10)], False)

    metas, _ = gh_selection.lire_metadonnees_issues(run)
    leger = len(json.dumps(metas))
    lourd = len(json.dumps([{"number": m["number"], "title": m["title"],
                              "body": "x" * 400,
                              "comments": [{"body": "y" * 400} for _ in range(6)]}
                             for m in metas]))
    assert leger < lourd / 10
