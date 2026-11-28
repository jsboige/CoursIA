"""La voie legere QUALIFIE la fenetre servie avant de la servir -- #28345.

Ces tests sont **extraits** de `test_tapis_leger.py` : ce module a franchi
le plafond des scripts neufs (800 lignes) et un depassement se paie en
extraction, jamais en relevant le plafond (cliquet
`scripts/tests/test_script_size_ratchet.py`).

Ce que la voie legere rend, une fois la qualification appliquee :

- un grain **refuse** (declaration hors flotte, #17713) n'est **pas** servi ;
- une qualification qui n'a pas pu decider ne sert **rien** (fail-CLOSED) :
  les grains restent declares, et la file confirmee vide bascule sur le
  **repli chronologique** (invariant I2) ;
- une fenetre entierement refusee bascule sur le meme repli.

Aucun test ne touche le reseau : `run` est un faux, le fil est monkeypatche.
"""
import json
import re
import sys
from datetime import UTC, datetime, timedelta
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from coordination import gh_bulk, tapis_ancre, tapis_leger
from coordination import tapis_qualification as tq

pytestmark = pytest.mark.usefixtures("forbid_shell_escape")

NOW = datetime(2026, 11, 18, 9, 0, tzinfo=UTC)
LANE = "myia-ai-01:CoursIA-2"


def _noeud(n: int, titre: str = "", cree: str = "2026-11-01T00:00:00Z",
           labels=()) -> dict:
    return {"number": n, "title": titre or f"Grain {n}", "createdAt": cree,
            "updatedAt": cree, "labels": {"nodes": [{"name": lab} for lab in labels]}}


def _page_metas(nodes: list[dict], suivant: bool = False) -> str:
    return json.dumps({"data": {"repository": {"issues": {
        "pageInfo": {"hasNextPage": suivant, "endCursor": "c"},
        "nodes": nodes}}}})


def _page_issues_multiples(requete: str) -> str:
    """La reponse au lot : un alias par issue demandee (`i0`, `i1`, ...)."""
    alias: dict[str, dict] = {}
    for k, n in re.findall(r"i(\d+):\s*issue\(number:(\d+)\)", requete):
        alias[f"i{k}"] = {"number": int(n), "title": f"Grain {n}",
                          "body": f"Part of #{n}", "createdAt": "2026-11-01T00:00:00Z",
                          "updatedAt": "2026-11-01T00:00:00Z", "labels": {"nodes": []},
                          "comments": {"totalCount": 0, "nodes": []}}
    return json.dumps({"data": {"repository": alias}})


def _issue(n: int, labels=(), commentaires: int = 0) -> dict:
    return {"number": n, "title": f"Grain {n}", "body": "",
            "created_at": "2026-11-01T00:00:00Z",
            "comments": [], "comments_total": commentaires,
            "labels": list(labels)}


def _run_faux(appels: list[list[str]] | None = None, nb: int = 4):
    """Un faux `run` : metadonnees, lecture ciblee, citations (vide), PRs (vides)."""
    def run(argv, timeout):
        if appels is not None:
            appels.append(list(argv))
        requete = " ".join(argv)
        if "graphql" in requete:
            # Une requete mal formee (accolade de trop) ne se voit qu'aupres
            # de GitHub : le faux la refuse ici, pour que le defaut soit vu
            # par les tests, pas par la flotte.
            if requete.count("{") != requete.count("}"):
                raise AssertionError(f"requete GraphQL mal formee : {requete[:160]}")
        if "issue(number:" in requete:
            return _page_issues_multiples(requete)
        if "graphql" in requete:
            return _page_metas([_noeud(7 + k) for k in range(nb)])
        if argv[0] == "git":
            return ""  # aucune citation : personne n'a visite ces issues
        return "[]"  # aucune PR ouverte

    return run


def _cache_repli(tmp_path, monkeypatch, numeros: list[int], jours: int = 45):
    """Le cache local que le REPLI CHRONOLOGIQUE lit (invariant I2).

    Sans lui, le repli est IMPOSSIBLE et la voie legere sort en 3 : un test
    du repli doit donc fournir le cache, sinon il dependrait du cache de la
    machine -- un poste qui a deja tire verrait le repli servir, et le cas
    « file confirmee vide -> repli » ne se declencherait jamais.
    """
    from coordination import gh_cache_fichier
    cree = (NOW - timedelta(days=30)).strftime("%Y-%m-%dT%H:%M:%SZ")
    issues = [gh_bulk.issue({"number": n, "title": f"Grain {n}", "body": "",
                             "createdAt": cree, "updatedAt": cree,
                             "labels": {"nodes": []},
                             "comments": {"totalCount": 0, "nodes": []}})
              for n in numeros]
    lecture = gh_bulk.Lecture(issues=issues, prs=[], citations={},
                               lu_a="2026-11-23T20:00:00Z", secondes=0.1, appels=1)
    monkeypatch.setattr(gh_bulk, "dossier_cache_defaut", lambda: tmp_path)
    gh_cache_fichier.ecrire(tmp_path / f"lecture-{jours}j.json", lecture)


def test_un_grain_refuse_par_la_qualification_n_est_pas_serve(monkeypatch):
    """Un grain que la qualification REFUSE n'est pas servi a la lane.

    La declaration hors flotte (#17713) se lit sur le CORPS : elle n'est pas
    decidable sur les metadonnees du classement, donc seule la qualification
    la voit -- et le grain sort avec son code et son motif (jamais en silence).
    """
    def faux_qualifier(run, depot, numeros=None):
        return {n: {**_issue(n),
                    "body": ("Suivi Marathon II hors flotte #17713" if n == 7 else "")}
                for n in (7, 8, 9, 10, 11, 12)}

    monkeypatch.setattr(tq.tapis_lot.gh_selection, "qualifier", faux_qualifier)
    rapport, code = tapis_leger.tirage(LANE, 4, NOW, 45, "g", Path("."),
                                       _run_faux(nb=6))
    assert code == 0
    servis = [g["numero"] for g in rapport["grains"]]
    assert 7 not in servis, "un grain refuse n'est pas servi"
    refus = {e["numero"]: e for e in rapport["qualification"]["ecartees"]}
    assert 7 in refus, "le refus est affiche"
    assert refus[7]["code"] == "HORSFLOTTE"
    assert refus[7]["motif"]


def test_un_grain_labelise_candidate_delivered_n_est_jamais_serve(monkeypatch):
    """c0172 / #28114 : un grain porte le label `candidate-delivered`.

    La qualification (ce que `tapis_prise_en_charge --issues` rejoue) ne le
    sert JAMAIS : l'ecart `LABEL` est une **donnees** (`tapis_labels`), comme
    au tirage -- il ne depend ni du fil ni de la preuve par le diff. Mesure
    c0172 : 20 grains ainsi labels etaient servis par la qualification avant
    que la livraison repartie ne soit corrigee (#28723) ; le label, lui,
    ecarte toujours. Le refus est declare (code + motif), jamais en silence.
    """
    def faux_qualifier(run, depot, numeros=None):
        return {n: _issue(n, labels=["candidate-delivered"]) for n in numeros}

    monkeypatch.setattr(tq.tapis_lot.gh_selection, "qualifier", faux_qualifier)
    servis, ecartees, *_ = tq.qualifier([7], LANE, NOW, 45, [],
                                        lambda *a: "[]", preuve=None)
    assert [e.numero for e in servis] == [], \
        "un grain labelise candidate-delivered n'est JAMAIS servi"
    assert ecartees[7]["code"] == "LABEL", "l'ecart est declare, pas un silence"


def test_un_grain_non_qualifie_n_est_pas_serve(monkeypatch, tmp_path):
    """Une qualification qui n'a pas pu decider ne sert RIEN (fail-CLOSED).

    Le mur atteint rend le verdict impossible : les grains restent en attente,
    ils sont DECLARES, et la file CONFIRMEE sort vide. Une file vide n'est pas
    un service (revue du 24/11, mandat #28114 « file sans fin par lane ») : le
    repli chronologique prend le relais, comme le fait le cap de livraisons --
    et les grains non decides restent declares, jamais servis en silence.
    """
    def faux_qualification(candidats, lane, maintenant, jours, prs, run,
                           echeance=None, **kw):
        return [], {}, [], True, 0, {"secondes": 0.0, "premier_servable_s": None}

    monkeypatch.setattr(tq, "qualifier", faux_qualification)
    _cache_repli(tmp_path, monkeypatch, [9001, 9002, 9003])
    rapport, code = tapis_leger.tirage(LANE, 4, NOW, 45, "g", Path("."),
                                       _run_faux(nb=6))
    assert code == 0
    assert rapport["voie"] == "repli", \
        "une file confirmee vide bascule sur le repli chronologique"
    assert rapport["qualification"]["budget_epuise"] is True
    assert rapport["qualification"]["non_qualifies"], \
        "les grains non decides sont declares, jamais servis en silence"
    assert rapport["qualification"]["repli"], "le motif du repli est dit"


def test_une_fenetre_entierement_refusee_bascule_sur_le_repli(monkeypatch,
                                                               tmp_path):
    """L'autre cause d'une file confirmee VIDE : toute la fenetre est refusee.

    Mesure du 24/11 : 16 des 24 candidats refuses pour une marge de 3 -- la
    marge est mince, et une fenetre entierement refusee est un fait, pas une
    hypothese. Le repli chronologique prend alors le relais ; les refus
    restent DECLARES (code + motif), et aucun grain refuse n'est servi.
    """
    def faux_qualification(candidats, lane, maintenant, jours, prs, run,
                           echeance=None, **kw):
        refuses = {n: {"code": "HORSFLOTTE", "motif": "hors flotte #17713"}
                   for n in candidats}
        return [], refuses, [], False, len(candidats), {
            "secondes": 1.0, "premier_servable_s": None}

    monkeypatch.setattr(tq, "qualifier", faux_qualification)
    _cache_repli(tmp_path, monkeypatch, [9001, 9002, 9003])
    rapport, code = tapis_leger.tirage(LANE, 4, NOW, 45, "g", Path("."),
                                       _run_faux(nb=6))
    assert code == 0
    assert rapport["voie"] == "repli", \
        "une fenetre entierement refusee bascule sur le repli chronologique"
    refuses = {e["numero"]: e for e in rapport["qualification"]["ecartees"]}
    assert refuses, "les refus sont declares (code + motif)"
    assert refuses[next(iter(refuses))]["code"] == "HORSFLOTTE"
    servis = [g["numero"] for g in rapport["grains"]]
    assert not (set(servis) & set(refuses)), \
        "aucun grain refuse n'est servi"
    assert rapport["qualification"]["repli"], "le motif du repli est dit"


def test_le_budget_de_la_commande_borne_la_qualification(monkeypatch, tmp_path):
    """I6 (#28114) : le budget est celui de la COMMANDE, pas celui de l'etage.

    La reserve du coordinateur (25/11) : la qualification repartait d'une
    horloge **neuve** (`debut + MUR_QUALIFICATION_S`, calculee apres la
    lecture du pool), si bien qu'une selection de 25 s suivie de 40 s de
    qualification depassait le contrat de 60 s de la commande entiere -- et le
    repli n'avait plus de place.

    Le test est au **point d'entree** (`tirage`), horloge controlee : la
    selection consomme 28 s du budget de 30 s ; la qualification doit etre
    **COUPEE** (fail-CLOSED : une decision non prise ne sert rien) et le repli
    prendre le relais. Les **refus** et les candidats **non lus** restent
    explicitement distingues.
    """
    import time as _time

    from coordination import gh_selection, tapis_leger_fenetre

    budget_s = 30.0
    decalage = {"s": 0.0}
    reel = _time.monotonic

    def horloge_fausse() -> float:
        """L'horloge simulee : le temps reel plus le temps SIMULE (`decalage`)."""
        return reel() + decalage["s"]

    monkeypatch.setattr(_time, "monotonic", horloge_fausse)

    vue: dict = {}

    def faux_lecture(run, depot=None, budget_s=30.0, horloge=None, echeance=None):
        """La lecture du pool : elle consomme 28 s du budget de la commande."""
        vue["echeance_lecture"] = echeance
        vue["maintenant_lecture"] = horloge_fausse()
        decalage["s"] += 28.0
        noeuds = [_noeud(7 + k) for k in range(6)]
        return [gh_selection.metadonnee(n) for n in noeuds], 28.0

    monkeypatch.setattr(gh_selection, "lire_metadonnees_issues", faux_lecture)

    def faux_qualification(candidats, lane, maintenant, jours, prs, run,
                           echeance=None, **kw):
        vue["echeance_qualif"] = echeance
        vue["candidats"] = list(candidats)
        arrete = horloge_fausse() > echeance
        vue["arrete"] = arrete
        refuses = {}
        if candidats:
            refuses[candidats[0]] = {"code": "HORSFLOTTE",
                                     "motif": "hors flotte #17713"}
        return [], refuses, [], arrete, 1, {"secondes": 0.0,
                                            "premier_servable_s": None}

    monkeypatch.setattr(tq, "qualifier", faux_qualification)
    # L'ANCRE est ISOLÉE : le tirage ecrit l'etat de la lane dans le repertoire
    # local de la machine -- un test qui lit l'ancre reelle faitdependre un
    # test sans rapport de l'etat du poste (faux rouge mesure).
    monkeypatch.setenv(tapis_ancre.ENV_ETAT, str(tmp_path))
    _cache_repli(tmp_path, monkeypatch, [9001, 9002, 9003])
    rapport, code = tapis_leger.tirage(LANE, 4, NOW, 45, "g", Path("."),
                                       _run_faux(nb=6), budget_s=budget_s)

    assert code == 0
    # L'ECHEANCE est MONOTONE : la selection et la qualification partagent la
    # meme, et le temps du repli est reserve.
    assert vue["echeance_lecture"] is not None
    ecart = vue["echeance_lecture"] - vue["maintenant_lecture"]
    assert ecart <= budget_s, \
        "la selection ne repart pas sur une horloge neuve (60 s)"
    assert ecart >= budget_s - 1.0, \
        "l'echeance de la selection est celle du point d'entree"
    assert vue["echeance_qualif"] == (vue["echeance_lecture"]
                                      - tapis_leger_fenetre.RESERVE_REPLI_S), \
        "la qualification partage l'echeance, moins le temps du repli"
    # La selection a consomme sa part : la qualification est COUPEE.
    assert vue["arrete"] is True, "la qualification est coupee, pas attendue"
    assert rapport["qualification"]["budget_epuise"] is True
    # Les REFUS et les candidats NON LUS restent distingues.
    refus = {e["numero"] for e in rapport["qualification"]["ecartees"]}
    non_qualifies = set(rapport["qualification"]["non_qualifies"])
    assert refus, "le refus est declare (code + motif)"
    assert refus.isdisjoint(non_qualifies), \
        "un refus et un grain non lu sont deux choses distinctes"
    assert non_qualifies, "les grains non decides sont declares"
    assert rapport["qualification"]["repli"], "le motif du repli est dit"
    assert rapport["voie"] == "repli", \
        "la file confirmee vide bascule sur le repli chronologique"
