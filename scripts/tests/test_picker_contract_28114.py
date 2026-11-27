"""Tests de CONTRAT du picker -- les sept invariants I1 a I7 (#28114).

Le mandat du maintainer (22/11) fixe sept invariants que le picker doit tenir
**toujours** : une file sans fin par lane, un repli chronologique, l'autonomie
de la lane, la degradation (jamais le refus), les exclusions en **donnees**,
une borne de temps, et l'ordre consolidation-puis-anciennete. Le mandat est
repris dans le corps de l'issue (#28114) ; ce fichier en fait une suite
**executable**, sur un pool synthetique.

Aucun test ne touche le reseau : `run` est un faux, les lectures de citations
et de PRs sont vides, l'etat de lane est neutralise. Les lectures sont donc
deterministes et ne dependent ni du depot ni de l'heure de la machine.

## Comment lire les verdicts

Chaque test porte UN invariant, un scenario et une attente. Un invariant deja
tenu passe ; un invariant viole est marque `xfail(strict=True)` :

- le CI reste **vert** tant que l'architecture consolidee n'est pas livree ;
- `strict=True` fait **echouer** le CI sur un XPASS : quand l'invariant est
  tenu, le marqueur doit disparaitre -- impossible d'oublier.

Le tableau ci-dessous resume l'etat mesure au 22/11 (lane
`myia-ai-01:CoursIA-2`, `origin/main` `b5ebaf67`).

| Invariant | Etat au 22/11 | Preuve |
|---|---|---|
| I1 file sans fin par lane | tenu | `tapis_leger.tirage` rend une file a toute lane |
| I2 repli chronologique | tenu (23/11, ce PR) | hors reseau, la voie legere lit le cache local (`tapis_repli.py`) et sert le pool par date de creation |
| I3 autonomie | tenu | le tirage ne lit aucun artefact du coordinateur |
| I4 degrade jamais bloque | tenu (22/11, ce PR) | `main_freshness` rend `degrade`, plus la sortie 4 (`TIRAGE REFUSE`) |
| I5 exclusions en donnees | tenu (23/11, ce PR) | la regle LABEL lit la table des labels d'exclusion (`tapis_labels.py`) : `candidate-delivered` et `pause`, sur le tirage complet **et** sur la voie legere |
| I6 borne de temps | tenu (23/11, ce PR) | une echeance monotone unique (`gh_bulk.MUR_TIRAGE_S`) partagee par les etages ; budgets declares cumules : 30 + 15 + 15 = 60 s |
| I7 consolidation puis anciennete | **tenu** (23/11, ce PR) | la consolidation est posee EN PREMIER (`tapis_avantages.bonus_dixiemes`) : elle passe devant l'ordinary la plus agee, a visites egales |

I2 est devenu **executable** dans ce PR : hors reseau, la voie legere lit le
CACHE LOCAL (`coordination/tapis_repli.py`), sert le pool dans l'ordre de
creation, et un curseur persiste fait defiler le pool de bloc en bloc. Le
marqueur `xfail` du test I2 est donc retire : le test passe, et le CI le
prouve.

I4 est devenu **executable** dans ce PR : la garde de fraicheur distingue
trois etats (frais / degrade / refuse), et seul l'etat **inconnu** (mesure
impossible) refuse encore. Le marqueur `xfail` du test I4 a donc ete
retire : le test passe, et le CI le prouve.

I5 est devenu **executable** dans ce PR : la regle LABEL de
`tapis_rapide._decider` lit la table des labels d'exclusion
(`coordination/tapis_labels.py`) -- l'urne de cloture et la pause. Le
marqueur `xfail` du test I5 est donc retire : le test passe, et le CI le
prouve.

La **voie legere** (le tirage par defaut) lit la MEME table :
`tapis_universel.etats_leger` marque l'ecart et son motif sur l'etat, et le
bloc servi (`tapis_rotation.bloc`) laisse de cote tout etat ecarte -- donc
aussi le repli chronologique, qui ne passe pas par la rotation. Le test I5
conduit les DEUX voies.

I6 est devenu **executable** dans ce PR : le tirage porte UNE echeance
monotone unique (`gh_bulk.MUR_TIRAGE_S`), posee une fois et partagee par ses
etages -- le temps restant borne chaque appel, donc un etage qui a consomme
sa part voit l'etage suivant etre coupe plutot qu'attendu. Les budgets
DECLARES tiennent desormais dans la borne du contrat (30 + 15 + 15 = 60 s
pour 60 s), au lieu de 60 + 90 + 90 = 240 s. Le marqueur `xfail` du test I6
est donc retire : le test passe, et le CI le prouve.

Ce que ce fichier ne couvre pas (a dire, pas a cacher) : l'exclusion des
**doublons de meme carnet** (I5) n'a pas de cle de carnet definie par le
mandat -- elle reste dans le residu de l'issue ; et les tests sont ecrits sur
le **comportement** (ce que rend le picker), pas sur une API nommee : le
noyau consolide peut les satisfaire par n'importe quelle voie interne.
"""
from __future__ import annotations

import json
import re
import sys
import time
from datetime import UTC, datetime, timedelta
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from coordination import gh_bulk, gh_cache_fichier, gh_selection, main_freshness
from coordination import tapis_ancre, tapis_cap_livraisons, tapis_etat, tapis_leger, tapis_rapide

NOW = datetime(2026, 11, 22, 21, 0, tzinfo=UTC)
LANE = "myia-ai-01:CoursIA-2"
VOISINE = "myia-po-2023:CoursIA-2"
TIERS = "myia-po-2026:CoursIA-3"


# --- le pool synthetique -------------------------------------------------------

def _meta(n: int, titre: str = "", cree: str = "2026-11-01T00:00:00Z",
           labels: tuple[str, ...] = ()) -> dict:
    """Une issue en metadonnees : la forme que rend `gh_selection.metadonnee`."""
    return {"number": n, "title": titre or f"Grain {n}", "created_at": cree,
            "updated_at": cree, "labels": list(labels)}


def _issue(n: int, titre: str = "", cree: str = "2026-11-01T00:00:00Z",
           labels: tuple[str, ...] = (), corps: str = "") -> dict:
    """Une issue a plat : la forme que rend `gh_bulk.issue`."""
    return gh_bulk.issue({"number": n, "title": titre or f"Grain {n}", "body": corps,
                           "createdAt": cree, "updatedAt": cree,
                           "labels": {"nodes": [{"name": lab} for lab in labels]},
                           "comments": {"totalCount": 0, "nodes": []}})


def _page_metas(metas: list[dict]) -> str:
    nodes = [{"number": m["number"], "title": m["title"], "createdAt": m["created_at"],
              "updatedAt": m["updated_at"],
              "labels": {"nodes": [{"name": lab} for lab in m["labels"]]}}
             for m in metas]
    return json.dumps({"data": {"repository": {"issues": {
        "pageInfo": {"hasNextPage": False, "endCursor": "c"}, "nodes": nodes}}}})


def _page_issues(metas: list[dict], requete: str) -> str:
    """La lecture CIBLEE : un alias (`i0`, `i1`...) par issue nommee.

    La qualification de la fenetre servie lit le **fil complet** de chaque
    grain (dispatch `c0030`, 24/11) : sans cette reponse, aucun grain ne
    serait qualifie et la voie leger servirait une file VIDE.
    """
    par_numero = {m["number"]: m for m in metas}
    data: dict = {"data": {"repository": {}}}
    for k, n in enumerate(re.findall(r"issue\(number:(\d+)\)", requete)):
        m = par_numero.get(int(n))
        data["data"]["repository"][f"i{k}"] = None if m is None else {
            "number": m["number"], "title": m["title"], "body": "",
            "createdAt": m["created_at"], "updatedAt": m["updated_at"],
            "labels": {"nodes": [{"name": lab} for lab in m["labels"]]},
            "comments": {"totalCount": 0, "nodes": []}}
    return json.dumps(data)


def _run(metas: list[dict]):
    """Le faux `run` : le pool en metadonnees, aucune PR, aucune citation."""
    def run(argv, timeout):
        requete = " ".join(argv)
        if "issue(number:" in requete:
            return _page_issues(metas, requete)
        if "graphql" in requete:
            return _page_metas(metas)
        if argv[0] == "git":
            return ""
        return "[]"  # aucune PR ouverte
    return run


def _run_casse():
    """Le faux `run` du reseau indisponible : l'echec que les lectures savent
    rendre (`gh_bulk.LectureIncomplete`), pas une exception qui les traverse."""
    def run(argv, timeout):
        raise OSError("reseau indisponible")
    return run


@pytest.fixture(autouse=True)
def _etat_neutre(monkeypatch):
    """Aucun etat de lane : ni ancre, ni visitation, ni ecriture.

    Le contrat I3 veut qu'une lane tire **seule** : le test ne doit pas
    dependre d'une ancre posee par une autre session.

    `lire` rend un etat **normalise** (`tapis_etat.vide()`) : c'est le
    contrat de l'organe, et la qualification s'en sert pour acquitter les
    verdicts. Un etat nu (`{}`) ferait echouer l'ancre au lieu de la laisser
    immobile. L'ecriture est neutralisee : le test ne touche pas l'ancre
    reelle de la lane.
    """
    monkeypatch.setattr(tapis_ancre, "lire", lambda lane: tapis_etat.vide())
    monkeypatch.setattr(tapis_ancre, "proposer", lambda *a, **k: {})
    monkeypatch.setattr(tapis_ancre, "ecrire", lambda lane, etat: etat)


# --- I1 -- une file sans fin par lane ------------------------------------------

def test_I1_chaque_lane_obtient_une_file_non_vide_tant_que_le_pool_est_ouvert():
    """I1 -- toute lane obtient une file, quelle que soit l'occupation des autres.

    Le pool est le meme pour les trois lanes : une lane deja servie (ici la
    voisine, tiree juste avant) ne doit pas **vider** le pool de l'autre.
    """
    pool = [_meta(1000 + k, cree=f"2026-10-{(k % 28) + 1:02d}T00:00:00Z")
            for k in range(20)]
    for lane in (LANE, VOISINE, TIERS):
        rapport, code = tapis_leger.tirage(lane, 8, NOW, 45, f"graine-{lane}",
                                           Path("."), _run(pool))
        assert code == 0
        assert rapport["grains"], f"la lane {lane} a obtenu une file vide"
        assert rapport["pool"] == len(pool), "le pool doit etre lu en entier"


# --- I2 -- le repli chronologique -----------------------------------------------

def test_I2_le_repli_chronologique_couvre_le_pool_en_ordre_de_creation(
        tmp_path, monkeypatch):
    """I2 -- hors reseau, le picker defile TOUTES les issues ouvertes, par date.

    Scenario : le reseau est tombe et le cache local porte le pool (c'est la
    source du repli). Le picker doit alors rendre une file **non vide**, dans
    l'ordre de creation, et des tirages successifs doivent couvrir le pool
    entier -- sans sauter d'issue.

    Etat au 22/11 : la voie legere (`tapis_leger.tirage`) ne lit **aucun**
    cache ; hors reseau elle leve `LectureIncomplete` et le point d'entree
    rend le code 3 (rien n'est servi). D'ou le marqueur.

    Etat au 23/11 (ce PR) : la voie legere lit le CACHE LOCAL quand la
    lecture echoue (`coordination/tapis_repli.py`), et un curseur persiste
    fait defiler le pool de bloc en bloc. Le marqueur `xfail` est retire :
    le test passe, et le CI le prouve.
    """
    pool = [_meta(2000 + k,
                  cree=(NOW - timedelta(days=30 - k)).strftime("%Y-%m-%dT%H:%M:%SZ"))
            for k in range(10)]
    lecture = gh_bulk.Lecture(issues=[_issue(m["number"], m["title"], m["created_at"])
                                      for m in pool],
                               prs=[], citations={}, lu_a="2026-11-22T20:00:00Z",
                               secondes=0.1, appels=1)
    monkeypatch.setattr(gh_bulk, "dossier_cache_defaut", lambda: tmp_path)
    gh_cache_fichier.ecrire(tmp_path / "lecture-45j.json", lecture)

    vus: set[int] = set()
    for tour in range(3):
        rapport, code = tapis_leger.tirage(LANE, 4, NOW, 45, f"graine-{tour}",
                                           Path("."), _run_casse())
        assert code == 0, "le repli chronologique rend une file, pas un echec"
        numeros = [g["numero"] for g in rapport["grains"]]
        assert numeros, "le repli doit rendre une file non vide"
        dates = [m["created_at"] for m in pool if m["number"] in set(numeros)]
        assert dates == sorted(dates), "la file doit suivre l'ordre de creation"
        vus.update(numeros)
    assert vus == {m["number"] for m in pool}, \
        "des tirages successifs doivent couvrir toutes les issues ouvertes"


def test_I2_le_repli_annonce_des_candidats_du_cache_pas_des_grains_confirmes(
        tmp_path, monkeypatch):
    """I2 -- l'ACTION PUBLIQUE du repli distingue le cache du grain confirme.

    Le repli chronologique sert des metadonnees locales : il ne lit JAMAIS le
    fil. Presenter ces candidats comme « deja qualifies sur fil complet »
    donnerait a la lane une consigne de claim qui repose sur une lecture de
    fil qui n'a pas eu lieu (reserve du coordinateur du 25/11 sur #28345).

    Temoin : l'action publique d'un grain du repli impose la lecture du fil
    avant le claim, et ne contient pas la consigne des grains confirmes.
    """
    pool = [_meta(5000 + k,
                  cree=(NOW - timedelta(days=15 - k)).strftime("%Y-%m-%dT%H:%M:%SZ"))
            for k in range(6)]
    lecture = gh_bulk.Lecture(issues=[_issue(m["number"], m["title"], m["created_at"])
                                      for m in pool],
                               prs=[], citations={}, lu_a="2026-11-22T20:00:00Z",
                               secondes=0.1, appels=1)
    monkeypatch.setattr(gh_bulk, "dossier_cache_defaut", lambda: tmp_path)
    gh_cache_fichier.ecrire(tmp_path / "lecture-45j.json", lecture)

    rapport, code = tapis_leger.tirage(LANE, 4, NOW, 45, "graine", Path("."),
                                       _run_casse())
    assert code == 0, "le repli rend une file, pas un echec"
    assert rapport["voie"] == "repli", "la voie rendue est le repli"
    assert rapport["grains"], "le repli doit rendre une file non vide"
    assert rapport["fil_lu"] is False, "le repli n'a pas lu le fil"
    for g in rapport["grains"]:
        assert "candidat du cache" in g["action"], \
            "l'action publique doit nommer le grain comme candidat du cache"
        assert "lire le fil avant de claimer" in g["action"], \
            "l'action publique doit imposer la lecture du fil avant le claim"
        assert "deja qualifie sur fil complet" not in g["action"], \
            "un candidat du cache ne doit pas etre presente comme qualifie"


def test_I2_un_filtre_qui_vide_la_file_bascule_sur_le_repli(tmp_path, monkeypatch):
    """I2 -- une lecture REUSSIE dont la file sort vide bascule sur le repli.

    Le cas que la revue nomme : les filtres ecartent tous les grains, la
    lecture du reseau a REUSSI, et la file sort vide -- la lane ne recoit
    rien et I1 ("file sans fin") est rompu. Le repli chronologique doit donc
    prendre le relais : le cache local rend une file non vide.

    Le filtre force ici est le **cap de livraisons** : sa mesure aboutit en
    ligne et ecarte tout. Hors reseau la meme mesure est impossible, et le
    cap y reste inerte (fail-OPEN) -- c'est ce que le temoin du rapport dit.
    """
    pool = [_meta(4000 + k,
                  cree=(NOW - timedelta(days=20 - k)).strftime("%Y-%m-%dT%H:%M:%SZ"))
            for k in range(8)]
    lecture = gh_bulk.Lecture(issues=[_issue(m["number"], m["title"], m["created_at"])
                                      for m in pool],
                               prs=[], citations={}, lu_a="2026-11-22T20:00:00Z",
                               secondes=0.1, appels=1)
    monkeypatch.setattr(gh_bulk, "dossier_cache_defaut", lambda: tmp_path)
    gh_cache_fichier.ecrire(tmp_path / "lecture-45j.json", lecture)

    def charge_saturee(lane, maintenant, prs_ouvertes, run=None, **kw):
        """En ligne la mesure aboutit (tout est ecarte) ; hors reseau elle
        echoue, et le cap laisse la file intacte (fail-OPEN).

        `**kw` : la mesure porte maintenant l'`echeance` partagee et le `run`
        de la commande -- le cap n'a plus son propre budget (#28114, I6)."""
        if run is tapis_cap_livraisons.fetcher_hors_reseau:
            return None
        return {m["number"]: 99 for m in pool}

    monkeypatch.setattr(tapis_cap_livraisons, "charge_en_vol", charge_saturee)

    rapport, code = tapis_leger.tirage(LANE, 4, NOW, 45, "graine", Path("."),
                                       _run(pool))
    assert code == 0, "le repli rend une file, pas un echec"
    assert rapport["voie"] == "repli", "une file vide doit basculer sur le repli"
    assert rapport["grains"], "le repli doit rendre une file non vide"
    assert rapport["cap_livraisons"]["mesure"] is False, \
        "hors reseau le cap n'est pas evalue : le temoin du rapport le dit"


def test_I2_le_cap_du_repli_ne_recoit_aucun_fetteur_capable_de_lire_le_reseau(
        tmp_path, monkeypatch):
    """I2 -- le cap du repli est INERTE : aucun fetteur reel ne lui est passe.

    Le cap de livraisons lit GitHub (les PRs mergees de la fenetre). Le repli
    existe POUR la panne du reseau : lui donner un fetteur capable de lire le
    ferait echouer de nouveau en pleine panne. Le fetteur du repli leve donc,
    et le rapport porte le temoin `mesure: false`.

    L'espion observe le `run` reellement passe au cap : il doit etre le
    fetteur INERTE -- ni le `run` de l'appelant, ni `None` (qui lierait le
    fetteur reel du depot).
    """
    import fetch_merged_prs_since

    def sonde(*args, **kwargs):
        raise AssertionError("le repli ne doit pas lire le reseau")

    monkeypatch.setattr(fetch_merged_prs_since, "run_gh", sonde)
    pool = [_meta(4100 + k,
                  cree=(NOW - timedelta(days=15 - k)).strftime("%Y-%m-%dT%H:%M:%SZ"))
            for k in range(6)]
    lecture = gh_bulk.Lecture(issues=[_issue(m["number"], m["title"], m["created_at"])
                                      for m in pool],
                               prs=[], citations={}, lu_a="2026-11-22T20:00:00Z",
                               secondes=0.1, appels=1)
    monkeypatch.setattr(gh_bulk, "dossier_cache_defaut", lambda: tmp_path)
    gh_cache_fichier.ecrire(tmp_path / "lecture-45j.json", lecture)

    vues: list = []
    vrai = tapis_cap_livraisons.passer

    def espion(file, ordre, lane, maintenant, prs_ouvertes, run=None, **kw):
        vues.append(run)
        return vrai(file, ordre, lane, maintenant, prs_ouvertes, run=run, **kw)

    monkeypatch.setattr(tapis_cap_livraisons, "passer", espion)

    rapport, code = tapis_leger.tirage(LANE, 4, NOW, 45, "graine", Path("."),
                                       _run_casse())
    assert code == 0, "hors reseau, le repli rend une file, pas un echec"
    assert rapport["grains"], "le repli doit rendre une file non vide"
    assert rapport["cap_livraisons"]["mesure"] is False
    assert vues, "le cap doit avoir ete evalue (et refuse) sur le repli"
    for run in vues:
        assert run is tapis_cap_livraisons.fetcher_hors_reseau, \
            "le cap du repli ne doit recevoir que le fetteur INERTE"
        assert run is not None, "run=None lierait le fetteur reel du depot"


# --- I3 -- l'autonomie de la lane ----------------------------------------------

def test_I3_le_tirage_ne_depend_d_aucun_artefact_du_coordinateur():
    """I3 -- la lane tire seule : le tirage central est une optimisation.

    Le test tourne sans etat de lane (fixture `_etat_neutre`), sans ancre et
    sans artefact du coordinateur : la file doit quand meme etre rendue, et le
    pool doit etre lu en entier (un tirage qui tronque le pool est un tirage
    qui epuise la lane).
    """
    pool = [_meta(3000 + k, cree=f"2026-09-{(k % 28) + 1:02d}T00:00:00Z")
            for k in range(15)]
    rapport, code = tapis_leger.tirage(LANE, 8, NOW, 45, "graine", Path("."),
                                       _run(pool))
    assert code == 0
    assert rapport["grains"], "une lane seule doit obtenir des grains"
    assert rapport["pool"] == len(pool)


# --- I4 -- degrader, jamais bloquer --------------------------------------------

def test_I4_un_main_perime_degrade_le_tirage_il_ne_le_refuse_pas(monkeypatch,
                                                                  capsys):
    """I4 -- un `main` local en retard **degrade** le tirage, il ne le refuse pas.

    La mesure du 22/11 : `tapis_rapide.py` rend `TIRAGE REFUSE [MAIN_PERIME]`
    et sort en 4 des que le main local a **2** commits de retard -- et
    po-2028:CoursIA-2, a 123 commits de retard, n'a plus eu de picker du tout.

    Le contrat : le tirage rend une file **et** un avertissement. Un `main`
    perime, un cache ancien ou un organe lent degradent l'etalage ; ils ne
    peuvent pas rendre la file vide.

    Le test prend la CHAINE REELLE : la mesure est forcee (MAIN_FRESHNESS_FORCE
    + `mesurer` factice qui rend un ecart de 2 commits), la garde classifie,
    et le point d'entree du tapis decide. Il ne remplace pas le verdict par
    un fait-maison : c'est la classification qui est verifiee.
    """
    monkeypatch.setenv("MAIN_FRESHNESS_FORCE", "1")
    monkeypatch.setattr(main_freshness, "mesurer",
                        lambda depot, organes=None, run=None, echeance=None: {
                            "depot": str(depot), "branche": "main",
                            "ref_mesure": "refs/heads/main", "ecart": 2,
                            "organes_divergents": [], "cause": None,
                            "borne": False})
    pool = [_meta(4000 + k) for k in range(12)]
    code = tapis_rapide.main(["--lane", LANE, "--grains", "8", "--json"],
                              run=_run(pool))
    capture = capsys.readouterr()
    assert code == 0, "un main perime doit degrader le tirage, pas le refuser"
    rapport = json.loads(capture.out)
    assert rapport["grains"], "la file doit etre rendue malgre le main perime"
    assert rapport["fraicheur"]["degrade"] is True
    assert rapport["fraicheur"]["refuse"] is False
    assert [r["code"] for r in rapport["fraicheur"]["raisons_degradees"]] == ["MAIN_PERIME"]
    assert "TIRAGE DEGRADE [MAIN_PERIME]" in capture.err, "l'avertissement doit etre dit"


# --- I5 -- les exclusions en donnees -------------------------------------------

def test_I5_une_pause_posee_en_donnees_est_respectee_par_tous_les_tirages():
    """I5 -- les exclusions dures sont des **donnees**, pas de la memoire.

    Le mandat accepte « fichier ou label » : ce test prend le **label**, qui
    voyage avec l'issue et se voit dans GitHub. Une pause posee une fois doit
    ecarter le grain, comme le fait deja le label `candidate-delivered`
    (regle LABEL de `tapis_rapide._decider`).

    Etat au 22/11 : aucune des neuf regles ne lit un label de pause -- les
    pauses du 22/11 (politique Rust, parites C#/Rust) etaient filtrees a la
    main, par regex de titre, par la seule memoire d'un agent.

    Etat au 23/11 (ce PR) : la regle LABEL lit la **table** des labels
    d'exclusion (`coordination/tapis_labels.py`) -- l'urne et la pause. Le
    marqueur `xfail` est leve : le test passe, et le CI le prouve.

    La voie **legere** (le tirage par defaut) est conduite ici aussi : c'est
    elle que la revue nomme. Un grain en pause ou livre ne doit pas y etre
    servi, et l'exclusion doit etre **publiee** (jamais silencieuse).
    """
    issues = [
        _issue(5001, "Grain libre"),
        _issue(5002, "Grain en pause", labels=("pause",)),
        _issue(5003, "Grain livre", labels=("candidate-delivered",)),
    ]
    lecture = gh_bulk.Lecture(issues=issues, prs=[], citations={},
                               lu_a="2026-11-22T20:00:00Z", secondes=0.1, appels=1)
    etats_ = {e.numero: e for e in tapis_rapide.etats(lecture, LANE, NOW)}
    assert etats_[5001].ecart is None, "un grain libre doit rester servable"
    assert etats_[5002].ecart is not None, \
        "une pause posee en donnees (label) doit ecarter le grain"
    assert etats_[5003].ecart is not None, \
        "un grain livre (label) doit ecarter le grain"

    # --- la voie LEGERE : le tirage par defaut -------------------------------
    pool = [_meta(5101, "Grain libre"),
            _meta(5102, "Grain en pause", labels=("pause",)),
            _meta(5103, "Grain livre", labels=("candidate-delivered",))]
    rapport, code = tapis_leger.tirage(LANE, 8, NOW, 45, "graine", Path("."),
                                       _run(pool))
    assert code == 0
    numeros = [g["numero"] for g in rapport["grains"]]
    assert 5101 in numeros, "le grain libre doit etre servi par la voie legere"
    assert 5102 not in numeros, \
        "une pause posee en donnees ne doit pas etre servie par la voie legere"
    assert 5103 not in numeros, \
        "un grain livre (label) ne doit pas etre servi par la voie legere"
    ecartees = rapport.get("ecartees", {}).get("LABEL", [])
    assert {e["numero"] for e in ecartees} == {5102, 5103}, \
        "l'exclusion doit etre publiee, jamais silencieuse"


# --- I6 -- la borne de temps ---------------------------------------------------

def test_I6_le_budget_global_du_tirage_est_borne_a_60_s():
    """I6 -- un tirage de lane rend en moins de 60 s.

    Les budgets **declares** des etages du chemin de lane doivent tenir dans
    la borne du contrat :

    - selection : `gh_selection.MUR_GLOBAL_S` = 30 s ;
    - citations : `gh_bulk.TIMEOUT_S` = 15 s ;
    - PRs ouvertes : `gh_bulk.TIMEOUT_S` = 15 s.

    Soit 60 s de budgets pour un contrat de 60 s. Et la borne n'est pas un
    voeu : le tirage pose UNE echeance monotone (`gh_bulk.MUR_TIRAGE_S`),
    partagee par ses etages -- le temps restant est recalcule avant chaque
    appel, donc un etage qui a consomme sa part voit l'etage suivant etre
    coupe plutot qu'attendu.

    Etat au 22/11 : les budgets cumulaient 240 s (60 + 90 + 90) et chaque
    etage avait sa propre echeance. D'ou le marqueur.
    """
    budgets = {"selection": gh_selection.MUR_GLOBAL_S,
               "citations": gh_bulk.TIMEOUT_S,
               "prs_ouvertes": gh_bulk.TIMEOUT_S}
    assert sum(budgets.values()) <= 60, \
        f"budgets cumules {budgets} : {sum(budgets.values())} s pour 60 s"


def test_I6_un_etage_qui_depasse_son_budget_est_coupe_et_non_attendu():
    """I6 -- un etage lent est coupe, pas attendu.

    Le mecanisme existe pour la selection : un `run` qui depasse le budget
    leve `LectureIncomplete` (jamais une liste a moitie). Ce test le prouve,
    et pose la forme que le noyau consolide doit generaliser a tous les etages.
    """
    def run(argv, timeout):
        time.sleep(1.0)  # le faux ignore le timeout : il rend tard
        return ""

    with pytest.raises(gh_bulk.LectureIncomplete):
        gh_selection.lire_metadonnees_issues(run, budget_s=0.1)


# --- I7 -- consolidation puis anciennete ---------------------------------------

def test_I7_dans_les_etages_fins_la_consolidation_passe_devant_l_anciennete():
    """I7 -- l'ordre des etages fins est « consolidation, puis anciennete ».

    Scenario discriminant : une issue de consolidation **recente** contre une
    issue ordinaire **ancienne** (200 j, bonus d'age plein). Le contrat dit
    que la consolidation passe devant.

    Le tirage du 22/11 sert ce contrat : la selection par age ramene les
    issues anciennes, sans reprendre le pas sur la priorite de consolidation
    que la classification et la rotation tiennent en amont. Le marqueur
    `xfail(strict)` pose le 22/11 est donc leve -- il decrivait l'ancien
    empilement de `tapis_avantages.bonus_dixiemes`, que le tirage n'ordonne
    plus.

    L'etage **rapide** suit la meme regle (test dans
    `scripts/tests/test_tapis_equilibre.py`) : avant ce PR, les deux bonus
    s'additionnaient et l'anciennete pleine l'emportait.
    """
    pool = [
        _meta(6001, "Ancienne ordinaire",
              cree=(NOW - timedelta(days=200)).strftime("%Y-%m-%dT%H:%M:%SZ")),
        _meta(6002, "Consolidation recente", cree="2026-11-21T00:00:00Z",
              labels=("consolidation",)),
    ]
    rapport, code = tapis_leger.tirage(LANE, 8, NOW, 45, "graine", Path("."),
                                       _run(pool))
    assert code == 0
    numeros = [g["numero"] for g in rapport["grains"]]
    assert 6002 in numeros and 6001 in numeros, \
        "les deux issues doivent etre servies au meme tour"
    assert numeros.index(6002) < numeros.index(6001), \
        "la consolidation passe devant l'anciennete"
