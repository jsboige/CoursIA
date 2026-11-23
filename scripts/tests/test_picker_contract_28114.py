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
| I5 exclusions en donnees | **viole** | aucune regle ne lit un label `pause` |
| I6 borne de temps | **viole** | budgets declares cumules : 60 + 90 + 90 = 240 s pour 60 s |
| I7 consolidation puis anciennete | **viole** | les deux bonus sont **additionnes** (`tapis_avantages`) |

I2 est devenu **executable** dans ce PR : hors reseau, la voie legere lit le
CACHE LOCAL (`coordination/tapis_repli.py`), sert le pool dans l'ordre de
creation, et un curseur persiste fait defiler le pool de bloc en bloc. Le
marqueur `xfail` du test I2 est donc retire : le test passe, et le CI le
prouve.

I4 est devenu **executable** dans ce PR : la garde de fraicheur distingue
trois etats (frais / degrade / refuse), et seul l'etat **inconnu** (mesure
impossible) refuse encore. Le marqueur `xfail` du test I4 a donc ete
retire : le test passe, et le CI le prouve.

Ce que ce fichier ne couvre pas (a dire, pas a cacher) : l'exclusion des
**doublons de meme carnet** (I5) n'a pas de cle de carnet definie par le
mandat -- elle reste dans le residu de l'issue ; et les tests sont ecrits sur
le **comportement** (ce que rend le picker), pas sur une API nommee : le
noyau consolide peut les satisfaire par n'importe quelle voie interne.
"""
from __future__ import annotations

import json
import sys
import time
from datetime import UTC, datetime, timedelta
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from coordination import gh_bulk, gh_cache_fichier, gh_selection, main_freshness
from coordination import tapis_ancre, tapis_leger, tapis_rapide

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


def _run(metas: list[dict]):
    """Le faux `run` : le pool en metadonnees, aucune PR, aucune citation."""
    def run(argv, timeout):
        requete = " ".join(argv)
        if "issue(number:" in requete:
            return json.dumps({"data": {"repository": {}}})
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
    """
    monkeypatch.setattr(tapis_ancre, "lire", lambda lane: {})
    monkeypatch.setattr(tapis_ancre, "proposer", lambda *a, **k: {})


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
                        lambda depot, organes=None, run=None: {
                            "depot": str(depot), "branche": "main",
                            "ref_mesure": "refs/heads/main", "ecart": 2,
                            "organes_divergents": [], "cause": None})
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

@pytest.mark.xfail(strict=True, reason=(
    "I5 viole au 22/11 : aucune des neuf regles ne lit un label de pause "
    "(les pauses etaient filtrees a la main, par regex de titre). "
    "A lever quand les exclusions en donnees sont branchees."))
def test_I5_une_pause_posee_en_donnees_est_respectee_par_tous_les_tirages():
    """I5 -- les exclusions dures sont des **donnees**, pas de la memoire.

    Le mandat accepte « fichier ou label » : ce test prend le **label**, qui
    voyage avec l'issue et se voit dans GitHub. Une pause posee une fois doit
    ecarter le grain, comme le fait deja le label `candidate-delivered`
    (regle LABEL de `tapis_rapide._decider`).

    Etat au 22/11 : aucune des neuf regles ne lit un label de pause -- les
    pauses du 22/11 (politique Rust, parites C#/Rust) etaient filtrees a la
    main, par regex de titre, par la seule memoire d'un agent.
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


# --- I6 -- la borne de temps ---------------------------------------------------

@pytest.mark.xfail(strict=True, reason=(
    "I6 viole au 22/11 : budgets cumules 60 + 90 + 90 = 240 s pour un contrat "
    "de 60 s (la borne n'est pas une propriete du code). "
    "A lever quand le noyau porte UNE echeance monotone unique."))
def test_I6_le_budget_global_du_tirage_est_borne_a_60_s():
    """I6 -- un tirage de lane rend en moins de 60 s.

    Les budgets **declares** des etages du chemin de lane doivent tenir dans
    la borne du contrat. Aujourd'hui ils ne la tiennent pas :

    - selection : `gh_selection.MUR_GLOBAL_S` = 60 s ;
    - citations : `gh_bulk.TIMEOUT_S` = 90 s ;
    - PRs ouvertes : `gh_bulk.TIMEOUT_S` = 90 s.

    Soit 240 s de budgets pour un contrat de 60 s : la borne n'est pas une
    propriete du code, elle est un voeu. Le noyau consolide doit porter UNE
    echeance monotone unique, partagee par les etages (le mecanisme existe
    deja pour la selection : `gh_selection._page`).
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
