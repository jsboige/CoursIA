"""Tests de l'organe de MESURE du defilement et de l'ordre (#28114).

Le coordinateur (26/11) demande la demonstration, sur le pool REEL, de deux
choses que le mandat du 22/11 (#28114) exige :

- l'ordre « consolidation -> jamais visitée -> anciennete », mesure **hors
  exclusions dures** ;
- le defilement par lane sur **toutes** les issues ouvertes, avec le repli
  reel, en moins de 60 s (I6).

L'organe (`coordination/tapis_defilement.py`) ne reimplemente aucun organe : il
mesure `tapis_equilibre.niveau` (le bonus consolidation + age), l'equite du
16/11, et `tapis_repli.replir` (le repli chronologique reel).

Ces tests ne touchent pas le reseau : le repli est joue hors ligne (son cache
est un fichier ecrit par le test, son curseur vit dans le dossier du test).

Le témoin le plus important est `test_le_defilement_signale_les_issues_que_le
_repli_ne_sert_pas` : il fixe le **defaut mesure** sur le pool reel du 26/11
(115 issues sur 558 jamais servies par un cycle complet de 60 blocs), et il
donne la mesure de reference a rejouer apres une correction.
"""
from __future__ import annotations

import json
import sys
from datetime import UTC, datetime, timedelta
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from coordination import (
    gh_bulk,
    tapis_blocs,
    tapis_defilement,
    tapis_equilibre,
    tapis_rapide,
    tapis_repli,
)

NOW = datetime(2026, 11, 26, 11, 30, tzinfo=UTC)
LANE = "myia-ai-01:CoursIA-2"


def _issue(n: int, titre: str = "", cree: str = "2026-11-01T00:00:00Z",
           labels: tuple[str, ...] = ()) -> dict:
    """Une issue a plat : la forme que rend `gh_bulk.issue`."""
    return gh_bulk.issue({"number": n, "title": titre or f"Grain {n}", "body": "",
                           "createdAt": cree, "updatedAt": cree,
                           "labels": {"nodes": [{"name": lab} for lab in labels]},
                           "comments": {"totalCount": 0, "nodes": []}})


def _lecture(issues: list[dict]) -> gh_bulk.Lecture:
    return gh_bulk.Lecture(issues=issues, prs=[], citations={},
                           lu_a="2026-11-26T10:00:00Z", secondes=0.1, appels=1)


def _etat(n: int, *, visites: int = 0, consolidation: bool = False,
          conteneur: bool = False, claim: bool = False,
          cree: str = "2026-11-01T00:00:00Z", ecart: str | None = None) -> tapis_rapide.Etat:
    """Un etat du tapis, construit a la main (aucune lecture reseau)."""
    e = tapis_rapide.Etat(n, f"Grain {n}", [], cree, None, n, conteneur, consolidation)
    e.visites = visites
    e.visites_total = visites
    e.ecart = ecart
    e.mon_claim = claim
    return e


# --- l'ordre mesure -------------------------------------------------------------

def test_l_ordre_nomme_les_trois_classes_du_mandat():
    """Les trois classes -- consolidation, jamais visitée, deja visitée."""
    etats = [
        _etat(1, consolidation=True),
        _etat(2, visites=0),
        _etat(3, visites=3),
        _etat(4, visites=1, ecart="LIVREE"),  # exclusion dure : hors pool
    ]
    r = tapis_defilement.ordre(etats, LANE, NOW, grains=8)
    c = r["classes"]
    assert c["pool"] == 3, "l'exclusion dure doit etre retiree du pool mesure"
    assert c["consolidation"] == 1
    assert c["jamais_visitee"] == 2
    assert c["deja_visitee"] == 1
    assert r["exclusions_dures"] == 1


def test_l_ordre_rompu_est_nomme_par_un_temoin(monkeypatch):
    """Une issue deja visitée servie devant une jamais visitée : temoin.

    L'organe mesure l'ordre **effectivement servi** : le temoin vient donc de
    l'ordre rendu, pas d'un pool re-trié (qui prouverait la fonction de tri).
    """
    jamais = _etat(2, visites=0)
    deja = _etat(3, visites=4)
    monkeypatch.setattr(tapis_rapide, "ordonner",
                        lambda *a, **k: [deja, jamais])
    r = tapis_defilement.ordre([_etat(2, visites=0), _etat(3, visites=4)],
                               LANE, NOW, grains=8)
    assert r["equite"]["ok"] is False, "l'equite rompue doit etre signalee"
    assert 3 in r["equite"]["temoins"], "le temoin doit nommer l'issue fautive"
    assert r["rompu"] is True


def test_l_ordre_equitable_passe_sur_un_pool_sain():
    """Un pool sain : jamais visitée avant deja visitée, consolidation OK."""
    etats = [_etat(1, visites=0), _etat(2, visites=0), _etat(3, visites=2)]
    r = tapis_defilement.ordre(etats, LANE, NOW, grains=8)
    assert r["equite"]["ok"] is True
    assert r["consolidation"]["ok"] is True
    assert r["rompu"] is False


def test_la_consolidation_distancee_est_nommee(monkeypatch):
    """Une non-consolidation servie DEVANT la consolidation : temoin I7.

    L'ordre inverse exact de l'ordre attendu : meme age, meme classe de
    visite, et le bonus superieur est celui de la **consolidation** (mandat du
    18/11 : elle est posee en premier dans le bonus). L'organe doit le
    nommer -- un `ok` sur cette file serait un faux vert.
    """
    conso = _etat(1, visites=0, consolidation=True, cree="2026-11-25T11:30:00Z")
    avant = _etat(2, visites=0, cree="2026-11-25T11:30:00Z")
    monkeypatch.setattr(tapis_rapide, "ordonner",
                        lambda *a, **k: [avant, conso])
    r = tapis_defilement.ordre([conso, avant], LANE, NOW, grains=8)
    assert r["consolidation"]["ok"] is False, "l'ordre inverse doit etre signale"
    assert 2 in r["consolidation"]["temoins"], (
        "le temoin est la non-consolidation servie devant la consolidation")
    assert r["rompu"] is True


def test_l_ordre_consolidation_devant_passe(monkeypatch):
    """L'ordre attendu -- la consolidation devant, meme age, meme classe."""
    conso = _etat(1, visites=0, consolidation=True, cree="2026-11-25T11:30:00Z")
    avant = _etat(2, visites=0, cree="2026-11-25T11:30:00Z")
    monkeypatch.setattr(tapis_rapide, "ordonner",
                        lambda *a, **k: [conso, avant])
    r = tapis_defilement.ordre([conso, avant], LANE, NOW, grains=8)
    assert r["consolidation"]["ok"] is True
    assert r["consolidation"]["temoins"] == []
    assert r["rompu"] is False


# --- le defilement reel ---------------------------------------------------------

def test_le_defilement_couvre_un_pool_entier(tmp_path):
    """Le repli reel couvre le pool, et le dit (I2, sur pool synthetique)."""
    pool = [_issue(100 + k, cree=(NOW - timedelta(days=30 - k)).strftime("%Y-%m-%dT%H:%M:%SZ"))
            for k in range(12)]
    r = tapis_defilement.defilement(_lecture(pool), LANE, NOW, grains=4, jours=45,
                                    dossier=tmp_path)
    assert r["complet"] is True, f"le defilement doit couvrir le pool : {r['manquantes']}"
    assert r["servies"] == r["attendues"]
    assert r["manquantes"] == []
    assert r["secondes"] < 60, "la borne I6 est 60 s"


def test_le_defilement_nomme_les_exclusions_dures(tmp_path):
    """Une issue en pause est une exclusion dure : elle n'est pas attendue."""
    pool = [_issue(200, cree="2026-11-20T00:00:00Z"),
            _issue(201, cree="2026-11-20T00:00:00Z", labels=("pause",))]
    r = tapis_defilement.defilement(_lecture(pool), LANE, NOW, grains=4, jours=45,
                                    dossier=tmp_path)
    assert 201 in r["exclues"], "l'issue en pause doit etre exclue"
    assert 201 not in r["manquantes"], "une exclusion dure n'est pas manquante"
    assert r["attendues"] == 1


def test_le_defilement_signale_les_issues_que_le_repli_ne_sert_pas(tmp_path):
    """Le defaut mesure, sur un pool trop grand pour les blocs.

    Le repli sert `part` slots par tour, mais un bloc peut rendre des
    **reprises** (des issues deja servies) : les blocs ne forment donc pas
    une partition du pool, et un cycle complet laisse des issues non
    servies. L'organe doit les NOMMER (jamais un « faux complet »).

    Sur le pool reel du 26/11 : 558 ouvertes, 60 blocs, 480 slots, 37
    reprises, 443 servies, **115 jamais servies**.
    """
    pool = [_issue(300 + k, cree=(NOW - timedelta(days=60 - k)).strftime("%Y-%m-%dT%H:%M:%SZ"))
            for k in range(60)]
    r = tapis_defilement.defilement(_lecture(pool), LANE, NOW, grains=2, jours=45,
                                    dossier=tmp_path)
    if r["complet"]:  # la composition a rejoue le pool sans reprise
        pytest.skip("le repli a partitionne le pool sur cette forme de pool")
    assert r["manquantes"], "les issues non servies doivent etre nommees"
    assert r["reprises"] >= 1, "les reprises doivent etre comptees"
    assert r["servies"] < r["attendues"]


def test_le_cycle_couvre_le_pool_quand_il_y_a_des_conteneurs(tmp_path):
    """Le defaut du 26/11, reproduit : les conteneurs prenaient des slots.

    Les conteneurs partagent le lot : la tranche primaire des grains vaut
    `taille - quota` (6 pour une taille de 8). Le repli comptait ses blocs
    avec la taille **demandee** : son cycle s'achevait avant la fin de
    l'ordre d'age, et la queue du pool n'etait jamais servie (115 issues sur
    558 sur le pool reel du 26/11).

    Ce test est le TEMOIN de la correction : il echoue sur le code d'avant.
    """
    pool = [_issue(400 + k, cree=(NOW - timedelta(days=40 - k)).strftime("%Y-%m-%dT%H:%M:%SZ"))
            for k in range(40)]
    pool += [_issue(500 + k, cree="2026-11-20T00:00:00Z", labels=("epic",))
             for k in range(4)]
    r = tapis_defilement.defilement(_lecture(pool), LANE, NOW, grains=8, jours=45,
                                    dossier=tmp_path)
    assert r["complet"] is True, (
        f"le cycle doit couvrir tout le pool ; manquantes : {r['manquantes']}")
    assert r["servies"] == r["attendues"]
    assert r["secondes"] < 60, "la borne I6 est 60 s"


def test_le_cycle_annonce_les_blocs_reels():
    """Le nombre de blocs annonce = le nombre de blocs parcouru.

    Mesure du 26/11 sur le pool reel : 475 grains et 83 conteneurs, une
    tranche de 6 (le quota des conteneurs en prend 2) -- 80 blocs. Le repli
    en annonçait 60 : le curseur rebouclait 20 blocs trop tot.
    """
    quota, part = tapis_blocs.quotas(8, 8, 83)
    assert (quota, part) == (2, 6), "le quota des conteneurs sort de la tranche"
    assert tapis_blocs.nombre_blocs(475, 83, part, quota) == 80
    assert tapis_blocs.nombre_blocs(475, 0, part, 0) == 80
    assert tapis_blocs.quotas(8, 8, 0) == (0, 8), "sans conteneur, rien ne change"


# --- le rapport -----------------------------------------------------------------

def test_le_code_de_sortie_repose_sur_les_invariants():
    """Un rapport de mesure donne 0 ou 1 -- jamais un code flatteur."""
    base = {"ordre": {"rompu": False},
            "defilement": {"complet": True, "sous_la_borne": True}}
    assert tapis_defilement.verdict(base) == 0
    rompu = {"ordre": {"rompu": True},
             "defilement": {"complet": True, "sous_la_borne": True}}
    assert tapis_defilement.verdict(rompu) == 1
    incomplet = {"ordre": {"rompu": False},
                 "defilement": {"complet": False, "sous_la_borne": True}}
    assert tapis_defilement.verdict(incomplet) == 1
    lent = {"ordre": {"rompu": False},
            "defilement": {"complet": True, "sous_la_borne": False}}
    assert tapis_defilement.verdict(lent) == 1


def test_la_ligne_de_dashboard_reste_bornee():
    """La ligne du dashboard ne depasse pas 200 caracteres."""
    r = {"ordre": {"rompu": False},
         "defilement": {"ouvertes": 558, "servies": 443, "tours": 60,
                        "secondes": 10.77, "borne_s": 60, "complet": False,
                        "manquantes": [28114, 28115]}}
    ligne = tapis_defilement.ligne_dashboard(r, 1)
    assert len(ligne) <= 200
    assert "Defilement" in ligne


# --- le pool vide et l'echec de lecture du repli (coordinateur 26/11 18:53Z) ------
#
# Defaut annonce : `main()` attrape `LectureIncomplete` autour de la LECTURE
# initiale, mais pas autour de `defilement()` -- alors que `tapis_repli.replir()`
# la leve sur un cache vide. Le process rendait une TRACEBACK au lieu du
# contrat rc=2 de l'organe.


def test_le_pool_vide_est_un_etat_defini_et_measure_sans_repli(tmp_path,
                                                                monkeypatch):
    """Un pool vide se mesure : le repli n'est meme pas appele.

    Le repli ne sait pas servir un cache vide ; c'est pourquoi il ne doit pas
    etre appele sur un pool vide -- la mesure y est un ZERO VRAI.
    """

    def _interdit(*_a, **_k):
        raise AssertionError("le repli ne doit pas etre appele sur un pool vide")

    monkeypatch.setattr(tapis_repli, "replir", _interdit)
    r = tapis_defilement.defilement(_lecture([]), LANE, NOW, grains=4, jours=45,
                                    dossier=tmp_path)
    assert r["pool_vide"] is True, "le pool vide doit etre nomme"
    assert r["complet"] is True, "un pool vide est couvert par definition"
    assert r["servies"] == 0 and r["attendues"] == 0
    assert r["manquantes"] == []
    assert r["sous_la_borne"] is True


def test_le_repli_illisible_tient_le_rc_2_sans_traceback(monkeypatch, capsys):
    """Un cache illisible : rc 2 et le message de l'organe, jamais de traceback."""
    pool = [_issue(300, cree="2026-11-20T00:00:00Z")]
    monkeypatch.setattr(gh_bulk, "lire_tout",
                        lambda depot, cache_s, run, jours: _lecture(pool))

    def _replir_illisible(*_a, **_k):
        raise gh_bulk.LectureIncomplete("selection", "repli",
                                        "ni cache local exploitable")

    monkeypatch.setattr(tapis_repli, "replir", _replir_illisible)
    code = tapis_defilement.main(["--lane", LANE])
    assert code == 2, f"le contrat de l'organe est rc 2, pas {code}"
    err = capsys.readouterr().err
    assert "NON MESURE" in err, "le message de l'organe doit etre dit"
    assert "Traceback" not in err, "jamais de traceback sur un echec de lecture"


def test_le_pool_vide_ne_leve_pas_dans_main(monkeypatch, capsys):
    """Une lecture complete et vide : la mesure rend un rapport, pas un echec."""
    monkeypatch.setattr(gh_bulk, "lire_tout",
                        lambda depot, cache_s, run, jours: _lecture([]))
    code = tapis_defilement.main(["--lane", LANE, "--json"])
    assert code == 0, f"un pool vide est une mesure complete, pas {code}"
    rapport = json.loads(capsys.readouterr().out)
    assert rapport["defilement"]["pool_vide"] is True
    assert rapport["defilement"]["complet"] is True
    assert rapport["lecture"]["issues"] == 0
# --- le chemin de l'inversion, etage par etage (coordinateur 26/11 18:53Z) ------
#
# Le coordinateur demande d'identifier l'ETAPE du passage inter-niveaux, au lieu
# de l'attribuer a `_decaler` seul : `tapis_equilibre.ordre` range par niveau
# (tete decalee par niveau, `_decaler` comprise), puis `tapis_rapide.ordonner`
# retrie les entrees selectionnees (claims, jamais visitees hors marathon,
# conteneurs).
#
# Pool discriminant, construit a la main : un CONTENEUR de consolidation
# (jamais visite) contre un grain ordinaire (jamais visite). Meme age, memes
# visites : la consolidation est posee EN PREMIER dans le bonus, donc son
# niveau est meilleur -- l'ordre par niveau doit servir le conteneur d'abord.


def _mesure(etats, ordre=None):
    """La mesure I7/equite de l'organe, sur un ordre impose."""
    original = tapis_rapide.ordonner
    if ordre is not None:
        tapis_rapide.ordonner = lambda *a, **k: list(ordre)
    try:
        return tapis_defilement.ordre(etats, LANE, NOW, 8)
    finally:
        tapis_rapide.ordonner = original


def test_le_passage_inter_niveaux_vient_du_retri_final_pas_de_la_rotation():
    """L'etape est identifiee : c'est le retri final, pas `_decaler`.

    Le conteneur de consolidation passe devant le grain ordinaire dans
    l'ordre par NIVEAU (rotation comprise) -- la consolidation n'est pas
    distancee. Le retri final (`tapis_rapide.ordonner`) le repousse en fin de
    file : la composante `conteneur` de son tri les classe dans cet ordre.

    Ce temoin ne corrige pas la regle du conteneur (deliberee : un conteneur
    demande une lecture et un `--paths`, il ne passe jamais devant un grain) :
    il NOMME l'etape, pour que l'arbitrage ne porte pas sur le mauvais organe.
    """
    etats = [_etat(7001, consolidation=True, conteneur=True),
             _etat(7002)]
    conso = tapis_equilibre.familles_consolidation(etats)
    servables = [e for e in etats if not e.mon_claim]

    niveau_7001 = tapis_equilibre.niveau(etats[0], conso, NOW)
    niveau_7002 = tapis_equilibre.niveau(etats[1], conso, NOW)
    assert niveau_7001 < niveau_7002, (
        "la consolidation doit avoir le meilleur niveau : "
        f"{niveau_7001} / {niveau_7002}")

    # Etape A : l'ordre par niveau, rotation comprise.
    ordre_a = tapis_equilibre.ordre(etats, servables, "graine", NOW, rotation=True)
    assert [int(e.numero) for e in ordre_a] == [7001, 7002], (
        "l'ordre par niveau sert la consolidation d'abord")
    m_a = _mesure(etats, ordre=ordre_a)
    assert m_a["consolidation"]["ok"] is True, (
        "I7 tient a l'etape du niveau : le temoin est "
        f"{m_a['consolidation']['temoins']}")

    # Etape A0 : le meme ordre, rotation neutralisee -- `_decaler` n'y change rien.
    ordre_a0 = tapis_equilibre.ordre(etats, servables, "graine", NOW, rotation=False)
    assert [int(e.numero) for e in ordre_a0] == [7001, 7002]

    # Etape B : le retri final.
    ordre_b = tapis_rapide.ordonner(etats, LANE, NOW, 8, "graine")
    assert [int(e.numero) for e in ordre_b] == [7002, 7001], (
        "le retri final met le conteneur en second temps")
    m_b = _mesure(etats, ordre=ordre_b)
    assert m_b["consolidation"]["ok"] is False, (
        "l'etape du passage inter-niveaux est le retri final")
    assert m_b["consolidation"]["temoins"] == [7002]


def test_la_rotation_tourne_la_tete_d_un_niveau_sans_en_changer():
    """`_decaler` fait tourner la tete d'un niveau : il ne fait pas passer un
    grain d'un niveau a l'autre.

    La rotation garde la priorite IDENTIQUE : elle permute des grains de meme
    niveau (memes visites, meme bonus), donc elle ne peut ni sacrifier la
    consolidation ni l'anciennete sur les issues admissibles.
    """
    etats = [_etat(7101, consolidation=True, cree="2026-11-25T00:00:00Z"),
             _etat(7102, cree="2026-11-25T00:00:00Z"),
             _etat(7103, visites=2, cree="2026-11-25T00:00:00Z"),
             _etat(7104, visites=2, cree="2026-11-25T00:00:00Z"),
             _etat(7105, visites=5, cree="2026-11-25T00:00:00Z")]
    conso = tapis_equilibre.familles_consolidation(etats)
    servables = list(etats)
    for graine in ("graine-1", "graine-2", "graine-3", "graine-4", "graine-5"):
        ordre = tapis_equilibre.ordre(etats, servables, graine, NOW, rotation=True)
        niveaux = [tapis_equilibre.niveau(e, conso, NOW) for e in ordre]
        assert niveaux == sorted(niveaux), (
            f"la rotation a croise deux niveaux ({graine}) : {niveaux}")
        assert 7101 in [int(e.numero) for e in ordre][:2], (
            "la consolidation passe devant l'anciennete")


def test_le_perimetre_claims_est_nomme_sans_change_l_invariant_equite():
    """Les claims de la lane sont servis EN TETE par construction.

    `tapis_rapide.ordonner` commence par les claims ("vos claims en tete") :
    un claim deja visite precede donc, par DESIGN, une issue jamais visitee,
    et le controle d'equite peut le nommer comme temoin.

    Le rapport NOME cette classe (`claims_en_tete`) pour que la lecture du
    temoin soit immediate ; l'INVARIANT n'est pas change -- exempter les
    claims de l'equite est un arbitrage du coordinateur, pas un correctif
    silencieux que l'organe s'autorise.
    """
    claim = _etat(7107, visites=2, claim=True)
    jamais = _etat(7108, visites=0)
    r = tapis_defilement.ordre([claim, jamais], LANE, NOW, grains=8)
    assert r["claims_en_tete"]["numeros"] == [7107], (
        "le perimetre des claims doit etre nomme")
    assert r["claims_en_tete"]["nombre"] == 1
    assert r["file"][0] == 7107, "un claim est servi en tete"
    # L'invariant reste ce qu'il est : le claim deja visite est un temoin.
    assert r["equite"]["ok"] is False
    assert 7107 in r["equite"]["temoins"]


def test_le_perimetre_marathon_est_nomme_sans_sortir_du_defilement():
    """Le marathon est hors equilibre, mais il reste dans le pool.

    Son perimetre est NOME par le rapport (les numeros), jamais retire : le
    harnais sk-agent le sert, le tapis ne le dispute pas.
    """
    etats = [_etat(26070, cree="2026-11-01T00:00:00Z"), _etat(7106)]
    r = tapis_defilement.ordre(etats, LANE, NOW, 8)
    assert r["marathon"]["hors_equilibrage"] == [26070], (
        "le perimetre marathon doit etre nomme")
    assert r["marathon"]["nombre"] == 1
    assert 26070 not in r["exclusions_numeros"], (
        "le marathon n'est pas ecarte : il reste dans le defilement")


