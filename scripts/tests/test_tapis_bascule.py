"""La BASCULE du tirage : la tranche PRIMAIRE et la REPRISE (19/11).

Le cas mesure par le coordinateur (DM du 19/11 10:54Z) : sur le pool 1..6,
tranche 2, #1 et #2 illisibles, la rotation se FIGEAIT sur [1, 2] -- #3
n'etait jamais propose, et le tour ne s'ouvrait plus. Cause : le tirage
deduisait le tour apres avoir filtre les inconnus, et l'ancre balayait la
reprise avec la primaire.

Ce que ces tests prouvent :

- la tranche **primaire** porte SEULE le curseur ; la **reprise** (les
  illisibles parkes) revient au service sans prendre sa place ;
- sur **trois tours** au moins, la primaire balaie tout le pool ;
- un pool **entierement illisible** reste COUVERT : tous les numeros sont
  servis sur les tours suivants, et le tour se rouvre ;
- la reprise revient aussi pour les **conteneurs** ;
- un `comments_total` **INCONNU** ne vaut pas zero : la fenetre n'est pas
  declaree fil complet, le fil complet se lit (fail-CLOSED).

Aucun test ne touche le reseau : le module est pur, l'etat d'ancre vit dans
un repertoire temporaire.
"""
from __future__ import annotations

import sys
from datetime import UTC, datetime
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from coordination import (gh_bulk, tapis_ancre, tapis_composition,  # noqa: E402
                          tapis_fenetre, tapis_fil_complet, tapis_rotation,
                          tapis_verdict)

pytestmark = pytest.mark.usefixtures("forbid_shell_escape")

MAINTENANT = datetime(2026, 11, 19, 10, 0, tzinfo=UTC)
LANE = "myia-ai-01:CoursIA-2"


class _Grain:
    """Un grain minimal : la rotation ne lit que son numero."""

    def __init__(self, numero: int, conteneur: bool = False):
        self.numero = numero
        self.titre = f"issue {numero}"
        self.visites = 0
        self.conteneur = conteneur
        self.notes: list[str] = []


def _etat_isole(tmp_path, monkeypatch):
    """L'etat d'ancre vit dans un repertoire temporaire : chaque test part
    d'un curseur neuf."""
    monkeypatch.setenv(tapis_ancre.ENV_ETAT, str(tmp_path))


def _tour(lane: str, illisibles: set[int], pool: int = 6, taille: int = 2,
          conteneurs: bool = False):
    """Rejoue un tour complet : bloc -> proposer -> avancer.

    Rend `(servis, primaire, reprise, etat)`.
    """
    grains = [_Grain(n) for n in range(1, pool + 1)]
    conts = ([_Grain(100 + n, conteneur=True) for n in range(1, 4)]
             if conteneurs else [])
    ancres = tapis_ancre.lire(lane)
    bloc, fenetre = tapis_rotation.bloc(grains, conts, pool, taille, lane,
                                         MAINTENANT, ancres=ancres)
    primaire = fenetre["primaires"]["grains"]
    reprise = fenetre["reprises"]["grains"]
    tapis_ancre.proposer(lane, "grains", primaire, reprise)
    servis = [g.numero for g in bloc]
    lus = {n for n in servis if n not in illisibles}
    ecartees = {n: {"code": "FIL_ILLISIBLE", "motif": "illisible"}
                for n in servis if n in illisibles}
    tapis_verdict.avancer(lane, lus, ecartees)
    return servis, primaire, reprise, tapis_ancre.lire(lane)


def test_la_primaire_balaie_le_pool_sur_trois_tours(tmp_path, monkeypatch):
    """Le cas du coordinateur : #1 et #2 illisibles, le pool continue.

    Contre-exemple mesure avant le correctif : les tours 4 a 8 servaient
    tous [1, 2], et #3, #4, #5, #6 n'etaient plus servis.
    """
    _etat_isole(tmp_path, monkeypatch)
    illisibles = {1, 2}
    primaires, servis = [], []
    for _ in range(4):
        serv, prim, _rep, etat = _tour(LANE, illisibles)
        primaires.append(sorted(prim))
        servis.append(serv)
        # La primaire porte SEULE le curseur : l'ancre est celle de la
        # primaire, jamais celle de la reprise.
        assert etat["grains"]["ancre"] == max(prim), \
            "le curseur suit la tranche primaire"
    assert set().union(*primaires) == {1, 2, 3, 4, 5, 6}, \
        "trois tours suffisent a balayer le pool"
    assert set().union(*servis) == {1, 2, 3, 4, 5, 6}, \
        "chaque numero du pool sort avec un verdict"


def test_la_reprise_revient_sans_prendre_la_place_de_la_primaire(
        tmp_path, monkeypatch):
    """Les illisibles parkes reviennent au service, par la REPRISE.

    La reprise est un canal distinct : elle s'ajoute au bloc, elle ne
    remplace pas la tranche que le curseur sert.
    """
    _etat_isole(tmp_path, monkeypatch)
    illisibles = {1, 2}
    _serv, _prim, reprise, etat = _tour(LANE, illisibles)
    assert reprise == [], "aucun illisible parke au premier tour"
    # Le tour suivant : #1 et #2 sont Illisibles, ils reviennent par la
    # reprise, et la primaire est une AUTRE tranche.
    _serv, prim, reprise, etat = _tour(LANE, illisibles)
    assert reprise == [2], "l'illisible parke revient par la reprise"
    assert 2 not in prim, "la reprise ne prend pas la place de la primaire"
    assert etat["grains"]["ancre"] == max(prim), \
        "le curseur suit la primaire, pas la reprise"


def test_un_pool_entierement_illisible_reste_couvert(tmp_path, monkeypatch):
    """Pool 1..6, TOUT illisible : la couverture ne s'arrete pas.

    Contre-exemple mesure avant le correctif : #3 et #4 n'etaient jamais
    servis, et le tour ne s'ouvrait plus.
    """
    _etat_isole(tmp_path, monkeypatch)
    illisibles = {1, 2, 3, 4, 5, 6}
    servis, tours = [], []
    for _ in range(6):
        serv, prim, _rep, etat = _tour(LANE, illisibles)
        servis.extend(serv)
        tours.append(etat["grains"]["tour"])
    assert set(servis) == {1, 2, 3, 4, 5, 6}, \
        "un pool entierement illisible reste couvert"
    assert tours[-1] > 0, "le tour se rouvre : le pool est couvert"


def test_l_ancre_ne_depasse_pas_la_primaire(tmp_path, monkeypatch):
    """Le curseur s'arrete a la PRIMAIRE : la reprise ne le pousse pas.

    Contre-exemple mesure (DM du 19/11) : le balayage prenait l'ensemble de
    l'attente, primaire ET reprise. La reprise portait le curseur jusqu'a son
    plus grand numero, la tranche suivante rebouclait, et le tour se
    refermait sur la meme tranche -- #3 et #4 n'etaient plus servis.
    """
    _etat_isole(tmp_path, monkeypatch)
    tapis_ancre.proposer(LANE, "grains", [1, 2], [5, 6])
    tapis_ancre.avancer(LANE, set(), {n: {"code": "FIL_ILLISIBLE",
                                           "motif": "illisible"}
                                       for n in (1, 2, 5, 6)})
    etat = tapis_ancre.lire(LANE)
    assert etat["grains"]["ancre"] == 2, \
        "l'ancre s'arrete a la primaire, pas a la reprise"


def test_l_ancre_ne_depasse_pas_la_primaire_decidee(tmp_path, monkeypatch):
    """Meme garantie quand la primaire est DECIDEE et la reprise illisible."""
    _etat_isole(tmp_path, monkeypatch)
    tapis_ancre.proposer(LANE, "grains", [3, 4], [5, 6])
    tapis_ancre.avancer(LANE, {3, 4}, {5: {"code": "FIL_ILLISIBLE",
                                            "motif": "illisible"},
                                    6: {"code": "FIL_ILLISIBLE",
                                        "motif": "illisible"}})
    etat = tapis_ancre.lire(LANE)
    assert etat["grains"]["ancre"] == 4, \
        "l'ancre s'arrete a la primaire decidee"


def test_le_trace_fige_du_coordinateur_ne_se_reproduit_plus(tmp_path,
                                                             monkeypatch):
    """Le trace mesure par le coordinateur : [1, 2] indefiniment.

    On rejoue l'etat decrit par le DM -- le pool a ete couvert, #1, #2, #5
    et #6 illisibles (les inconnus HISTORIQUES 5 et 6 sont la cause du gel)
    -- puis on exige que le tour suivant REPARTE.
    """
    _etat_isole(tmp_path, monkeypatch)
    illisible = {"code": "FIL_ILLISIBLE", "motif": "illisible"}
    tapis_ancre.proposer(LANE, "grains", [3, 4])
    tapis_ancre.avancer(LANE, {3, 4}, {})
    tapis_ancre.proposer(LANE, "grains", [5, 6])
    tapis_ancre.avancer(LANE, set(), {5: illisible, 6: illisible})
    tapis_ancre.proposer(LANE, "grains", [1, 2])
    tapis_ancre.avancer(LANE, set(), {1: illisible, 2: illisible})
    assert tapis_ancre.lire(LANE)["grains"]["ancre"] == 2, \
        "l'ancre s'arrete a la primaire [1, 2]"
    _serv, primaire, _rep, _etat = _tour(LANE, {1, 2, 5, 6})
    assert primaire == [3, 4], \
        "le tour repart : il ne ressert pas [1, 2] indefiniment"


def test_la_reprise_revient_aussi_pour_les_conteneurs():
    """Un conteneur illisible revient au service, lui aussi.

    Le bloc n'ajoutait la reprise qu'aux grains : le conteneur parke ne
    revenait jamais.
    """
    grains = [_Grain(n) for n in range(1, 7)]
    conts = [_Grain(100 + n, conteneur=True) for n in range(1, 4)]
    inc_c = {102: {"code": "FIL_ILLISIBLE", "motif": "illisible"}}
    b_g, b_c, primaires, reprises = tapis_composition.compose(
        grains, conts, 2, 1, None, None, {}, inc_c, 0, 0)
    assert [c.numero for c in b_c] == [101, 102], \
        "le conteneur illisible revient au service"
    assert reprises["conteneurs"] == [102], "il revient par la REPRISE"
    assert 102 not in primaires["conteneurs"], \
        "sans prendre la place de la tranche primaire"


def test_un_total_de_commentaires_inconnu_ne_vaut_pas_zero():
    """Fail-CLOSED : un total INCONNU ne s'acquitte pas.

    Avant la correction, `comments_total` absent etait lu comme 0, donc la
    fenetre etait declaree complete et le fil complet n'etait jamais lu.
    """
    assert tapis_fenetre.total_connus({}) is None
    assert tapis_fenetre.suffit({"comments": []}) is False, \
        "un total inconnu ne prouve pas la completude de la fenetre"
    assert tapis_fenetre.suffit({"comments_total": 0, "comments": []}) is True
    assert tapis_fenetre.suffit({"comments_total": 3, "comments": [1, 2, 3]}) \
        is True
    assert tapis_fenetre.suffit({"comments_total": 9, "comments": [1]}) is False


def test_le_producteur_ne_fabrique_pas_un_zero():
    """Le producteur ne masque plus l'absence par un zero.

    `gh_bulk.issue` mettait `comments_total: 0` quand la lecture ne donnait
    pas le total : le fail-CLOSED etait donc arme en aval mais coupe a la
    source. Desormais l'absence reste une absence, et c'est
    `tapis_fenetre.total_connus` qui en fait un INCONNU.
    """
    sans_total = gh_bulk.issue({"number": 7, "title": "grain", "body": "",
                                "createdAt": "", "updatedAt": "",
                                "labels": {"nodes": []}})
    assert sans_total["comments_total"] is None, \
        "l'absence reste une absence, pas un zero"
    assert tapis_fenetre.total_connus(sans_total) is None
    avec_total = gh_bulk.issue({"number": 8, "title": "grain", "body": "",
                                "createdAt": "", "updatedAt": "",
                                "labels": {"nodes": []},
                                "comments": {"totalCount": 4, "nodes": []}})
    assert avec_total["comments_total"] == 4
    assert tapis_fenetre.total_connus(avec_total) == 4


def test_le_fil_complet_se_lit_quand_le_total_est_inconnu(monkeypatch):
    """Le fil complet se lit, et son echec REFUSE le grain (fail-CLOSED).

    La fenetre dont on ignore la taille n'est pas le fil complet : la
    relecture du fil est donc due -- et une relecture impossible ne
    confirme rien.
    """
    appeles: list[int] = []

    def _fil(numero):
        appeles.append(numero)
        raise RuntimeError("fil illisible")

    monkeypatch.setattr(tapis_fil_complet.tapis_fenetre, "fil_complet", _fil)
    lecture = gh_bulk.Lecture(issues=[{"number": 7, "comments": [],
                                        "labels": [], "title": "grain"}],
                               prs=[])
    confirmes, rejetes, echecs, _appels = tapis_fil_complet.confirmer(
        [_Grain(7)], lecture, LANE, MAINTENANT, 45)
    assert appeles == [7], "le fil complet se lit : le total est inconnu"
    assert confirmes == [], "rien n'est confirme sans fil complet"
    assert [r["code"] for r in rejetes] == ["FIL_ILLISIBLE"]
    assert echecs == [7], "le grain refuse sort avec son code"


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-q"]))
