"""L'echeance monotone unique du tirage (#28114, I6).

Le contrat I6 veut qu'un tirage de lane rende en moins de 60 s, et que la
borne soit une **propriete du code**, pas un voeu : une echeance unique,
posee une fois, partagee par les etages, et le temps restant recalcule
avant chaque appel.

Ces tests ne touchent ni le reseau ni l'horloge de la machine : l'horloge
est un faux que l'on fait avancer a la main, et les etages sont des stubs
qui rendent l'echeance qu'ils recoivent.

Sans parent : ce fichier est le TEMOIN de l'invariant I6 du contrat du
picker (`scripts/tests/test_picker_contract_28114.py`), pas un module de
production.
"""

from __future__ import annotations

import json
import sys
from datetime import UTC, datetime
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from coordination import gh_bulk, gh_issues, gh_selection, tapis_leger

LANE = "myia-ai-01:CoursIA-2"
NOW = datetime(2026, 11, 22, 21, 0, tzinfo=UTC)


class _Horloge:
    """Une horloge qu'on fait avancer a la main."""

    def __init__(self, depart: float = 100.0):
        self.t = depart

    def __call__(self) -> float:
        return self.t

    def avancer(self, secondes: float) -> None:
        self.t += secondes


def test_sans_echeance_le_plafond_de_l_appel_s_applique_seul():
    """Un appel isole garde son propre plafond."""
    assert gh_bulk._timeout(None) == gh_bulk.TIMEOUT_S
    assert gh_bulk._timeout(None, gh_bulk.FETCH_TIMEOUT_S) == gh_bulk.FETCH_TIMEOUT_S


def test_le_timeout_tient_le_plus_petit_du_plafond_et_du_temps_restant():
    horloge = _Horloge()
    echeance = horloge() + 10.0
    # Le temps restant (10 s) est plus serre que le plafond de l'appel (15 s).
    assert gh_bulk._timeout(echeance, horloge=horloge) == 10
    horloge.avancer(8.0)
    assert gh_bulk._timeout(echeance, horloge=horloge) == 2


def test_une_echeance_epuisee_laisse_une_seconde_pas_zero():
    """Jamais zero : un appel coupe a zero ne rendrait rien du tout."""
    horloge = _Horloge()
    echeance = horloge()
    horloge.avancer(30.0)
    assert gh_bulk._timeout(echeance, horloge=horloge) == 1


def test_les_etages_partagent_le_meme_chronometre():
    """L'etage suivant ne repart pas de zero : il herite du temps restant."""
    horloge = _Horloge()
    echeance = horloge() + gh_bulk.MUR_TIRAGE_S
    assert gh_bulk._timeout(echeance, horloge=horloge) == gh_bulk.TIMEOUT_S
    horloge.avancer(45.0)  # la selection a pris 45 s
    assert gh_bulk._timeout(echeance, horloge=horloge) == gh_bulk.TIMEOUT_S
    horloge.avancer(10.0)  # les citations ont pris 10 s
    assert gh_bulk._timeout(echeance, horloge=horloge) == 5


def test_le_tirage_passe_une_echance_unique_aux_trois_etages(monkeypatch):
    """Les trois etages recoivent la MEME echeance, et elle existe."""
    vus: list = []

    def _capture(cle):
        def faux(*args, **kwargs):
            vus.append(kwargs.get("echeance"))
            return cle
        return faux

    monkeypatch.setattr(gh_selection, "lire_metadonnees_issues",
                        lambda *a, **k: (_capture([])(*a, **k), 0.1))
    monkeypatch.setattr(gh_bulk, "lire_citations_mergees", _capture({}))
    monkeypatch.setattr(gh_bulk, "lire_prs_ouvertes", _capture([]))

    tapis_leger.classer(LANE, NOW, 45, "graine", Path("."))

    assert len(vus) == 3, "les trois etages du tirage doivent etre appeles"
    assert all(e is not None for e in vus), "chaque etage recoit une echeance"
    assert len(set(vus)) == 1, "les etages partagent UNE echeance, pas trois"


def test_un_appel_qui_porte_des_corps_garde_le_plafond_large():
    """Les lectures qui portent des corps ne sont pas coupees par le plafond court.

    Mesure du 23/11 sur ce siege : la page du pool (50 issues, corps + 12
    commentaires) dure **3,76 s**, la qualification d'un lot de 50 dure
    **2,05 s**, la page de metadonnees (sans corps) **0,78 s**. Le plafond
    court (15 s, celui des appels de metadonnees) couperait les deux
    lectures longues sur un reseau lent -- sans mesure derriere : elles
    gardent le plafond large, la mesure a l'appui.
    """
    vus: list = []

    def faux(argv, timeout):
        vus.append(timeout)
        return json.dumps({"data": {"repository": {"issues": {
            "pageInfo": {"hasNextPage": False}, "nodes": []}}}})

    gh_bulk._page_issues(faux, "jsboige/CoursIA", None, 1)

    assert vus, "la page du pool doit etre lue"
    assert all(t == gh_bulk.TIMEOUT_S_CORPS for t in vus), \
        "la page du pool garde le plafond large"
    assert gh_bulk.TIMEOUT_S_CORPS >= gh_bulk.TIMEOUT_S


def test_la_qualification_d_un_lot_garde_le_plafond_large():
    """La qualification ciblee (corps + 12 commentaires) aussi."""
    vus: list = []

    def faux(argv, timeout):
        vus.append(timeout)
        return json.dumps({"data": {"repository": {"i0": {"number": 1}}}})

    lues = gh_issues.lire_champs(faux, "jsboige/CoursIA", [1], "number",
                                 "qualification")

    assert lues, "le lot doit etre lu"
    assert vus == [gh_bulk.TIMEOUT_S_CORPS], \
        "la qualification garde le plafond large"
