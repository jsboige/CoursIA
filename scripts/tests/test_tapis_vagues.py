"""Les VAGUES de la prise en charge : la file se remplit, ou le pool est vide.

Ce que ces tests prouvent :

- la qualification **ouvre la vague suivante** tant que la file n'est pas
  pleine (le cas mesure du 18/11 : les 24 candidats de la vague 0 sont tous
  ecartes -- servir 0 grain alors que le pool en contient serait un echec de
  methode) ;
- une vague est le **bloc suivant** du pool classe : sur un pool d'un multiple
  du bloc, deux vagues successives sont disjointes (la vague herite le
  retour-au-debut de la rotation, comme la fenetre) ;
- la file pleine **arrete** le balayage, et le plafond de vagues tient ;
- le **mur** (l'echeance) arrete les vagues comme il arrete la qualification :
  un refus, jamais un demi-resultat.

Aucun test ne touche le reseau : l'organe de qualification est simule.
"""
from __future__ import annotations

import sys
from datetime import UTC, datetime
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from coordination import tapis_rotation, tapis_vagues  # noqa: E402

pytestmark = pytest.mark.usefixtures("forbid_shell_escape")

MAINTENANT = datetime(2026, 11, 18, 17, 20, tzinfo=UTC)
LANE = "myia-ai-01:CoursIA-2"
GRAINS = 8
TAILLE = 24  # le bloc servi : 3 x grains, comme le tirage leger


class _Grain:
    """Un grain minimal : l'ordre classe ne lit que son numero."""

    def __init__(self, numero: int):
        self.numero = numero
        self.titre = f"issue {numero}"
        self.visites = 0
        self.conteneur = False
        self.notes: list[str] = []


def _simule(accepte: set[int], arrete: bool = False):
    """Un organe de qualification simule : il refuse tout sauf `accepte`.

    Il note aussi les candidats recus, vague par vague : les tests verifient
    ainsi que les vagues sont disjointes.
    """
    vus: list[list[int]] = []

    def _q(candidats, lane, maintenant, jours, prs, citations, run,
           echeance=None, lot=50, horloge=None, debut=None):
        vus.append(list(candidats))
        servis = [_Grain(n) for n in candidats if n in accepte]
        ecartes = {n: {"numero": n, "code": "LABEL", "motif": "simule"}
                   for n in candidats if n not in accepte}
        chrono = {"secondes": 0.1,
                  "premier_servable_s": 0.1 if servis else None}
        return servis, ecartes, [], arrete, 1, chrono

    _q.vus = vus
    return _q


def _ordre(n: int) -> list[_Grain]:
    return [_Grain(1000 + i) for i in range(n)]


def _vagues(accepte: set[int], monkeypatch, max_vagues: int = 4,
            arrete: bool = False, pool: int = 48, grains: int = GRAINS):
    """Les vagues sur un pool de `pool` grains, sans reseau."""
    simule = _simule(accepte, arrete)
    monkeypatch.setattr(tapis_vagues.tq, "qualifier", simule)
    servis, ecartees, rapport = tapis_vagues.vagues(
        _ordre(pool), [], LANE, MAINTENANT, 45, [], None, grains,
        max_vagues, taille=TAILLE, echeance=None, debut=0.0)
    return servis, ecartees, rapport, simule


def test_la_vague_suivante_ouvre_la_file(monkeypatch):
    """La vague 0 entierement ecartee ouvre la vague 1 : la file se remplit."""
    bloc1, _ = tapis_rotation.bloc(_ordre(48), [], GRAINS, TAILLE, LANE,
                                     MAINTENANT, bloc_suivant=1)
    accepte = {bloc1[0].numero}
    services, ecartees, rapport, _ = _vagues(accepte, monkeypatch, grains=1)
    assert rapport["vagues"][0]["servis"] == 0
    assert rapport["vagues"][1]["servis"] == 1
    assert [s.numero for s in services] == [bloc1[0].numero]
    assert ecartees, "les ecarts restent affiches"


def test_le_plafond_de_vagues_tient_la_file(monkeypatch):
    """Une file qui ne se remplit pas s'arrete au plafond : 4 vagues au plus."""
    _, _, rapport, _ = _vagues({1000}, monkeypatch)
    assert rapport["vagues_jouees"] == rapport["vagues_max"] == 4


def test_les_vagues_sont_disjointes(monkeypatch):
    """Sur un pool de trois blocs, trois vagues ne se recouvrent pas."""
    _, _, _, simule = _vagues(set(), monkeypatch, max_vagues=3, pool=72)
    vus = simule.vus
    assert len(vus) == 3
    for i in range(len(vus) - 1):
        assert not set(vus[i]) & set(vus[i + 1]), "deux vagues se recouvrent"


def test_la_file_pleine_arrete_le_balayage(monkeypatch):
    """Des que la file est pleine, aucune vague supplementaire n'est ouverte."""
    services, _, rapport, _ = _vagues(set(range(1000, 1100)), monkeypatch)
    assert rapport["vagues_jouees"] == 1
    assert len(services) >= GRAINS


def test_le_plafond_de_vagues_tient(monkeypatch):
    """Un pool qui ne donne rien ne fait pas balayer le pool entier."""
    services, ecartees, rapport, _ = _vagues(set(), monkeypatch, max_vagues=3)
    assert rapport["vagues_jouees"] == 3
    assert rapport["vagues_max"] == 3
    assert services == []
    assert ecartees, "les refus restent affiches"


def test_le_mur_arrete_les_vagues(monkeypatch):
    """Le mur (l'echeance) arrete les vagues : un refus, pas un demi-resultat."""
    _, _, rapport, _ = _vagues(set(), monkeypatch, arrete=True)
    assert rapport["vagues_jouees"] == 1
    assert rapport["vagues"][0]["servis"] == 0
