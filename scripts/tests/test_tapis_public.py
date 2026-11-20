#!/usr/bin/env python3
"""Les temoins de la FAMINE, mesures sur le LOT PUBLIC (revue du 19/11).

Le peer a mesure deux famines sur la voie publique :

- **cas A** : un pool de 80 grains, priorite decroissante, taille 40, un
  seul candidat lu par tour -> **4 numeros lus sur 80** en 400 tours ;
- **cas B** : 6 grains et 2 conteneurs, taille 2, un lu par tour ->
  6/6 grains mais **0/2 conteneurs** (le conteneur etait exilie en fin de
  lot, il n'avait donc jamais de tour).

Ces deux temoins sont **la** regression : ils se rejouent ici sur le lot
public (`coordination.tapis_public`), pas sur une reconstruction de la
mesure -- un temoin qui ne teste pas la voie reelle ne prouve rien.
"""
import sys
from datetime import UTC, datetime
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from coordination import tapis_ancre, tapis_public, tapis_verdict

LANE = "test:famine"
MAINTENANT = datetime(2026, 11, 19, 12, 0, tzinfo=UTC)


class Grain:
    """Le minimum qu'un grain doit porter pour composer un lot."""

    def __init__(self, numero: int, conteneur: bool = False):
        self.numero = numero
        self.conteneur = conteneur


def _tour(grains: list, conteneurs: list, n_grains: int, taille: int,
          budget: int) -> list[int]:
    """Un tour de lecture sur le lot PUBLIC : proposition, lecture, verdict."""
    lot, _ = tapis_public.lot_public(LANE, grains, conteneurs, n_grains,
                                      taille, MAINTENANT)
    lus = [g.numero for g in lot][:budget]
    tapis_verdict.avancer(LANE, {n: object() for n in lus}, {})
    return lus


def test_le_lot_public_couvre_le_pool_entier(monkeypatch, tmp_path):
    """Cas A : les 80 numeros du pool sont lus (le peer mesurait 4/80)."""
    monkeypatch.setenv(tapis_ancre.ENV_ETAT, str(tmp_path))
    pool = [Grain(n) for n in range(80, 0, -1)]
    lus: list[int] = []
    for _ in range(400):
        lus.extend(_tour(pool, [], 40, 40, 1))
    assert len(set(lus)) == 80, \
        f"le pool n'est pas couvert : {len(set(lus))}/80 lus en 400 tours"


def test_le_lot_public_donne_un_creneau_a_chaque_classe(monkeypatch, tmp_path):
    """Cas B : les 6 grains ET les 2 conteneurs sont lus (le peer mesurait 0/2)."""
    monkeypatch.setenv(tapis_ancre.ENV_ETAT, str(tmp_path))
    grains = [Grain(n) for n in range(1, 7)]
    conteneurs = [Grain(101 + n, conteneur=True) for n in range(2)]
    lus: list[int] = []
    for _ in range(40):
        lus.extend(_tour(grains, conteneurs, 2, 2, 1))
    lus = set(lus)
    assert {n for n in lus if n <= 6} == set(range(1, 7)), \
        "un grain n'a pas ete lu"
    assert {n for n in lus if n > 100} == {101, 102}, \
        "un conteneur n'a pas de creneau de lecture"
