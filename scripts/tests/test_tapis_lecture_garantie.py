"""La GARANTIE de LECTURE du pool : deux contre-epreuves (#27368).

Le coordinateur (19/11 14:21Z) a mesure deux contre-epreuves sur la tete
d'avant le correctif « creneau par classe » (6d11511e94524) :

1. 80 grains en priorite decroissante par numero, taille 40, un seul candidat
   confirme par tour : seuls 47, 48, 79 et 80 etaient lus ;
2. 6 grains (1..6) et 2 conteneurs (7..8), taille 2 : les 6 grains etaient
   lus, aucun conteneur.

Ces deux cas sont des WITESSAINS : ils echouent sur la tete d'avant et
passent sur la tete d'apres. Ils distinguent trois etats :

- PROPOSE : servi par le bloc ;
- FIL LU : confirme (le verdict de la lane) ;
- VERDICT : publie par la fenetre (visite / non visite).

Run : python -m pytest scripts/tests/test_tapis_lecture_garantie.py
"""
from __future__ import annotations

import sys
from datetime import UTC, datetime
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from coordination import tapis_ancre, tapis_public, tapis_verdict  # noqa: E402

pytestmark = pytest.mark.usefixtures("forbid_shell_escape")

MAINTENANT = datetime(2026, 11, 19, 12, 0, tzinfo=UTC)
LANE = "test:real-lot"
TOURS = 400


class _Grain:
    """Un grain minimal : la rotation ne lit que son numero."""

    def __init__(self, numero: int, conteneur: bool = False):
        self.numero = numero
        self.titre = "issue %d" % numero
        self.visites = 0
        self.conteneur = conteneur
        self.notes: list[str] = []


def _rejouer(grains, conteneurs, n_grains, taille):
    """Rejoue le chemin PUBLIC : bloc -> proposer -> avancer.

    Seul le PREMIER candidat du lot est confirme a chaque tour : c'est le
    budget de qualification du coordinateur. Rend `(proposes, lus, verdicts)`.
    """
    proposes, lus, verdicts = set(), set(), set()
    for _ in range(TOURS):
        ancres = tapis_ancre.lire(LANE)
        lot, fen = tapis_public.lot_public(LANE, grains, conteneurs,
                                            n_grains, taille, MAINTENANT,
                                            ancres=ancres)
        nums = [g.numero for g in lot]
        proposes.update(nums)
        verdicts.update(fen["visites"])
        verdicts.update(fen["non_visites"])
        confirmes = {nums[0]} if nums else set()
        lus.update(confirmes)
        tapis_verdict.avancer(LANE, confirmes, {})
    return proposes, lus, verdicts


def test_chaque_classe_a_un_creneau_de_lecture(tmp_path, monkeypatch):
    """CONTRE-EPREUVE 2 : 6 grains et 2 conteneurs, taille 2.

    Sur la tete d'avant, les 6 grains etaient lus et AUCUN conteneur : le
    bloc concatennait les conteneurs derriere des grains toujours presents.
    Un conteneur servi n'est pas un conteneur lu : la garantie porte sur le
    FIL LU, pas sur le service.
    """
    monkeypatch.setenv(tapis_ancre.ENV_ETAT, str(tmp_path))
    grains = [_Grain(n) for n in range(1, 7)]
    conteneurs = [_Grain(n, conteneur=True) for n in (7, 8)]
    proposes, lus, verdicts = _rejouer(grains, conteneurs, 6, 2)

    assert {1, 2, 3, 4, 5, 6} <= lus, "les grains doivent etre lus"
    assert {7, 8} <= lus, ("un conteneur servi sans etre lu : le creneau par "
                           "classe a disparu")
    assert {7, 8} <= verdicts, "chaque numero sort avec un verdict"
    assert proposes >= lus, "on ne lit que ce qui est servi"


def test_le_pool_entier_est_lus_meme_en_priorite_decroissante(tmp_path,
                                                              monkeypatch):
    """CONTRE-EPREUVE 1 : 80 grains en priorite decroissante, taille 40.

    Sur la tete d'avant, seuls 47, 48, 79 et 80 etaient lus : la file de
    reprise saturait a 32 et le curseur passait au max de la tranche.
    """
    monkeypatch.setenv(tapis_ancre.ENV_ETAT, str(tmp_path))
    grains = [_Grain(n) for n in range(80, 0, -1)]
    proposes, lus, verdicts = _rejouer(grains, [], 80, 40)

    assert set(range(1, 81)) <= lus, ("le pool n'est pas entierement lu : "
                                       "la famine du tapis est revenue")
    assert set(range(1, 81)) <= verdicts, "chaque numero sort avec un verdict"
