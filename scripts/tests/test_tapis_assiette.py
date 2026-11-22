"""Tests de ``coordination.tapis_assiette`` -- la composition du pool (#25082).

Run: python -m pytest scripts/tests/test_tapis_assiette.py

Aucun test ne touche le reseau : les tirages sont des dictionnaires
construits en memoire, le journal est une liste d'enregistrements.
"""
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from coordination import tapis_acceptance, tapis_assiette, tirage_journal


def _tirage(lecture: dict, ecartees: dict) -> dict:
    return {"lane": "myia-ai-01:CoursIA-2", "lecture": lecture, "ecartees": ecartees}


def _record(numero: int, *, conteneur: bool | None = None,
            draw_id: str = "d1", mode: str = tapis_acceptance.MODE):
    extras = {"famille": numero, "consolidation": False}
    if conteneur is not None:
        extras["conteneur"] = conteneur
    return tirage_journal.TirageRecord.new(
        lane="myia-ai-01:CoursIA-2", candidates=[numero], retained=numero,
        urn=tapis_acceptance.URN, mode=mode, draw_id=draw_id, extras=extras)


def test_le_pool_separe_feuilles_et_conteneurs():
    """Le tirage du 21/11 : 29 servables, dont 28 conteneurs."""
    lecture = {"issues": 32, "servables": 29, "servables_feuilles": 1,
               "servables_conteneurs": 28}
    ecartees = {
        "COUVERTE": [{"numero": 10, "motif": "x", "feuille": True},
                     {"numero": 11, "motif": "x", "feuille": True}],
        "MERGEE": [{"numero": 12, "motif": "x", "feuille": False}],
    }
    m = tapis_assiette.mesurer_pool(_tirage(lecture, ecartees))
    assert m["feuilles"] == 3 and m["conteneurs"] == 29
    assert m["servables_feuilles"] == 1 and m["servables_conteneurs"] == 28
    assert m["part_feuilles_servables"] == 1 / 3
    assert m["code_qui_retient_les_feuilles"] == "COUVERTE"
    assert m["ecartees_par_code"]["COUVERTE"] == {"feuilles": 2, "conteneurs": 0}


def test_un_tirage_anterieur_ne_compte_pas_de_feuilles_au_poids():
    """Sans le flag feuille, l'entree est non mesuree -- jamais une feuille."""
    lecture = {"issues": 10, "servables": 2}
    ecartees = {"COUVERTE": [{"numero": 10, "motif": "x"}]}
    m = tapis_assiette.mesurer_pool(_tirage(lecture, ecartees))
    assert m["non_mesure"] == 1
    assert m["feuilles"] is None and m["conteneurs"] is None
    assert m["part_feuilles_servables"] is None


def test_le_service_compte_ce_qui_a_ete_servi():
    recs = [_record(1, conteneur=False), _record(2, conteneur=True, draw_id="d2")]
    m = tapis_assiette.mesurer_service(recs)
    assert m["tirages"] == 2 and m["grains"] == 2
    assert m["feuilles"] == 1 and m["conteneurs"] == 1
    assert m["part_feuilles"] == 0.5
    assert m["tirages_sans_feuille"] == 1


def test_le_rejeu_ne_compte_pas():
    recs = [_record(1, conteneur=False, mode="belt") for _ in range(10)]
    m = tapis_assiette.mesurer_service(recs)
    assert m["tirages"] == 0 and m["grains"] == 0
    assert m["part_feuilles"] is None


def test_les_grains_sans_le_flag_restent_hors_mesure():
    recs = [_record(1, conteneur=None), _record(2, conteneur=True)]
    m = tapis_assiette.mesurer_service(recs)
    assert m["grains"] == 2 and m["grains_mesures"] == 1
    assert m["grains_sans_mesure"] == 1
    assert m["feuilles"] == 0 and m["conteneurs"] == 1
