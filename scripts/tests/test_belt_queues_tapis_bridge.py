#!/usr/bin/env python3
"""Tests for the bridge between ``belt_queues.py`` and the fast belt (14/11).

The coordinator's draw changed shape: the fast belt (``tapis_rapide.py --json``)
renders its grains under the key ``grains`` with the field names ``numero`` /
``titre`` / ``famille``, while the heavy belt (``pick_idle_grain.py --belt
--json``) renders them under ``picks``. The board reads both; ``record``
refuses a grain ``delivered`` in the queue of a worker lane (the closing urn
belongs to the coordinator, his adjoint and the secretary).

Measured cause (2026-11-14): 34 of the 40 grains drawn by the coordinator were
already delivered, and some of them went into worker queues.
Never calls ``gh``.
Run: python -m pytest scripts/tests/test_belt_queues_tapis_bridge.py
"""
from __future__ import annotations

import sys
from datetime import datetime, timezone
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "coordination"))

import belt_queues as bq  # noqa: E402

NOW = datetime(2026, 11, 14, 10, 0, tzinfo=timezone.utc)
WORKER = "myia-po-2023:CoursIA"
COORD = "myia-ai-01:CoursIA"


def _tapis(grains: list[dict]) -> dict:
    """Le JSON du tapis rapide, tel que `tapis_rapide.py --json` le rend."""
    return {"lane": COORD, "graine": "g", "grains": grains, "ecartees": {}}


def _grain(numero: int, *, famille: int = 900, titre: str = "grain",
           derniere_visite: str | None = "2026-11-01T08:00:00+00:00",
           consolidation: bool = False, klass: str | None = None) -> dict:
    g = {"rang": 1, "numero": numero, "titre": titre, "famille": famille,
         "parent": None, "conteneur": False, "notes": [], "consolidation": consolidation,
         "derniere_visite": derniere_visite, "priorite": []}
    if klass is not None:
        g["klass"] = klass
    return g


def _pick(n: int, *, title: str = "t", body: str = "", labels=None, genre: str = "docs",
          klass: str = "grain", created: str = "2026-09-01T00:00:00Z") -> dict:
    return {"number": n, "title": title, "body": body, "labels": labels or [],
            "genre": genre, "klass": klass, "idle": 0, "last_delivery_stamp": None,
            "last_claim_stamp": None, "created_at": created}


# --- le tableau lit les deux formes de tirage --------------------------------

def test_le_tapis_rapide_alimente_le_tableau():
    belt = _tapis([_grain(11), _grain(12, famille=901)])
    b = bq.board(belt, [WORKER], None, NOW)
    assert b["drawn"] == 2
    numeros = [it["number"] for g in b["families"] for it in g["items"]]
    assert sorted(numeros) == [11, 12]


def test_la_famille_vient_du_tapis():
    belt = _tapis([_grain(11, famille=900), _grain(12, famille=900),
                   _grain(13, famille=901)])
    b = bq.board(belt, [WORKER], None, NOW)
    familles = {g["family"]: len(g["items"]) for g in b["families"]}
    assert familles == {"#900": 2, "#901": 1}


def test_l_age_de_visite_vient_du_tapis():
    belt = _tapis([_grain(11, derniere_visite="2026-11-04T10:00:00+00:00")])
    b = bq.board(belt, [WORKER], None, NOW)
    item = b["families"][0]["items"][0]
    assert item["since_visit"] == 10.0


def test_le_tapis_lourd_reste_accepte():
    belt = {"picks": [_pick(21), _pick(22, title="[EPIC] racine")]}
    b = bq.board(belt, [WORKER], None, NOW)
    assert b["drawn"] == 2
    numeros = [it["number"] for g in b["families"] for it in g["items"]]
    assert sorted(numeros) == [21, 22]


def test_le_tapis_rapide_ne_declenche_pas_de_refus_de_famille():
    """Un grain du tapis rapide n'a pas de corps : la famille vient du tirage."""
    belt = _tapis([_grain(11, titre="MyIA.AI.Notebooks/ML/ML-04-Evaluation-Python")])
    b = bq.board(belt, [WORKER], None, NOW)
    assert b["families"][0]["family"] == "#900"


def test_l_absence_d_etat_origami_est_nommee():
    belt = _tapis([_grain(11)])
    b = bq.board(belt, [WORKER], None, NOW)
    assert b["origami_parking"]["measured"] is False
    assert "origami" in b["origami_parking"]["reason"]


# --- record : l'urne de cloture n'est pas celle d'un worker -------------------

def test_record_refuse_un_grain_delivered_dans_la_file_d_un_worker():
    belt = {"picks": [_pick(31, klass="delivered")]}
    with pytest.raises(ValueError) as exc:
        bq.record({"lanes": {WORKER: {"arc": "a", "queue": [31]}}}, belt, NOW)
    message = str(exc.value)
    assert "#31" in message
    assert WORKER in message
    assert "delivered" in message


def test_record_accepte_un_grain_delivered_pour_le_coordinateur():
    belt = {"picks": [_pick(31, klass="delivered")]}
    out = bq.record({"lanes": {COORD: {"arc": "a", "queue": [31]}}}, belt, NOW)
    assert out["lanes"][COORD]["queue"][0]["number"] == 31


def test_record_accepte_un_grain_normal_dans_la_file_d_un_worker():
    belt = {"picks": [_pick(32, klass="grain")]}
    out = bq.record({"lanes": {WORKER: {"arc": "a", "queue": [32]}}}, belt, NOW)
    assert out["lanes"][WORKER]["queue"][0]["number"] == 32


def test_le_refus_touche_la_seule_lane_worker():
    """Une repartition mixte est refusee sur la lane worker, pas sur l'autre."""
    belt = {"picks": [_pick(31, klass="delivered"), _pick(32, klass="grain")]}
    with pytest.raises(ValueError):
        bq.record({"lanes": {COORD: {"arc": "a", "queue": [31]},
                             WORKER: {"arc": "a", "queue": [32, 31]}}}, belt, NOW)


def test_record_accepte_le_tapis_rapide():
    belt = _tapis([_grain(41), _grain(42)])
    out = bq.record({"lanes": {WORKER: {"arc": "a", "queue": [41, 42]}}}, belt, NOW)
    queue = out["lanes"][WORKER]["queue"]
    assert [q["number"] for q in queue] == [41, 42]
    assert queue[0]["title"] == "grain"
    assert queue[0]["family"] == "#900"


def test_le_refus_ne_depend_pas_du_nombre_de_lignes():
    """Le refus porte sur la classe du grain, pas sur la taille de la file."""
    belt = {"picks": [_pick(51, klass="grain"), _pick(52, klass="delivered")]}
    with pytest.raises(ValueError):
        bq.record({"lanes": {WORKER: {"arc": "a", "queue": [51, 52]}}}, belt, NOW)
