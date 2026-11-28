#!/usr/bin/env python3
"""Tests for the bridge between ``belt_queues.py`` and the fast belt (14/11).

The coordinator's draw changed shape: the fast belt (``tapis_rapide.py --json``)
renders its grains under the key ``grains`` with the field names ``numero`` /
``titre`` / ``famille``, while the heavy belt (``pick_idle_grain.py --belt
--json``) renders them under ``picks``. The board reads both; ``record``
refuses a grain ``delivered`` in the queue of a worker lane (the closing urn
belongs to the coordinator, his adjoint and the secretary), and a grain
already carried by an OPEN PR of ANOTHER lane (27/11, ``belt_occupation``).

Measured cause (2026-11-14): 34 of the 40 grains drawn by the coordinator were
already delivered, and some of them went into worker queues.
Never calls ``gh``.
Run: python -m pytest scripts/tests/test_belt_queues_tapis_bridge.py
"""
from __future__ import annotations

import json
import subprocess
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
           consolidation: bool = False, klass: str | None = None,
           conteneur: bool = False) -> dict:
    g = {"rang": 1, "numero": numero, "titre": titre, "famille": famille,
         "parent": None, "conteneur": conteneur, "notes": [], "consolidation": consolidation,
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


# --- record : un grain deja en vol chez une autre lane (27/11, c0166) ----------
#
# Mesure du coordinateur : sur 37 grains dispatches, 29 avaient une PR ouverte,
# dont 24 portees par une AUTRE lane. Les lecteurs de PR sont ceux de
# ``belt_queues`` (``pr_lane``, ``pr_issue_refs``) : le temoin passe par eux.

AUTRE_LANE = "myia-po-2024:CoursIA"


def _pr(numero: int, lane: str | None, *refs: int) -> dict:
    corps = "Part of " + ", ".join(f"#{r}" for r in refs)
    if lane:
        corps = f"Grain: MED/tooling — lane {lane} — prev: LIGHT/guard #1\n\n{corps}"
    return {"number": numero, "title": "Fix(tooling): t", "body": corps,
            "createdAt": "2026-11-27T08:00:00Z", "closingIssuesReferences": []}


def _un_grain(assignment, prs):
    return bq.record(assignment, {"picks": [_pick(61, klass="grain")]}, NOW,
                     open_prs=prs)


def test_record_refuse_un_grain_porte_par_une_pr_ouverte_d_une_autre_lane():
    with pytest.raises(ValueError) as exc:
        _un_grain({"lanes": {WORKER: {"arc": "a", "queue": [61]}}},
                  [_pr(28440, AUTRE_LANE, 61)])
    message = str(exc.value)
    assert "#61" in message and "#28440" in message
    assert AUTRE_LANE in message and WORKER in message


def test_record_accepte_un_grain_dont_la_pr_ouverte_est_celle_de_la_lane():
    """La lane continue son propre travail : sa PR n'est pas un refus."""
    out = _un_grain({"lanes": {WORKER: {"arc": "a", "queue": [61]}}},
                    [_pr(28440, WORKER, 61)])
    assert out["occupation"] == "mesuree"
    assert [q["number"] for q in out["lanes"][WORKER]["queue"]] == [61]


def test_record_accepte_un_grain_que_la_lane_porte_deja_meme_si_une_autre_le_porte():
    """Une consolidation se sert a plusieurs (#20298, trois lanes) : la lane qui
    porte deja le grain le continue ; celle qui ne le porte pas est refusee."""
    assignment = {"lanes": {WORKER: {"arc": "a", "queue": [61]}}}
    out = _un_grain(assignment, [_pr(28489, WORKER, 61), _pr(26864, AUTRE_LANE, 61)])
    assert [q["number"] for q in out["lanes"][WORKER]["queue"]] == [61]
    with pytest.raises(ValueError) as exc:
        _un_grain({"lanes": {AUTRE_LANE: {"arc": "a", "queue": [61]}}},
                  [_pr(28489, WORKER, 61)])
    assert "#28489" in str(exc.value)


def test_record_accepte_un_conteneur_dont_une_autre_lane_cite_une_fille():
    """Un conteneur se sert par ses filles : `Part of #N` est sa livraison."""
    for belt in ({"picks": [_pick(61, klass="umbrella")]},
                 _tapis([_grain(61, conteneur=True)])):
        out = bq.record({"lanes": {WORKER: {"arc": "a", "queue": [61]}}}, belt, NOW,
                        open_prs=[_pr(28440, AUTRE_LANE, 61)])
        assert [q["number"] for q in out["lanes"][WORKER]["queue"]] == [61]


def test_record_refuse_un_grain_d_une_pr_sans_tag_et_nomme_la_pr():
    """Sans tag, la lane porteuse est inconnue : rien ne prouve qu'elle n'est
    pas une autre lane (fail-CLOSED), et le motif designe la PR."""
    with pytest.raises(ValueError) as exc:
        _un_grain({"lanes": {WORKER: {"arc": "a", "queue": [61]}}, },
                  [_pr(28440, None, 61)])
    assert "sans tag" in str(exc.value) and "#28440" in str(exc.value)


def test_record_sans_lecture_des_prs_n_est_pas_une_mesure_de_vacance():
    """`open_prs=None` : la lecture n'a pas eu lieu -- le refus ne s'applique
    pas, et la repartition le dit."""
    out = _un_grain({"lanes": {WORKER: {"arc": "a", "queue": [61]}}}, None)
    assert out["occupation"] == "non mesuree"


def test_record_via_main_refuse_et_n_ecrit_rien(monkeypatch, tmp_path, capsys):
    """Par la ligne de commande : REFUS en sortie, code 1, aucun fichier."""
    monkeypatch.setattr(bq, "store_dir", lambda: tmp_path)
    monkeypatch.setattr(bq, "gh_open_prs",
                        lambda: [_pr(28440, AUTRE_LANE, 61)])
    assignment = tmp_path / "files.json"
    assignment.write_text(json.dumps(
        {"lanes": {WORKER: {"arc": "a", "queue": [61]}}}), encoding="utf-8")
    rc = bq.main(["record", "--assignment", str(assignment)])
    assert rc == 1
    assert "REFUS" in capsys.readouterr().out
    assert list(tmp_path.glob("draw-*.json")) == []


def test_record_via_main_une_lecture_impossible_est_dite(monkeypatch, tmp_path,
                                                         capsys):
    """La lecture des PRs ouvertes echoue : la repartition est ecrite, et
    l'absence de mesure est nommee en sortie et dans le fichier."""
    monkeypatch.setattr(bq, "store_dir", lambda: tmp_path)

    def _illisible():
        raise subprocess.CalledProcessError(1, "gh pr list", stderr="", output="")
    monkeypatch.setattr(bq, "gh_open_prs", _illisible)
    assignment = tmp_path / "files.json"
    assignment.write_text(json.dumps(
        {"lanes": {WORKER: {"arc": "a", "queue": [61]}}}), encoding="utf-8")
    rc = bq.main(["record", "--assignment", str(assignment)])
    assert rc == 0
    ecrits = list(tmp_path.glob("draw-*.json"))
    assert len(ecrits) == 1
    assert json.loads(ecrits[0].read_text(encoding="utf-8"))["occupation"] == "non mesuree"
    assert "NON MESUREE" in capsys.readouterr().err
