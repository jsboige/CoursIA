"""Tests du tapis simple : une seule regle d'ordre, deux exclusions par label."""
from __future__ import annotations

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "coordination"))

import tapis_simple as ts


def issue(n: int, cree: str, maj: str | None = None, titre: str = "", labels=()) -> dict:
    return {"number": n, "title": titre or f"issue {n}", "createdAt": cree,
            "updatedAt": maj or cree, "labels_noms": list(labels)}


def fils_vides(numeros):
    return {n: [] for n in numeros}


def test_les_plus_vieilles_passent_d_abord():
    issues = [issue(3, "2026-11-20T00:00:00Z"), issue(1, "2026-08-01T00:00:00Z"),
              issue(2, "2026-10-01T00:00:00Z")]
    servis, _, _ = ts.ordonner(issues, {}, {}, fils_vides, n=3)
    assert [g["numero"] for g in servis] == [1, 2, 3]


def test_un_grain_recent_renvoie_en_queue():
    issues = [issue(1, "2026-08-01T00:00:00Z"), issue(2, "2026-10-01T00:00:00Z")]
    servis, _, _ = ts.ordonner(issues, {1: "2026-11-27T10:00:00Z"}, {}, fils_vides, n=2)
    assert [g["numero"] for g in servis] == [2, 1]
    assert servis[1]["source_cle"] == "servi"


def test_un_vieux_grain_ne_bat_pas_une_issue_plus_vieille_jamais_servie():
    # cle = derniere intervention, ou creation : l'issue servie en septembre passe
    # avant celle creee en novembre, et apres celle creee en aout jamais servie.
    issues = [issue(1, "2026-07-01T00:00:00Z"), issue(2, "2026-08-01T00:00:00Z"),
              issue(3, "2026-11-01T00:00:00Z")]
    servis, _, _ = ts.ordonner(issues, {1: "2026-09-01T00:00:00Z"}, {}, fils_vides, n=3)
    assert [g["numero"] for g in servis] == [2, 1, 3]


def test_le_fil_lu_fait_reculer_une_issue_reclamee():
    issues = [issue(1, "2026-08-01T00:00:00Z", maj="2026-11-27T00:00:00Z"),
              issue(2, "2026-09-01T00:00:00Z")]

    def fils(numeros):
        return {n: ([{"createdAt": "2026-11-27T00:00:00Z",
                      "body": "[CLAIMED] lane x:y -- paths: a/**"}] if n == 1 else [])
                for n in numeros}

    cache: dict = {}
    servis, _, lectures = ts.ordonner(issues, {}, cache, fils, n=2)
    assert [g["numero"] for g in servis] == [2, 1]
    assert servis[1]["source_cle"] == "fil"
    assert lectures == 2
    assert cache[1]["dernier_grain"] == "2026-11-27T00:00:00Z"


def test_un_marqueur_hors_premiere_ligne_ne_compte_pas():
    coms = [{"createdAt": "2026-11-27T00:00:00Z", "body": "Voir le [CLAIMED] plus haut"},
            {"createdAt": "2026-11-20T00:00:00Z", "body": "  [DELIVERED] lane a:b -- PR #1"}]
    assert ts.dernier_marqueur(coms) == "2026-11-20T00:00:00Z"
    assert ts.dernier_marqueur([{"createdAt": "x", "body": "[RELEASED] lane a:b"}]) is None


def test_le_cache_evite_de_relire_une_issue_qui_n_a_pas_bouge():
    issues = [issue(1, "2026-08-01T00:00:00Z", maj="2026-11-01T00:00:00Z")]
    cache = {1: {"lu_le": "2026-11-01T00:00:00Z", "dernier_grain": None}}
    appels = []

    def fils(numeros):
        appels.append(list(numeros))
        return fils_vides(numeros)

    servis, _, lectures = ts.ordonner(issues, {}, cache, fils, n=1)
    assert appels == [] and lectures == 0 and servis[0]["fil_lu"]


def test_lecture_en_panne_sert_la_suite_comme_non_lue():
    issues = [issue(1, "2026-08-01T00:00:00Z"), issue(2, "2026-09-01T00:00:00Z")]
    servis, _, _ = ts.ordonner(issues, {}, {}, lambda numeros: None, n=2)
    assert [g["numero"] for g in servis] == [1, 2]
    assert not any(g["fil_lu"] for g in servis)


def test_tirer_ecarte_l_urne_et_la_pause_et_garde_les_epics(tmp_path):
    issues = [issue(1, "2026-07-01T00:00:00Z", labels=["candidate-delivered"]),
              issue(2, "2026-07-02T00:00:00Z", labels=["pause"]),
              issue(3, "2026-07-03T00:00:00Z", titre="[EPIC] Consolidation"),
              issue(4, "2026-07-04T00:00:00Z")]
    r = ts.tirer(10, issues, tmp_path / "s", tmp_path / "d", fils_vides, 200)
    assert [g["numero"] for g in r["grains"]] == [4]
    assert [g["numero"] for g in r["conteneurs"]] == [3]
    assert r["urne"] == 1 and r["pause"] == 1
    assert r["urne_plus_vieilles"][0]["numero"] == 1


def test_drapeau_manuel_et_tirages_enregistres(tmp_path):
    store, draws = tmp_path / "s", tmp_path / "d"
    draws.mkdir()
    (draws / "draw-2026-11-27T100000Z.json").write_text(json.dumps({
        "assigned_at": "2026-11-27T10:00:00Z",
        "lanes": {"a:b": {"queue": [{"number": 1}]}}}), encoding="utf-8")
    ts.marquer_servi(store, [2], lane="a:b", quand="2026-11-28T09:00:00Z")
    issues = [issue(n, f"2026-0{n + 6}-01T00:00:00Z") for n in (1, 2, 3)]
    r = ts.tirer(3, issues, store, draws, fils_vides, 200)
    assert [g["numero"] for g in r["grains"]] == [3, 1, 2]


def test_le_json_se_lit_par_belt_queues(tmp_path):
    import belt_queues as bq
    issues = [issue(5, "2026-07-01T00:00:00Z", titre="[README #3973] Physique")]
    r = ts.tirer(1, issues, tmp_path / "s", tmp_path / "d", fils_vides, 200)
    grains = bq.grains_du_belt(r)
    assert grains[0]["number"] == 5 and grains[0]["title"].startswith("[README")


def test_les_epics_ne_prennent_pas_les_places_des_grains():
    issues = [issue(n, f"2026-07-{n:02d}T00:00:00Z", titre=f"[EPIC] e{n}") for n in range(1, 6)]
    issues += [issue(n, f"2026-08-{n - 9:02d}T00:00:00Z") for n in range(10, 13)]
    grains, conteneurs, _ = ts.ordonner(issues, {}, {}, fils_vides, n=2, n_conteneurs=3)
    assert [g["numero"] for g in grains] == [10, 11]
    assert [g["numero"] for g in conteneurs] == [1, 2, 3]
