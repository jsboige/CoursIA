"""Mandat user 2026-11-11 : les workers ne doivent plus etre bloques, et le
tapis doit servir toutes les issues.

Deux defauts mesures le 11/11 sur le journal de tirage d'ai-01 :

1. **La fenetre de service ne s'etendait que si AUCUN grain n'etait
   retenu.** Une lane qui trouvait 1 grain libre sur 4 demandes dans les 70
   premieres positions s'arretait la, alors que la suite du pool avait des
   grains libres.
2. **Une tete sautee n'est pas une visite.** Une EPIC sans sous-grain libre
   ou une barriere de lane restait en tete, et chaque tirage de la lane la
   lui resservait : en 24 h, `myia-ai-01:CoursIA-2` s'est vu servir #21310
   15 fois, #18258 et #25497 9 fois, #13737 8 fois.

Les tests sont hors ligne : sondes injectees, journal fabrique.
"""

import sys
import types
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import pick_idle_grain as pig  # noqa: E402

LANE = "myia-po-2024:CoursIA-2"
OTHER_LANE = "myia-po-2023:CoursIA"
NOW = pig.dt.datetime(2026, 11, 11, 12, 0, 0, tzinfo=pig.dt.timezone.utc)


def _ts(hours_ago: float) -> str:
    return (NOW - pig.dt.timedelta(hours=hours_ago)).strftime(
        "%Y-%m-%dT%H:%M:%SZ")


def _item(number, visit=None):
    return {"number": number, "klass": "grain", "age": 5, "idle": 1,
            "genre": "docs", "labels": [], "title": f"issue #{number}",
            "created_at": "2026-11-01T00:00:00Z",
            "last_delivery_stamp": None, "last_claim_stamp": visit}


def _rec(candidates, hours_ago, lane=LANE, mode="belt"):
    return types.SimpleNamespace(lane=lane, mode=mode, ts=_ts(hours_ago),
                                 candidates=list(candidates))


def _args(grains=4):
    return types.SimpleNamespace(grains=grains, include_delivered=False,
                                 lane=LANE)


def _no_probe(n, lane=None):
    return False


# --- 1. La fenetre s'etend tant que le quota n'est pas rempli --------------

def test_un_quota_partiel_etend_la_fenetre_jusqu_aux_grains_libres():
    """Controle POSITIF : 2 grains libres dans la fenetre (70), 2 au-dela.

    Avant le 11/11, la boucle s'arretait a 70 avec 2 grains : la condition
    d'extension etait « rien de retenu ». La lane en demandait 4.
    """
    pool = [_item(3000 + i) for i in range(150)]
    free = {pool[10]["number"], pool[20]["number"],
            pool[100]["number"], pool[120]["number"]}
    claims = {it["number"]: ((pig.CLAIM_CODE_FREE, "libre")
                             if it["number"] in free else
                             (pig.CLAIM_CODE_BLOCKED, "claim d'une autre lane"))
              for it in pool[:70]}
    seen_batches = []

    def claims_probe(numbers):
        seen_batches.append(list(numbers))
        return {n: ((pig.CLAIM_CODE_FREE, "libre") if n in free else
                    (pig.CLAIM_CODE_BLOCKED, "claim d'une autre lane"))
                for n in numbers}

    # c2817 : le plafond de sondes gate desormais le SERVICE (un candidat
    # dont la livraison n'a pas ete lue est ecarte « a sonder », pas servi).
    # Un plafond etroit viderait la fenetre et MASQUERAIT la logique de
    # quota testee ici : le budget couvre donc toute la fenetre.
    picks, _withheld, state = pig.belt_pick_with_replacements(
        pool, claims, _args(grains=4), probe_budget=1000,
        delivered_probe=_no_probe, merged_pr_probe=_no_probe,
        claims_probe=claims_probe)
    assert sorted(p["number"] for p in picks) == sorted(free)
    assert state["service_window_extended"] is True
    # Les claims de la tranche d'extension partent en UN appel groupe.
    assert seen_batches and len(seen_batches[0]) == 70


def test_un_quota_rempli_dans_la_fenetre_ne_l_etend_pas():
    """Controle NEGATIF : 4 grains libres dans la fenetre -> pas d'extension."""
    pool = [_item(4000 + i) for i in range(150)]
    claims = {it["number"]: (pig.CLAIM_CODE_FREE, "libre") for it in pool[:70]}
    # c2817 : meme raison que le controle positif -- le plafond de sondes
    # doit couvrir la fenetre, sinon la fenetre est videe par le plafond
    # et le test mesurerait le plafond, pas le quota.
    picks, _withheld, state = pig.belt_pick_with_replacements(
        pool, claims, _args(grains=4), probe_budget=1000,
        delivered_probe=_no_probe, merged_pr_probe=_no_probe,
        claims_probe=lambda numbers: {
            n: (pig.CLAIM_CODE_FREE, "libre") for n in numbers})
    assert len(picks) == 4
    assert state["service_window_extended"] is False
    assert state["service_window"] == 70


# --- 2. Les tetes mortes passent en queue pour la lane ---------------------

def test_une_issue_servie_deux_fois_sans_visite_est_une_tete_morte():
    pool = [_item(1), _item(2), _item(3)]
    records = [_rec([1, 2], 10), _rec([1, 3], 4)]
    dead = pig.belt_dead_heads(pool, records, lane=LANE, now=NOW)
    assert [d["number"] for d in dead] == [1]
    assert dead[0]["served"] == 2
    assert dead[0]["first_served"] == _ts(10)


def test_une_visite_apres_le_service_efface_la_tete_morte():
    """Un claim pose apres les services : l'issue a ete servie, pas sautee."""
    pool = [_item(1, visit=_ts(2)), _item(2, visit=_ts(20))]
    records = [_rec([1, 2], 10), _rec([1, 2], 4)]
    dead = pig.belt_dead_heads(pool, records, lane=LANE, now=NOW)
    assert [d["number"] for d in dead] == [2]


def test_les_services_d_un_meme_cycle_comptent_une_fois():
    """Deux tirages a 10 minutes d'ecart = un seul service."""
    pool = [_item(1)]
    records = [_rec([1], 3.0), _rec([1], 3.0 - 10 / 60)]
    assert pig.belt_dead_heads(pool, records, lane=LANE, now=NOW) == []


def test_les_tirages_d_une_autre_lane_ou_hors_fenetre_ne_comptent_pas():
    pool = [_item(1)]
    records = [_rec([1], 10, lane=OTHER_LANE), _rec([1], 4, lane=OTHER_LANE),
               _rec([1], 30), _rec([1], 5, mode="weighted"), _rec([1], 3)]
    assert pig.belt_dead_heads(pool, records, lane=LANE, now=NOW) == []


def test_une_visite_illisible_ne_deplace_rien():
    pool = [_item(1, visit="pas-une-date")]
    records = [_rec([1], 10), _rec([1], 4)]
    assert pig.belt_dead_heads(pool, records, lane=LANE, now=NOW) == []


def test_la_rotation_garde_l_ordre_relatif_et_envoie_les_mortes_en_queue():
    pool = [_item(n) for n in (5, 1, 6, 2, 7)]
    moved = pig.rotate_dead_heads(pool, [1, 2])
    assert moved == 2
    assert [it["number"] for it in pool] == [5, 6, 7, 1, 2]


def test_la_rotation_sans_tete_morte_ne_touche_pas_le_pool():
    pool = [_item(n) for n in (3, 1, 2)]
    assert pig.rotate_dead_heads(pool, []) == 0
    assert [it["number"] for it in pool] == [3, 1, 2]

