"""Le tirage ne propose jamais un grain qu une autre lane tient (#13310 & al.).

Valide par ses FAUX NEGATIFS : le cas qui compte n est pas << le grain bloque
est retire >> (facile), c est << un grain de remplacement est bien rendu >>.
Un garde qui retire sans remplacer fabriquerait de l idle, ce que la regle 4 de
coordinator-discipline interdit -- et il passerait un test qui ne compte que
les retraits.
"""
import argparse
import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import pick_idle_grain as pick


def _it(n, genre="docs"):
    return {"number": n, "title": "issue %d" % n, "genre": genre,
            "age": 30, "idle": 10, "parent": None, "labels": [],
            "polarity": "neutral", "created_at": "2026-07-01T00:00:00Z",
            "body": "", "updated": "2026-08-01T00:00:00Z"}


def _args(**kw):
    d = dict(grains=1, umbrellas=0, delivered=0, prev_genre=None,
             lane="myia-po-2099:CoursIA", check_claims=True)
    d.update(kw)
    return argparse.Namespace(**d)


def _run(by_class, args, held):
    """Tire en simulant check_lane_claim : ``held`` = numeros tenus ailleurs."""
    real = pick.check_claims
    pick.check_claims = lambda nums, lane: {
        n: ("BLOQUE par myia-po-2000:CoursIA" if n in held else "libre")
        for n in nums}
    try:
        return pick.draw_unclaimed(by_class, args, random.Random(7),
                                   None, None, None)
    finally:
        pick.check_claims = real


EMPTY = {"grain": [], "umbrella": [], "delivered": []}


def test_grain_tenu_par_une_autre_lane_est_retire():
    by = dict(EMPTY, grain=[_it(1)])
    picks, _, conflicts = _run(by, _args(), held={1})
    assert picks == []
    assert len(conflicts) == 1
    assert conflicts[0][0]["number"] == 1
    assert conflicts[0][1].startswith("CLAIM :")


def test_un_remplacant_est_rendu_le_faux_negatif_qui_compte():
    """Retirer sans remplacer fabriquerait l idle que la regle 4 interdit."""
    by = dict(EMPTY, grain=[_it(1), _it(2)])
    picks, _, conflicts = _run(by, _args(), held={1})
    assert [p["number"] for p in picks] == [2], "aucun remplacant rendu"
    assert len(conflicts) == 1


def test_urne_entierement_tenue_ne_boucle_pas():
    by = dict(EMPTY, grain=[_it(1), _it(2), _it(3)])
    picks, _, conflicts = _run(by, _args(grains=2), held={1, 2, 3})
    assert picks == []
    assert len(conflicts) == 3


def test_le_quota_est_tenu_malgre_les_retraits():
    by = dict(EMPTY, grain=[_it(i) for i in range(1, 7)])
    picks, _, conflicts = _run(by, _args(grains=2), held={1, 2, 3})
    assert len(picks) == 2, "quota non tenu apres remplacement"
    assert all(p["number"] not in {1, 2, 3} for p in picks)


def test_check_desactive_ne_retire_rien():
    by = dict(EMPTY, grain=[_it(1)])
    picks, _, conflicts = _run(by, _args(check_claims=False), held={1})
    assert [p["number"] for p in picks] == [1]
    assert conflicts == []


def test_sans_lane_le_check_ne_sabote_pas_le_tirage():
    """--admissible et --orphans-report tirent sans lane : pas de plantage."""
    by = dict(EMPTY, grain=[_it(1)])
    picks, _, conflicts = _run(by, _args(lane=None), held={1})
    assert [p["number"] for p in picks] == [1]
    assert conflicts == []


def test_les_trois_urnes_sont_filtrees():
    """Aucun tenu dans les picks, et tout conflit rapporte est bien un tenu.

    Compter les conflits serait sur-specifier : le tirage est pondere-aleatoire,
    donc un grain tenu ne devient un conflit que s il est effectivement TIRE.
    Une urne qui sort d abord le libre n a jamais vu le tenu -- c est correct,
    et une assertion `len(conflicts) == 3` le declarerait faux (mesure : elle
    rendait 2 sur graine 7).
    """
    held = {1, 3, 5}
    by = {"grain": [_it(1), _it(2)], "umbrella": [_it(3), _it(4)],
          "delivered": [_it(5), _it(6)]}
    picks, _, conflicts = _run(
        by, _args(grains=1, umbrellas=1, delivered=1), held=held)
    nums = {p["number"] for p in picks}
    assert nums == {2, 4, 6}, nums
    assert not (nums & held), "un grain tenu a ete propose"
    assert {c[0]["number"] for c in conflicts} <= held


def test_deja_claim_par_cette_lane_n_est_pas_un_conflit():
    """Reprendre son propre grain est le cas nominal, pas une collision."""
    real = pick.check_claims
    pick.check_claims = lambda nums, lane: {
        n: "deja claim par cette lane" for n in nums}
    try:
        picks, _, conflicts = pick.draw_unclaimed(
            dict(EMPTY, grain=[_it(1)]), _args(), random.Random(7),
            None, None, None)
    finally:
        pick.check_claims = real
    assert [p["number"] for p in picks] == [1]
    assert conflicts == []
