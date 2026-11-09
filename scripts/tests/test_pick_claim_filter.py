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
        n: (pick.CLAIM_CODE_BLOCKED if n in held else pick.CLAIM_CODE_FREE,
            "BLOQUE par myia-po-2000:CoursIA" if n in held else "libre")
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


def test_poignee_etroite_tenue_puise_dans_la_reserve_globale():
    """Une passe locale non vide ne devient pas terminale apres claim-check."""
    real = pick.check_claims
    pick.check_claims = lambda nums, lane: {
        n: (pick.CLAIM_CODE_BLOCKED if n == 1 else pick.CLAIM_CODE_FREE,
            "BLOQUE par other:lane" if n == 1 else "libre") for n in nums}
    state = {}
    try:
        picks, _, conflicts = pick.draw_unclaimed(
            dict(EMPTY, grain=[_it(1)]), _args(), random.Random(7),
            None, None, None,
            fallback_by_class=dict(EMPTY, grain=[_it(1), _it(2)]),
            continuity_state=state,
        )
    finally:
        pick.check_claims = real
    assert [p["number"] for p in picks] == [2]
    assert state == {"used": True}
    assert [item[0]["number"] for item in conflicts] == [1]
    assert all(p["number"] != 1 for p in picks)


def test_reserve_globale_ne_reintroduit_ni_claim_ni_livraison():
    """Le repli post-check garde les deux exclusions live sur sa reserve."""
    primary = _it(1)
    delivered = _it(2)
    delivered["labels"] = [pick.DELIVERED_LABEL]
    free = _it(3)
    real_check = pick.check_claims
    real_draw = pick.draw
    pick.check_claims = lambda nums, lane: {
        n: (pick.CLAIM_CODE_BLOCKED if n == 1 else pick.CLAIM_CODE_FREE,
            "BLOQUE par other:lane" if n == 1 else "libre") for n in nums}
    pick.draw = lambda items, n, *args, **kwargs: items[:n]
    state = {}
    try:
        picks, _, conflicts = pick.draw_unclaimed(
            dict(EMPTY, grain=[primary]), _args(), random.Random(7),
            None, None, None,
            fallback_by_class=dict(
                EMPTY, grain=[primary, delivered, free]),
            continuity_state=state,
        )
    finally:
        pick.check_claims = real_check
        pick.draw = real_draw
    assert [p["number"] for p in picks] == [3]
    assert state == {"used": True}
    assert {item[0]["number"] for item in conflicts} == {1, 2}
    assert any(cause.startswith("CLAIM :") for _, cause in conflicts)
    assert any(cause.startswith("LIVRAISON :") for _, cause in conflicts)


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
        n: (pick.CLAIM_CODE_OWNED_BY_ME, "deja claim par cette lane")
        for n in nums}
    try:
        picks, _, conflicts = pick.draw_unclaimed(
            dict(EMPTY, grain=[_it(1)]), _args(), random.Random(7),
            None, None, None)
    finally:
        pick.check_claims = real
    assert [p["number"] for p in picks] == [1]
    assert conflicts == []


# --- #20265 : le fail-OPEN du claim, et sa moitie RAPPORTEE ----------------
#
# Le tirage servait deja un candidat dont le claim n'avait pas pu etre lu
# (fail-OPEN, correct) mais SE TAISAIT : le candidat partait avec un statut
# de claim INCONNU, indiscernable d'un claim verifie libre. Les tests
# ci-dessous sont apparies en TEMOINS DISCRIMINANTS : le positif (echec ->
# trace) ne vaut que par le negatif (meme sonde, reussie -> trace ABSENTE).
# Un test qui n'exerce que l'echec ne prouve pas que la trace ne se declenche
# pas a tort.


def _probe_returns(**verdicts):
    """Fabrique une sonde de claim rendant le meme verdict pour tout numero."""
    def probe(nums, lane):
        return {n: verdicts["v"] for n in nums}
    return probe


def test_lecture_de_claim_en_echec_est_servie_mais_tracee():
    """Temoin POSITIF : la sonde n'aboutit pas -> le candidat est CONSERVE
    (fail-OPEN) et son numero est rapporte dans l'etat."""
    real = pick.check_claims
    pick.check_claims = _probe_returns(
        v=(pick.CLAIM_CODE_ERROR, "lecture ratee (reseau)"))
    state = {}
    try:
        picks, _, conflicts = pick.draw_unclaimed(
            dict(EMPTY, grain=[_it(1)]), _args(), random.Random(7),
            None, None, None, delivered_state=state)
    finally:
        pick.check_claims = real
    assert [p["number"] for p in picks] == [1], "le fail-OPEN doit conserver"
    assert conflicts == [], "un ERROR n'est pas un BLOQUE"
    assert state["claim_unread"] == [1], "lecture ratee non rapportee"


def test_sonde_qui_aboutit_en_free_ne_trace_rien():
    """Temoin NEGATIF -- la moitie discriminante : la MEME sonde, reussie en
    FREE, ne doit RIEN rapporter. Sans ce test, une trace qui se declenche a
    tort passerait pour une reussite."""
    real = pick.check_claims
    pick.check_claims = _probe_returns(v=(pick.CLAIM_CODE_FREE, "libre"))
    state = {}
    try:
        picks, _, _ = pick.draw_unclaimed(
            dict(EMPTY, grain=[_it(1)]), _args(), random.Random(7),
            None, None, None, delivered_state=state)
    finally:
        pick.check_claims = real
    assert [p["number"] for p in picks] == [1]
    assert state.get("claim_unread") == [], "lecture reussie mais rapportee"


def test_controle_non_demande_ne_declenche_pas_de_fausse_alerte():
    """Le repli `ERROR` couvre DEUX cas opposes : une lecture TENTEE qui
    echoue, et un controle JAMAIS DEMANDE (`--no-check-claims`, tirage sans
    lane). Seul le premier est un fail-OPEN a signaler -- sinon chaque tirage
    sans lane alerterait sur tous ses candidats."""
    real = pick.check_claims

    def _never(nums, lane):
        raise AssertionError("check_claims appele alors qu'aucune lecture "
                             "n'a ete demandee")

    pick.check_claims = _never
    state = {}
    try:
        for kw in ({"check_claims": False}, {"lane": None}):
            picks, _, _ = pick.draw_unclaimed(
                dict(EMPTY, grain=[_it(1)]), _args(**kw), random.Random(7),
                None, None, None, delivered_state=state)
            assert [p["number"] for p in picks] == [1]
    finally:
        pick.check_claims = real
    assert state.get("claim_unread") == [], (
        "un controle non demande a produit une alerte")


# --- Le tapis (2e chemin) : meme fail-OPEN, meme trace --------------------
#
# Le tapis n'emprunte pas `draw_unclaimed` : sa boucle de service est
# `belt_pick_with_replacements`. Les deux chemins sont couverts ici plutot
# que supposes convergents -- c'est le tapis que lance la Phase 2 du cycle.


def _belt(minimal_number, code, human, lane="myia-po-2099:CoursIA"):
    import types
    args = types.SimpleNamespace(grains=1, include_delivered=True, lane=lane)
    return pick.belt_pick_with_replacements(
        [{"number": minimal_number, "klass": "grain"}],
        {minimal_number: (code, human)}, args, probe_budget=4)


def test_tapis_trace_la_lecture_de_claim_en_echec():
    picks, _, state = _belt(1, pick.CLAIM_CODE_ERROR, "lecture ratee")
    assert [p["number"] for p in picks] == [1], "le tapis doit servir"
    assert state["claim_unread"] == [1]


def test_tapis_ne_trace_pas_une_lecture_reussie():
    picks, _, state = _belt(1, pick.CLAIM_CODE_FREE, "libre")
    assert [p["number"] for p in picks] == [1]
    assert state["claim_unread"] == []


def test_tapis_sans_lane_ne_trace_pas():
    """Sans lane, le tapis tire des lanes non identifiees (`--admissible`) :
    une alerte y serait du bruit systematique."""
    picks, _, state = _belt(1, pick.CLAIM_CODE_ERROR, "lecture ratee",
                            lane=None)
    assert [p["number"] for p in picks] == [1]
    assert state["claim_unread"] == []


# --- Le rendu : la trace est VISIBLE, et muette quand il n'y a rien -------


def test_le_rapport_rend_la_trace_visible(capsys):
    pick.print_claim_unread_report([20265], "myia-po-2024:CoursIA-2")
    out = capsys.readouterr().out
    assert "claim NON LU" in out
    assert "#20265" in out
    assert "check_lane_claim.py <N> --lane myia-po-2024:CoursIA-2" in out


def test_le_rapport_est_muet_sans_lecture_ratee(capsys):
    """Contre-epreuve du rendu : un rapport qui bavarde a vide serait du
    bruit a chaque tirage -- y compris ceux ou tout s'est bien passe."""
    pick.print_claim_unread_report([], "myia-po-2024:CoursIA-2")
    pick.print_claim_unread_report(None, "myia-po-2024:CoursIA-2")
    assert capsys.readouterr().out == ""
