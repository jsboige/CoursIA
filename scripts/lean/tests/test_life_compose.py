"""Tests du générateur de contraintes compositionnelles (tranches 3+4 de #15635).

Le contrat testé ici est celui des critères 3 a 8 de #15635 : les contraintes
spatiales, temporelles, de ports et de clearance sont toutes ACTIVES et
chacune couverte par un contrôle négatif ; les quatres familles d'élagage
sont instrumentées et ablatables (jamais la certification) ; les verdicts
FOUND / IMPOSSIBLE_BOUNDED / TIMEOUT sont distincts ; le replay indépendant
attrape les erreurs de modèle.

Deux leçons mesurées de la tranche 3 ont leur test de non-régression :
- la non-interaction universelle est Chebyshev >= 3 ; a distance 2 elle
  dépend du contenu (naissances croisées possible) ;
- un placement réactif déclaré doit être ATTEIGNABLE par dérive pure le
  long de la direction du port (le placement tranche 1+2 de
  block_catalyses_glider démarrait au milieu de l'interaction).
"""

from __future__ import annotations

import copy
import json
import sys
from pathlib import Path

import pytest

LEAN_DIR = Path(__file__).resolve().parent.parent
FIXTURE = LEAN_DIR / "life_components_fixture.json"

sys.path.insert(0, str(LEAN_DIR))

import life_compose as lc  # noqa: E402
from life_components import load_catalog  # noqa: E402
from life_synthesize import step, synthesize  # noqa: E402


CATALOG = load_catalog(FIXTURE)


def spawn_cells(motif_id: str, anchor: tuple[int, int], p0: int, t: int) -> set:
    return set(lc.cells_at(CATALOG, lc.Spawn(motif_id, anchor, p0), t))


# ---------------------------------------------------------------------------
# Trajectoires exactes (socle du modèle propositionnel)
# ---------------------------------------------------------------------------


def test_trajectoires_exactes_contre_le_moteur() -> None:
    """cells_at == evolve pour chaque motif, chaque phase, 3 ancres, 13 pas."""
    mismatches = 0
    for motif_id in sorted(CATALOG.motifs):
        for p0 in range(CATALOG.motifs[motif_id].period):
            for anchor in [(0, 0), (-5, 3), (7, -4)]:
                real = spawn_cells(motif_id, anchor, p0, 0)
                for t in range(13):
                    if real != spawn_cells(motif_id, anchor, p0, t):
                        mismatches += 1
                    real = step(real)
    assert mismatches == 0


def test_compteur_de_periodes_depends_de_p0() -> None:
    """Glider p0=3 a t=1 : une période COMPLETE ecoulee (coin avance d'une
    diagonale) -- le compteur est (p0+t)//P, pas t//P."""
    a = spawn_cells("glider", (0, 0), 3, 1)
    b = spawn_cells("glider", (1, -1), 0, 0)
    assert a == b


# ---------------------------------------------------------------------------
# Ports (critere 5 : contraintes d'interface)
# ---------------------------------------------------------------------------


def test_semantique_port_mobile_et_statique() -> None:
    """in0 mobile = signes de la translation par période ; in1 statique = axe."""
    reaction = CATALOG.reactions["block_catalyses_glider"]
    d0 = reaction.ports[0].direction
    tx, ty = CATALOG.motifs["glider"].translation_step
    assert d0 == (1 if tx > 0 else -1 if tx < 0 else 0,
                  1 if ty > 0 else -1 if ty < 0 else 0)
    # port statique du bloc : axe connecteur vers la ligne d'approche
    assert reaction.ports[1].direction[1] == 0


def test_compatibilite_de_port_filtre_les_directions() -> None:
    assert lc.port_compatible(CATALOG, "glider", (1, -1))
    # direction opposée : le glider s'éloignerait du connecteur
    assert not lc.port_compatible(CATALOG, "glider", (-1, 1))
    # axe statique sur un reactif mobile : incompatible
    assert not lc.port_compatible(CATALOG, "glider", (1, 0))
    # translation orthogonale : pas la ligne du motif
    assert not lc.port_compatible(CATALOG, "glider", (1, 1))


def test_congruence_de_phase_a_larrivee() -> None:
    """Le reactif mobile doit arriver dans la phase déclarée (R4)."""
    reaction = CATALOG.reactions["block_catalyses_glider"]
    decl = reaction.reactants[0]
    t_fire = 15
    period = CATALOG.motifs["glider"].period
    for p0 in range(period):
        forced = (decl.phase - t_fire) % period
        ph = lc.phase_at(CATALOG, lc.Spawn("glider", (16, 8), p0), t_fire)
        assert (ph == decl.phase) == (p0 == forced)


# ---------------------------------------------------------------------------
# Physique mesurée : seuils de non-interaction (leçon tranche 3)
# ---------------------------------------------------------------------------


def test_chebyshev_2_engendre_des_naissances_croisees() -> None:
    """Glider + bloc a distance 2 : naissance combinée mesurée a t=7."""
    block = {(4, 2), (5, 2), (4, 3), (5, 3)}
    spawn = lc.Spawn("glider", (-3, 3), 1)
    scene = set(lc.cells_at(CATALOG, spawn, 0)) | block
    first_dev = None
    for t in range(12):
        expected = set(lc.cells_at(CATALOG, spawn, t)) | block
        if scene != expected:
            first_dev = t
            break
        scene = step(scene)
    assert first_dev == 11  # pur jusqu'a t=10 inclus : le depart declare
    # la fenetre démarre au DERNIER etat pur ; le produit est un bloc stable
    window0 = set(lc.cells_at(CATALOG, spawn, 10)) | block
    cells = set(window0)
    for _ in range(8):
        cells = step(cells)
    assert cells == {(2, 3), (3, 3), (2, 4), (3, 4)}
    assert step(cells) == cells


def test_chebyshev_3_est_sur_sans_interaction() -> None:
    """Toute paire d'objets a distance >= 3 n'interagit jamais (propriété)."""
    block = {(7, 2), (8, 2), (7, 3), (8, 3)}  # a distance 3 du bloc reactif
    spawn = lc.Spawn("glider", (-3, 3), 1)
    scene = set(lc.cells_at(CATALOG, spawn, 0)) | block
    for t in range(16):
        expected = set(lc.cells_at(CATALOG, spawn, t)) | block
        assert scene == expected, f"interaction inattendue a t={t}"
        scene = step(scene)


def test_deux_blocs_a_distance_2_sont_stables() -> None:
    """Contenu-dépendant : la cible gap-1 est stable malgré la distance 2."""
    target = set(lc.TWO_BLOCKS_TARGET)
    assert step(target) == target


# ---------------------------------------------------------------------------
# Atteignabilité du placement déclaré (leçon tranche 3)
# ---------------------------------------------------------------------------


def _reachability(catalog, doc_reaction: dict) -> tuple[bool, int]:
    """Dérive le réactif mobile le long de son port et cherche le fenêtrage.

    Retourne (atteignable, pas de la première déviation) : le placement est
    atteignable s'il existe un spawn sur la ligne du port dont la scène reste
    pure jusqu'à l'état déclaré exactement.
    """
    decl = doc_reaction["reactants"][0]
    motif_id = decl["motif_id"]
    tx, ty = catalog.motifs[motif_id].translation_step
    static = set()
    for r in doc_reaction["reactants"][1:]:
        phase_cells = lc._motif_phases(catalog, r["motif_id"])[r["phase"]]
        dx, dy = r["offset"]
        static |= {(x + dx, y + dy) for (x, y) in phase_cells}
    # spawn 4 périodes en amont le long de la direction du port
    period = catalog.motifs[motif_id].period
    corner = lc._motif_phase_offsets(catalog, motif_id)[decl["phase"]]
    back = (
        decl["offset"][0] - 4 * tx - corner[0],
        decl["offset"][1] - 4 * ty - corner[1],
    )
    p0 = decl["phase"]  # phase d'arrivée = phase déclarée
    spawn = lc.Spawn(motif_id, back, p0)
    scene = set(lc.cells_at(catalog, spawn, 0)) | static
    declared = set(lc.cells_at(catalog, spawn, 4 * period)) | static
    for t in range(4 * period + 1):
        expected = set(lc.cells_at(catalog, spawn, t)) | static
        if scene != expected:
            return False, t
        if t == 4 * period:
            return scene == declared, t
        scene = step(scene)
    return False, -1


def test_placement_declare_atteignable_par_derivee() -> None:
    doc = json.loads(FIXTURE.read_text(encoding="utf-8"))
    entry = [r for r in doc["reactions"] if r["id"] == "block_catalyses_glider"][0]
    ok, _ = _reachability(CATALOG, entry)
    assert ok


def test_placement_milieu_dinteraction_inatteignable() -> None:
    """Contrôle négatif : le placement tranche 1+2 (phase 0, bloc (3,0))
    démarrait au milieu de l'interaction -- la dérive dévie avant de l'atteindre."""
    doc = json.loads(FIXTURE.read_text(encoding="utf-8"))
    entry = copy.deepcopy(
        [r for r in doc["reactions"] if r["id"] == "block_catalyses_glider"][0]
    )
    entry["reactants"][0]["phase"] = 0
    entry["reactants"][1]["offset"] = [3, 0]
    ok, first_dev = _reachability(CATALOG, entry)
    assert not ok
    assert first_dev < 4 * CATALOG.motifs["glider"].period


# ---------------------------------------------------------------------------
# R3 : élagage spatial et ses non-régressions
# ---------------------------------------------------------------------------


def _state_after_e0():
    sp0 = (lc.Spawn("glider", (0, 0), 0), lc.Spawn("glider_mirror", (4, 0), 0))
    ev0 = lc.EventInst(
        idx=0, reaction_id="glider_pair_two_blocks",
        offset=(0, 0), t_fire=0, bindings=sp0,
    )
    live0 = tuple(lc.product_handles(CATALOG, ev0))
    return lc.SearchState(spawns=sp0, events=(ev0,), live=live0), sp0, ev0


def test_produit_pas_confronte_a_sa_propre_fenetre() -> None:
    """Non-régression R3 : un candidat E1 distant doit passer _spatial_ok."""
    state0, _, _ = _state_after_e0()
    goal = lc.OBJECTIVES["two_blocks_catalyse_free"]
    s = lc.Searcher(CATALOG, goal, node_budget=10)
    e, tf2 = (20, 4), 15
    gspawn = lc.Spawn("glider", (16, 8), 0)
    bspawn = lc.Spawn("block", (24, 6), 0)
    ev1 = lc.EventInst(
        idx=1, reaction_id="block_catalyses_glider",
        offset=e, t_fire=tf2, bindings=(gspawn, bspawn),
    )
    consumed = {lc.handle_key(b) for b in ev1.bindings}
    assert s._spatial_ok(state0, (gspawn, bspawn), ev1, consumed)
    # et la scène complète certifie (le témoin libre est réel)
    all_spawns = state0.spawns + (gspawn, bspawn)
    new_live = tuple(
        h for h in state0.live if lc.handle_key(h) not in consumed
    ) + tuple(lc.product_handles(CATALOG, ev1))
    state1 = lc.SearchState(spawns=all_spawns, events=(ev0_of(state0), ev1), live=new_live)
    assert lc.goal_reached(CATALOG, goal, state1.events, state1.live)
    verdict = lc.certify(CATALOG, goal, state1.spawns, state1.events)
    assert verdict["ok"]
    assert len(verdict["blocks_final"]) == 3


def ev0_of(state):
    return state.events[0]


def test_cle_dedup_injective_sur_ancre_et_temps() -> None:
    """Non-régression R1 : la clé d'état distingue les ancres ET les tirs.

    Deux faux positifs mesurés, tous deux des faux négatifs de complétude :
    (a) une clé indépendante de la position avalait le produit d'un second
    épisode ; (b) une clé réduite à la signature des vivants confondait deux
    scènes aux mêmes produits à des temps de tir différents — sous ablation
    de R4, un état non certifiant partageant la clé du témoin était déplié en
    premier, le témoin était dédupliqué, et la recherche concluait
    IMPOSSIBLE_BOUNDED alors qu'un témoin existait.
    """
    state0, sp0, _ = _state_after_e0()
    assert lc._state_key(state0) == lc._state_key(state0)
    # (a) même structure, ancre décalée de 9 cellules
    sp_b = (lc.Spawn("glider", (9, 9), 0), lc.Spawn("glider_mirror", (13, 9), 0))
    ev_b = lc.EventInst(
        idx=0, reaction_id="glider_pair_two_blocks",
        offset=(9, 9), t_fire=0, bindings=sp_b,
    )
    state_b = lc.SearchState(
        spawns=sp_b, events=(ev_b,), live=tuple(lc.product_handles(CATALOG, ev_b))
    )
    # (b) même structure, même ancre, tir décalé d'un pas
    ev_c = lc.EventInst(
        idx=0, reaction_id="glider_pair_two_blocks",
        offset=(0, 0), t_fire=1, bindings=sp0,
    )
    state_c = lc.SearchState(
        spawns=sp0, events=(ev_c,), live=tuple(lc.product_handles(CATALOG, ev_c))
    )
    assert lc._state_key(state0) != lc._state_key(state_b)
    assert lc._state_key(state0) != lc._state_key(state_c)
    # et la clé est CANONIQUE : l'ordre de tir des épisodes indépendants ne
    # la change pas (certify est insensible à l'ordre : union pas à pas,
    # consommation last-writer unique, comptage d'identifiants de réaction)
    state_swapped = lc.SearchState(
        spawns=sp0,
        events=(ev0_of(state0), lc.EventInst(
            idx=1, reaction_id="glider_pair_two_blocks",
            offset=(9, 9), t_fire=3, bindings=sp_b,
        )),
        live=(),
    )
    state_direct = lc.SearchState(
        spawns=sp0,
        events=(lc.EventInst(
            idx=0, reaction_id="glider_pair_two_blocks",
            offset=(9, 9), t_fire=3, bindings=sp_b,
        ), ev0_of(state0)),
        live=(),
    )
    assert lc._state_key(state_swapped) == lc._state_key(state_direct)


def test_elagage_rejette_le_spawn_dans_la_fenetre() -> None:
    """Contrôle négatif R3 : un bloc posé SUR la fenêtre d'un événement actif
    est rejeté (distance 0 aux cellules de fenêtre)."""
    state0, _, ev0 = _state_after_e0()
    goal = lc.OBJECTIVES["two_blocks_catalyse_free"]
    s = lc.Searcher(CATALOG, goal, node_budget=10)
    # bloc statique posé sur la trajectoire des gliders de E0 (x in [0,6])
    bspawn = lc.Spawn("block", (2, 1), 0)
    gspawn = lc.Spawn("glider", (-40, 44), 0)  # loin, n'interagit jamais
    ev1 = lc.EventInst(
        idx=1, reaction_id="block_catalyses_glider",
        offset=(-44, 40), t_fire=55, bindings=(gspawn, bspawn),
    )
    consumed = {lc.handle_key(b) for b in ev1.bindings}
    assert not s._spatial_ok(state0, (gspawn, bspawn), ev1, consumed)


# ---------------------------------------------------------------------------
# Budgets (critere 3 : contraintes bornées)
# ---------------------------------------------------------------------------


def test_budgets_composants_et_gliders_rejetes() -> None:
    goal = lc.Goal(
        name="ping",
        final_min_counts={"block": 2},
        required_events={"glider_pair_two_blocks": 1},
        max_events=2,
        max_components=2,   # la paire seule = 2 composants : budget exact
        horizon=24,
        surface=(24, 24),
        max_gliders=2,
    )
    r = lc.run_compositional(goal, fixture=str(FIXTURE), reps=1)
    assert r["report"]["verdict"] == "FOUND"
    tight = lc.Goal(
        name="ping_serre",
        final_min_counts={"block": 2},
        required_events={"glider_pair_two_blocks": 1},
        max_events=2,
        max_components=1,   # impossible : la paire exige 2 spawns
        horizon=24,
        surface=(24, 24),
        max_gliders=2,
    )
    r2 = lc.run_compositional(tight, fixture=str(FIXTURE), reps=1)
    assert r2["report"]["verdict"] == "IMPOSSIBLE_BOUNDED"
    assert r2["report"]["stats"]["budget"] > 0


def test_glider_seuls_impossible_borne() -> None:
    """Sans événement, deux gliders restent des gliders : épuisement trivial."""
    goal = lc.Goal(
        name="gliders_seuls",
        final_min_counts={"block": 2},
        required_events={},
        max_events=0,
        max_components=2,
        horizon=24,
        surface=(24, 24),
        max_gliders=2,
    )
    r = lc.run_compositional(goal, fixture=str(FIXTURE), reps=1)
    assert r["report"]["verdict"] == "IMPOSSIBLE_BOUNDED"
    assert r["report"]["stats"]["candidates"] >= 0  # énumération vide mais bornée


def test_timeout_distinct_de_impossible() -> None:
    """Budget de noeuds épuisé AVANT épuisement de l'espace = TIMEOUT."""
    goal = lc.Goal(
        name="large",
        final_min_counts={"block": 2},
        required_events={"glider_pair_two_blocks": 1},
        max_events=2,
        max_components=2,
        horizon=40,
        surface=(32, 32),
        max_gliders=2,
    )
    r = lc.run_compositional(goal, fixture=str(FIXTURE), reps=1, node_budget=1)
    assert r["report"]["verdict"] == "TIMEOUT"


# ---------------------------------------------------------------------------
# Certification : le replay dispose (critere 7)
# ---------------------------------------------------------------------------


def test_replay_rejette_une_erreur_de_modele() -> None:
    """Un témoin falsifié (ancre décalée d'une cellule) est rejeté par certify."""
    sp0 = (lc.Spawn("glider", (0, 0), 0), lc.Spawn("glider_mirror", (4, 0), 0))
    ev0 = lc.EventInst(
        idx=0, reaction_id="glider_pair_two_blocks",
        offset=(0, 0), t_fire=0, bindings=sp0,
    )
    goal = lc.OBJECTIVES["two_blocks"]
    assert lc.certify(CATALOG, goal, sp0, (ev0,))["ok"]
    faux = (lc.Spawn("glider", (1, 0), 0), sp0[1])  # glider décalé
    assert not lc.certify(CATALOG, goal, faux, (ev0,))["ok"]


def test_clearance_jamais_traversee_pendant_la_fenetre() -> None:
    """Contrôle négatif : un bloc tiers posé DANS la zone de clearance
    (mais a distance >= 3 de l'épisode, sans perturber la physique) est
    attrapé par la règle de clearance de la certification."""
    goal = lc.OBJECTIVES["two_blocks_catalyse_free"]
    sp0 = (lc.Spawn("glider", (0, 0), 0), lc.Spawn("glider_mirror", (4, 0), 0))
    ev0 = lc.EventInst(
        idx=0, reaction_id="glider_pair_two_blocks",
        offset=(0, 0), t_fire=0, bindings=sp0,
    )
    e, tf2 = (20, 4), 15
    gspawn = lc.Spawn("glider", (16, 8), 0)
    bspawn = lc.Spawn("block", (24, 6), 0)
    ev1 = lc.EventInst(
        idx=1, reaction_id="block_catalyses_glider",
        offset=e, t_fire=tf2, bindings=(gspawn, bspawn),
    )
    # coin de clearance (reaction) = (-3,3) : a l'interieur du rect, a
    # distance >= 3 de toute cellule de l'episode (aucune interaction physique)
    rogue = lc.Spawn("block", (-3 + e[0], 3 + e[1]), 0)
    spawns = sp0 + (gspawn, bspawn, rogue)
    verdict = lc.certify(CATALOG, goal, spawns, (ev0, ev1))
    assert not verdict["ok"]
    assert verdict["clearance_violations"]
    # sans le bloc voyou, la même scène certifie
    verdict_ok = lc.certify(CATALOG, goal, sp0 + (gspawn, bspawn), (ev0, ev1))
    assert verdict_ok["ok"]


# ---------------------------------------------------------------------------
# Verdicts de bout en bout (critere 8 : démonstrateur discriminant)
# ---------------------------------------------------------------------------


def test_two_blocks_found_et_deterministe() -> None:
    results = [lc.run_compositional(lc.OBJECTIVES["two_blocks"], fixture=str(FIXTURE), reps=1) for _ in range(3)]
    assert all(r["report"]["verdict"] == "FOUND" for r in results)
    w0 = results[0]["report"]["witness"]
    assert all(r["report"]["witness"] == w0 for r in results[1:])
    assert len(w0["blocks_final"]) == 2
    assert w0["steps_checked"] > 0


def test_reutilisation_stricte_impossible_borne() -> None:
    """Variante stricte : tout candidat de réutilisation est rejeté par le
    replay (naissances croisées a distance 2 pendant la transmutation)."""
    r = lc.run_compositional(lc.OBJECTIVES["two_blocks_catalyse"], fixture=str(FIXTURE), reps=1)
    assert r["report"]["verdict"] == "IMPOSSIBLE_BOUNDED"
    assert r["report"]["stats"]["replay_rejected"] >= 1
    assert r["report"]["witness"] is None


def test_variante_libre_found() -> None:
    r = lc.run_compositional(lc.OBJECTIVES["two_blocks_catalyse_free"], fixture=str(FIXTURE), reps=1)
    assert r["report"]["verdict"] == "FOUND"
    fired = {ev["reaction_id"] for ev in r["report"]["witness"]["events"]}
    assert fired == {"block_catalyses_glider", "glider_pair_two_blocks"}
    assert len(r["report"]["witness"]["blocks_final"]) >= 2


@pytest.mark.parametrize("famille", ["r1", "r2", "r3", "r4"])
def test_ablations_conservent_le_verdict(famille: str) -> None:
    """Ablation d'une famille d'élagage : le verdict de two_blocks tient
    (la certification n'est JAMAIS ablatable)."""
    r = lc.run_compositional(lc.OBJECTIVES["two_blocks"], fixture=str(FIXTURE), reps=1, ablations=frozenset([famille]))
    assert r["report"]["verdict"] == "FOUND"


# ---------------------------------------------------------------------------
# Baseline cellulaire #15571 : machinerie rapide (le rapport complet la
# rejoue en reps=3 sur la vraie cible, 1,8 M candidats ~ 58 s)
# ---------------------------------------------------------------------------


def test_machinerie_baseline_sur_petite_boite() -> None:
    found = synthesize(1, (0, 0), 4, 4)
    shapes = {frozenset(s) for s in found}
    bloc = frozenset({(0, 0), (1, 0), (0, 1), (1, 1)})
    assert bloc in shapes
    for s in found:
        cells = set(s)
        assert step(cells) == cells  # tout résultat est bien un still life
