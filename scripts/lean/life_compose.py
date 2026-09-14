#!/usr/bin/env python3
"""Générateur de contraintes compositionnelles + démonstrateur (tranche 3+4 de #15635).

Ce module ajoute la couche de recherche par composants au-dessus du schéma
symbolique de `life_components` (tranche 1+2, PR #15653) et du moteur cellulaire
de #15571 (`life_synthesize`). La chaîne visée par l'issue :

    objectif génératif
      -> sélection et assemblage de composants/réactions
      -> contraintes temporelles, spatiales et d'interface
      -> replay indépendant dans le moteur Life
      -> témoin ou frontière d'impossibilité bornée

Le modèle à contraintes PROPOSE, le replay du moteur dispose : toute scène
jugée satisfaisante au niveau symbolique est re-certifiée pas à pas contre le
vrai moteur avant d'être publiée. Un écart modèle/replay est compté comme
``replay_rejected``, jamais maquillé.

Sémantique des ports (définie par cette tranche — la tranche 1 ne spécifiait
que la structure) :

  * pour un réactif MOBILE, ``direction`` = les signes, par axe, de la
    translation par période du motif qui emprunte le port (le glider
    ``t=(1,-1)`` entre par un port ``[1,-1]``) ;
  * pour un réactif STATIQUE, ``direction`` = l'axe du connecteur : la
    direction, depuis le placement déclaré, vers le lieu de l'interaction
    (le bloc de ``block_catalyses_glider`` porte ``[-1,0]``).

Quatre familles de pruning, toutes instrumentées (compteurs, ablations une à
une, le replay de certification n'étant JAMAIS ablé) :

  * **R1 bris de symétrie** : ancrage du premier événement à l'origine
    (invariance par translation de la scène entière) et déduplication des
    états de recherche équivalents ;
  * **R2 filtrage type/port** : un réactif ne se lie qu'à un composant du
    motif déclaré dont la translation est compatible avec le port ; les
    réactions sans contribution possible à l'objectif sont écartées ;
  * **R3 pruning spatial** : enveloppes gonflées (+1, seuil de
    non-interaction de Conway) disjointes pour toute paire non réagissante,
    respect des zones de clearance et des cellules de fenêtre des événements ;
  * **R4 pruning temporel** : congruence de phase (un ``t`` hors de la classe
    requise élimine le candidat) et fenêtres de tir dans l'horizon borné.

Usage :
    python scripts/lean/life_compose.py --objective two_blocks_catalyse
    python scripts/lean/life_compose.py --objective two_blocks --json
    python scripts/lean/life_compose.py --objective two_blocks_catalyse --ablate r3
    python scripts/lean/life_compose.py --objective two_blocks --full-report --json
"""

from __future__ import annotations

import argparse
import itertools
import json
import time
import tracemalloc
from dataclasses import dataclass
from math import comb
from pathlib import Path
from typing import Any, Iterator, Sequence

import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))

from life_synthesize import Cell, Grid, evolve, normalize, step  # noqa: E402
from life_components import (  # noqa: E402
    Catalog,
    Reaction,
    load_catalog,
    measure_motif,
)

# Seuil de non-interaction de Conway : deux groupes de cellules à distance
# de Chebysyshev >= 2 ne se voient pas. Gonfler chaque enveloppe de 1
# matérialise exactement cette frontière.
GROW = 1

DEFAULT_NODE_BUDGET = 200_000

ABLATION_FAMILIES = ("r1", "r2", "r3", "r4")


class BudgetHit(RuntimeError):
    """Le budget de noeuds est épuisé : verdict TIMEOUT, pas un échec."""


# ---------------------------------------------------------------------------
# Modèle : composants (variables de choix) et événements
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Spawn:
    """Composant initial : un motif posé à t=0 (variable de choix)."""

    motif_id: str
    anchor: tuple[int, int]
    phase0: int


@dataclass(frozen=True)
class ProductBirth:
    """Composant né d'un événement (placement produit déclaré)."""

    event_idx: int
    placement_idx: int
    motif_id: str
    anchor: tuple[int, int]
    phase0: int
    t0: int


@dataclass(frozen=True)
class StaticProduct:
    """Produit statique brut (champ product_cells d'une réaction)."""

    event_idx: int
    cells: tuple[Cell, ...]
    t0: int


Handle = Spawn | ProductBirth | StaticProduct


@dataclass(frozen=True)
class EventInst:
    """Une réaction tirée : cadre translaté, instant, liaisons par réactif."""

    idx: int
    reaction_id: str
    offset: tuple[int, int]
    t_fire: int
    bindings: tuple[Handle, ...]


def handle_key(h: Handle) -> tuple:
    if isinstance(h, Spawn):
        return ("spawn", h.motif_id, h.anchor, h.phase0)
    if isinstance(h, ProductBirth):
        return ("product", h.event_idx, h.placement_idx)
    return ("static", h.event_idx)


def t_start(h: Handle) -> int:
    if isinstance(h, Spawn):
        return 0
    return h.t0


def is_spawn_like(h: Handle) -> bool:
    return isinstance(h, (Spawn, ProductBirth))


def _motif_phases(catalog: Catalog, motif_id: str) -> dict[int, tuple[Cell, ...]]:
    motif = catalog.motifs[motif_id]
    if motif.phases is not None:
        return motif.phases
    return measure_motif(motif.cells).phases


_PHASE_OFFSET_CACHE: dict[str, dict[int, tuple[int, int]]] = {}


def _motif_phase_offsets(catalog: Catalog, motif_id: str) -> dict[int, tuple[int, int]]:
    """Coin min de chaque phase, relativement au coin de la phase de base.

    Les phases stockées par la tranche 1 sont NORMALISÉES (coin à l'origine) :
    la forme seule ne dit pas où elle se trouve dans le cycle. Un glider dont
    on efface ce décalage inter-phases suit une fausse trajectoire dès t=1 —
    c'est le premier écart modèle/replay que la certification a attrapé.
    """
    cached = _PHASE_OFFSET_CACHE.get(motif_id)
    if cached is not None:
        return cached
    motif = catalog.motifs[motif_id]
    base = normalize(set(motif.cells))
    corners: dict[int, tuple[int, int]] = {}
    for k in range(motif.period):
        evolved = evolve(k, set(base))
        corners[k] = (
            min(x for x, _ in evolved),
            min(y for _, y in evolved),
        )
    _PHASE_OFFSET_CACHE[motif_id] = corners
    return corners


def _phase_position(
    catalog: Catalog, motif_id: str, anchor: tuple[int, int], p0: int, t0: int, t: int
) -> tuple[tuple[int, int], int]:
    """(position de la forme normalisée courante, index de phase) à l'instant t.

    Le cycle démarre à la phase p0 : l'index de phase à t est (p0 + t - t0)
    mod P et le nombre de périodes écoulées est (p0 + t - t0) // P — pas
    (t - t0) // P, qui oublierait les périodes déjà parcourues par la phase
    initiale (piège mesuré : glider p0=3 décalé d'une diagonale à t=1).
    """
    motif = catalog.motifs[motif_id]
    tx, ty = motif.translation_step
    elapsed = p0 + t - t0
    k = elapsed // motif.period
    phase = elapsed % motif.period
    corner = _motif_phase_offsets(catalog, motif_id)[phase]
    return (
        (anchor[0] + corner[0] + tx * k, anchor[1] + corner[1] + ty * k),
        phase,
    )


def cells_at(catalog: Catalog, h: Handle, t: int) -> Grid:
    """Cellules exactes d'un composant à l'instant t (trajectoire dérivée).

    Pour un motif de période P et de translation par période T, posé avec la
    phase p0 à l'ancre `anchor` (position de la forme normalisée de phase 0)
    et né à t0 :
        phase(t)    = (p0 + t - t0) mod P
        position(t) = anchor + coin(phase) + T * ((t - t0) // P)
    Exact, pas approché : la certification replay le vérifie pas à pas.
    """
    if isinstance(h, StaticProduct):
        return set(h.cells) if t >= h.t0 else set()
    if isinstance(h, Spawn):
        motif_id, p0, t0, anchor = h.motif_id, h.phase0, 0, h.anchor
    else:
        motif_id, p0, t0, anchor = h.motif_id, h.phase0, h.t0, h.anchor
    if t < t0:
        return set()
    (dx, dy), phase = _phase_position(catalog, motif_id, anchor, p0, t0, t)
    return {(x + dx, y + dy) for (x, y) in _motif_phases(catalog, motif_id)[phase]}


def anchor_at(catalog: Catalog, h: Handle, t: int) -> tuple[int, int] | None:
    """Position de la forme normalisée courante d'un composant à l'instant t."""
    if not is_spawn_like(h):
        return None
    if isinstance(h, Spawn):
        motif_id, p0, t0, anchor = h.motif_id, h.phase0, 0, h.anchor
    else:
        motif_id, p0, t0, anchor = h.motif_id, h.phase0, h.t0, h.anchor
    if t < t0:
        return None
    return _phase_position(catalog, motif_id, anchor, p0, t0, t)[0]


def phase_at(catalog: Catalog, h: Handle, t: int) -> int | None:
    if not is_spawn_like(h):
        return None
    motif = catalog.motifs[h.motif_id]
    if isinstance(h, Spawn):
        p0, t0 = h.phase0, 0
    else:
        p0, t0 = h.phase0, h.t0
    if t < t0:
        return None
    return (p0 + t - t0) % motif.period


def _rect_of(cells: Iterable[Cell]) -> tuple[int, int, int, int] | None:
    grid = set(cells)
    if not grid:
        return None
    x0 = min(x for x, _ in grid)
    y0 = min(y for _, y in grid)
    x1 = max(x for x, _ in grid)
    y1 = max(y for _, y in grid)
    return (x0, y0, x1 - x0 + 1, y1 - y0 + 1)


def swept_rect(
    catalog: Catalog, h: Handle, t_from: int, t_to: int
) -> tuple[int, int, int, int] | None:
    """Sur-ensemble rectangulaire du volume parcouru sur [t_from, t_to].

    Conservateur : union des cellules aux instants extrêmes et médian (la
    dérive est linéaire par période, donc monotone par axe).
    """
    if isinstance(h, StaticProduct):
        return _rect_of(h.cells)
    if t_to < t_start(h):
        return None
    t_from = max(t_from, t_start(h))
    union: Grid = set()
    for t in {t_from, t_to, (t_from + t_to) // 2}:
        union |= cells_at(catalog, h, t)
    return _rect_of(union)


def _grown(
    rect: tuple[int, int, int, int], g: int = GROW
) -> tuple[int, int, int, int]:
    x0, y0, w, h = rect
    return (x0 - g, y0 - g, w + 2 * g, h + 2 * g)


def _rects_overlap(a: tuple[int, int, int, int], b: tuple[int, int, int, int]) -> bool:
    ax0, ay0, aw, ah = a
    bx0, by0, bw, bh = b
    return ax0 < bx0 + bw and bx0 < ax0 + aw and ay0 < by0 + bh and by0 < ay0 + ah


def _rect_contains_cell(
    rect: tuple[int, int, int, int], cell: Cell
) -> bool:
    x0, y0, w, h = rect
    x, y = cell
    return x0 <= x < x0 + w and y0 <= y < y0 + h


def _min_chebyshev(a: Grid, b: Grid) -> int:
    best = 10**9
    for (x1, y1) in a:
        for (x2, y2) in b:
            d = max(abs(x1 - x2), abs(y1 - y2))
            if d < best:
                best = d
    return best


# ---------------------------------------------------------------------------
# Fenêtres de réaction : replay solo (mémoïsé)
# ---------------------------------------------------------------------------

_WINDOW_CACHE: dict[tuple[str, tuple[int, int]], list[Grid]] = {}


def reaction_initial_cells(catalog: Catalog, reaction: Reaction) -> Grid:
    """Réactifs déclarés posés dans le cadre propre de la réaction."""
    grid: Grid = set()
    for placement in reaction.reactants:
        phase_cells = _motif_phases(catalog, placement.motif_id)[placement.phase]
        dx, dy = placement.offset
        grid |= {(x + dx, y + dy) for (x, y) in phase_cells}
    return grid


def reaction_window_cells(
    catalog: Catalog, reaction: Reaction, offset: tuple[int, int]
) -> list[Grid]:
    """Évolution solo de la réaction translatée : cellules à t=0..stabilisation."""
    key = (reaction.id, offset)
    cached = _WINDOW_CACHE.get(key)
    if cached is not None:
        return cached
    base = reaction_initial_cells(catalog, reaction)
    dx, dy = offset
    cells = {(x + dx, y + dy) for (x, y) in base}
    window = [set(cells)]
    for _ in range(reaction.stabilization_time):
        cells = step(cells)
        window.append(set(cells))
    _WINDOW_CACHE[key] = window
    return window


def product_handles(catalog: Catalog, event: EventInst) -> list[Handle]:
    """Composants nés d'un événement : placements produits, ou cellules brutes."""
    reaction = catalog.reactions[event.reaction_id]
    t0 = event.t_fire + reaction.stabilization_time
    born: list[Handle] = []
    if reaction.products:
        for k, placement in enumerate(reaction.products):
            born.append(
                ProductBirth(
                    event_idx=event.idx,
                    placement_idx=k,
                    motif_id=placement.motif_id,
                    anchor=(
                        placement.offset[0] + event.offset[0],
                        placement.offset[1] + event.offset[1],
                    ),
                    phase0=placement.phase,
                    t0=t0,
                )
            )
    elif reaction.product_cells is not None:
        dx, dy = event.offset
        born.append(
            StaticProduct(
                event_idx=event.idx,
                cells=tuple((x + dx, y + dy) for (x, y) in reaction.product_cells),
                t0=t0,
            )
        )
    return born


# ---------------------------------------------------------------------------
# Objectifs
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Goal:
    """Objectif borné : comptes finaux, événements exigés, budgets."""

    name: str
    final_min_counts: dict[str, int]
    required_events: dict[str, int]
    max_events: int
    max_components: int
    horizon: int
    surface: tuple[int, int]
    max_gliders: int
    spawn_kinds: tuple[str, ...] = ("spaceship",)


OBJECTIVES: dict[str, Goal] = {
    "two_blocks": Goal(
        name="two_blocks",
        final_min_counts={"block": 2},
        required_events={},
        max_events=1,
        max_components=2,
        horizon=24,
        surface=(24, 24),
        max_gliders=2,
    ),
    # Variante stricte : la catalyse DOIT réutiliser un bloc produit par un
    # événement antérieur (aucun spawn statique autorisé). Le produit de
    # glider_pair_two_blocks est une paire de blocs séparés d'une colonne :
    # tout épisode catalytique sur l'un des deux voit l'autre à Chebyshev 2,
    # et la transmutation du bloc lié engendre des naissances croisées dans
    # la colonne intercalaire -- le replay exact rejette tous les candidats.
    # Objectif démonstrateur d'impossibilité bornée racinée.
    "two_blocks_catalyse": Goal(
        name="two_blocks_catalyse",
        final_min_counts={"block": 2},
        required_events={"block_catalyses_glider": 1},
        max_events=2,
        max_components=3,
        horizon=60,
        surface=(32, 32),
        max_gliders=3,
    ),
    # Variante libre : même chaîne, mais le bloc catalysé peut être un spawn
    # statique (4 composants). Démontreuse FOUND avec réutilisation temporelle
    # des événements et contrainte d'interface port/phase active.
    "two_blocks_catalyse_free": Goal(
        name="two_blocks_catalyse_free",
        final_min_counts={"block": 2},
        required_events={
            "block_catalyses_glider": 1,
            "glider_pair_two_blocks": 1,
        },
        max_events=2,
        max_components=4,
        horizon=60,
        surface=(40, 40),
        max_gliders=3,
        spawn_kinds=("spaceship", "still_life"),
    ),
}

BLOCK_SHAPE: tuple[Cell, ...] = ((0, 0), (1, 0), (0, 1), (1, 1))

# Cible partagée avec la baseline cellulaire de #15571 : deux blocs 2x2
# séparés par une colonne vide (le produit de glider_pair_two_blocks).
TWO_BLOCKS_TARGET: tuple[Cell, ...] = (
    (0, 0), (1, 0), (0, 1), (1, 1),
    (3, 0), (4, 0), (3, 1), (4, 1),
)


def blocks_in(cells: Grid) -> list[tuple[int, int]]:
    """Positions des blocs 2x2 disjoints présents dans un ensemble de cellules."""
    found: list[tuple[int, int]] = []
    used: Grid = set()
    for (x, y) in sorted(cells):
        if (x, y) in used:
            continue
        square = {(x + dx, y + dy) for (dx, dy) in BLOCK_SHAPE}
        if square <= cells and not (square & used):
            found.append((x, y))
            used |= square
    return found


def goal_reached(
    catalog: Catalog, goal: Goal, events: Sequence[EventInst], live: Sequence[Handle]
) -> bool:
    """Évaluation symbolique de l'objectif (le replay certifie ensuite)."""
    fired: dict[str, int] = {}
    for event in events:
        fired[event.reaction_id] = fired.get(event.reaction_id, 0) + 1
    for reaction_id, count in goal.required_events.items():
        if fired.get(reaction_id, 0) < count:
            return False
    final: Grid = set()
    for h in live:
        final |= cells_at(catalog, h, goal.horizon)
    for motif_id, required in goal.final_min_counts.items():
        if motif_id == "block":
            if len(blocks_in(final)) < required:
                return False
        else:
            count = sum(
                1
                for h in live
                if is_spawn_like(h) and h.motif_id == motif_id
            )
            if count < required:
                return False
    return True


def reaction_useful(catalog: Catalog, goal: Goal, reaction_id: str) -> bool:
    """Une réaction contribue-t-elle à l'objectif (filtrage R2) ?

    Heuristique : la réaction est un événement exigé, ou produit (par
    placement ou par cellules brutes) un motif compté par l'objectif.
    """
    if reaction_id in goal.required_events:
        return True
    reaction = catalog.reactions[reaction_id]
    for placement in reaction.products:
        if placement.motif_id in goal.final_min_counts:
            return True
    if reaction.product_cells is not None:
        if "block" in goal.final_min_counts and blocks_in(set(reaction.product_cells)):
            return True
    return False


# ---------------------------------------------------------------------------
# Compatibilité des ports (sémantique de la tranche 3)
# ---------------------------------------------------------------------------


def port_compatible(catalog: Catalog, motif_id: str, port_direction: tuple[int, int]) -> bool:
    """Compatibilité port <-> motif, selon la sémantique documentée.

    Réactif mobile : les axes non nuls du port doivent être exactement les
    axes non nuls de la translation par période, avec les mêmes signes.
    Réactif statique (translation nulle) : tout port non nul est accepté —
    le port décrit l'orientation du connecteur, pas un mouvement.
    """
    motif = catalog.motifs[motif_id]
    tx, ty = motif.translation_step
    dx, dy = port_direction
    if tx == 0 and ty == 0:
        return not (dx == 0 and dy == 0)
    if (tx == 0) != (dx == 0) or (ty == 0) != (dy == 0):
        return False
    if dx != 0 and (dx > 0) != (tx > 0):
        return False
    if dy != 0 and (dy > 0) != (ty > 0):
        return False
    return True


# ---------------------------------------------------------------------------
# Recherche
# ---------------------------------------------------------------------------


def _new_counters() -> dict[str, int]:
    keys = [
        "candidates",
        "r1_anchor_collapsed",
        "r1_state_dedup",
        "r2_useful",
        "r2_type",
        "r2_port",
        "r3_envelope",
        "r3_clearance",
        "r4_phase",
        "r4_window",
        "model_anchor",
        "budget",
        "replay_rejected",
        "certified",
        "nodes",
    ]
    return {k: 0 for k in keys}


@dataclass
class SearchState:
    spawns: tuple[Spawn, ...] = ()
    events: tuple[EventInst, ...] = ()
    live: tuple[Handle, ...] = ()


def _handle_desc(h: Handle) -> tuple:
    """Descripteur structurel : ce dont le futur de l'objet dépend.

    L'identité de bookkeeping (index de l'événement producteur) est remplacée
    par la géométrie et le temps de naissance : deux états où le même objet
    naît au même endroit au même instant sont isomorphes, quel que soit
    l'ordre de tir des épisodes indépendants.
    """
    if isinstance(h, Spawn):
        return ("spawn", h.motif_id, h.anchor, h.phase0)
    if isinstance(h, ProductBirth):
        return ("product", h.motif_id, h.anchor, h.t0)
    return ("static", tuple(sorted(h.cells)), h.t0)


def _state_key(state: SearchState) -> tuple:
    """Clé de dédup canonique : multiset des spawns et des événements.

    Deux états de même clé ne diffèrent que par l'ORDRE de tir d'épisodes
    indépendants — et la sémantique du module est insensible à cet ordre :
    `certify` calcule la scène pas à pas comme une union (fenêtres indexées
    par temps, consommation last-writer unique puisqu'un réactif n'est lié
    qu'une fois), et `goal_reached` compte des identifiants de réaction. Le
    `live` n'est pas dans la clé : il est dérivé de (spawns, events).

    Deux clés TROP GROSSIÈRES ont produit des faux négatifs de complétude
    (mesurés) : une clé indépendante de la position avalait le produit d'un
    second épisode né ailleurs ; une clé réduite aux vivants + nombre
    d'événements confondait deux scènes aux mêmes produits à des temps de tir
    différents — sous ablation de R4, un état non certifiant partageant la
    clé du témoin était déplié d'abord, le témoin dédupliqué, et la recherche
    concluait IMPOSSIBLE_BOUNDED alors qu'un témoin existait. La clé porte
    désormais tout ce dont les transitions dépendent.
    """
    spawns = tuple(
        sorted((s.motif_id, s.anchor, s.phase0) for s in state.spawns)
    )
    events = tuple(
        sorted(
            (
                ev.reaction_id,
                ev.offset,
                ev.t_fire,
                tuple(sorted(_handle_desc(b) for b in ev.bindings)),
            )
            for ev in state.events
        )
    )
    return (spawns, events)


class Searcher:
    """Parcours déterministe des scènes compositionnelles bornées."""

    def __init__(
        self,
        catalog: Catalog,
        goal: Goal,
        ablations: frozenset[str] = frozenset(),
        allowed_spawns: set[str] | None = None,
        node_budget: int = DEFAULT_NODE_BUDGET,
        allow_static_spawns: bool = False,
    ) -> None:
        self.catalog = catalog
        self.goal = goal
        self.ablations = ablations
        self.allowed = allowed_spawns
        self.node_budget = node_budget
        self.allow_static_spawns = allow_static_spawns
        self.counters = _new_counters()
        self.seen_states: set[tuple] = set()
        self.witness: dict[str, Any] | None = None
        self.certified_count = 0

    # -- critères ----------------------------------------------------------

    def _end_times(
        self,
        state: SearchState,
        new_spawns: Sequence[Spawn],
        event: EventInst,
        consumed: set[tuple],
    ) -> dict[tuple, int]:
        """Instant de fin de vie de chaque composant du candidat.

        Un composant consommé par l'événement cesse d'exister à t_fire :
        le balayer au-delà ferait dériver son enveloppe après sa mort et
        rejetterait des scènes valides (leçon mesurée sur le premier run).
        """
        ends: dict[tuple, int] = {}
        for h in list(state.live) + list(new_spawns):
            key = handle_key(h)
            ends[key] = event.t_fire if key in consumed else self.goal.horizon
        return ends

    def _spawn_allowed(self, motif_id: str) -> bool:
        if self.allowed is not None and motif_id not in self.allowed:
            return False
        motif = self.catalog.motifs[motif_id]
        if motif.kind in self.goal.spawn_kinds:
            return True
        return self.allow_static_spawns

    def _extent_grid(self, state: SearchState) -> list[tuple[int, int]]:
        """Grille de décalages autour de l'emprise courante (énumération e).

        Deux échelles : une grille fine à ±4 (alignements proches) et un
        anneau grossier au pas 4 borné par la surface, pour garer un épisode
        indépendant loin de la scène existante -- la liaison sur un handle
        existant résout e par équation, l'anneau ne sert donc qu'aux spawns
        neufs (scènes multi-épisodes disjointes).
        """
        rects = [
            swept_rect(self.catalog, h, 0, self.goal.horizon)
            for h in state.live
        ]
        rects = [r for r in rects if r is not None]
        if not rects:
            return [(0, 0)]
        x0 = min(r[0] for r in rects) - 4
        x1 = max(r[0] + r[2] for r in rects) + 4
        y0 = min(r[1] for r in rects) - 4
        y1 = max(r[1] + r[3] for r in rects) + 4
        fine = [
            (x, y)
            for x in range(x0, x1 + 1)
            for y in range(y0, y1 + 1)
        ]
        reach = max(self.goal.surface) // 2
        ring = [
            (x, y)
            for x in range(x0 - reach, x1 + reach + 1, 4)
            for y in range(y0 - reach, y1 + reach + 1, 4)
            if not (x0 <= x <= x1 and y0 <= y <= y1)
        ]
        return fine + ring

    def _surface_ok(
        self,
        handles: Sequence[Handle],
        events: Sequence[EventInst],
        ends: dict[tuple, int],
    ) -> bool:
        """Emprise globale de la scène (enveloppes + fenêtres) sous budget."""
        rects: list[tuple[int, int, int, int]] = []
        for h in handles:
            r = swept_rect(self.catalog, h, 0, ends[handle_key(h)])
            if r is not None:
                rects.append(r)
        for event in events:
            reaction = self.catalog.reactions[event.reaction_id]
            window = reaction_window_cells(self.catalog, reaction, event.offset)
            ever: Grid = set()
            for cells in window:
                ever |= cells
            r = _rect_of(ever)
            if r is not None:
                rects.append(r)
        if not rects:
            return True
        x0 = min(r[0] for r in rects)
        y0 = min(r[1] for r in rects)
        w = max(r[0] + r[2] for r in rects) - x0
        h = max(r[1] + r[3] for r in rects) - y0
        return w <= self.goal.surface[0] and h <= self.goal.surface[1]

    def _spatial_ok(
        self,
        state: SearchState,
        new_spawns: Sequence[Spawn],
        event: EventInst,
        consumed: set[tuple],
    ) -> bool:
        """R3 : non-interaction spatiale de toute paire non réagissante.

        Paires réagissantes (consommées par le même événement) : distance
        de Chebyshev exacte >= 2 pour tout t < t_fire (elles doivent se
        rejoindre à l'instant déclaré, pas avant).
        Paires non réagissantes : enveloppes balayées gonflées disjointes
        sur la coexistence ; composants vs fenêtres/clearances des événements.
        """
        catalog = self.catalog
        horizon = self.goal.horizon
        handles = list(state.live) + list(new_spawns)
        ends = self._end_times(state, new_spawns, event, consumed)
        # fenêtres : cet événement + les événements déjà tirés
        all_events = list(state.events) + [event]
        windows = {
            ev.idx: reaction_window_cells(
                catalog, catalog.reactions[ev.reaction_id], ev.offset
            )
            for ev in all_events
        }
        for i in range(len(handles)):
            for j in range(i + 1, len(handles)):
                a, b = handles[i], handles[j]
                ka, kb = handle_key(a), handle_key(b)
                reacting_pair = ka in consumed and kb in consumed
                if reacting_pair:
                    for t in range(max(t_start(a), t_start(b)), event.t_fire):
                        if _min_chebyshev(
                            cells_at(catalog, a, t), cells_at(catalog, b, t)
                        ) < 2:
                            return False
                else:
                    t_end = min(ends[ka], ends[kb])
                    ra = swept_rect(catalog, a, 0, t_end)
                    rb = swept_rect(catalog, b, 0, t_end)
                    if ra and rb and _rects_overlap(_grown(ra), _grown(rb)):
                        # emprises proches : contrôle exact, instant par instant
                        # (deux blocs séparés d'une colonne sont à Chebyshev 2 :
                        # non-interaction réelle que les rectangles se touchent)
                        for t in range(max(t_start(a), t_start(b)), t_end + 1):
                            if _min_chebyshev(
                                cells_at(catalog, a, t), cells_at(catalog, b, t)
                            ) < 2:
                                return False
        for h in handles:
            if handle_key(h) in consumed:
                continue
            for ev in all_events:
                # un produit EST la dernière image de la fenêtre de son
                # propre événement : le confronter à elle est un faux positif
                # (le replay couvre déjà la transition aux bornes exactes)
                if isinstance(h, (ProductBirth, StaticProduct)) and h.event_idx == ev.idx:
                    continue
                reaction = catalog.reactions[ev.reaction_id]
                window = windows[ev.idx]
                ever: Grid = set()
                for cells in window:
                    ever |= cells
                wrect = _rect_of(ever)
                if wrect is None:
                    continue
                r = swept_rect(catalog, h, 0, ends[handle_key(h)])
                if r is None:
                    continue
                if not _rects_overlap(_grown(wrect), _grown(r)):
                    continue
                # emprises proches : contrôle exact, instant par instant
                for k, cells in enumerate(window):
                    t = ev.t_fire + k
                    hc = cells_at(catalog, h, t)
                    if hc and _min_chebyshev(hc, cells) < 2:
                        return False
                for rect in reaction.clearance:
                    x0, y0, w, hgt = rect
                    abs_rect = (x0 + ev.offset[0], y0 + ev.offset[1], w, hgt)
                    for t in range(ev.t_fire, ev.t_fire + reaction.stabilization_time):
                        for cell in cells_at(catalog, h, t):
                            if _rect_contains_cell(abs_rect, cell):
                                return False
        return True

    # -- énumération ---------------------------------------------------------

    def _enumerate_events(
        self, state: SearchState, depth: int
    ) -> Iterator[tuple[EventInst, tuple[Spawn, ...], set[tuple]]]:
        catalog = self.catalog
        goal = self.goal
        counters = self.counters
        ablate = self.ablations
        for reaction_id in sorted(catalog.reactions):
            reaction = catalog.reactions[reaction_id]
            if "r2" not in ablate and not reaction_useful(catalog, goal, reaction_id):
                counters["r2_useful"] += 1
                continue
            stab = reaction.stabilization_time
            for t_fire in range(0, goal.horizon - stab + 1):
                option_lists: list[list[tuple[str, Handle | None]]] = []
                feasible = True
                for i, decl in enumerate(reaction.reactants):
                    options: list[tuple[str, Handle | None]] = []
                    port = reaction.ports[i] if i < len(reaction.ports) else None
                    for h in state.live:
                        if not is_spawn_like(h):
                            continue
                        if t_start(h) > t_fire:
                            counters["r4_window"] += 1
                            continue
                        motif = catalog.motifs[h.motif_id]
                        if "r2" not in ablate:
                            if motif.id != decl.motif_id:
                                counters["r2_type"] += 1
                                continue
                            if port is not None and not port_compatible(
                                catalog, motif.id, port.direction
                            ):
                                counters["r2_port"] += 1
                                continue
                        if "r4" not in ablate:
                            ph = phase_at(catalog, h, t_fire)
                            if ph != decl.phase:
                                counters["r4_phase"] += 1
                                continue
                        options.append(("bind", h))
                    if self._spawn_allowed(decl.motif_id):
                        options.append(("spawn", None))
                    if not options:
                        feasible = False
                        counters["r2_type"] += 1
                        break
                    option_lists.append(options)
                if not feasible:
                    continue
                for combo in itertools.product(*option_lists):
                    counters["candidates"] += 1
                    spawn_slots = [
                        i
                        for i, (kind, _) in enumerate(combo)
                        if kind == "spawn"
                    ]
                    phase_domains = []
                    for i in spawn_slots:
                        decl = reaction.reactants[i]
                        period = catalog.motifs[decl.motif_id].period
                        phase_domains.append(range(period))
                    for phases in itertools.product(*phase_domains) if phase_domains else [()]:
                        phase_map = dict(zip(spawn_slots, phases))
                        # détermination du décalage e
                        offset: tuple[int, int] | None = None
                        consistent = True
                        for i, (kind, h) in enumerate(combo):
                            if kind != "bind":
                                continue
                            decl = reaction.reactants[i]
                            anchor = anchor_at(catalog, h, t_fire)  # type: ignore[arg-type]
                            if anchor is None:
                                consistent = False
                                break
                            candidate_e = (
                                anchor[0] - decl.offset[0],
                                anchor[1] - decl.offset[1],
                            )
                            if offset is None:
                                offset = candidate_e
                            elif offset != candidate_e:
                                counters["model_anchor"] += 1
                                consistent = False
                                break
                        if not consistent:
                            continue
                        offset_iter: Iterator[tuple[int, int]]
                        if offset is not None:
                            offset_iter = iter([offset])
                        elif depth == 0 and "r1" not in ablate:
                            counters["r1_anchor_collapsed"] += 1
                            offset_iter = iter([(0, 0)])
                        else:
                            offset_iter = iter(self._extent_grid(state))
                        for e in offset_iter:
                            # dérivation des spawns (phase énumérée, R4 filtre)
                            spawns: list[Spawn] = []
                            ok = True
                            for i in spawn_slots:
                                decl = reaction.reactants[i]
                                motif = catalog.motifs[decl.motif_id]
                                tx, ty = motif.translation_step
                                p0 = phase_map[i]
                                if "r4" not in ablate:
                                    forced = decl.phase - t_fire
                                    forced %= motif.period
                                    if p0 != forced:
                                        counters["r4_phase"] += 1
                                        ok = False
                                        break
                                corner = _motif_phase_offsets(
                                    catalog, decl.motif_id
                                )[decl.phase]
                                periods = (p0 + t_fire) // motif.period
                                anchor = (
                                    e[0] + decl.offset[0] - corner[0] - tx * periods,
                                    e[1] + decl.offset[1] - corner[1] - ty * periods,
                                )
                                spawns.append(
                                    Spawn(motif_id=decl.motif_id, anchor=anchor, phase0=p0)
                                )
                            if not ok:
                                continue
                            bindings = tuple(
                                h if kind == "bind" else spawns[spawn_slots.index(i)]
                                for i, (kind, h) in enumerate(combo)
                            )
                            consumed = {handle_key(b) for b in bindings}
                            event = EventInst(
                                idx=len(state.events),
                                reaction_id=reaction_id,
                                offset=e,
                                t_fire=t_fire,
                                bindings=bindings,
                            )
                            # budgets
                            total_spawns = tuple(state.spawns) + tuple(spawns)
                            gliders = sum(
                                1
                                for s in total_spawns
                                if catalog.motifs[s.motif_id].kind == "spaceship"
                            )
                            if (
                                len(total_spawns) > goal.max_components
                                or gliders > goal.max_gliders
                            ):
                                counters["budget"] += 1
                                continue
                            if not self._surface_ok(
                                list(state.live) + spawns,
                                list(state.events) + [event],
                                self._end_times(state, spawns, event, consumed),
                            ):
                                counters["budget"] += 1
                                continue
                            # R3 spatial
                            if "r3" not in ablate and not self._spatial_ok(
                                state, spawns, event, consumed
                            ):
                                counters["r3_envelope"] += 1
                                continue
                            yield event, tuple(spawns), consumed

    # -- parcours ------------------------------------------------------------

    def run(self) -> dict[str, Any]:
        try:
            self._search(SearchState(), 0)
        except BudgetHit:
            if self.witness is not None:
                return self._report("FOUND")
            return self._report("TIMEOUT")
        if self.witness is not None:
            return self._report("FOUND")
        return self._report("IMPOSSIBLE_BOUNDED")

    def _search(self, state: SearchState, depth: int) -> None:
        self.counters["nodes"] += 1
        if self.counters["nodes"] > self.node_budget:
            raise BudgetHit
        if goal_reached(self.catalog, self.goal, state.events, state.live):
            verdict = certify(self.catalog, self.goal, state.spawns, state.events)
            if verdict["ok"]:
                self.counters["certified"] += 1
                if self.witness is None:
                    self.witness = {
                        "spawns": [s.__dict__ | {"anchor": list(s.anchor)} for s in state.spawns],
                        "events": [
                            {
                                "reaction_id": ev.reaction_id,
                                "offset": list(ev.offset),
                                "t_fire": ev.t_fire,
                                "bindings": [
                                    handle_key(b).__repr__() for b in ev.bindings
                                ],
                            }
                            for ev in state.events
                        ],
                        "initial_cells": sorted(
                            tuple(c)
                            for s in state.spawns
                            for c in cells_at(self.catalog, s, 0)
                        ),
                        "final_cells": sorted(tuple(c) for c in verdict["final_cells"]),
                        "blocks_final": verdict["blocks_final"],
                        "steps_checked": verdict["steps_checked"],
                    }
                return
            self.counters["replay_rejected"] += 1
            return
        if depth >= self.goal.max_events:
            return
        for event, spawns, _consumed in self._enumerate_events(state, depth):
            if self.witness is not None:
                return
            new_live = tuple(
                h for h in state.live if handle_key(h) not in {handle_key(b) for b in event.bindings}
            ) + tuple(product_handles(self.catalog, event))
            new_state = SearchState(
                spawns=state.spawns + spawns,
                events=state.events + (event,),
                live=new_live,
            )
            key = _state_key(new_state)
            if "r1" not in self.ablations:
                if key in self.seen_states:
                    self.counters["r1_state_dedup"] += 1
                    continue
                self.seen_states.add(key)
            self._search(new_state, depth + 1)

    def _report(self, verdict: str) -> dict[str, Any]:
        return {
            "objective": self.goal.name,
            "verdict": verdict,
            "witness": self.witness,
            "stats": dict(self.counters),
        }


# Convention du fixture (tranche 1+2) : les ports sont listés dans l'ordre des
# réactifs (in0 -> reactants[0], in1 -> reactants[1]). L'énumération indexe
# directement reaction.ports[i].


# ---------------------------------------------------------------------------
# Certification : replay indépendant pas à pas
# ---------------------------------------------------------------------------


def certify(
    catalog: Catalog, goal: Goal, spawns: Sequence[Spawn], events: Sequence[EventInst]
) -> dict[str, Any]:
    """Rejoue la scène entière dans le moteur et vérifie, à chaque pas :

    * scène(t) == union(trajectoires pures) + fenêtres des événements actifs ;
    * les zones de clearance ne sont jamais traversées pendant leur fenêtre.

    La trajectoire pure d'un composant non réagissant et la fenêtre d'une
    réaction sont deux mondes qui ne se mélangent pas : leur réunion exacte à
    chaque pas est la preuve d'absence de rétrointeraction destructive.
    """
    handles: list[Handle] = list(spawns)
    for event in events:
        handles.extend(product_handles(catalog, event))
    consumed_at: dict[tuple, int] = {}
    for event in events:
        for b in event.bindings:
            consumed_at[handle_key(b)] = event.t_fire
    windows = {
        ev.idx: reaction_window_cells(catalog, catalog.reactions[ev.reaction_id], ev.offset)
        for ev in events
    }
    scene: Grid = set()
    for s in spawns:
        scene |= cells_at(catalog, s, 0)
    initial_cells = set(scene)
    mismatches: list[dict[str, Any]] = []
    clearance_violations: list[dict[str, Any]] = []
    final_cells: Grid = set()
    for t in range(goal.horizon + 1):
        expected: Grid = set()
        for h in handles:
            key = handle_key(h)
            if t < t_start(h):
                continue
            if consumed_at.get(key, 10**9) <= t:
                continue
            expected |= cells_at(catalog, h, t)
        for ev in events:
            reaction = catalog.reactions[ev.reaction_id]
            if ev.t_fire <= t < ev.t_fire + reaction.stabilization_time:
                expected |= windows[ev.idx][t - ev.t_fire]
        if scene != expected:
            mismatches.append(
                {
                    "t": t,
                    "delta": sorted(
                        tuple(c) for c in (scene ^ expected)
                    )[:8],
                }
            )
        for ev in events:
            reaction = catalog.reactions[ev.reaction_id]
            if ev.t_fire <= t < ev.t_fire + reaction.stabilization_time:
                for (x0, y0, w, h) in reaction.clearance:
                    abs_rect = (x0 + ev.offset[0], y0 + ev.offset[1], w, h)
                    hit = sorted(
                        tuple(c)
                        for c in scene
                        if _rect_contains_cell(abs_rect, c)
                    )
                    if hit:
                        clearance_violations.append({"t": t, "rect": abs_rect, "hit": hit[:4]})
        final_cells = set(scene)
        if t < goal.horizon:
            scene = step(scene)
    return {
        "ok": not mismatches and not clearance_violations,
        "steps_checked": goal.horizon + 1,
        "mismatches": mismatches[:5],
        "clearance_violations": clearance_violations[:5],
        "final_cells": final_cells,
        "blocks_final": blocks_in(final_cells),
    }


# ---------------------------------------------------------------------------
# Comparaison avec la baseline cellulaire de #15571
# ---------------------------------------------------------------------------


def _run_sig(run: dict[str, Any]) -> dict[str, Any]:
    # la stabilité compare le CONTENU des répétitions (verdict, nœuds,
    # candidats, témoin) — jamais wall_s/peak, qui varient avec la machine
    return {k: v for k, v in run.items() if k not in ("wall_s", "peak_mem_kib")}


def run_baseline(reps: int = 3) -> dict[str, Any]:
    """Baseline B1 : énumération cellulaire de life_synthesize sur la cible.

    `synthesize(1, (0,0), box, max_cells)` retourne TOUTES les formes de
    still lifes de taille <= max_cells dans la boîte : la baseline n'accepte
    pas de cible, son coût pour atteindre LA forme visée est donc son
    énumération complète (appartenance vérifiée a posteriori). Elle produit
    une existence, pas une construction — c'est mesuré, pas caché.
    """
    from life_synthesize import synthesize

    box, max_cells = 5, 8
    target = normalize(set(TWO_BLOCKS_TARGET))
    runs = []
    for _ in range(reps):
        tracemalloc.start()
        t0 = time.perf_counter()
        found = synthesize(1, (0, 0), box, max_cells)
        wall = time.perf_counter() - t0
        _, peak = tracemalloc.get_traced_memory()
        tracemalloc.stop()
        normalized = [normalize(set(p)) for p in found]
        runs.append(
            {
                "wall_s": round(wall, 3),
                "peak_mem_kib": peak // 1024,
                "candidates": sum(
                    comb(box * box, k) for k in range(1, max_cells + 1)
                ),
                "still_lifes_found": len(found),
                "target_found": target in normalized,
            }
        )
    return {
        "engine": "life_synthesize.synthesize (enumeration B1, #15571)",
        "spec": "evolve^1 T = T (still lifes), boite 5x5, <= 8 cellules",
        "target": [list(c) for c in target],
        "runs": runs,
        "stable": len({json.dumps(_run_sig(r), sort_keys=True) for r in runs}) == 1,
    }


def run_compositional(goal: Goal, reps: int = 3, **kwargs: Any) -> dict[str, Any]:
    runs = []
    for _ in range(reps):
        _WINDOW_CACHE.clear()
        tracemalloc.start()
        t0 = time.perf_counter()
        searcher = Searcher(load_catalog_fixture(kwargs["fixture"]), goal, **{
            k: v for k, v in kwargs.items() if k != "fixture"
        })
        report = searcher.run()
        wall = time.perf_counter() - t0
        _, peak = tracemalloc.get_traced_memory()
        tracemalloc.stop()
        runs.append(
            {
                "wall_s": round(wall, 4),
                "peak_mem_kib": peak // 1024,
                "verdict": report["verdict"],
                "nodes": report["stats"]["nodes"],
                "candidates": report["stats"]["candidates"],
            }
        )
    return {
        "engine": "life_compose (recherche compositionnelle, tranche 3+4)",
        "runs": runs,
        "stable": len({json.dumps(_run_sig(r), sort_keys=True) for r in runs}) == 1,
        "report": report,
    }


def load_catalog_fixture(path: str) -> Catalog:
    return load_catalog(path)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Recherche compositionnelle Life : générateur de contraintes + "
            "démonstrateur (tranche 3+4 de #15635)."
        )
    )
    parser.add_argument(
        "--fixture",
        default=str(Path(__file__).resolve().parent / "life_components_fixture.json"),
        help="catalogue de composants (tranche 1+2)",
    )
    parser.add_argument(
        "--objective",
        default="two_blocks_catalyse",
        choices=sorted(OBJECTIVES),
        help="objectif borné à résoudre",
    )
    parser.add_argument(
        "--ablate",
        default="",
        help="famille de pruning à désactiver (r1, r2, r3 ou r4)",
    )
    parser.add_argument("--node-budget", type=int, default=DEFAULT_NODE_BUDGET)
    parser.add_argument(
        "--restrict-motifs",
        default="",
        help="liste de motifs autorisés au spawn, séparés par des virgules (contrôle négatif)",
    )
    parser.add_argument(
        "--full-report",
        action="store_true",
        help="exécute base + 4 ablations + comparaison baseline (3 répétitions)",
    )
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)

    goal = OBJECTIVES[args.objective]
    allowed = set(args.restrict_motifs.split(",")) if args.restrict_motifs else None
    ablations = frozenset(a for a in args.ablate.split(",") if a)
    unknown = ablations - set(ABLATION_FAMILIES)
    if unknown:
        parser.error(f"familles d'ablation inconnues : {sorted(unknown)}")

    catalog = load_catalog(args.fixture)

    if args.full_report:
        payload = {
            "objective": args.objective,
            "base": run_compositional(
                goal, fixture=args.fixture, node_budget=args.node_budget
            ),
            "ablations": {
                fam: run_compositional(
                    goal,
                    fixture=args.fixture,
                    ablations=frozenset([fam]),
                    node_budget=args.node_budget,
                )
                for fam in ABLATION_FAMILIES
            },
        }
        if args.objective == "two_blocks":
            payload["baseline"] = run_baseline(reps=3)
        print(json.dumps(payload, ensure_ascii=False, indent=2))
        return 0

    tracemalloc.start()
    t0 = time.perf_counter()
    searcher = Searcher(
        catalog,
        goal,
        ablations=ablations,
        allowed_spawns=allowed,
        node_budget=args.node_budget,
    )
    report = searcher.run()
    report["wall_s"] = round(time.perf_counter() - t0, 4)
    _, peak = tracemalloc.get_traced_memory()
    tracemalloc.stop()
    report["peak_mem_kib"] = peak // 1024

    if args.json:
        print(json.dumps(report, ensure_ascii=False, indent=2))
        return 0 if report["verdict"] == "FOUND" else 1

    verdict = report["verdict"]
    stats = report["stats"]
    print(f"Objectif : {goal.name} — verdict : {verdict} ({report['wall_s']} s)")
    print(
        f"  noeuds={stats['nodes']} candidats={stats['candidates']} "
        f"certifiés={stats['certified']} replay_rejetés={stats['replay_rejected']}"
    )
    print(
        f"  pruning : r1(ancre+dedup)={stats['r1_anchor_collapsed'] + stats['r1_state_dedup']} "
        f"r2(useful/type/port)={stats['r2_useful'] + stats['r2_type'] + stats['r2_port']} "
        f"r3(envelope)={stats['r3_envelope']} r4(phase)={stats['r4_phase']}"
    )
    print(
        f"  rejets modèle : anchor={stats['model_anchor']} budget={stats['budget']} "
        f"fenêtre={stats['r4_window']}"
    )
    witness = report.get("witness")
    if witness:
        print(f"  témoin : {len(witness['initial_cells'])} cellules initiales")
        for ev in witness["events"]:
            print(
                f"    événement {ev['reaction_id']} à t={ev['t_fire']} "
                f"décalage={ev['offset']}"
            )
        print(f"  blocs finaux : {witness['blocks_final']}")
        print(f"  pas certifiés : {witness['steps_checked']}")
    return 0 if verdict == "FOUND" else 1


if __name__ == "__main__":
    raise SystemExit(main())
