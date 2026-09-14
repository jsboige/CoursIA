#!/usr/bin/env python3
"""Schema versionne de motifs et de reactions de Game of Life (tranche 1+2 de #15635).

Ce module ajoute la couche **symbolique** que le moteur cellulaire de #15571
n'a pas : un format machine-readable pour decrire des *motifs/composants*
(still lifes, oscillateurs, spaceships, conduits) et des *reactions*
(reactifs -> produits), avec une **validation par replay** dans le moteur Life
du depot (`life_synthesize`) plutot qu'une confiance dans les metadonnees
declarees.

La regle est celle de #15635, section 1 : « Chaque champ inconnu reste explicite
(`null`/absent documente), jamais invente. » Un motif dont la periode, la
translation, la population ou l'enveloppe declaree ne correspond pas a son
evolution reelle est **refuse** ; une reaction dont le produit declare ne
correspond pas a l'evolution jointe de ses reactifs est **refusee**.

Ce que cette tranche livre (criteres 1 et 2 de #15635) :

  * un schema versionne motifs + reactions, avec validation et tests de donnees
    invalides ;
  * un catalogue (fixture) cure, source, et **rejoue** : aucune metadonnee
    declaree n'est acceptee sur confiance ;
  * une canonicalisation par translation/rotation/reflexion qui **ne fusionne
    pas** des objets non equivalents (un glider qui monte n'est pas un glider
    qui descend).

Hors scope de cette tranche (tranches suivantes de #15635) : le generateur de
contraintes compositionnelles, les mecanismes de pruning et le demonstrateur
multi-composants.

Usage :
    python scripts/lean/life_components.py --fixture scripts/lean/life_components_fixture.json
    python scripts/lean/life_components.py --fixture <path> --json
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Iterable, Sequence

sys.path.insert(0, str(Path(__file__).resolve().parent))

from life_synthesize import Cell, Grid, evolve, normalize, step  # noqa: E402

SCHEMA_VERSION = "1.0.0"
CONWAY_RULE = "B3/S23"

# Reglages de surete de la mesure : un motif dont la periode ou la translation
# depasse ces bornes n'est pas « mesure », il est « hors du domaine de l'organe ».
MAX_PERIOD = 64
MAX_TRANSLATION = 16

# Operations de symetrie. Une symetrie n'est *admissible* pour un motif que si
# elle preserve son vecteur de translation : sinon elle echangerait deux objets
# non equivalents (un glider nord-est contre un glider sud-est).
SYMMETRY_OPS: dict[str, Any] = {
    "T": lambda c: [(x, y) for (x, y) in c],
    "R90": lambda c: [(y, -x) for (x, y) in c],
    "R180": lambda c: [(-x, -y) for (x, y) in c],
    "R270": lambda c: [(-y, x) for (x, y) in c],
    "Mx": lambda c: [(-x, y) for (x, y) in c],
    "My": lambda c: [(x, -y) for (x, y) in c],
    "D1": lambda c: [(y, x) for (x, y) in c],
    "D2": lambda c: [(-y, -x) for (x, y) in c],
}
FULL_DIHEDRAL = ("T", "R90", "R180", "R270", "Mx", "My", "D1", "D2")


class SchemaError(ValueError):
    """Un document ne respecte pas le schema, ou declare un fait faux."""


def _apply_symmetry(name: str, translation: tuple[int, int]) -> tuple[int, int]:
    """Image du vecteur de translation par la symetrie nommee."""
    (x, y) = SYMMETRY_OPS[name]([(translation[0], translation[1])])[0]
    return (x, y)


def admissible_symmetries(translation: tuple[int, int]) -> tuple[str, ...]:
    """Symetries qui preservent la direction de deplacement du motif."""
    return tuple(s for s in FULL_DIHEDRAL if _apply_symmetry(s, translation) == translation)


def canonical_form(
    cells: Iterable[Cell], symmetries: Sequence[str] = ("T",)
) -> tuple[Cell, ...]:
    """Forme canonique : minimum lexicographique sur les symetries autorisees.

    Le groupe applique est `symmetries`, jamais le groupe complet : passer
    `FULL_DIHEDRAL` a un spaceship fusionnerait ses quatre directions de vol.
    """
    grid = set(cells)
    if not grid:
        return ()
    best: tuple[Cell, ...] | None = None
    for name in symmetries:
        if name not in SYMMETRY_OPS:
            raise SchemaError(f"symetrie inconnue : {name!r}")
        cand = normalize(set(SYMMETRY_OPS[name](list(grid))))
        if best is None or cand < best:
            best = cand
    assert best is not None
    return best


def same_object(a: Iterable[Cell], b: Iterable[Cell]) -> bool:
    """Deux formes sont-elles le MEME objet, au sens de leurs translations ?

    Deux objets ne sont compares que si leurs symetries admissibles coincident :
    un glider nord-est et un glider nord-ouest ont la meme forme a une reflexion
    pres, mais des translations differentes -- les fusionner ferait disparaitre
    la direction de vol, qui est precisement ce qu'une reaction doit contraindre.
    """
    ta = measure_motif(a).translation
    tb = measure_motif(b).translation
    if admissible_symmetries(ta) != admissible_symmetries(tb):
        return False
    return canonical_form(a, admissible_symmetries(ta)) == canonical_form(b, admissible_symmetries(tb))


def bounding_box(cells: Iterable[Cell]) -> tuple[int, int]:
    """Largeur x hauteur de la boite englobante (cellules supposees canoniques)."""
    grid = set(cells)
    if not grid:
        return (0, 0)
    return (max(x for x, _ in grid) + 1, max(y for _, y in grid) + 1)


def _translation_between(origin: Grid, image: Grid) -> tuple[int, int]:
    """Translation qui envoie `origin` sur `image` (memes formes canoniques)."""
    ox = min(x for x, _ in origin); oy = min(y for _, y in origin)
    ix = min(x for x, _ in image); iy = min(y for _, y in image)
    return (ix - ox, iy - oy)


@dataclass(frozen=True)
class MeasuredMotif:
    """Ce que le moteur mesure reellement pour une forme cellulaire."""

    period: int
    translation: tuple[int, int]
    population: int
    box: tuple[int, int]
    envelope: tuple[int, int]
    phases: dict[int, tuple[Cell, ...]]
    kind: str


def measure_motif(cells: Iterable[Cell], max_period: int = MAX_PERIOD) -> MeasuredMotif:
    """Mesure periode, translation, population, boite et enveloppe par replay.

    C'est l'oracle de la tranche : toute metadonnee declaree dans le catalogue
    est comparee a cette mesure.

    Cout : O(max_period * |grid|) appels a `step`, au lieu de O(max_period^2 * |grid|)
    dans la version qui recalculait `evolve(p, grid)` from scratch pour chaque p.
    La trajectoire cumulative `step^i(grid)` est partagee entre la detection de
    la periode et le calcul des phases (acceptance #1 de #15635 : memes
    periodes, memes phases, memes controles negatifs, byte-equivalence des
    rapports).
    """
    seq = [tuple(c) for c in cells]
    grid = set(seq)
    if not grid:
        raise SchemaError("motif vide : la forme canonique n'a aucune cellule")
    if len(grid) != len(seq):
        raise SchemaError("cellules dupliquees : la forme n'est pas un ensemble")

    base = normalize(grid)
    # Trajectoire cumulative : trajectory[i] == step^i(grid) pour i >= 1.
    # La comparaison `normalize(image) == base` sur chaque generation detecte
    # la periode minimale ; les phases sont ensuite extraites de la trajectoire
    # deja calculee, sans recalcul `evolve(k, grid)` pour k=0..period-1.
    trajectory: list[Grid] = [grid]
    for period in range(1, max_period + 1):
        trajectory.append(step(trajectory[-1]))
        image = trajectory[period]
        if normalize(image) == base:
            translation = _translation_between(grid, image)
            if max(abs(translation[0]), abs(translation[1])) > MAX_TRANSLATION:
                raise SchemaError(
                    f"translation {translation} hors domaine (>{MAX_TRANSLATION})"
                )
            phases = {k: normalize(trajectory[k]) for k in range(period)}
            acc: Grid = set()
            for phase in phases.values():
                acc |= set(phase)
            if translation != (0, 0):
                kind = "spaceship"
            elif period == 1:
                kind = "still_life"
            else:
                kind = "oscillator"
            return MeasuredMotif(
                period=period,
                translation=translation,
                population=len(grid),
                box=bounding_box(base),
                envelope=bounding_box(acc),
                phases=phases,
                kind=kind,
            )
    raise SchemaError(f"forme non periodique dans {max_period} generations")


# --------------------------------------------------------------------------
# Schema : provenance, motif, reaction
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class Provenance:
    source: str
    license: str
    retrieved: str
    note: str | None = None

    def to_dict(self) -> dict[str, Any]:
        return {
            "source": self.source,
            "license": self.license,
            "retrieved": self.retrieved,
            "note": self.note,
        }

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> "Provenance":
        for key in ("source", "license", "retrieved"):
            if not data.get(key):
                raise SchemaError(f"provenance : champ {key!r} manquant")
        return cls(
            source=str(data["source"]),
            license=str(data["license"]),
            retrieved=str(data["retrieved"]),
            note=data.get("note"),
        )


@dataclass(frozen=True)
class Motif:
    """Motif/composant : la forme, ses invariants mesures, sa provenance."""

    id: str
    kind: str
    period: int
    phase: str
    translation_step: tuple[int, int]
    population: int
    box: tuple[int, int]
    envelope: tuple[int, int]
    rule: str
    symmetries: tuple[str, ...]
    provenance: Provenance
    cells: tuple[Cell, ...]
    rle: str | None = None
    phases: dict[int, tuple[Cell, ...]] | None = None
    direction: tuple[int, int] | None = None
    speed: float | None = None

    def to_dict(self) -> dict[str, Any]:
        return {
            "id": self.id,
            "kind": self.kind,
            "period": self.period,
            "translation": list(self.translation_step),
            "population": self.population,
            "box": list(self.box),
            "envelope": list(self.envelope),
            "rule": self.rule,
            "symmetries": list(self.symmetries),
            "provenance": self.provenance.to_dict(),
            "cells": [list(c) for c in self.cells],
            "rle": self.rle,
            "phases": (
                None
                if self.phases is None
                else {str(k): [list(c) for c in v] for k, v in sorted(self.phases.items())}
            ),
            "direction": None if self.direction is None else list(self.direction),
            "speed": self.speed,
        }

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> "Motif":
        for key in (
            "id", "kind", "period", "translation", "population", "box",
            "envelope", "rule", "symmetries", "provenance", "cells",
        ):
            if key not in data:
                raise SchemaError(f"motif {data.get('id')!r} : champ {key!r} manquant")
        return cls(
            id=str(data["id"]),
            kind=str(data["kind"]),
            period=int(data["period"]),
            phase=str(data.get("phase", "unknown")),
            translation_step=tuple(data["translation"]),  # type: ignore[arg-type]
            population=int(data["population"]),
            box=tuple(data["box"]),  # type: ignore[arg-type]
            envelope=tuple(data["envelope"]),  # type: ignore[arg-type]
            rule=str(data["rule"]),
            symmetries=tuple(data["symmetries"]),
            provenance=Provenance.from_dict(data["provenance"]),
            cells=tuple(tuple(c) for c in data["cells"]),  # type: ignore[misc]
            rle=data.get("rle"),
            phases=(
                None
                if data.get("phases") is None
                else {int(k): tuple(tuple(c) for c in v) for k, v in data["phases"].items()}
            ),
            direction=(
                None if data.get("direction") is None else tuple(data["direction"])
            ),
            speed=None if data.get("speed") is None else float(data["speed"]),
        )


@dataclass(frozen=True)
class Placement:
    motif_id: str
    offset: tuple[int, int]
    phase: int = 0

    def to_dict(self) -> dict[str, Any]:
        return {"motif_id": self.motif_id, "offset": list(self.offset), "phase": self.phase}

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> "Placement":
        if "motif_id" not in data or "offset" not in data:
            raise SchemaError("placement : 'motif_id' et 'offset' sont requis")
        return cls(
            motif_id=str(data["motif_id"]),
            offset=tuple(data["offset"]),  # type: ignore[arg-type]
            phase=int(data.get("phase", 0)),
        )


@dataclass(frozen=True)
class Port:
    name: str
    offset: tuple[int, int]
    direction: tuple[int, int]
    phase: int

    def to_dict(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "offset": list(self.offset),
            "direction": list(self.direction),
            "phase": self.phase,
        }

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> "Port":
        for key in ("name", "offset", "direction", "phase"):
            if key not in data:
                raise SchemaError(f"port : champ {key!r} manquant")
        return cls(
            name=str(data["name"]),
            offset=tuple(data["offset"]),  # type: ignore[arg-type]
            direction=tuple(data["direction"]),  # type: ignore[arg-type]
            phase=int(data["phase"]),
        )


@dataclass(frozen=True)
class Reaction:
    id: str
    reactants: tuple[Placement, ...]
    products: tuple[Placement, ...]
    ports: tuple[Port, ...]
    temporal_offset: int
    stabilization_time: int
    occupied_region: tuple[int, int, int, int] | None
    clearance: tuple[tuple[int, int, int, int], ...]
    nature: str
    spatial_transform: str | None
    preconditions: tuple[str, ...]
    effects: tuple[str, ...]
    provenance: Provenance
    product_cells: tuple[Cell, ...] | None = None

    def to_dict(self) -> dict[str, Any]:
        return {
            "id": self.id,
            "reactants": [p.to_dict() for p in self.reactants],
            "products": [p.to_dict() for p in self.products],
            "product_cells": (
                None if self.product_cells is None else [list(c) for c in self.product_cells]
            ),
            "ports": [p.to_dict() for p in self.ports],
            "temporal_offset": self.temporal_offset,
            "stabilization_time": self.stabilization_time,
            "occupied_region": (
                None if self.occupied_region is None else list(self.occupied_region)
            ),
            "clearance": [list(r) for r in self.clearance],
            "nature": self.nature,
            "spatial_transform": self.spatial_transform,
            "preconditions": list(self.preconditions),
            "effects": list(self.effects),
            "provenance": self.provenance.to_dict(),
        }

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> "Reaction":
        for key in (
            "id", "reactants", "ports", "temporal_offset", "stabilization_time",
            "clearance", "nature", "preconditions", "effects", "provenance",
        ):
            if key not in data:
                raise SchemaError(f"reaction {data.get('id')!r} : champ {key!r} manquant")
        return cls(
            id=str(data["id"]),
            reactants=tuple(Placement.from_dict(p) for p in data["reactants"]),
            products=tuple(Placement.from_dict(p) for p in data.get("products", [])),
            ports=tuple(Port.from_dict(p) for p in data["ports"]),
            temporal_offset=int(data["temporal_offset"]),
            stabilization_time=int(data["stabilization_time"]),
            occupied_region=(
                None
                if data.get("occupied_region") is None
                else tuple(data["occupied_region"])  # type: ignore[arg-type]
            ),
            clearance=tuple(tuple(r) for r in data["clearance"]),  # type: ignore[misc]
            nature=str(data["nature"]),
            spatial_transform=data.get("spatial_transform"),
            preconditions=tuple(data["preconditions"]),
            effects=tuple(data["effects"]),
            provenance=Provenance.from_dict(data["provenance"]),
            product_cells=(
                None
                if data.get("product_cells") is None
                else tuple(tuple(c) for c in data["product_cells"])  # type: ignore[misc]
            ),
        )


@dataclass
class Catalog:
    motifs: dict[str, Motif] = field(default_factory=dict)
    reactions: dict[str, Reaction] = field(default_factory=dict)

    def motif(self, motif_id: str) -> Motif:
        try:
            return self.motifs[motif_id]
        except KeyError:
            raise SchemaError(f"motif inconnu du catalogue : {motif_id!r}") from None


# --------------------------------------------------------------------------
# Validation par replay
# --------------------------------------------------------------------------


def validate_motif(motif: Motif) -> MeasuredMotif:
    """Rejoue le motif et confronte chaque metadonnee declaree a la mesure."""
    where = f"motif {motif.id!r}"
    if motif.rule != CONWAY_RULE:
        raise SchemaError(
            f"{where} : regle {motif.rule!r} inconnue du moteur (seule {CONWAY_RULE} est implementee)"
        )

    measured = measure_motif(motif.cells)

    canonical = normalize(set(motif.cells))
    if tuple(motif.cells) != canonical:
        raise SchemaError(
            f"{where} : cellules non canoniques (translation canonique triee attendue) -- "
            f"attendu {canonical}, recu {tuple(motif.cells)}"
        )

    checks: list[tuple[str, Any, Any]] = [
        ("periode", motif.period, measured.period),
        ("translation", tuple(motif.translation_step), measured.translation),
        ("population", motif.population, measured.population),
        ("boite", tuple(motif.box), measured.box),
        ("enveloppe", tuple(motif.envelope), measured.envelope),
        ("nature", motif.kind, measured.kind),
    ]
    for label, declared, actual in checks:
        if declared != actual:
            raise SchemaError(f"{where} : {label} declaree {declared!r} != mesuree {actual!r}")

    allowed = admissible_symmetries(measured.translation)
    for name in motif.symmetries:
        if name not in SYMMETRY_OPS:
            raise SchemaError(f"{where} : symetrie inconnue {name!r}")
        if name not in allowed:
            raise SchemaError(
                f"{where} : symetrie {name!r} inadmissible -- elle change la translation "
                f"{measured.translation} en {_apply_symmetry(name, measured.translation)}"
            )
    if "T" not in motif.symmetries:
        raise SchemaError(f"{where} : la symetrie 'T' (translation) est obligatoire")

    if motif.phases is not None:
        declared_phases = {k: tuple(v) for k, v in motif.phases.items()}
        if set(declared_phases) != set(measured.phases):
            raise SchemaError(
                f"{where} : phases declarees {sorted(declared_phases)} != mesurees {sorted(measured.phases)}"
            )
        for k, cells in declared_phases.items():
            if tuple(normalize(set(cells))) != measured.phases[k]:
                raise SchemaError(f"{where} : phase {k} declaree != mesuree {measured.phases[k]}")

    if measured.translation != (0, 0):
        speed = (measured.translation[0] ** 2 + measured.translation[1] ** 2) ** 0.5 / measured.period
        if motif.speed is not None and abs(motif.speed - speed) > 1e-9:
            raise SchemaError(f"{where} : vitesse declaree {motif.speed} != mesuree {speed}")
        if motif.direction is not None and tuple(motif.direction) != measured.translation:
            raise SchemaError(
                f"{where} : direction declaree {tuple(motif.direction)} != mesuree {measured.translation}"
            )
    return measured


def _place(catalog: Catalog, placement: Placement) -> Grid:
    motif = catalog.motif(placement.motif_id)
    phases = motif.phases
    if phases is None:
        # Les phases sont derivees a la validation du motif ; on les recalcule ici
        # pour que la reaction reste verifiable meme si le catalogue ne les porte pas.
        measured = measure_motif(motif.cells)
        phases = measured.phases
    if placement.phase not in phases:
        raise SchemaError(
            f"placement de {placement.motif_id!r} : phase {placement.phase} hors de "
            f"[0, {max(phases)})"
        )
    dx, dy = placement.offset
    return {(x + dx, y + dy) for (x, y) in phases[placement.phase]}


def _reactant_survives(cells: Grid, final: Grid) -> bool:
    """Le reactif apparait-il verbatim (a une translation pres) dans l'etat final ?"""
    if not final:
        return False
    fminx = min(x for x, _ in final); fminy = min(y for _, y in final)
    shifted = {(x - fminx, y - fminy) for (x, y) in final}
    nx = min(x for x, _ in cells); ny = min(y for _, y in cells)
    target = {(x - nx, y - ny) for (x, y) in cells}
    tw = max(x for x, _ in target); th = max(y for _, y in target)
    fw = max(x for x, _ in shifted); fh = max(y for _, y in shifted)
    for ox in range(0, fw - tw + 1):
        for oy in range(0, fh - th + 1):
            if {(x + ox, y + oy) for (x, y) in target} <= shifted:
                return True
    return False


def validate_reaction(reaction: Reaction, catalog: Catalog) -> dict[str, Any]:
    """Rejoue la reaction jointe et confronte produit, clearance et nature."""
    where = f"reaction {reaction.id!r}"
    if reaction.nature not in ("consumable", "reusable", "catalytic"):
        raise SchemaError(f"{where} : nature {reaction.nature!r} inconnue")
    if not reaction.reactants:
        raise SchemaError(f"{where} : aucune espece reactive")
    if reaction.stabilization_time < 0:
        raise SchemaError(f"{where} : stabilisation negative")

    placement_grids = [_place(catalog, p) for p in reaction.reactants]
    initial: Grid = set()
    for g in placement_grids:
        initial |= g

    final: Grid = set(initial)
    ever: Grid = set(initial)
    for _ in range(reaction.stabilization_time):
        final = step(final)
        ever |= final

    # 1. produit declare vs produit mesure
    has_placements = bool(reaction.products)
    has_cells = reaction.product_cells is not None
    if has_placements and has_cells:
        raise SchemaError(f"{where} : 'products' et 'product_cells' sont exclusifs")
    if has_placements:
        expected: Grid = set()
        for p in reaction.products:
            expected |= _place(catalog, p)
    elif has_cells:
        expected = {tuple(c) for c in reaction.product_cells}
    else:
        expected = set()
    if final != expected:
        raise SchemaError(
            f"{where} : produit mesure {sorted(final)} != produit declare {sorted(expected)} "
            f"a t={reaction.stabilization_time}"
        )
    if step(final) != final:
        raise SchemaError(
            f"{where} : le produit declare n'est pas stable a t={reaction.stabilization_time} "
            "(les reactions a produit mobile sont hors domaine de ce validateur)"
        )

    # 2. zones de clearance : jamais traversees, sur toute la fenetre
    for rect in reaction.clearance:
        x0, y0, w, h = rect
        if w <= 0 or h <= 0:
            raise SchemaError(f"{where} : clearance {rect} de taille nulle")
        occupied = {
            (x, y)
            for (x, y) in ever
            if x0 <= x < x0 + w and y0 <= y < y0 + h
        }
        if occupied:
            raise SchemaError(
                f"{where} : clearance {rect} traversee par {sorted(occupied)[:4]}"
            )

    # 3. nature : consomme vs catalyse, mesuree
    survivors = [
        p.motif_id
        for p, g in zip(reaction.reactants, placement_grids)
        if _reactant_survives(g, final)
    ]
    if reaction.nature == "consumable" and survivors:
        raise SchemaError(
            f"{where} : declaree 'consumable' mais {survivors} survit dans l'etat final"
        )
    if reaction.nature in ("reusable", "catalytic") and not survivors:
        raise SchemaError(
            f"{where} : declaree {reaction.nature!r} mais aucun reactif ne survit"
        )

    # 4. region occupee : boite englobante de tout ce qui a vecu
    if reaction.occupied_region is not None:
        x0, y0, w, h = reaction.occupied_region
        measured_region = (
            min(x for x, _ in ever),
            min(y for _, y in ever),
            max(x for x, _ in ever) - min(x for x, _ in ever) + 1,
            max(y for _, y in ever) - min(y for _, y in ever) + 1,
        )
        if tuple(measured_region) != (x0, y0, w, h):
            raise SchemaError(
                f"{where} : region occupee declaree {(x0, y0, w, h)} != mesuree {measured_region}"
            )

    # 5. ports : coherence structurelle (la compatibilite releve de la tranche 3)
    for port in reaction.ports:
        if not port.name:
            raise SchemaError(f"{where} : port sans nom")
        if abs(port.direction[0]) + abs(port.direction[1]) == 0:
            raise SchemaError(f"{where} : port {port.name!r} de direction nulle")
        if reaction.occupied_region is not None:
            x0, y0, w, h = reaction.occupied_region
            px, py = port.offset
            if not (x0 <= px < x0 + w and y0 <= py < y0 + h):
                raise SchemaError(
                    f"{where} : port {port.name!r} en {port.offset} hors de la region occupee"
                )

    return {
        "id": reaction.id,
        "nature": reaction.nature,
        "stabilization_time": reaction.stabilization_time,
        "population_final": len(final),
        "survivors": survivors,
    }


def load_catalog(path: str | Path) -> Catalog:
    data = json.loads(Path(path).read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise SchemaError("le document doit etre un objet JSON")
    if data.get("schema_version") != SCHEMA_VERSION:
        raise SchemaError(
            f"schema_version declaree {data.get('schema_version')!r} != {SCHEMA_VERSION!r}"
        )
    catalog = Catalog()
    for raw in data.get("motifs", []):
        motif = Motif.from_dict(raw)
        if motif.id in catalog.motifs:
            raise SchemaError(f"motif duplique : {motif.id!r}")
        catalog.motifs[motif.id] = motif
    for raw in data.get("reactions", []):
        reaction = Reaction.from_dict(raw)
        if reaction.id in catalog.reactions:
            raise SchemaError(f"reaction dupliquee : {reaction.id!r}")
        catalog.reactions[reaction.id] = reaction
    return catalog


def validate_catalog(catalog: Catalog) -> list[dict[str, Any]]:
    """Valide tout le catalogue : motifs d'abord, puis reactions (qui les citent)."""
    report: list[dict[str, Any]] = []
    for motif in catalog.motifs.values():
        measured = validate_motif(motif)
        report.append(
            {
                "kind": "motif",
                "id": motif.id,
                "categorie": measured.kind,
                "periode": measured.period,
                "translation": list(measured.translation),
                "population": measured.population,
                "enveloppe": list(measured.envelope),
            }
        )
    for reaction in catalog.reactions.values():
        report.append({"kind": "reaction", **validate_reaction(reaction, catalog)})
    return report


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Valide un catalogue de motifs et de reactions de Game of Life contre "
            "le moteur Life du depot (aucune metadonnee acceptee sur confiance)."
        )
    )
    parser.add_argument(
        "--fixture",
        default=str(Path(__file__).resolve().parent / "life_components_fixture.json"),
        help="catalogue JSON a valider",
    )
    parser.add_argument("--json", action="store_true", help="sortie JSON")
    args = parser.parse_args(argv)

    try:
        catalog = load_catalog(args.fixture)
        report = validate_catalog(catalog)
    except (SchemaError, json.JSONDecodeError) as exc:
        if args.json:
            print(json.dumps({"ok": False, "error": str(exc)}, ensure_ascii=False, indent=2))
        else:
            print(f"ECHEC : {exc}")
        return 1

    if args.json:
        print(json.dumps({"ok": True, "schema_version": SCHEMA_VERSION, "items": report},
                         ensure_ascii=False, indent=2))
        return 0

    print(f"Schema {SCHEMA_VERSION} -- {args.fixture}")
    for row in report:
        if row["kind"] == "motif":
            print(
                f"  motif    {row['id']:24s} {row['categorie']:11s} p={row['periode']} "
                f"t={tuple(row['translation'])} pop={row['population']} env={tuple(row['enveloppe'])}"
            )
        else:
            print(
                f"  reaction {row['id']:24s} {row['nature']:11s} "
                f"st={row['stabilization_time']} pop_final={row['population_final']} "
                f"survivants={row['survivors']}"
            )
    print("OK -- toutes les metadonnees declarees correspondent au replay.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
