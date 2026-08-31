#!/usr/bin/env python3
"""Redécouverte mécanique de patterns de Game of Life (Loi II, EPIC #12205).

Cherche un pattern T (sous-ensemble de cellules d'une boîte bornée) tel que
    evolve^n T = shift_v T
pour un couple (n, v) imposé. C'est le moteur de la « Loi II » : la machine
retrouve un pattern périodique en translation — en l'espèce le glider canonique
(n = 4, v = (1, -1)) — sans le recopier. La cible se certifie ensuite en Lean
(`by decide`, zéro axiome) dans le lake conway_lean.

Le pattern est un ensemble de cellules sur la grille infinie ; evolve est la
règle de Conway (vie/mort par voisinage 8), shift_v est la translation.

Usage :
    python scripts/lean/life_synthesize.py --n 4 --vx 1 --vy -- -1 --box 4
    python scripts/lean/life_synthesize.py --n 4 --vx 1 --vy -1 --box 4 --json

L'énumération est déterministe (combinaisons dans l'ordre du parcours de boîte) :
le résultat est reproductible d'une exécution à l'autre.
"""

from __future__ import annotations

import argparse
import itertools
import json
from typing import Iterable

Cell = tuple[int, int]
Grid = set[Cell]


def step(cells: Grid) -> Grid:
    """Une génération de Conway sur la grille infinie."""
    neighbors: dict[Cell, int] = {}
    for (x, y) in cells:
        for dx in (-1, 0, 1):
            for dy in (-1, 0, 1):
                if dx == 0 and dy == 0:
                    continue
                p = (x + dx, y + dy)
                neighbors[p] = neighbors.get(p, 0) + 1
    out: Grid = set()
    for p, count in neighbors.items():
        if count == 3 or (count == 2 and p in cells):
            out.add(p)
    return out


def evolve(n: int, cells: Grid) -> Grid:
    """n générations de Conway."""
    for _ in range(n):
        cells = step(cells)
    return cells


def shift_v(v: tuple[int, int], cells: Grid) -> Grid:
    """Translation de tous les cellules de v."""
    return {(x + v[0], y + v[1]) for (x, y) in cells}


def normalize(cells: Grid) -> tuple[Cell, ...]:
    """Translation canonique : min x = min y = 0, cellules triées."""
    if not cells:
        return ()
    min_x = min(x for x, _ in cells)
    min_y = min(y for _, y in cells)
    return tuple(sorted((x - min_x, y - min_y) for (x, y) in cells))


def box_cells(w: int, h: int) -> list[Cell]:
    """Cellules d'une boîte w×h (positions absolues (0..w-1, 0..h-1))."""
    return [(x, y) for x in range(w) for y in range(h)]


def synthesize(
    n: int,
    v: tuple[int, int],
    box: int,
    max_cells: int,
) -> list[tuple[Cell, ...]]:
    """Toutes les formes normalisées T vérifiant evolve^n T = shift_v T.

    On teste chaque sous-ensemble de la boîte box×box de taille ≤ max_cells.
    Le résultat est dédupliqué par translation canonique (normalize).
    """
    found: dict[tuple[Cell, ...], tuple[Cell, ...]] = {}
    universe = box_cells(box, box)
    for size in range(1, max_cells + 1):
        for combo in itertools.combinations(universe, size):
            T: Grid = set(combo)
            if evolve(n, T) == shift_v(v, T):
                norm = normalize(T)
                found.setdefault(norm, tuple(sorted(combo)))
    return [found[k] for k in sorted(found)]


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Redécouverte mécanique d'un pattern Life vérifiant "
            "evolve^n T = shift_v T."
        )
    )
    parser.add_argument("--n", type=int, default=4, help="nombre de générations")
    parser.add_argument("--vx", type=int, default=1, help="composante x du déplacement")
    parser.add_argument("--vy", type=int, default=-1, help="composante y du déplacement")
    parser.add_argument("--box", type=int, default=4, help="côté de la boîte explorée")
    parser.add_argument(
        "--max-cells",
        type=int,
        default=None,
        help="taille max du pattern (défaut : min(box², 6))",
    )
    parser.add_argument("--json", action="store_true", help="sortie JSON")
    args = parser.parse_args()

    v = (args.vx, args.vy)
    max_cells = args.max_cells if args.max_cells is not None else min(args.box ** 2, 6)

    found = synthesize(args.n, v, args.box, max_cells)

    canonical_glider = tuple(sorted([(0, 0), (1, 0), (1, 2), (2, 0), (2, 1)]))

    if args.json:
        print(
            json.dumps(
                {
                    "spec": f"evolve^{args.n} T = shift_{v} T",
                    "box": args.box,
                    "max_cells": max_cells,
                    "count_normalized": len(found),
                    "patterns": [list(p) for p in found],
                    "canonical_glider_present": canonical_glider in found,
                },
                ensure_ascii=False,
                indent=2,
            )
        )
        return 0

    print(f"Spec : evolve^{args.n} T == shift_{v} T")
    print(f"Boîte {args.box}x{args.box}, patterns de taille <= {max_cells}")
    print(f"Trouvé {len(found)} forme(s) normalisée(s) :")
    for p in found:
        marker = "  <-- glider canonique" if p == canonical_glider else ""
        print(f"  {list(p)}{marker}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
