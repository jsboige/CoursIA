#!/usr/bin/env python3
"""Synthese SAT de translateurs de Game of Life (Loi II, EPIC #12205, variante -b).

Le moteur B1 (`life_synthesize.py`) enumere *tous* les sous-ensembles d'une
boite bornee. Son cout est combinatoire : une boite 4x4 a <= 6 cellules tient
en 14 892 essais, une boite 5x5 a <= 9 cellules en demande 3,9 millions, et une
boite 6x6 est hors d'atteinte. Ses deux residuels sont ecrits dans le body de
la PR #13814 : les bornes, et « le moteur le decouvre, il ne l'unicise pas ».

Ce module code la meme specification en SAT — le moteur que le cahier des
charges de #12205 nommait (« SAT / Z3 / CP-SAT ») — et en tire les trois
choses que l'enumeration ne donnait pas :

  * **des bornes plus larges** : le LWSS (9 cellules, boite 5x4) est atteint,
    la ou l'enumeration devrait parcourir ~168 000 combinaisons rien que pour
    sa taille exacte ;
  * **la minimalite** : la recherche monte k = 1, 2, 3, ... et s'arrete au
    premier k satisfiable. Ce k est le minimum, parce que le solveur est
    complet : les k inferieurs ne sont pas « non trouves », ils sont
    **refutes** ;
  * **le temoin d'impossibilite** : quand aucun k <= max_cells ne passe, la
    sortie porte `IMPOSSIBLE` et la borne exacte de ce qui a ete refute. Le
    critere 4 de #12205 — « un generateur qui ne sait pas dire "aucune
    solution, et voici pourquoi" n'a pas franchi le cran, il l'a contourne ».

La semantique de Life n'est **pas** reecrite ici : `step`, `evolve`, `shift_v`
et `normalize` sont importes de `life_synthesize` (moteur B1). Toute solution
rendue par le solveur est **revalidee contre cette reference** avant d'etre
publiee (`verify_solution`) : le modele SAT est une hypothese, l'oracle est le
moteur d'origine.

Usage :
    python scripts/lean/life_synthesize_sat.py --n 4 --vx 1 --vy=-1 --box 4
    python scripts/lean/life_synthesize_sat.py --n 4 --vx 2 --vy 0 --box-w 5 --box-h 4
    python scripts/lean/life_synthesize_sat.py --n 4 --vx 1 --vy 0 --box 6 --json
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path
from typing import Iterable, Sequence

sys.path.insert(0, str(Path(__file__).resolve().parent))

from life_synthesize import Cell, Grid, evolve, normalize, shift_v  # noqa: E402

try:
    import z3
except ImportError:  # pragma: no cover - depend de l'environnement
    z3 = None


NEIGHBOUR_OFFSETS: tuple[tuple[int, int], ...] = tuple(
    (dx, dy) for dx in (-1, 0, 1) for dy in (-1, 0, 1) if (dx, dy) != (0, 0)
)


def universe_bounds(
    box_w: int, box_h: int, n: int, v: tuple[int, int]
) -> tuple[range, range]:
    """Fenetre hors de laquelle aucune cellule ne peut vivre avant n pas.

    Un motif inclus dans la boite s'etend d'au plus une cellule par generation,
    donc au plus de `n` apres `n` pas. On ajoute `|v|` (la cible translatee doit
    tenir dedans) et 1 de marge : le bord de la fenetre est alors mort a toutes
    les generations, ce qui rend **exact** — et pas seulement approche — le fait
    de traiter l'exterieur comme mort dans l'encodage.
    """
    pad = n + max(abs(v[0]), abs(v[1])) + 1
    return range(-pad, box_w + pad), range(-pad, box_h + pad)


def build_solver(
    n: int,
    v: tuple[int, int],
    box_w: int,
    box_h: int,
) -> tuple["z3.Solver", dict[Cell, "z3.BoolRef"]]:
    """Encode `evolve^n T = shift_v T`, T inclus dans la boite, en SAT."""
    xs, ys = universe_bounds(box_w, box_h, n, v)
    cells = [(x, y) for x in xs for y in ys]
    inside = set(cells)

    alive = {
        (g, p): z3.Bool(f"a_{g}_{p[0]}_{p[1]}")
        for g in range(n + 1)
        for p in cells
    }

    def at(g: int, p: Cell) -> "z3.BoolRef":
        """Hors fenetre = mort (exact, cf. universe_bounds)."""
        return alive[(g, p)] if p in inside else z3.BoolVal(False)

    solver = z3.Solver()

    # Generation 0 : le motif cherche vit dans la boite.
    for (x, y) in cells:
        if not (0 <= x < box_w and 0 <= y < box_h):
            solver.add(z3.Not(alive[(0, (x, y))]))

    # Regle de Conway, generation par generation.
    for g in range(n):
        for p in cells:
            live_nbrs = z3.Sum(
                [z3.If(at(g, (p[0] + dx, p[1] + dy)), 1, 0)
                 for dx, dy in NEIGHBOUR_OFFSETS]
            )
            solver.add(
                alive[(g + 1, p)]
                == z3.Or(live_nbrs == 3, z3.And(at(g, p), live_nbrs == 2))
            )

    # Invariant de translation, impose sur toute la fenetre.
    for p in cells:
        solver.add(alive[(n, p)] == at(0, (p[0] - v[0], p[1] - v[1])))

    seeds = {p: alive[(0, p)] for p in cells
             if 0 <= p[0] < box_w and 0 <= p[1] < box_h}
    solver.add(z3.Or(list(seeds.values())))  # motif non vide
    return solver, seeds


def _model_pattern(model: "z3.ModelRef", seeds: dict[Cell, "z3.BoolRef"]) -> Grid:
    return {p for p, var in seeds.items() if z3.is_true(model.eval(var, True))}


def verify_solution(pattern: Grid, n: int, v: tuple[int, int]) -> bool:
    """Revalide contre le moteur B1 — l'oracle n'est pas le solveur."""
    return bool(pattern) and evolve(n, set(pattern)) == shift_v(v, set(pattern))


def solve_exact_size(
    n: int,
    v: tuple[int, int],
    box_w: int,
    box_h: int,
    k: int,
    enumerate_all: bool,
) -> list[tuple[Cell, ...]]:
    """Toutes les formes normalisees de taille exactement k (ou la premiere)."""
    solver, seeds = build_solver(n, v, box_w, box_h)
    solver.add(z3.Sum([z3.If(var, 1, 0) for var in seeds.values()]) == k)

    found: dict[tuple[Cell, ...], tuple[Cell, ...]] = {}
    while solver.check() == z3.sat:
        pattern = _model_pattern(solver.model(), seeds)
        if not verify_solution(pattern, n, v):
            raise AssertionError(
                f"modele SAT refute par le moteur de reference : {sorted(pattern)}"
            )
        # On publie la forme NORMALISEE, pas le representant brut rendu par
        # le solveur : deux modeles translates l'un de l'autre sont la meme
        # forme, et seule la forme canonique est comparable au moteur B1.
        norm = normalize(pattern)
        found[norm] = norm
        # Bloque cette configuration exacte (translations comprises : elles
        # seront dedupliquees par `normalize`).
        solver.add(z3.Not(z3.And([
            var if p in pattern else z3.Not(var) for p, var in seeds.items()
        ])))
        if not enumerate_all:
            break
    return [found[key] for key in sorted(found)]


CANONICAL_GLIDER: tuple[Cell, ...] = tuple(
    sorted([(0, 0), (1, 0), (1, 2), (2, 0), (2, 1)])
)


def search_minimal(
    n: int,
    v: tuple[int, int],
    box_w: int,
    box_h: int,
    max_cells: int,
    enumerate_all: bool = True,
) -> dict:
    """Monte k jusqu'au premier satisfiable. Sinon : temoin d'impossibilite."""
    started = time.perf_counter()
    refuted: list[int] = []
    for k in range(1, max_cells + 1):
        shapes = solve_exact_size(n, v, box_w, box_h, k, enumerate_all)
        if shapes:
            return {
                "verdict": "FOUND",
                "min_cells": k,
                "sizes_refuted": refuted,
                "count_normalized": len(shapes),
                "patterns": [list(shape) for shape in shapes],
                "canonical_glider_present": CANONICAL_GLIDER in set(shapes),
                "elapsed_s": round(time.perf_counter() - started, 3),
            }
        refuted.append(k)
    return {
        "verdict": "IMPOSSIBLE",
        "min_cells": None,
        "sizes_refuted": refuted,
        "count_normalized": 0,
        "patterns": [],
        "canonical_glider_present": False,
        "elapsed_s": round(time.perf_counter() - started, 3),
    }


def render(pattern: Sequence[Cell]) -> list[str]:
    """Rendu ASCII d'un motif normalise (lecture humaine du temoin)."""
    if not pattern:
        return []
    cells = set(pattern)
    w = max(x for x, _ in cells) + 1
    h = max(y for _, y in cells) + 1
    return ["".join("#" if (x, y) in cells else "." for x in range(w))
            for y in range(h)]


def emit_lean(name: str, pattern: Sequence[Cell], n: int,
              v: tuple[int, int]) -> str:
    """Rend le certificat Lean d'un motif synthetise, pret a coller.

    Le moteur **produit** le certificat, il ne l'installe pas : le lake
    `conway_lean` appartient a une autre lane (claim `conway_lean/**` sur
    #12205). Emettre le texte plutot que l'ecrire garde la frontiere nette
    tout en livrant la matiere — et c'est de toute facon la bonne forme
    pour un generateur : l'objet sort avec de quoi se faire verifier par un
    tiers qui n'est pas lui.

    Conversion de convention : le moteur raisonne en `(x, y)` (colonne,
    ligne), `Conway.Life` en `(row, col)`. Les cellules sortent triees
    lexicographiquement (row puis col), ce que `decide` exige pour comparer
    structurellement les listes.
    """
    rows: dict[int, list[int]] = {}
    for x, y in pattern:
        rows.setdefault(y, []).append(x)
    lines = [
        "   " + ", ".join(f"({r}, {c})" for c in sorted(cols))
        for r, cols in sorted(rows.items())
    ]
    body = ",\n".join(lines).lstrip()
    dr, dc = v[1], v[0]
    return "\n".join([
        f"/-- Motif synthetise par `life_synthesize_sat.py` (SAT), verifie",
        f"    independamment par le moteur d'enumeration `life_synthesize.py`.",
        f"    {len(pattern)} cellules, periode {n}, deplacement `({dr}, {dc})`. -/",
        f"def {name} : Grid :=",
        f"  [{body}]",
        "",
        f"/-- Certificat noyau : `{name}` est un vaisseau de periode {n} et",
        f"    deplacement `({dr}, {dc})`. -/",
        f"theorem {name}_spaceship : isSpaceship {name} {n} ({dr}, {dc}) = true := by decide",
    ])


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Synthese SAT d'un translateur Life verifiant evolve^n T = shift_v T, "
            "avec minimalite prouvee et temoin d'impossibilite."
        )
    )
    parser.add_argument("--n", type=int, default=4, help="nombre de generations")
    parser.add_argument("--vx", type=int, default=1, help="composante x du deplacement")
    parser.add_argument("--vy", type=int, default=-1, help="composante y du deplacement")
    parser.add_argument("--box", type=int, default=5, help="cote de la boite (carree)")
    parser.add_argument("--box-w", type=int, default=None, help="largeur (prime --box)")
    parser.add_argument("--box-h", type=int, default=None, help="hauteur (prime --box)")
    parser.add_argument(
        "--max-cells", type=int, default=None,
        help="taille max exploree (defaut : box_w * box_h)",
    )
    parser.add_argument(
        "--first-only", action="store_true",
        help="s'arreter a la premiere forme au lieu de toutes les enumerer",
    )
    parser.add_argument("--json", action="store_true", help="sortie JSON")
    parser.add_argument(
        "--lean", metavar="NOM",
        help=(
            "emettre le certificat Lean des motifs trouves, prefixe par NOM "
            "(le moteur produit le certificat, il n'ecrit dans aucun lake)"
        ),
    )
    args = parser.parse_args(list(argv) if argv is not None else None)

    if z3 is None:
        print(
            "z3 est requis : pip install z3-solver",
            file=sys.stderr,
        )
        return 2

    box_w = args.box_w if args.box_w is not None else args.box
    box_h = args.box_h if args.box_h is not None else args.box
    max_cells = args.max_cells if args.max_cells is not None else box_w * box_h
    v = (args.vx, args.vy)

    result = search_minimal(
        args.n, v, box_w, box_h, max_cells, enumerate_all=not args.first_only
    )
    result["spec"] = f"evolve^{args.n} T = shift_{v} T"
    result["box"] = [box_w, box_h]
    result["max_cells"] = max_cells
    if args.json:
        print(json.dumps(result, ensure_ascii=False, indent=2))
        return 0

    print(f"Spec : {result['spec']}")
    print(f"Boite {box_w}x{box_h}, tailles explorees 1..{max_cells}")
    if result["verdict"] == "IMPOSSIBLE":
        print(
            f"IMPOSSIBLE — aucune solution. Tailles refutees : "
            f"{result['sizes_refuted']} (refutation complete, pas un echec de "
            f"recherche : le solveur est complet sur cet espace borne)."
        )
        print(f"({result['elapsed_s']} s)")
        return 0
    print(
        f"FOUND — taille minimale {result['min_cells']} cellules "
        f"(tailles refutees : {result['sizes_refuted'] or 'aucune'})"
    )
    print(f"{result['count_normalized']} forme(s) normalisee(s) a cette taille :")
    for pattern in result["patterns"]:
        shape = tuple(map(tuple, pattern))
        marker = "  <-- glider canonique" if shape == CANONICAL_GLIDER else ""
        print(f"  {list(shape)}{marker}")
        for line in render(shape):
            print(f"      {line}")
    print(f"({result['elapsed_s']} s)")

    if args.lean:
        print()
        print("-- Certificats Lean (a coller dans le lake, cf. emit_lean) :")
        for i, pattern in enumerate(result["patterns"], start=1):
            suffix = "" if result["count_normalized"] == 1 else f"_{i}"
            print()
            print(emit_lean(f"{args.lean}{suffix}",
                            [tuple(c) for c in pattern], args.n, v))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
