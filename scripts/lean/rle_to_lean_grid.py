#!/usr/bin/env python3
"""Convertit un motif RLE Golly en litteral Lean ``Grid`` (``List (Int x Int)``).

Organe de la tranche 1 de l'issue #19989 (Part of #17465) : les quatre temoins
de ``conway_lean/Conway/Life/Pillars.lean`` sont vacuous parce que leurs grilles
``*Initial``/``*Target`` sont vides. Cet outil parse le format RLE standard
(``b`` mort, ``o`` vivant, ``$`` fin de ligne, ``!`` fin de motif) et emet la
liste eparse des coordonnees des cellules vivantes, normalisee au coin
(0, 0).

Usage :
    python scripts/lean/rle_to_lean_grid.py --input patterns/p5760unitlifecell.rle \
        --name unitcellInitial [--output out.lean] [--json]
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

_HEADER_RE = re.compile(r"x\s*=\s*(\d+)\s*,\s*y\s*=\s*(\d+)")


class RleError(ValueError):
    """RLE malforme : erreur explicite plutot qu'une grille silencieusement fausse."""


def parse_rle(text: str) -> tuple[int, int, list[tuple[int, int]]]:
    """Retourne (largeur, hauteur, cellules vivantes) depuis un corps RLE.

    Les lignes ``#`` (commentaires) et l'en-tete ``x = ..., y = ...`` sont
    ignores ; le reste est le corps. Un caractere inconnu est une ``RleError``
    -- un motif tronque ou corrompu ne doit jamais produire une grille
    plausible.
    """
    body_lines: list[str] = []
    width = height = None
    for line in text.splitlines():
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        if _HEADER_RE.search(stripped) and "rule" not in stripped[:0]:
            match = _HEADER_RE.search(stripped)
            if match and width is None:
                width, height = int(match.group(1)), int(match.group(2))
                continue
        body_lines.append(stripped)
    if width is None or height is None:
        raise RleError("en-tete 'x = ..., y = ...' introuvable")

    cells: list[tuple[int, int]] = []
    x = y = 0
    count_str = ""
    for char in "".join(body_lines):
        if char.isdigit():
            count_str += char
            continue
        count = int(count_str) if count_str else 1
        count_str = ""
        if char == "b":
            x += count
        elif char == "o":
            cells.extend((x + dx, y) for dx in range(count))
            x += count
        elif char == "$":
            y += count
            x = 0
        elif char == "!":
            break
        else:
            raise RleError(f"caractere RLE inconnu : {char!r} (apres ({x}, {y}))")

    if x > width or y > height:
        raise RleError(f"corps deborde de l'en-tete : corps {x}x{y}, en-tete {width}x{height}")
    return width, height, cells


def normalize(cells: list[tuple[int, int]]) -> list[tuple[int, int]]:
    """Translate le coin superieur gauche du bounding box en (0, 0)."""
    min_x = min(x for x, _ in cells)
    min_y = min(y for _, y in cells)
    return sorted((x - min_x, y - min_y) for x, y in cells)


def emit_lean(name: str, cells: list[tuple[int, int]], per_line: int = 8) -> str:
    """Emit une definition Lean ``def name : Grid := [...]``."""
    lines: list[str] = [f"def {name} : Grid := ["]
    for i in range(0, len(cells), per_line):
        chunk = ", ".join(f"({x}, {y})" for x, y in cells[i : i + per_line])
        lines.append(f"  {chunk},")
    lines[-1] = lines[-1].rstrip(",")
    lines.append("]")
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--input", required=True, type=Path, help="fichier .rle source")
    parser.add_argument("--name", required=True, help="nom de la def Lean emise")
    parser.add_argument("--output", type=Path, default=None, help="fichier .lean cible (stdout sinon)")
    parser.add_argument("--per-line", type=int, default=8, help="coordonnees par ligne")
    parser.add_argument("--json", action="store_true", help="rapport JSON au lieu du Lean")
    args = parser.parse_args()

    try:
        width, height, cells = parse_rle(args.input.read_text(encoding="utf-8", errors="strict"))
    except (OSError, RleError, UnicodeDecodeError) as exc:
        print(f"ERREUR : {exc}", file=sys.stderr)
        return 1

    normalized = normalize(cells)
    if args.json:
        report = {
            "input": str(args.input),
            "header": {"x": width, "y": height},
            "live_cells": len(normalized),
            "bbox": {"x": max(x for x, _ in normalized), "y": max(y for _, y in normalized)},
            "name": args.name,
        }
        print(json.dumps(report))
        return 0

    lean = emit_lean(args.name, normalized, args.per_line)
    if args.output:
        args.output.write_text(lean, encoding="utf-8", newline="\n")
        print(f"{args.output} : {len(normalized)} cellules")
    else:
        sys.stdout.write(lean)
    return 0


if __name__ == "__main__":
    sys.exit(main())
