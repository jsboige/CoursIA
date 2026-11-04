#!/usr/bin/env python3
"""Detecteur de sorties de flux dont les fins de ligne sont perdues (#22181).

Une sortie de flux (``stream``) est comptee *defectueuse* quand sa liste
``text`` a plus de deux elements, qu'aucun element hors le dernier ne finit
par ``\\n`` (un rapport multiligne recolle sur une seule ligne par l'executeur
defectueux), ET qu'aucun element ne finit par ``\\r``.

La derniere condition est le raffinement fondamental. Une barre de
progression (tqdm / yfinance) se redessine sur place avec des cadres termines
par ``\\r`` : c'est du texte legitime, pas un rapport aplati. La mesure
initiale du body de #22181 comptait ces barres comme defectueuses, ce qui
bloquait la cloture de l'issue. Sur ``main`` (mesure du 2026-11-03, 240
carnets QuantConnect) la mesure naive rend 15 sorties / 9 carnets ; la mesure
raffinee en rend 0. Re-execute les carnets ne fait que relancer la loterie du
nombre de cadres de la barre (QC-Py-31 : 1 -> 2) : il n'y a rien a
re-execute, il y a une mesure a corriger.

Discriminante : un rapport aplati a perdu ses ``\\n`` et ne porte aucun
``\\r`` ; une barre de progression porte des ``\\r``. La presence d'au moins
un cadre termine par ``\\r`` marque une barre, pas un defaut. Faux negatif
theorique : un rapport dont une ligne legitime s'acheverait par ``\\r`` --
absent de la population QC mesuree ; le detecteur est un audit, jamais un
gate dur.

Usage:
    python scripts/notebook_tools/scan_stream_newline_loss.py <chemin> [--json]

``<chemin>`` est un ``.ipynb`` ou un repertoire (parcours recursif).
Exit 0 = aucune sortie defectueuse ; exit 1 = au moins une (lisible en CI).
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any


def is_defective_stream(output: dict) -> bool:
    """Vrai si ``output`` est un flux multiligne aplati (et non une barre).

    Conditions conjonctives :
    1. ``text`` est une liste d'au moins 3 elements ;
    2. aucun element hors le dernier ne finit par ``\\n`` (fins de ligne perdues) ;
    3. aucun element ne finit par ``\\r`` (exclut les barres de progression).
    """
    text = output.get("text")
    if not isinstance(text, list) or len(text) <= 2:
        return False
    if any(e.endswith("\n") for e in text[:-1]):
        return False
    if any(e.endswith("\r") for e in text):
        return False
    return True


def count_defects_in_notebook(nb: dict) -> int:
    """Nombre de sorties de flux defectueuses d'un notebook (dict nbformat)."""
    n = 0
    for cell in nb.get("cells", []):
        if cell.get("cell_type") != "code":
            continue
        for output in cell.get("outputs", []):
            if is_defective_stream(output):
                n += 1
    return n


def scan_path(path: Path) -> dict[str, int]:
    """Carte ``chemin relatif -> nb de sorties defectueuses`` (>= 1 seulement).

    ``path`` est un ``.ipynb`` ou un repertoire parcouru recursivement. Les
    carnets illisables (JSON corrompu) sont sautes silencieusement, comme une
    mesure : elle compte des sorties, elle ne repare pas un notebook casse.
    """
    result: dict[str, int] = {}
    if path.is_file():
        files = [path]
        base = path.parent
    else:
        files = sorted(path.rglob("*.ipynb"))
        base = path
    for f in files:
        try:
            nb = json.loads(f.read_text(encoding="utf-8"))
        except (json.JSONDecodeError, UnicodeDecodeError, OSError):
            continue
        n = count_defects_in_notebook(nb)
        if n:
            result[str(f.relative_to(base))] = n
    return result


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Detecteur de sorties de flux sans fin de ligne (#22181, "
                    "barres de progression \\r exclues).")
    parser.add_argument("chemin", help="fichier .ipynb ou repertoire (recursif)")
    parser.add_argument("--json", action="store_true", help="sortie JSON")
    args = parser.parse_args(argv)

    path = Path(args.chemin)
    if not path.exists():
        print(f"erreur: chemin introuvable: {path}", file=sys.stderr)
        return 2

    findings = scan_path(path)
    total = sum(findings.values())

    if args.json:
        print(json.dumps(
            {"defect_outputs": total, "defect_notebooks": len(findings),
             "findings": findings},
            ensure_ascii=False, indent=2))
    else:
        if not findings:
            print(f"OK: 0 sortie de flux sans fin de ligne ({path})")
        else:
            print(f"{total} sortie(s) de flux sans fin de ligne "
                  f"dans {len(findings)} carnet(s) sous {path}:")
            for rel, n in sorted(findings.items(), key=lambda kv: -kv[1]):
                print(f"  {n:2d}  {rel}")

    return 1 if total else 0


if __name__ == "__main__":
    raise SystemExit(main())
