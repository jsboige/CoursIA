#!/usr/bin/env python3
"""Detecteur de sorties de flux dont les fins de ligne sont perdues (#22181).

Une sortie de flux (``stream``) est comptee *defectueuse* quand elle porte un
**rapport multiligne aplati** : les fins de ligne ``\\n`` ont disparu, parce que
l'executeur faisait ``text.split("\\n")`` au lieu de ``splitlines(keepends=True)``.

La discrimination repose sur les **cadres** (les elements de la liste ``text``
hors le dernier) :

1. la liste a plus de deux elements (seuil herite de la mesure de #22181) ;
2. aucun cadre ne finit par ``\\n`` -- sinon les fins de ligne sont la ;
3. **tous** les cadres finissent par ``\\r``.

La condition 3 est la regle de blanchiment. Une barre de progression (tqdm /
yfinance) se redessine sur place : chacun de ses cadres est termine par un
retour chariot ``\\r``. Un flux dont *tous* les cadres sont ``\\r``-termines est
donc une barre, pas un rapport aplati. Symetriquement, un flux ou **un seul**
cadre n'est termine ni par ``\\n`` ni par ``\\r`` est un defaut, meme si
d'autres cadres portent un ``\\r`` : c'est le cas d'un rapport qui suit une barre
dans le meme ``stdout``, que la regle permissive blanchissait en bloc.

Sur ``main`` (mesure du 2026-11-03, 240 carnets QuantConnect) la mesure naive
du body de #22181 rend 15 sorties / 9 carnets ; la mesure raffinee en rend 0.
Re-execute les carnets ne fait que relancer la loterie du nombre de cadres de
la barre (mesure du 2026-11-04 sur ``QC-Py-31/32/33`` : 4 sorties comptees sur
``main``, 4 apres re-execution -- 31 : 1 -> 2, 32 : 2 -> 2, 33 : 1 -> 0) : il
n'y a rien a re-execute, il y a une mesure a corriger.

Deux etats sont distingues d'un zero sain, parce qu'un outil qui mesure la
mesure doit pouvoir dire « je n'ai pas su mesurer » :

- ``unreadable`` : carnet illisible (JSON corrompu, encodage, I/O) ;
- ``inconclusive`` : sortie dont la liste ``text`` contient un element non
  textuel -- le contrat nbformat le garantit en pratique, mais l'organe balaie
  un depot entier et ne doit pas s'arreter sur une sortie etrangere.

Usage:
    python scripts/notebook_tools/scan_stream_newline_loss.py <chemin> [--json]

``<chemin>`` est un ``.ipynb`` ou un repertoire (parcours recursif).

Codes de sortie :
    0 = aucune sortie defectueuse, mesure complete ;
    1 = au moins une sortie defectueuse ;
    2 = chemin introuvable (erreur d'usage) ;
    3 = aucun defaut, mais la mesure est **incomplete** (carnets illisibles ou
        sorties non concluantes) -- un « zero » qui n'a pas tout mesure.
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any


def _ends_with(element: Any, suffix: str) -> bool:
    """Vrai si ``element`` est une chaine terminant par ``suffix``.

    Le test d'egalite du type est explicite : ``str.endswith`` leve une
    ``AttributeError`` sur un element non textuel, ce qui interromprait le
    parcours d'un depot entier au lieu de rendre la sortie non concluante.
    """
    return isinstance(element, str) and element.endswith(suffix)


def is_defective_stream(output: dict) -> bool:
    """Vrai si ``output`` est un rapport multiligne aplati (et non une barre).

    Conditions conjonctives :
    1. ``text`` est une liste d'au moins 3 elements ;
    2. aucun cadre ne finit par ``\\n`` (fins de ligne perdues) ;
    3. au moins un cadre ne finit **ni** par ``\\n`` **ni** par ``\\r``
       (le flux melange une barre et un rapport, ou n'est qu'un rapport).
    """
    text = output.get("text")
    if not isinstance(text, list) or len(text) <= 2:
        return False
    if any(not isinstance(e, str) for e in text):
        # sortie non concluante : elle n'est ni un defaut, ni une barre
        # (comptee par ``is_inconclusive_stream``)
        return False
    frames = text[:-1]
    if any(_ends_with(e, "\n") for e in frames):
        return False
    return not all(_ends_with(e, "\r") for e in frames)


def is_inconclusive_stream(output: dict) -> bool:
    """Vrai si ``output`` ne peut pas etre tranche (element non textuel)."""
    text = output.get("text")
    if not isinstance(text, list) or len(text) <= 2:
        return False
    return any(not isinstance(e, str) for e in text)


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


def count_inconclusive_in_notebook(nb: dict) -> int:
    """Nombre de sorties de flux non concluantes d'un notebook (dict nbformat)."""
    n = 0
    for cell in nb.get("cells", []):
        if cell.get("cell_type") != "code":
            continue
        for output in cell.get("outputs", []):
            if is_inconclusive_stream(output):
                n += 1
    return n


@dataclass
class ScanResult:
    """Resultat d'un balayage : defauts, etats non concluants, etat de mesure.

    Les trois etats sont distincts : ``defects`` est le verdict, ``unreadable``
    et ``inconclusive`` disent ce que la mesure n'a **pas** su voir.
    """

    defects: dict[str, int] = field(default_factory=dict)
    inconclusive: dict[str, int] = field(default_factory=dict)
    unreadable: list[str] = field(default_factory=list)
    scanned: int = 0

    @property
    def complete(self) -> bool:
        """Vrai si la mesure a pu voir tous les fichiers et toutes les sorties."""
        return not self.unreadable and not self.inconclusive


def scan_path(path: Path) -> ScanResult:
    """Balaye ``path`` et rend defauts, non-concluants et illisibles.

    ``path`` est un ``.ipynb`` ou un repertoire parcouru recursivement. Les
    carnets illisibles (JSON corrompu) ne sont plus sautes en silence : ils
    sont comptes et nommes, pour qu'un « zero » reste distinguable d'une
    mesure incomplete.
    """
    result = ScanResult()
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
            result.unreadable.append(str(f.relative_to(base)))
            continue
        result.scanned += 1
        n = count_defects_in_notebook(nb)
        if n:
            result.defects[str(f.relative_to(base))] = n
        m = count_inconclusive_in_notebook(nb)
        if m:
            result.inconclusive[str(f.relative_to(base))] = m
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

    result = scan_path(path)
    total = sum(result.defects.values())
    inconcl = sum(result.inconclusive.values())

    if args.json:
        print(json.dumps(
            {"defect_outputs": total,
             "defect_notebooks": len(result.defects),
             "findings": result.defects,
             "inconclusive_outputs": inconcl,
             "inconclusive_notebooks": len(result.inconclusive),
             "inconclusive": result.inconclusive,
             "unreadable": len(result.unreadable),
             "unreadable_files": result.unreadable,
             "scanned_files": result.scanned,
             "complete": result.complete},
            ensure_ascii=False, indent=2))
    else:
        if result.defects:
            print(f"{total} sortie(s) de flux sans fin de ligne "
                  f"dans {len(result.defects)} carnet(s) sous {path}:")
            for rel, n in sorted(result.defects.items(), key=lambda kv: -kv[1]):
                print(f"  {n:2d}  {rel}")
        else:
            print(f"OK: 0 sortie de flux sans fin de ligne ({path})")

    if result.unreadable:
        print(f"ATTENTION: {len(result.unreadable)} carnet(s) illisible(s), "
              f"la mesure est incomplente :", file=sys.stderr)
        for rel in result.unreadable:
            print(f"  illisible: {rel}", file=sys.stderr)
    if inconcl:
        print(f"ATTENTION: {inconcl} sortie(s) non concluante(s) "
              f"(element non textuel dans `text`)", file=sys.stderr)

    if total:
        return 1
    if not result.complete:
        return 3
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
