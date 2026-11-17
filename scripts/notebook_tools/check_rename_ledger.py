#!/usr/bin/env python3
"""Garde d'integrite du ledger des renommages (docs/reference/rename-ledger.tsv).

Le ledger est un TSV append-only (colonnes ancien/nouveau/date/lane) ecrit en
parallele par plusieurs lanes : chaque renommage de carnet y ajoute une ligne en
fin de fichier. Depuis l'entree `.gitattributes` `merge=union`, un merge local
de deux branches qui ont chacune ajoute des lignes **concatene** les deux bouts
sans juger : le driver ne peut pas distinguer une histoire legitime d'un artefact
de fusion. Cette garde est la moitie porteuse du dispositif (GO ai-01,
2026-11-16) : elle echoue sur les deux signatures d'un artefact d'union --

- **cle source dupliquee** : `ancien` apparaissant sur deux lignes (deux lanes
  ayant renomme le meme carnet de deux facons, concatenees sans conflit) ;
- **cycle sans dates strictement croissantes** : un aller-retour X->Y puis Y->X
  dont les dates ne montent pas autour de la boucle. Un cycle a dates
  strictement croissantes est une histoire legitime (renommages iteratifs d'un
  meme carnet, p. ex. les iterations de structure de dossier ICT 2026-10-26 ->
  2026-10-28 -> 2026-11-15) et passe, avec une note.

Echoue aussi sur toute ligne malformee (colonnes != 4, ligne vide, date hors
format ISO YYYY-MM-DD) : une union qui collee des fragments produit aussi ces
formes.

Codes retour : 0 = propre, 1 = constats, 2 = ledger illisible (chemin,
encodage). Convention des gardes du depot : un fichier introuvable n'est pas
un constat, c'est un instrument casse.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

HEADER = "ancien\tnouveau\tdate\tlane"
DATE_RE = re.compile(r"^\d{4}-\d{2}-\d{2}$")
LEDGER_RELPATH = Path("docs/reference/rename-ledger.tsv")


def parse_ledger(text: str) -> tuple[list[str], list[dict[str, str | int]], list[str]]:
    """Decoupe le ledger en lignes, lignes valides, et messages d'erreur.

    Une ligne valide porte exactement 4 colonnes separees par des tabulations,
    une date ISO, et des champs non vides. Les lignes invalides produisent un
    message cite (numero + contenu), pas une exception.
    """
    lines = text.split("\n")
    rows: list[dict[str, str | int]] = []
    errors: list[str] = []
    # La derniere ligne d'un fichier fini par \\n est vide par construction :
    # elle n'est pas une ligne du ledger et ne compte pas comme malformee.
    body = lines[1:-1] if lines and lines[-1] == "" else lines[1:]
    for offset, raw in enumerate(body, start=2):
        if not raw.strip():
            errors.append(f"ligne {offset}: ligne vide (une union ou une edition "
                          f"manuelle a laisse une ligne blanche)")
            continue
        fields = raw.split("\t")
        if len(fields) != 4:
            errors.append(f"ligne {offset}: {len(fields)} colonnes au lieu de 4 "
                          f"(contenu: {raw!r})")
            continue
        ancien, nouveau, date, lane = fields
        if not ancien or not nouveau or not lane:
            errors.append(f"ligne {offset}: colonne vide (contenu: {raw!r})")
            continue
        if not DATE_RE.match(date):
            errors.append(f"ligne {offset}: date {date!r} hors format YYYY-MM-DD")
            continue
        rows.append({"ancien": ancien, "nouveau": nouveau, "date": date,
                     "lane": lane, "line": offset})
    return lines, rows, errors


def find_duplicate_sources(rows: list[dict[str, str | int]]) -> list[str]:
    """Cle `ancien` vue deux fois : la signature directe d'un artefact d'union.

    Deux lanes qui renomment le meme carnet produisent deux lignes de meme
    source ; le driver union les concatene sans conflit, et le ledger ne dit
    plus lequel des deux renommages a eu lieu.
    """
    seen: dict[str, int] = {}
    messages: list[str] = []
    for row in rows:
        ancien = str(row["ancien"])
        if ancien in seen:
            messages.append(
                f"cle source dupliquee {ancien!r}: lignes {seen[ancien]} et "
                f"{row['line']} -> {row['nouveau']!r} (une union a concatene "
                f"deux renommages du meme carnet)")
        else:
            seen[ancien] = int(row["line"])  # type: ignore[assignment]
    return messages


def find_cycles(rows: list[dict[str, str | int]]) -> tuple[list[list[dict[str, str | int]]], dict[str, int]]:
    """Detecte les cycles du graphe ancien -> nouveau (DFS a marques d'etat).

    Retourne chaque cycle une seule fois, comme une liste de lignes dans
    l'ordre du parcours, plus l'index de chaque ligne dans `rows` (pour
    re-ordonner le cycle par date a l'affichage).
    """
    by_source: dict[str, dict[str, str | int]] = {}
    for row in rows:
        by_source[str(row["ancien"])] = row
    state: dict[str, int] = {}  # 1 = dans le chemin courant, 2 = fini
    path: list[dict[str, str | int]] = []
    index_of: dict[str, int] = {}
    cycles: list[list[dict[str, str | int]]] = []

    def visit(node: str) -> None:
        mark = state.get(node)
        if mark == 1:
            start = next(i for i, r in enumerate(path) if str(r["ancien"]) == node)
            cycles.append(list(path[start:]))
            return
        if mark == 2 or node not in by_source:
            return
        state[node] = 1
        row = by_source[node]
        index_of[str(row["ancien"])] = len(path)
        path.append(row)
        visit(str(row["nouveau"]))
        path.pop()
        state[node] = 2

    for source in by_source:
        if source not in state:
            visit(source)
    return cycles, index_of


def cycle_verdicts(cycles: list[list[dict[str, str | int]]]) -> tuple[list[str], list[str]]:
    """Classe chaque cycle : dates toutes distinctes = histoire legitime.

    Une boucle triee par date est strictement croissante si et seulement si
    ses dates sont toutes distinctes : le carnet a ete renomme, encore renomme
    plus tard, et fini par revenir -- chaque arete plus tardive que la
    precedente. Une union qui colle deux branches qui ont renomme le meme
    jour produit des dates repetees dans la boucle -- c'est le critere
    d'echec. Limite documentee : un artefact a dates toutes distinctes est
    indiscernable d'une histoire coherente et passe.
    """
    failures: list[str] = []
    notes: list[str] = []
    for cycle in cycles:
        if len(cycle) == 1:
            row = cycle[0]
            failures.append(
                f"auto-renommage {row['ancien']}->{row['nouveau']} (ligne "
                f"{row['line']}) : renommer un carnet vers son propre nom "
                f"n'est pas une histoire legitime")
            continue
        ordered = sorted(cycle, key=lambda r: str(r["date"]))
        chain = " -> ".join(f"{r['ancien']}->{r['nouveau']}" for r in ordered)
        dates = [str(r["date"]) for r in ordered]
        loop = dates + [dates[0]]
        if all(dates[i] < dates[i + 1] for i in range(len(dates) - 1)):
            notes.append(f"cycle legitime (dates croissantes {dates}): {chain}")
        else:
            failures.append(
                f"cycle de renommage sans dates croissantes ({dates}): {chain} "
                f"-- signature d'un artefact d'union (aller-retour colle)")
    return failures, notes


def check_ledger(text: str) -> tuple[int, list[str], list[str]]:
    """Retourne (code retour, echecs, notes) pour le contenu du ledger."""
    lines, rows, errors = parse_ledger(text)
    if not lines or lines[0] != HEADER:
        errors.insert(0, f"en-tete attendu {HEADER!r}, lu {lines[0] if lines else '<vide>'!r}")
    failures = list(errors)
    failures.extend(find_duplicate_sources(rows))
    cycles, _ = find_cycles(rows)
    cycle_failures, notes = cycle_verdicts(cycles)
    failures.extend(cycle_failures)
    code = 1 if failures else 0
    return code, failures, notes


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--ledger", type=Path, default=LEDGER_RELPATH,
                        help=f"chemin du ledger (defaut: {LEDGER_RELPATH})")
    parser.add_argument("--json", action="store_true",
                        help="sortie JSON (failures, notes) pour les outils")
    args = parser.parse_args(argv)
    try:
        text = args.ledger.read_text(encoding="utf-8")
    except OSError as exc:
        print(f"ledger illisible ({args.ledger}): {exc}", file=sys.stderr)
        return 2
    code, failures, notes = check_ledger(text)
    if args.json:
        print(json.dumps({"ledger": str(args.ledger), "failures": failures,
                          "notes": notes}, ensure_ascii=False, indent=2))
    else:
        for note in notes:
            print(f"[NOTE] {note}")
        for failure in failures:
            print(f"[FAIL] {failure}")
        if code == 0 and notes:
            print(f"ledger propre ({len(notes)} cycle(s) legitime(s), notes ci-dessus)")
        elif code == 0:
            print("ledger propre")
    return code


if __name__ == "__main__":
    sys.exit(main())
