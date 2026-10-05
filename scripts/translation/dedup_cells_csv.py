#!/usr/bin/env python3
"""Deduplique les lignes d'un CSV de cellules translations (notebook, cell_id).

Contexte (#19023) : `translations/iit/iit.csv` portait une duplication
systemique preexistante (~1164 cles (notebook, cell_id) en double, toutes
byte-identiques). La regen integrale (T1 --full) reecrit 85k lignes a cause
du reordonnancement lexicographique ; ce outil deduplique SANS reordonner :
premiere occurrence conservee, lignes suivantes supprimees.

Invariants verifies par l'outil (echec = rc 1, fichier inchange) :
- les lignes dupliquees sont byte-identiques (toute divergence = refus,
  arbitrage manuel requis : quelle ligne est conforme au hash notebook) ;
- l'ordre des carnets (sequence des premieres occurrences) est inchange ;
- le round-trip csv est byte-identique sur les lignes conservees.

Usage :
    python scripts/translation/dedup_cells_csv.py translations/iit/iit.csv
    python scripts/translation/dedup_cells_csv.py --check <csv>   # mesure seule, ecriture prohibee
"""

from __future__ import annotations

import argparse
import csv
import io
import sys
from pathlib import Path

KEY_COLUMNS = 2  # notebook, cell_id


def serialize(rows: list[list[str]]) -> str:
    buffer = io.StringIO(newline="")
    csv.writer(buffer, lineterminator="\n").writerows(rows)
    return buffer.getvalue()


def dedup(rows: list[list[str]]) -> tuple[list[list[str]], int, list[str]]:
    """Renvoie (lignes dedupliquees, nombre supprime, erreurs).

    Les lignes conservees gardent leur ordre relatif ; chaque cle
    (notebook, cell_id) garde sa premiere occurrence. Une cle dont les
    occurrences divergent n'est PAS tranchee : erreur nommee.
    """
    header, body = rows[0], rows[1:]
    kept: list[list[str]] = []
    seen: dict[tuple[str, str], list[str]] = {}
    removed = 0
    errors: list[str] = []
    for row in body:
        key = (row[0], row[1])
        if key not in seen:
            seen[key] = row
            kept.append(row)
            continue
        if row != seen[key]:
            errors.append(
                f"divergence pour {key[0]} cell_id={key[1]} : "
                "occurrences non identiques, arbitrage manuel requis"
            )
        removed += 1
    return [header, *kept], removed, errors


def notebook_order(rows: list[list[str]]) -> list[str]:
    order: list[str] = []
    seen: set[str] = set()
    for row in rows[1:]:
        if row[0] not in seen:
            seen.add(row[0])
            order.append(row[0])
    return order


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("csv_path", type=Path, help="CSV de cellules (ex. translations/iit/iit.csv)")
    parser.add_argument(
        "--check",
        action="store_true",
        help="mesurer seulement : aucune ecriture, rc 0 meme si des doublons existent",
    )
    args = parser.parse_args(argv)

    with io.open(args.csv_path, encoding="utf-8", newline="") as handle:
        raw = handle.read()
    rows = list(csv.reader(io.StringIO(raw, newline="")))
    deduped, removed, errors = dedup(rows)
    order_before = notebook_order(rows)
    order_after = notebook_order(deduped)

    failures = list(errors)
    if order_before != order_after:
        failures.append("ordre des carnets modifie : refus")
    if serialize(rows) != raw:
        failures.append(
            "round-trip csv non byte-identique sur ce fichier : refus "
            "(le writer ne reproduit pas la serialisation en place)"
        )

    print(f"fichier: {args.csv_path}")
    print(f"lignes: {len(rows) - 1} -> {len(deduped) - 1} ({removed} doublons supprimables)")
    print(f"carnets: {len(order_after)} (ordre inchange: {order_before == order_after})")
    for error in failures:
        print(f"ERREUR: {error}", file=sys.stderr)

    if failures:
        return 1
    if args.check or not removed:
        return 0

    rewritten = serialize(deduped)
    if parse_rows_from_string(rewritten) != deduped:
        print("ERREUR: relecture de la sortie diverge", file=sys.stderr)
        return 1
    with io.open(args.csv_path, "w", encoding="utf-8", newline="") as handle:
        handle.write(rewritten)
    print(f"OK: {removed} doublons supprimes, ordre preserve, ecrit {args.csv_path}")
    return 0


def parse_rows_from_string(text: str) -> list[list[str]]:
    return list(csv.reader(io.StringIO(text, newline="")))


if __name__ == "__main__":
    sys.exit(main())
