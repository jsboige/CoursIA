#!/usr/bin/env python3
"""Deduplique les lignes d'un CSV de cellules translations (notebook, cell_id).

Contexte (#19023) : `translations/iit/iit.csv` portait une duplication
systemique preexistante (1164 cles (notebook, cell_id) en double, toutes
byte-identiques). Mesure (#19230, blob SHAs) : 3739 -> 2575 lignes
(-1164), 4 540 097 -> 3 103 067 octets. Ce outil deduplique SANS
reordonner : premiere occurrence conservee, lignes suivantes supprimees.

Nuance : « sans reordonner » est vrai en LIGNES du CSV deduplique (l'outil
n'ecrit que par suppression). La regen integrale (T1 --full) qui alimente
le chantier n'est PAS garantie sans reordonnancement lexicographique --
elle reecrit le fichier entier, d'ou un volume de regen sans rapport avec
le delta de ce dedup (les « 85k lignes » cites au depart venaient de la).

Invariants verifies par l'outil (echec = rc 1, fichier inchange) :
- les lignes dupliquees sont byte-identiques (toute divergence = refus,
  arbitrage manuel requis : quelle ligne est conforme au hash notebook) ;
- l'ordre des carnets (sequence des premieres occurrences) est inchange ;
- le round-trip csv est byte-identique sur les lignes conservees.

Usage :
    python scripts/translation/dedup_cells_csv.py translations/iit/iit.csv
    python scripts/translation/dedup_cells_csv.py --check <csv>   # mesure seule, ecriture prohibee
    python scripts/translation/dedup_cells_csv.py --resolve <csv> # dedup a divergence (#21489)

Mode --resolve (#21489) : pour les cles dont les occurrences DIVERGENT (53
mesurees sur ml-datascience + planners), l'outil tranche au lieu de refuser :
- garde l'occurrence dont le pivot (src_hash, text_fr, hash_fr) correspond au
  notebook courant (extraction T1 en memoire) ;
- si aucune ne correspond : garde la DERNIERE occurrence (la plus recemment
  appendee par T1) et rafraichit son pivot depuis le notebook -- exactement
  ce que `T1 --update` ferait a la prochaine passe, ce qui rend le rejeu
  idempotent (0 ligne modifiee) ;
- notebook absent du disque (archive) : garde la derniere occurrence telle
  quelle (pas de source a laquelle se referer) ;
- fusionne les colonnes cibles non vides des occurrences ecartees -- une
  traduction deposee n'est JAMAIS ecrasee par une chaine vide.
Le mode byte-identique historique reste le comportement par défaut.
"""

from __future__ import annotations

import argparse
import csv
import io
import sys
from collections import defaultdict
from pathlib import Path

KEY_COLUMNS = 2  # notebook, cell_id

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(Path(__file__).resolve().parent))
from extract_cells_to_csv import PIVOT_LANG, TARGET_LANGS, extract_notebook  # noqa: E402


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


def resolve(
    rows: list[list[str]], repo_root: Path, src_lang: str = PIVOT_LANG
) -> tuple[list[list[str]], dict, list[str]]:
    """Deduplique en tranchant les divergences au notebook courant (#21489).

    Retourne (lignes resolues, stats, erreurs). Les occurrences ecartees sont
    supprimees ; l'occurrence gardee reste a SA position (ordre relatif des
    lignes conserves inchange). Colonnes cibles = text_<lang>/hash_<lang> pour
    lang != src_lang : fusion non-vide-sur-vide uniquement.
    """
    header, body = rows[0], rows[1:]
    col = {name: idx for idx, name in enumerate(header)}
    target_cols = [
        f"{kind}_{lang}"
        for lang in TARGET_LANGS
        for kind in ("text", "hash")
        if lang != src_lang
    ]
    pivot_text_col = f"text_{src_lang}"
    pivot_hash_col = f"hash_{src_lang}"

    groups: dict[tuple[str, str], list[int]] = defaultdict(list)
    for idx, row in enumerate(body):
        groups[(row[0], row[1])].append(idx)

    fresh_cache: dict[str, dict[str, dict] | None] = {}

    def fresh_rows_for(nb_rel: str) -> dict[str, dict] | None:
        if nb_rel not in fresh_cache:
            nb_path = repo_root / nb_rel
            if not nb_path.exists():
                fresh_cache[nb_rel] = None
            else:
                rows_fresh = extract_notebook(nb_path, repo_root, src_lang)
                fresh_cache[nb_rel] = {r["cell_id"]: r for r in rows_fresh}
        return fresh_cache[nb_rel]

    drop: set[int] = set()
    stats = {
        "keys_resolved": 0,
        "kept_pivot_match": 0,
        "kept_last_refreshed": 0,
        "kept_last_notebook_absent": 0,
        "byte_identical": 0,
        "target_values_merged": 0,
    }
    errors: list[str] = []
    for (nb_rel, cell_id), idxs in sorted(groups.items()):
        if len(idxs) < 2:
            continue
        occs = [body[i] for i in idxs]
        if all(o == occs[0] for o in occs[1:]):
            # Byte-identiques : comportement historique, premiere occurrence.
            stats["byte_identical"] += 1
            drop.update(idxs[1:])
            stats["keys_resolved"] += 1
            continue
        fresh_by_cell = fresh_rows_for(nb_rel)
        fresh = fresh_by_cell.get(cell_id) if fresh_by_cell else None
        if fresh is not None:
            match = next(
                (
                    o
                    for o in occs
                    if o[col["src_hash"]] == fresh["src_hash"]
                    and o[col[pivot_text_col]] == fresh[pivot_text_col]
                ),
                None,
            )
            keep = match if match is not None else occs[-1]
            # Toujours rafraichir le pivot depuis le notebook : identique a
            # ce que T1 --update ferait a la prochaine passe, donc le rejeu
            # rend 0 ligne modifiee (idempotence, cible #21489 point 3).
            keep[col["cell_type"]] = fresh["cell_type"]
            keep[col["src_lang"]] = fresh["src_lang"]
            keep[col["src_hash"]] = fresh["src_hash"]
            keep[col[pivot_text_col]] = fresh[pivot_text_col]
            keep[col[pivot_hash_col]] = fresh[pivot_hash_col]
            keep[col["translate_policy"]] = fresh["translate_policy"]
            if match is not None:
                stats["kept_pivot_match"] += 1
            else:
                stats["kept_last_refreshed"] += 1
        elif fresh_by_cell is None:
            # Notebook absent (archive) : derniere occurrence telle quelle.
            keep = occs[-1]
            stats["kept_last_notebook_absent"] += 1
        else:
            # Notebook lisible mais cell_id disparu : ORPHAN en double --
            # garder la derniere (donnees les plus recentes), pas de pivot a
            # rafraichir ; check_translation_sync signalera ORPHAN_ROW.
            keep = occs[-1]
            errors.append(
                f"WARNING cle orpheline dupliquee, derniere occurrence conservee : "
                f"{nb_rel} cell_id={cell_id}"
            )
        for occ in occs:
            if occ is keep:
                continue
            for name in target_cols:
                if not keep[col[name]] and occ[col[name]]:
                    keep[col[name]] = occ[col[name]]
                    stats["target_values_merged"] += 1
        drop.update(i for i, o in zip(idxs, occs) if o is not keep)
        stats["keys_resolved"] += 1

    kept_rows = [row for idx, row in enumerate(body) if idx not in drop]
    return [header, *kept_rows], stats, errors


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
    parser.add_argument(
        "--resolve",
        action="store_true",
        help="dedup a divergence (#21489) : garde l'occurrence conforme au notebook "
        "(repli : derniere), rafraichit le pivot, fusionne les cibles non vides",
    )
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=REPO_ROOT,
        help="racine du depot pour resoudre les chemins notebooks (defaut : racine git)",
    )
    parser.add_argument(
        "--src-lang",
        default=PIVOT_LANG,
        help=f"langue pivot des notebooks source (defaut : {PIVOT_LANG})",
    )
    args = parser.parse_args(argv)

    with io.open(args.csv_path, encoding="utf-8", newline="") as handle:
        raw = handle.read()
    rows = list(csv.reader(io.StringIO(raw, newline="")))

    if args.resolve:
        if serialize(rows) != raw:
            print(
                "ERREUR: round-trip csv non byte-identique sur ce fichier : refus "
                "(le writer ne reproduit pas la serialisation en place)",
                file=sys.stderr,
            )
            return 1
        resolved, stats, warnings = resolve(rows, args.repo_root, args.src_lang)
        order_before = notebook_order(rows)
        order_after = notebook_order(resolved)
        if order_before != order_after:
            print("ERREUR: ordre des carnets modifie : refus", file=sys.stderr)
            return 1
        print(f"fichier: {args.csv_path}")
        print(f"lignes: {len(rows) - 1} -> {len(resolved) - 1}")
        for key, value in stats.items():
            print(f"  {key}: {value}")
        for warning in warnings:
            print(f"  {warning}", file=sys.stderr)
        if args.check or stats["keys_resolved"] == 0:
            return 0
        rewritten = serialize(resolved)
        if parse_rows_from_string(rewritten) != resolved:
            print("ERREUR: relecture de la sortie diverge", file=sys.stderr)
            return 1
        with io.open(args.csv_path, "w", encoding="utf-8", newline="") as handle:
            handle.write(rewritten)
        print(f"OK: {stats['keys_resolved']} cles resolues, ecrit {args.csv_path}")
        return 0

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
