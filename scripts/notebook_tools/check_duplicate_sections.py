#!/usr/bin/env python3
"""Recensement des sections DUPLIQUEES a l'identique dans un notebook.

Demande user (2026-09-20) : « Il denonce notamment le fait qu'un redressement
laisse des sections d'interpretation en double et meme un resume en double.
Peut-etre que tu pourrais mesurer deja le nombre de Notebooks qui possedent
ainsi le resume final double, pour avoir une idee de l'ampleur du probleme ? »

Le defaut vise est le sous-produit mesurable de la campagne de densification
#13410 : chaque tranche ajoute une section sans consolider celle qui existe,
si bien qu'un notebook finit avec deux « ## Conclusion », trois
« ### Interpretation », ou un « Resume » suivi d'un « Ce qu'il faut retenir ».
Contrairement au recouvrement PARTIEL mesure par ``check_split_reading_cells``
(cellules de lecture scindees), la repetition d'un MEME titre est un signal
DUR : un notebook n'a pas legitimement deux « ## Resume ».

Trois signaux, de force decroissante :

  1. ``dup_closing``   -- un meme titre de CLOTURE (conclusion / resume /
                          synthese / bilan / points cles / recapitulatif /
                          take-aways) apparait plus d'une fois, apres
                          normalisation. Signal DUR, faux positif quasi nul.
  2. ``dup_reading``   -- un meme titre d'INTERPRETATION (lecture / lecture
                          chiffree / interpretation / analyse du resultat)
                          apparait plus d'une fois. Signal DUR : c'est
                          l'empilement de lectures nomme par le user.
  3. ``multi_closing`` -- au moins deux titres de cloture DISTINCTS dans le
                          dernier quart des cellules. Signal FAIBLE, rendu
                          en ``advisory`` : une section peut legitimement
                          finir par « Points cles ». Jamais bloquant.

CE QUE CET ORGANE N'EST PAS
---------------------------
Ce n'est PAS un critere d'acceptation, et un compte tombe a zero n'est PAS
une preuve qu'un notebook est presentable. Mandat user du 2026-09-20 :

    « on arrete de faire des MAJ au petit bonheur la chance. On se pose avec
    un regard critique devant chaque Notebook, et on garantit en sorte qu'il
    n'est plus du tout degenere et qu'il est franchement presentable, pas
    juste qu'une metrique de verification a evolue dans la bonne direction,
    car ce sont ces edits mecaniques sans reelle consideration du produit
    final qui ont produit l'etat actuel. »

L'organe repond donc a une seule question : *ou regarder, et le defaut
nomme a-t-il disparu ?* La consolidation -- quel contenu garder des deux
sections, dans quel ordre, avec quelle progression -- est une lecture
critique du notebook entier, qui ne se delegue a aucun compteur. Le JSON
porte ce rappel dans son champ ``not_an_acceptance_criterion``.

Robustesse : un notebook illisible est rendu comme finding ``unreadable`` et
n'interrompt PAS le balayage (lecon #17044 : un scanner qui s'arrete au
premier JSON corrompu ne mesure que le prefixe de l'arborescence).

Codes de retour : 0 = aucun finding dur ; 2 = findings durs (avec
``--fail-on-findings``) ; 1 = erreur d'invocation.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import unicodedata
from collections import defaultdict
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_ROOT = REPO_ROOT / "MyIA.AI.Notebooks"

CLOSING_RE = re.compile(
    # « ### **3. Resume** » doit se reconnaitre comme « ## Resume » : l'emphase
    # et la numerotation peuvent s'intercaler entre le diese et le mot-cle.
    r"^\s{0,3}#{1,4}[\s*_`]*(?:\d+[\.\)][\s*_`]*)?"
    r"(conclusion|r[ée]sum[ée]|synth[èe]se|bilan|en r[ée]sum[ée]|"
    r"ce que nous avons appris|ce qu'il faut retenir|[àa] retenir|"
    r"points?\s+cl[ée]s?|take[-\s]?aways?|r[ée]capitulatif)\b",
    re.IGNORECASE | re.MULTILINE,
)
READING_RE = re.compile(
    r"(lecture\s+chiffr|lecture\s+du\s+r[ée]sultat|lecture\s+ancr|"
    r"^lecture\b|interpr[ée]tation|analyse\s+du\s+r[ée]sultat)",
    re.IGNORECASE,
)
HEADING_RE = re.compile(r"^\s{0,3}(#{1,4})\s+(.+?)\s*$", re.MULTILINE)
TAIL_FRACTION = 0.75  # « dernier quart » pour le signal multi_closing
TAIL_MIN_CELLS = 4  # ... mais au moins 4 cellules : sur un notebook court,
# le dernier quart vaut une seule cellule et le signal ne peut jamais tirer.


def normalise(text: str) -> str:
    """Titre -> forme canonique : sans emphase, sans numerotation, sans accent."""
    text = re.sub(r"[`*_#]", "", text).strip().lower()
    text = re.sub(r"^\d+[\.\)]\s*", "", text)
    text = unicodedata.normalize("NFKD", text)
    text = "".join(ch for ch in text if not unicodedata.combining(ch))
    return re.sub(r"\s+", " ", text).strip()


def markdown_cells(notebook: dict) -> list:
    """Rend les couples (index de cellule, source markdown concatenee)."""
    out = []
    for index, cell in enumerate(notebook.get("cells", [])):
        if cell.get("cell_type") == "markdown":
            source = cell.get("source")
            if isinstance(source, list):
                source = "".join(source)
            out.append((index, source or ""))
    return out


def analyse_notebook(path: Path, root: Path) -> dict:
    """Rend le verdict d'un notebook. Ne leve jamais sur un JSON corrompu."""
    try:
        rel = str(path.relative_to(root))
    except ValueError:
        rel = str(path)
    record = {"notebook": rel.replace("\\", "/"), "findings": [], "advisory": []}
    try:
        notebook = json.loads(path.read_text(encoding="utf-8"))
    except Exception as exc:  # noqa: BLE001 -- on veut signaler TOUTES les causes
        record["findings"].append(
            {"kind": "unreadable", "detail": "%s: %s" % (type(exc).__name__, exc)}
        )
        return record

    cells = notebook.get("cells", [])
    md = markdown_cells(notebook)

    # --- signal 1 : meme titre de cloture repete -------------------------
    closing_positions = defaultdict(list)
    for index, source in md:
        for match in CLOSING_RE.finditer(source):
            closing_positions[normalise(match.group(0))].append(index)
    for title, positions in sorted(closing_positions.items()):
        if len(positions) > 1:
            record["findings"].append(
                {
                    "kind": "dup_closing",
                    "title": title,
                    "occurrences": len(positions),
                    "cells": positions,
                }
            )

    # --- signal 2 : meme titre d'interpretation repete -------------------
    reading_positions = defaultdict(list)
    for index, source in md:
        for match in HEADING_RE.finditer(source):
            title = match.group(2)
            if READING_RE.search(title.strip()):
                reading_positions[normalise(title)].append(index)
    for title, positions in sorted(reading_positions.items()):
        if len(positions) > 1:
            record["findings"].append(
                {
                    "kind": "dup_reading",
                    "title": title,
                    "occurrences": len(positions),
                    "cells": positions,
                }
            )

    # --- signal 3 (advisory) : clotures distinctes en fin de notebook ----
    if cells:
        cut = min(int(len(cells) * TAIL_FRACTION), max(0, len(cells) - TAIL_MIN_CELLS))
        distinct = set()
        for index, source in md:
            if index >= cut:
                for match in CLOSING_RE.finditer(source):
                    distinct.add(normalise(match.group(0)))
        if len(distinct) > 1:
            record["advisory"].append(
                {
                    "kind": "multi_closing",
                    "distinct": sorted(distinct),
                    "count": len(distinct),
                }
            )

    return record


def iter_notebooks(targets: list, root: Path):
    for target in targets:
        if target.is_dir():
            for path in sorted(target.rglob("*.ipynb")):
                if ".ipynb_checkpoints" in path.parts:
                    continue
                yield path
        elif target.suffix == ".ipynb":
            yield target


NOT_ACCEPTANCE = (
    "Zero finding est NECESSAIRE, jamais SUFFISANT : cet organe ne mesure que "
    "la repetition d'un titre a l'identique. Il ne dit rien de la coherence de "
    "la sequence, de la progression pedagogique, ni de la qualite de la "
    "consolidation. Un notebook se declare presentable apres une lecture "
    "critique de bout en bout, pas parce qu'un compteur est tombe a zero."
)


def excess_count(record: dict) -> int:
    """Nombre de sections EN TROP (occurrences au-dela de la premiere)."""
    return sum(f.get("occurrences", 1) - 1 for f in record["findings"])


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument(
        "paths", nargs="*", help="notebooks ou repertoires (defaut : MyIA.AI.Notebooks)"
    )
    parser.add_argument("--json", action="store_true", help="sortie machine")
    parser.add_argument(
        "--fail-on-findings", action="store_true", help="exit 2 si findings durs"
    )
    parser.add_argument(
        "--worklist", action="store_true", help="liste triee par nombre de sections en trop"
    )
    parser.add_argument(
        "--root", default=str(DEFAULT_ROOT), help="racine pour les chemins relatifs"
    )
    args = parser.parse_args(argv)

    root = Path(args.root)
    targets = [Path(p) for p in args.paths] or [root]
    records = [analyse_notebook(p, root) for p in iter_notebooks(targets, root)]

    carriers = [r for r in records if r["findings"]]
    unreadable = [
        r for r in carriers if any(f["kind"] == "unreadable" for f in r["findings"])
    ]
    hard = [
        r for r in carriers if any(f["kind"] != "unreadable" for f in r["findings"])
    ]

    if args.json:
        print(
            json.dumps(
                {
                    "scanned": len(records),
                    "carriers": len(hard),
                    "unreadable": len(unreadable),
                    "advisory_only": sum(
                        1 for r in records if r["advisory"] and not r["findings"]
                    ),
                    "not_an_acceptance_criterion": NOT_ACCEPTANCE,
                    "records": [r for r in records if r["findings"] or r["advisory"]],
                },
                ensure_ascii=False,
                indent=2,
            )
        )
    elif args.worklist:
        ranked = sorted(hard, key=lambda r: (-excess_count(r), r["notebook"]))
        for record in ranked:
            kinds = ",".join(sorted({f["kind"] for f in record["findings"]}))
            print("%3d  %-24s  %s" % (excess_count(record), kinds, record["notebook"]))
        print("\n%d notebooks porteurs / %d scannes" % (len(ranked), len(records)))
    else:
        for record in hard:
            print(record["notebook"])
            for finding in record["findings"]:
                if finding["kind"] == "unreadable":
                    print("    unreadable : %s" % finding["detail"])
                else:
                    cells = ",".join(str(c) for c in finding["cells"])
                    print(
                        "    %-12s « %s » x%d (cellules %s)"
                        % (
                            finding["kind"],
                            finding["title"],
                            finding["occurrences"],
                            cells,
                        )
                    )
        print(
            "\n%d porteurs, %d illisibles, %d scannes"
            % (len(hard), len(unreadable), len(records))
        )
        print("\nRAPPEL : %s" % NOT_ACCEPTANCE)

    if args.fail_on_findings and hard:
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
