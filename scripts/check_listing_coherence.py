#!/usr/bin/env python3
"""Organe listing-coherence (#18354, tranche stale-table, issue #23394).

Compare des **ENSEMBLES D'IDENTIFIANTS**, pas des comptes. Le defaut qu'il
voit est celui du cas fondateur de #20035 : la prose annonce « les huit
carnets », et la table de la section 2 s'arrete a `08` la ou le stream de la
cellule de code liste `01` a `15`. Une comparaison de comptes ne peut pas le
voir -- elle compare des nombres, la ou la preuve est une liste tronquee.

Trois conditions, toutes requises, pour un finding :

1. cote STREAM : une cellule de code dont une sortie `stream` contient un
   listing numerote (`01-...`, `02-...`), au moins deux identifiants ;
2. cote PROSE : une cellule markdown portant un tableau dont la **premiere
   colonne** est faite d'identifiants de meme largeur, et dont la cellule de
   prose **annonce un total** (« huit carnets », « 12 notebooks ») -- sans
   cette annonce, un tableau partiel est legitime ;
3. DISCRIMINANT : les identifiants du tableau forment un **prefixe contigu**
   du listing du stream ET sont moins nombreux. Une table qui liste un
   sous-ensemble arbitraire (« les 3 plus longs ») ne forme pas un prefixe
   et n'est pas signalee.

Sortie : rc=0 propre, rc=1 au moins un finding, rc=2 erreur d'usage.
Advisory par construction (patron #11435) -- jamais bloquant seul.

MESURE CORPUS : a relever au corps de la PR (taux de faux positifs lu a la
source, comme l'exige #20035), jamais recopiee ici -- un taux mesure sur un
corpus qui grossit se perime.

Usage :
    python scripts/check_listing_coherence.py --paths MyIA.AI.Notebooks/SymbolicAI/Lean
    python scripts/check_listing_coherence.py --json nb1.ipynb nb2.ipynb
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

# Identifiant de listing : deux chiffres, un separateur, puis du texte.
STREAM_ID_RE = re.compile(r"^\s*(\d{2})-[A-Za-z0-9]")
TABLE_ID_RE = re.compile(r"^\d{2}$")

# Nombres en toutes lettres utilises dans les annonces de total (1..20).
MOTS_NOMBRES = {
    "un": 1, "une": 1, "deux": 2, "trois": 3, "quatre": 4, "cinq": 5,
    "six": 6, "sept": 7, "huit": 8, "neuf": 9, "dix": 10, "onze": 11,
    "douze": 12, "treize": 13, "quatorze": 14, "quinze": 15, "seize": 16,
    "dix-sept": 17, "dix-huit": 18, "dix-neuf": 19, "vingt": 20,
}
_MOTS = "|".join(sorted(MOTS_NOMBRES, key=len, reverse=True))
# « huit carnets », « 12 notebooks », « les sept carnets » : un total annonce
# devant un substantif pluriel. Le pluriel est exige : « un carnet » ne fixe
# pas un total.
ANNONCE_RE = re.compile(
    r"\b(?:" + _MOTS + r"|\d{1,3})\s+(?:carnets?|notebooks?|modules?|fichiers?|fiches?|le[cç]ons?)\b",
    re.IGNORECASE,
)


def _source(cell: dict) -> str:
    src = cell.get("source", "")
    return "".join(src) if isinstance(src, list) else str(src)


def _stream_text(cell: dict) -> str:
    """Concatene les sorties `stream` d'une cellule de code."""
    morceaux: list[str] = []
    for sortie in cell.get("outputs", []) or []:
        if sortie.get("output_type") == "stream":
            texte = sortie.get("text", "")
            morceaux.append("".join(texte) if isinstance(texte, list) else str(texte))
    return "".join(morceaux)


def _ids_stream(texte: str) -> list[str]:
    ids: list[str] = []
    for ligne in texte.splitlines():
        m = STREAM_ID_RE.match(ligne)
        if m:
            ident = m.group(1)
            if not ids or ids[-1] != ident:
                ids.append(ident)
    return ids


def _ids_tableau(cellule: dict) -> tuple[list[str], bool]:
    """Identifiants de la premiere colonne + presence d'un tableau markdown."""
    ids: list[str] = []
    vu_tableau = False
    for ligne in _source(cellule).splitlines():
        brut = ligne.strip()
        if not brut.startswith("|"):
            continue
        cellules = [c.strip() for c in brut.strip("|").split("|")]
        if not cellules:
            continue
        if len(cellules) >= 2 and all(set(c) <= set("-: ") for c in cellules):
            vu_tableau = True
            continue
        if TABLE_ID_RE.match(cellules[0]):
            ids.append(cellules[0])
            vu_tableau = True
    return ids, vu_tableau


def _prefixe_tronque(table: list[str], stream: list[str]) -> list[str] | None:
    """Rend les identifiants manquants si `table` est un prefixe contigu tronque."""
    if len(table) < 2 or len(table) >= len(stream):
        return None
    if stream[: len(table)] != table:
        return None
    return stream[len(table):]


def scan_notebook(path: Path) -> list[dict]:
    """Findings d'un notebook, sous forme de dictionnaires serialisables."""
    try:
        nb = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        return [{"notebook": str(path), "erreur": str(exc)}]
    cellules = nb.get("cells", [])
    listings: list[tuple[int, list[str]]] = []
    for i, cellule in enumerate(cellules):
        if cellule.get("cell_type") != "code":
            continue
        ids = _ids_stream(_stream_text(cellule))
        if len(ids) >= 2:
            listings.append((i, ids))
    findings: list[dict] = []
    for i, cellule in enumerate(cellules):
        if cellule.get("cell_type") != "markdown":
            continue
        source = _source(cellule)
        if not ANNONCE_RE.search(source):
            continue
        table, vu_tableau = _ids_tableau(cellule)
        if not vu_tableau or len(table) < 2:
            continue
        # Le listing le plus proche de la cellule de prose, dans un sens ou
        # dans l'autre : la table annonce ce que la mesure montre.
        if not listings:
            continue
        j, stream = min(listings, key=lambda item: abs(item[0] - i))
        manquants = _prefixe_tronque(table, stream)
        if manquants:
            findings.append({
                "notebook": str(path),
                "cell_markdown": i,
                "cell_code": j,
                "identifiants_table": table,
                "identifiants_stream": stream,
                "manquants": manquants,
            })
    return findings


def _notebooks(specs: list[str]) -> list[Path]:
    trouves: list[Path] = []
    for spec in specs:
        p = Path(spec)
        if p.is_dir():
            trouves.extend(sorted(p.rglob("*.ipynb")))
        elif p.is_file():
            trouves.append(p)
        else:
            print(f"[listing-coherence] chemin introuvable : {spec}", file=sys.stderr)
            raise SystemExit(2)
    return trouves


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--json", action="store_true", help="sortie JSON")
    ap.add_argument(
        "--paths",
        action="append",
        default=[],
        metavar="CHEMIN",
        help="dossier ou carnet a scanner (repetable)",
    )
    ap.add_argument("notebooks", nargs="*", type=str, help="carnets a scanner")
    args = ap.parse_args(argv)

    cibles = _notebooks(args.paths + args.notebooks)
    if not cibles:
        print("[listing-coherence] aucun carnet dans le perimetre", file=sys.stderr)
        return 2

    findings: list[dict] = []
    for chemin in cibles:
        findings.extend(scan_notebook(chemin))

    erreurs = [f for f in findings if "erreur" in f]
    vrais = [f for f in findings if "erreur" not in f]

    if args.json:
        print(json.dumps({"carnets": len(cibles), "findings": vrais, "erreurs": erreurs},
                         ensure_ascii=False, indent=2))
    else:
        for f in vrais:
            print(
                f"{f['notebook']} : table (cellule {f['cell_markdown']}) tronquee a "
                f"{len(f['identifiants_table'])} identifiants sur les "
                f"{len(f['identifiants_stream'])} du listing (cellule {f['cell_code']}) "
                f"-- manquants : {', '.join(f['manquants'])}"
            )
        for e in erreurs:
            print(f"{e['notebook']} : illisible -- {e['erreur']}", file=sys.stderr)
        print(f"[listing-coherence] carnets={len(cibles)} findings={len(vrais)}")

    return 1 if vrais else 0


if __name__ == "__main__":
    sys.exit(main())
