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

Sortie : rc=0 propre, rc=1 au moins un finding **ou au moins un carnet
illisible**, rc=2 erreur d'usage. Un carnet qu'on n'a pas pu lire n'est pas
un carnet propre : il rend rc=1 et le compte des non-lus voyage dans le
rapport JSON (`non_lus`), pour qu'un « 0 finding » ne puisse pas se lire
comme une couverture complete (#23394, reserve 1).

BORNES DE L'ORGANE -- a lire avant de prendre un `0` pour une couverture :
`STREAM_ID_RE` fixe la largeur de l'identifiant a deux chiffres, donc une
serie a trois chiffres (`001-...`) n'est pas vue du tout ; une table PLUS
LONGUE que le stream (serie qui a retreci) n'est pas signalee ; un prefixe
troue par un identifiant absent du listing (`01`..`07` + `99`) ne forme pas
un prefixe contigu et reste muet. Ces trois-la sont coherents avec le
discriminant annonce, ce ne sont pas des defauts -- mais un `0` sur 1750
carnets ne dit pas « aucun tableau tronque existe », il dit « aucun tableau
tronque de cette forme-la ».

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
    r"\b(?P<total>" + _MOTS + r"|\d{1,3})\s+"
    r"(?:carnets?|notebooks?|modules?|fichiers?|fiches?|le[cç]ons?)\b",
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


def _annonce(cellule: dict) -> int | None:
    """Total annonce par la prose de la cellule, ou None s'il n'y en a pas.

    Le nombre capture n'etait lu par personne : `ANNONCE_RE` ne servait que
    de booleen, donc une prose qui annonce « huit carnets » au-dessus d'une
    table de 15 restait muette une fois la table reparee (#23394, reserve 4).
    """
    m = ANNONCE_RE.search(_source(cellule))
    if not m:
        return None
    brut = m.group("total").strip().lower()
    if brut.isdigit():
        return int(brut)
    return MOTS_NOMBRES.get(brut)


def scan_notebook(path: Path) -> list[dict]:
    """Findings d'un notebook, sous forme de dictionnaires serialisables."""
    try:
        nb = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        # UnicodeDecodeError n'herite pas de JSONDecodeError : un carnet
        # latin-1/UTF-16 non attrape sortait en traceback + rc=1, c'est-a-dire
        # avec le code du FINDING -- une accusation de troncature sur un
        # carnet qui n'a jamais ete lu (#23394, reserve 2).
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
        annonce = _annonce(cellule)
        if annonce is None:
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
                "kind": "prefixe",
                "identifiants_table": table,
                "identifiants_stream": stream,
                "manquants": manquants,
            })
        elif table == stream and annonce != len(stream):
            # Classe INVERSE de la fondatrice : la table a ete reparee, la
            # prose ne l'a pas ete. Restreinte a `table == stream` -- sur un
            # sous-ensemble assume (« les trois plus longs »), le nombre
            # annonce decrit la selection, pas le listing, et n'a rien a
            # comparer (#23394, reserve 4).
            findings.append({
                "notebook": str(path),
                "cell_markdown": i,
                "cell_code": j,
                "kind": "annonce",
                "annonce": annonce,
                "identifiants_stream": stream,
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
        print(json.dumps({
            "carnets": len(cibles),
            "findings": vrais,
            "erreurs": erreurs,
            "non_lus": len(erreurs),
        }, ensure_ascii=False, indent=2))
    else:
        for f in vrais:
            if f.get("kind") == "annonce":
                print(
                    f"{f['notebook']} : la prose (cellule {f['cell_markdown']}) annonce "
                    f"{f['annonce']} elements, le listing (cellule {f['cell_code']}) en "
                    f"porte {len(f['identifiants_stream'])}"
                )
                continue
            print(
                f"{f['notebook']} : table (cellule {f['cell_markdown']}) tronquee a "
                f"{len(f['identifiants_table'])} identifiants sur les "
                f"{len(f['identifiants_stream'])} du listing (cellule {f['cell_code']}) "
                f"-- manquants : {', '.join(f['manquants'])}"
            )
        for e in erreurs:
            print(f"{e['notebook']} : illisible -- {e['erreur']}", file=sys.stderr)
        print(f"[listing-coherence] carnets={len(cibles)} findings={len(vrais)} "
              f"non_lus={len(erreurs)}")

    # Un carnet illisible n'est pas un carnet propre : rc=1, jamais 0. Sinon
    # le commentaire vert dit « aucun tableau tronque » alors qu'un carnet
    # n'a jamais ete ouvert (#23394, reserve 1).
    return 1 if (vrais or erreurs) else 0


if __name__ == "__main__":
    sys.exit(main())
