#!/usr/bin/env python3
"""Pose les identifiants de cellule manquants (ratchet `Cell ID`).

Pourquoi cet outil existe
-------------------------
Un carnet ne par le MCP `jupyter-papermill` (`create_notebook` + `add_cell` +
`write_notebook`) **n'a pas d'identifiant de cellule** : les trois ecritures
produisent des cellules sans la cle `id`. Le ratchet
`notebook-cell-id-ratchet` compte alors une identite invalide par cellule, et
une PR qui **ajoute** un carnet passe de `0` a `N` : le CI la refuse
(`ECHEC ... : 0 -> 22`). Le MCP n'a pas d'equivalent de
`nbformat.read(..., as_version=4)`, qui repare silencieusement les ids
manquants.

Ce que fait l'outil
-------------------
INSERTION TEXTUELLE d'une ligne `"id": ...` dans chaque cellule qui n'en a
pas. Le reste du fichier est preserve **octet pour octet** : les sorties, les
`execution_count`, l'ordre des cles, le formatage, les fins de ligne. Aucun
contenu n'est reecrit -- c'est la difference avec un aller-retour
`json.dumps`, qui reformate tout le carnet.

Garde-fous :
- le fichier produit est **relu et valide** (`json.loads`) avant ecriture ;
- le carnet reparse est compare a l'original : seule la cle `id` a change ;
- une copie de sauvegarde est ecrite a cote (`.ensure_cell_ids.bak`) ;
- `--check` ne modifie rien et sort 1 si un identifiant manque.

L'identifiant est **deterministe** (`<prefixe><index>` sur deux chiffres) :
rejouer l'outil sur le meme carnet ne produit pas de churn, et l'identifiant
survit a l'insertion d'une cellule (l'index ne bouge que si la cellule
elle-meme bouge). Le prefixe par defaut derive du nom du fichier.

Usage :
    python scripts/notebook_tools/ensure_cell_ids.py --check <carnet> ...
    python scripts/notebook_tools/ensure_cell_ids.py --apply --prefix z318rust <carnet> ...
"""
from __future__ import annotations

import argparse
import json
import re
import shutil
import sys
import tempfile
from pathlib import Path

ID_RE = re.compile(r"^[A-Za-z0-9_-]{1,64}$")
# Chaque cellule commence par sa ligne `"cell_type"`, suivie d'une virgule
# (une cellule porte toujours au moins `metadata` et `source`).
CELL_TYPE_RE = re.compile(r'(?m)^([ \t]*)"cell_type":\s*"[a-z]+",[ \t]*\r?$')
EOL_RE = re.compile(r"[ \t]*(\r?\n)")


def default_prefix(path: Path) -> str:
    """Prefixe derive du nom du fichier, dans le jeu de caracteres des ids."""
    stem = "".join(c for c in path.stem.lower() if c.isalnum() or c in "_-")
    return (stem[:24] or "cell")


def missing_ids(doc: dict) -> list[int]:
    """Indices des cellules dont l'identifiant est absent, invalide ou duplique."""
    seen: set[str] = set()
    out: list[int] = []
    for index, cell in enumerate(doc.get("cells") or []):
        value = cell.get("id")
        if not isinstance(value, str) or not ID_RE.fullmatch(value) or value in seen:
            out.append(index)
        else:
            seen.add(value)
    return out


def apply_ids(text: str, doc: dict, targets: list[int], prefix: str) -> str:
    """Insere une ligne `"id"` dans chaque cellule cible, dans l'ordre du texte.

    L'insertion se fait sur le texte brut : le reste du fichier n'est pas
    reecrit, donc pas de reformatage global. On insere de la FIN vers le
    DEBUT, pour que les positions deja calculees restent valides.
    """
    matches = list(CELL_TYPE_RE.finditer(text))
    cells = doc.get("cells") or []
    if len(matches) != len(cells):
        raise ValueError(
            f"{len(matches)} ligne(s) 'cell_type' pour {len(cells)} cellule(s) : "
            "carnet inattendu")
    positions: list[tuple[int, str, str]] = []
    for match in matches:
        eol = EOL_RE.match(text, match.end())
        if eol is None:
            raise ValueError("fin de ligne introuvable apres 'cell_type'")
        fin = eol.group(1)
        if fin == "\n" and match.end() > 0 and text[match.end() - 1] == "\r":
            fin = "\r\n"  # le "\r" a deja ete consomme par le motif
        positions.append((eol.end(), fin, match.group(1)))
    for index in reversed(targets):
        pos, eol, indent = positions[index]
        insertion = f'{indent}"id": "{prefix}{index:02d}",{eol}'
        text = text[:pos] + insertion + text[pos:]
    return text


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("notebooks", nargs="+", help="carnets a traiter")
    parser.add_argument("--check", action="store_true",
                        help="ne rien ecrire ; sortie 1 si un identifiant manque")
    parser.add_argument("--apply", action="store_true", help="ecrire les identifiants")
    parser.add_argument("--prefix", default=None,
                        help="prefixe des identifiants (defaut : derive du nom)")
    args = parser.parse_args(argv)
    if not args.check and not args.apply:
        parser.error("il faut --check ou --apply")

    rc = 0
    for raw in args.notebooks:
        path = Path(raw)
        text = path.read_text(encoding="utf-8", newline="")
        doc = json.loads(text)
        targets = missing_ids(doc)
        if not targets:
            print(f"OK {path}: toutes les cellules portent un identifiant")
            continue
        if args.check:
            print(f"MANQUE {path}: {len(targets)} cellule(s) sans identifiant "
                  f"({', '.join(str(i) for i in targets)})")
            rc = 1
            continue
        prefix = args.prefix or default_prefix(path)
        new_text = apply_ids(text, doc, targets, prefix)
        new_doc = json.loads(new_text)  # le fichier produit est relu et valide
        # Controle : rien d'autre que les cles `id` n'a bouge.
        for cell_old, cell_new in zip(doc["cells"], new_doc["cells"]):
            attendu = dict(cell_old)
            reel = dict(cell_new)
            reel.pop("id", None)
            if attendu != reel:
                raise ValueError(f"{path} : contenu modifie hors identifiants")
        backup = Path(tempfile.gettempdir()) / f"{path.name}.ensure_cell_ids.bak"
        shutil.copyfile(path, backup)
        path.write_text(new_text, encoding="utf-8", newline="")
        print(f"OK {path}: {len(targets)} identifiant(s) pose(s) "
              f"(prefixe {prefix}) ; sauvegarde {backup}")
    return rc


if __name__ == "__main__":
    sys.exit(main())
