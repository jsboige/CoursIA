#!/usr/bin/env python3
"""Fixer deterministe des ids de cellules (issue #25136).

Ne touche QUE les identifiants de cellules : aucune source, aucune sortie,
aucun execution_count, aucune cle de serialisation autre que les lignes
"id":. Auto-verification structurelle systematique : l'arbre JSON
 resultant doit etre identique a l'original en dehors des ids.

Classes traitees (nbformat >= 4.5, schema : ^[a-zA-Z0-9-_]{1,64}$, unique) :
  - id absent           -> nouvel id (nbformat.v4.new_cell_id, 8 hexa)
  - id vide             -> nouvel id
  - id hors motif       -> nouvel id (apres verification git grep, cf --list-renames)
  - id duplique valide  -> la premiere occurrence est gardee, les suivantes reçoivent un nouvel id
  - id deja valide      -> jamais modifie

Sortie : par carnet, le decompte avant/apres ; --json pour la machine.
Codes retour : 0 = plus aucun defaut apres passage (ou rien a faire),
1 = il reste des defauts (mode --check) ou une erreur est survenue.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
ID_PATTERN = re.compile(r"^[a-zA-Z0-9_-]{1,64}$")


def new_id() -> str:
    """Nouvel identifiant, forme nbformat.v4.new_cell_id (8 hexa).

    Import differe : nbformat reste facultatif en mode --check pur, mais la
    forme canonique vient de lui quand il est present (flotte : toujours).
    """
    try:
        from nbformat.v4 import new_cell_id

        return new_cell_id()
    except Exception:
        import secrets

        return secrets.token_hex(4)


def classify(cells: list[dict]) -> list[tuple[int, str, str]]:
    """Retourne [(index_cellule, classe, id_courant)] pour chaque defaut.

    Classes : absent | empty | pattern | duplicate. Un id vide compte aussi
    comme doublon entre eux ; la premiere occurrence vide reste classee
    empty, les suivantes duplicate (garde la premiere occurrence).
    """
    defects: list[tuple[int, str, str]] = []
    seen: set[str] = set()
    for i, cell in enumerate(cells):
        cid = cell.get("id")
        if cid is None:
            defects.append((i, "absent", ""))
        elif cid == "":
            defects.append((i, "empty", ""))
        elif not isinstance(cid, str) or not ID_PATTERN.match(cid):
            defects.append((i, "pattern", str(cid)))
        elif cid in seen:
            defects.append((i, "duplicate", cid))
        if isinstance(cid, str) and ID_PATTERN.match(cid) and cid:
            seen.add(cid)
    return defects


def rebuild_cell(cell: dict, fixed_id: str) -> dict:
    """Reconstruit la cellule avec l'id en position canonique (apres cell_type)."""
    rest = {k: v for k, v in cell.items() if k != "id"}
    out: dict = {}
    for k, v in rest.items():
        out[k] = v
        if k == "cell_type":
            out["id"] = fixed_id
    if "id" not in out:  # cell_type absent (degenere) : id en tete
        out = {"id": fixed_id, **out}
    return out


def strip_cell_ids(nb: dict) -> dict:
    """Copie du carnet sans les cles 'id' des cellules (comparaison exacte)."""
    out = dict(nb)
    if "cells" in out:
        out["cells"] = [
            {k: v for k, v in cell.items() if k != "id"} for cell in out["cells"]
        ]
    return out


def process_file(path: Path, apply: bool, id_map: dict | None = None) -> dict:
    """Analyse (et optionnellement corrige) un carnet. Retourne le rapport."""
    raw = path.read_bytes()
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        return {"file": str(path), "error": f"utf8: {exc}", "before": -1, "after": -1}
    try:
        nb = json.loads(text)
    except json.JSONDecodeError as exc:
        return {"file": str(path), "error": f"json: {exc}", "before": -1, "after": -1}
    if (nb.get("nbformat", 0), nb.get("nbformat_minor", 0)) < (4, 5):
        return {"file": str(path), "skipped": "nbformat < 4.5", "before": 0, "after": 0}

    cells = nb.get("cells", [])
    defects = classify(cells)
    report = {
        "file": str(path.relative_to(REPO_ROOT)) if str(path).startswith(str(REPO_ROOT)) else str(path),
        "before": len(defects),
        "detail": {c: sum(1 for _, k, _ in defects if k == c) for _, c, _ in defects},
    }
    if not defects:
        report["after"] = 0
        return report
    if not apply:
        report["after"] = None
        return report

    # Attribution : ids neufs pour toutes les classes ; premiere occurrence gardee.
    # Ids existants (vide/hors-motif/duplique) : remplacement EN PLACE, la
    # position de la cle ne bouge pas (diff purement ligne "id":). Ids
    # absents : insertion canonique apres cell_type (rebuild_cell).
    new_cells = []
    fixed_records = []
    for i, cell in enumerate(cells):
        cls = next((k for j, k, _ in defects if j == i), None)
        if cls is None:
            new_cells.append(cell)
            continue
        old = cell.get("id")
        fid = new_id()
        if cls == "absent":
            new_cells.append(rebuild_cell(cell, fid))
        else:
            cell["id"] = fid
            new_cells.append(cell)
        fixed_records.append({"index": i, "class": cls, "old": old, "new": fid})
    nb["cells"] = new_cells

    # Auto-verification structurelle : rien d'autre que les ids ne doit changer.
    original = json.loads(text)
    if strip_cell_ids(original) != strip_cell_ids(nb):
        report["error"] = "structural check FAILED: diff hors ids refuse"
        report["after"] = -1
        return report

    eol = "\r\n" if "\r\n" in text else "\n"
    out_text = json.dumps(nb, indent=1, ensure_ascii=False)
    if text.endswith("\n"):  # preserver la presence/absence de fin de fichier
        out_text += eol
    path.write_bytes(out_text.encode("utf-8"))

    # Relecture + reclassification : le fichier ecrit doit etre propre.
    reread = json.loads(path.read_bytes().decode("utf-8"))
    report["after"] = len(classify(reread.get("cells", [])))
    report["fixed"] = fixed_records
    if id_map is not None:
        for rec in fixed_records:
            if isinstance(rec["old"], str) and rec["old"]:
                # Seuls les ids existants non vides peuvent etre des cles externes.
                id_map[f"{path.as_posix()}::{rec['old']}"] = rec["new"]
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("paths", nargs="+", help="carnets ou repertoires")
    parser.add_argument("--apply", action="store_true", help="corriger (defaut : lecture seule)")
    parser.add_argument("--check", action="store_true", help="exit 1 si un defaut reste")
    parser.add_argument("--json", action="store_true", help="sortie machine")
    parser.add_argument(
        "--map-file",
        help="ecrit un JSON {fichier::ancien_id: nouvel_id} pour re-cler les index externes (CSV de traduction)",
    )
    args = parser.parse_args()

    files: list[Path] = []
    for p in map(Path, args.paths):
        if p.is_dir():
            files.extend(sorted(p.rglob("*.ipynb")))
        else:
            files.append(p)

    id_map: dict = {}
    reports = [process_file(f, apply=args.apply, id_map=id_map) for f in files]
    if args.map_file and id_map:
        map_path = Path(args.map_file)
        map_path.parent.mkdir(parents=True, exist_ok=True)
        map_path.write_text(json.dumps(id_map, indent=1, ensure_ascii=False), encoding="utf-8")
    if args.json:
        print(json.dumps(reports, ensure_ascii=False))
    else:
        for r in reports:
            if "error" in r:
                print(f"ERREUR {r['file']}: {r['error']}")
            elif r.get("skipped"):
                print(f"SKIP   {r['file']}: {r['skipped']}")
            elif r["before"] == 0 and r.get("after") == 0:
                pass
            else:
                after = "?" if r.get("after") is None else r["after"]
                print(f"{r['before']:>3} -> {after:<3} {r['file']} {r.get('detail', '')}")
    remaining = sum(r.get("after") or 0 for r in reports)
    total_before = sum(r["before"] for r in reports if r["before"] > 0)
    touched = sum(1 for r in reports if r["before"] > 0)
    if not args.json:
        print(f"-- {touched} carnet(s), {total_before} defaut(s), restant {remaining}")
    if args.check and remaining:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
