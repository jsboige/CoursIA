"""Fabrique la charge de distillation **reelle** des pilotes P1/P2/P3 (#14499).

Difference d'avec `distill_charge_fixture.md` : la fixture est **figee** (une copie
d'une section a une tete donnee, ecriture pour que les trois moteurs distillent le
meme octet). Cette charge-ci est **extraite du carnet vivant** : le fichier produit
est une section reelle d'un carnet du depot, extraite par ce script, avec sa
provenance (chemin, plage de cellules, tete du depot, horodatage).

Pourquoi les deux coexistent : la fixture est le **controle** (charge byte-stable
d'un moteur a l'autre, d'une execution a l'autre), la charge reelle est la **mesure**
(le comportement des moteurs sur une section qui n'a pas ete ecrite pour l'occasion).
Les deux pilotes ne sont donc pas interchangeables : chacun sa charge, et c'est le
comparatif entre moteurs qui les rapproche.

Usage :
    python build_real_charge.py --notebook <chemin .ipynb> --from-cell N --to-cell M \
        --out distill_charge_vraie.md
    python build_real_charge.py --notebook <chemin .ipynb> --list   # inventaire des cellules
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO_ROOT = HERE.parents[3]


def head_sha() -> str:
    try:
        return subprocess.run(
            ["git", "-C", str(REPO_ROOT), "rev-parse", "--short", "HEAD"],
            capture_output=True, text=True, encoding="utf-8", errors="replace",
            check=True,
        ).stdout.strip()
    except Exception:  # pragma: no cover - hors depot
        return "inconnu"


def cell_source(cell: dict) -> str:
    return "".join(cell.get("source", []))


def cell_outputs(cell: dict) -> str:
    """Sorties textuelles des cellules code (le distillateur doit voir ce que le
    code a produit, pas seulement son texte)."""
    chunks = []
    for out in cell.get("outputs", []) or []:
        text = out.get("text")
        if isinstance(text, list):
            text = "".join(text)
        if text:
            chunks.append(text)
        data = out.get("data")
        if isinstance(data, dict) and isinstance(data.get("text/plain"), list):
            chunks.append("".join(data["text/plain"]))
    return "\n".join(chunks).strip()


def render(cell: dict, index: int) -> str:
    kind = cell.get("cell_type")
    src = cell_source(cell).strip()
    if kind == "markdown":
        return f"## [cellule {index} | markdown]\n\n{src}\n"
    out = cell_outputs(cell)
    block = f"## [cellule {index} | code]\n\n```python\n{src}\n```\n"
    if out:
        block += f"\n### Sortie de la cellule\n\n```\n{out[:2000]}\n```\n"
    return block


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--notebook", required=True, help="chemin du carnet .ipynb")
    ap.add_argument("--from-cell", type=int, default=None)
    ap.add_argument("--to-cell", type=int, default=None)
    ap.add_argument("--out", default=str(HERE / "distill_charge_vraie.md"))
    ap.add_argument("--list", action="store_true", help="inventaire des cellules, rien n'est ecrit")
    args = ap.parse_args()

    notebook = Path(args.notebook)
    payload = json.loads(notebook.read_text(encoding="utf-8"))
    cells = payload.get("cells", [])

    if args.list:
        for i, cell in enumerate(cells):
            src = cell_source(cell)
            head = " ".join(src.strip().splitlines()[:1])[:90]
            print(f"{i:3d}  {cell.get('cell_type'):8s}  {len(src):6d} car.  {head}")
        return 0

    if args.from_cell is None or args.to_cell is None:
        raise SystemExit("--from-cell et --to-cell sont requis (ou --list)")
    if not 0 <= args.from_cell <= args.to_cell < len(cells):
        raise SystemExit(f"plage invalide pour un carnet de {len(cells)} cellules")

    parts = [
        "# Charge de distillation REELLE (issue #14499, point 3)",
        "",
        f"Provenance : `{notebook.as_posix()}`, cellules {args.from_cell}..{args.to_cell}, "
        f"extraction live a la tete `{head_sha()}` du depot.",
        "",
        "Cette charge n'est pas **figee** : elle est extraite du carnet vivant par "
        "`build_real_charge.py`. Elle complete `distill_charge_fixture.md` (charge "
        "figee, utilisee comme controle byte-stable entre moteurs), elle ne s'y "
        "substitue pas : le comparatif des trois moteurs se fait sur la meme charge "
        "dans les trois, jamais sur une charge differente.",
        "",
    ]
    for i in range(args.from_cell, args.to_cell + 1):
        parts.append(render(cells[i], i))
        parts.append("")

    out = Path(args.out)
    out.write_text("\n".join(parts), encoding="utf-8", newline="\n")
    print(f"charge reelle ecrite : {out.name} ({out.stat().st_size} octets, "
          f"cellules {args.from_cell}..{args.to_cell} de {notebook.name}, tete {head_sha()})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
