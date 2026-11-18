"""Detecter le churn d'identifiants de cellules dans un carnet modifie.

Contexte : issue #22595 (suite de #22588). Quand on integre une contribution
dans un carnet existant en SUPPRIMANT puis RE-CREANT des cellules (au lieu de
les modifier en place via `update_cell` du MCP jupyter-papermill), les cellules
inchangees recoivent de NOUVEAUX ids. Le CSV de traduction
(`translations/<famille>/<serie>.csv`) est cle par `cell_id` : chaque cellule
re-identifiee re-cree sa ligne (+N/-M), d'ou le churn releve par la review
Hermes de #22588 (21 cellules re-identifiees pour 3 vraiment nouvelles).

Ce controle ne juge pas le fond (le contenu reste coherent) : il signale la
FORME. La signature de « supprime + recree » : un id present en base, absent a
la tete, dont la SOURCE reapparait a l'identique sous un autre id. Une
suppression reel (source absente de la tete) n'est PAS du churn et n'est pas
signalee.

Usage :
  # Mode PR : tous les carnets modifies de la PR, base = baseRefOid,
  #          tete = headRefOid
  python scripts/notebook_tools/check_cell_id_churn.py --pr <N> [--json-out PATH]

  # Mode atomique : un carnet, base = ref git, tete = disque (ou --head)
  python scripts/notebook_tools/check_cell_id_churn.py <chemin.ipynb> \
      --base origin/main [--head <ref>]

Sortie : un rapport par cellule churnee (id base -> id(s) tete, type, apercu
de la source) + les compteurs d'ids ajoutes/retires. Exit 1 si au moins une
cellule churnee, 0 sinon, 2 sur erreur d'usage. `--json-out` pour la forme
machine.

Pure lecture JSON + `git show`. Zero execution de notebook.
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

try:
    sys.stdout.reconfigure(encoding="utf-8")
except Exception:
    pass


def cell_id(cell: dict) -> str:
    return cell.get("id") or ""


def cell_source(cell: dict) -> str:
    """Source d'une cellule en texte unique (liste de lignes ou chaine)."""
    src = cell.get("source", [])
    if isinstance(src, list):
        return "".join(src)
    return src or ""


def cells_from_text(text: str) -> list[dict]:
    """Cellules d'un carnet fourni en texte JSON (vide si texte vide)."""
    if not text.strip():
        return []
    return json.loads(text).get("cells", [])


def load_cells_from_path(path: Path) -> list[dict]:
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f).get("cells", [])


def git_show(ref: str, path: str) -> str:
    """Contenu d'un fichier a une ref git (vide si le fichier n'y est pas)."""
    out = subprocess.run(
        ["git", "show", f"{ref}:{path}"],
        capture_output=True, text=True, encoding="utf-8",
    )
    return out.stdout if out.returncode == 0 else ""


def detect_churn(base_cells: list[dict], head_cells: list[dict]) -> dict:
    """Compare les ids de base et de tete d'un carnet.

    Retourne ``{"churned": [...], "added": n, "removed": n}`` ou ``churned``
    porte une entree par cellule dont l'id a change a source identique.
    """
    base_by_id = {cell_id(c): c for c in base_cells if cell_id(c)}
    head_by_id = {cell_id(c): c for c in head_cells if cell_id(c)}

    # source (identique) -> ids de tete qui la portent
    head_source_to_ids: dict[str, list[str]] = {}
    for cid, c in head_by_id.items():
        head_source_to_ids.setdefault(cell_source(c), []).append(cid)

    churned: list[dict] = []
    for cid, c in base_by_id.items():
        if cid in head_by_id:
            continue  # id conserve -> pas de churn
        new_ids = head_source_to_ids.get(cell_source(c), [])
        if new_ids:
            churned.append({
                "base_id": cid,
                "head_ids": sorted(new_ids),
                "cell_type": c.get("cell_type"),
                "source_preview": " ".join(cell_source(c).split())[:120],
            })

    return {
        "churned": churned,
        "added": sum(1 for cid in head_by_id if cid not in base_by_id),
        "removed": sum(1 for cid in base_by_id if cid not in head_by_id),
    }


def pr_changed_notebooks(pr: int) -> tuple[str, str, list[str]]:
    """(base_oid, head_oid, [chemins .ipynb]) pour les fichiers changes d'une PR."""
    out = subprocess.run(
        ["gh", "pr", "view", str(pr), "--json", "baseRefOid,headRefOid,files"],
        capture_output=True, text=True, encoding="utf-8",
    )
    if out.returncode != 0:
        raise RuntimeError(f"gh pr view {pr} : {out.stderr.strip()}")
    data = json.loads(out.stdout)
    paths = [f["path"] for f in data["files"] if f["path"].endswith(".ipynb")]
    return data["baseRefOid"], data["headRefOid"], paths


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument("notebook", nargs="?", type=Path,
                        help="Chemin du carnet (relatif a la racine du depot).")
    parser.add_argument("--base", default=None,
                        help="Ref git de base (ex. origin/main).")
    parser.add_argument("--head", default=None,
                        help="Ref git de tete (defaut : le fichier sur disque).")
    parser.add_argument("--pr", type=int, default=None,
                        help="Mode PR : tous les carnets modifies de la PR.")
    parser.add_argument("--json-out", default=None, type=Path)
    args = parser.parse_args(argv)

    if args.pr is None and (args.notebook is None or args.base is None):
        parser.error("soit --pr <N>, soit <notebook> --base <ref>")

    per_notebook: list[dict] = []

    if args.pr is not None:
        base_oid, head_oid, paths = pr_changed_notebooks(args.pr)
        for path in paths:
            base_cells = cells_from_text(git_show(base_oid, path))
            head_cells = cells_from_text(git_show(head_oid, path))
            res = detect_churn(base_cells, head_cells)
            res["path"] = path
            per_notebook.append(res)
    else:
        rel = str(args.notebook)
        base_cells = cells_from_text(git_show(args.base, rel))
        if args.head:
            head_cells = cells_from_text(git_show(args.head, rel))
        else:
            head_cells = load_cells_from_path(args.notebook)
        res = detect_churn(base_cells, head_cells)
        res["path"] = rel
        per_notebook.append(res)

    total_churned = sum(len(r["churned"]) for r in per_notebook)

    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        with open(args.json_out, "w", encoding="utf-8") as f:
            json.dump(per_notebook, f, indent=2, ensure_ascii=False)

    # Resume stdout
    print("== Churn d'identifiants de cellules (#22595) ==")
    for r in per_notebook:
        if not r["churned"]:
            continue
        print(f"\n{r['path']} : {len(r['churned'])} cellule(s) re-identifiee(s) "
              f"(+{r['added']} / -{r['removed']} ids)")
        for c in r["churned"]:
            print(f"  {c['base_id']} -> {','.join(c['head_ids'])} "
                  f"[{c['cell_type']}]")
            print(f"      > {c['source_preview']}")
    if total_churned == 0:
        print("Aucun churn : les ids des cellules inchangees sont preserves.")
    else:
        print(f"\n{total_churned} cellule(s) churnee(s) au total.")

    return 1 if total_churned else 0


if __name__ == "__main__":
    sys.exit(main())
