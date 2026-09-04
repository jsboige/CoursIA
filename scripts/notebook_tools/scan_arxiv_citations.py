#!/usr/bin/env python3
"""Scan repo-wide des citations arXiv dans les cellules markdown des notebooks.

Sortie : JSON + rapport console. Le script ne résout PAS les IDs contre l'API arXiv
(criterion de fermeture exige une mesure, pas une vérification complète -- voir #11168).

Usage :
    python scripts/notebook_tools/scan_arxiv_citations.py --exclude "_archives, .ipynb_checkpoints, .lake/packages" \\
        --covered <ids_conus.csv> --out docs/arxiv-rescan.json

Le critère de fermeture exige de comparer aux IDs déjà couverts par les 9 PRs de la passe 1+
passe 2 (cf tableau dans #11168). Le format de `--covered` est un fichier CSV avec un ID
par ligne. Les IDs découverts mais non couverts sont publiés dans le rapport.
"""

import argparse
import json
import re
import sys
from collections import defaultdict
from pathlib import Path

ARXIV_RE = re.compile(r"\barXiv:\s*(\d{4}\.\d{4,5})\b")
# Legacy : arXiv:cs.LG/NNNNNNN ou arXiv:math.AG/NNNNNNN ou arXiv:hep-th/NNNNNNN
# Le préfixe d'archive FAIT partie de l'identifiant legacy : l'API arXiv
# rejette (400) un identifiant ancien réduit à ses 7 chiffres. La capture
# inclut donc le préfixe quand il est présent (#14435, rem. 3).
ARXIV_RE_LEGACY = re.compile(
    r"\barXiv:\s*((?:[a-z\-]+(?:\.[A-Z]{2})?/)?\d{7})\b"
)


def iter_markdown_cells(nb_path: Path):
    """Yield (cell_index, source_text) pour les cellules markdown d'un notebook."""
    try:
        import nbformat
    except ImportError:
        return
    try:
        with nb_path.open("r", encoding="utf-8") as f:
            nb = nbformat.read(f, as_version=4)
    except Exception:
        return
    for idx, cell in enumerate(nb.cells):
        if cell.cell_type != "markdown":
            continue
        src = cell.get("source", "")
        if isinstance(src, list):
            src = "".join(src)
        yield idx, src


def scan_notebook(nb_path: Path):
    """Retourne une liste de (cell_idx, arxiv_id) pour ce notebook."""
    found = []
    for idx, src in iter_markdown_cells(nb_path):
        for m in ARXIV_RE.finditer(src):
            found.append((idx, m.group(1)))
        for m in ARXIV_RE_LEGACY.finditer(src):
            arxiv_id = m.group(1)
            # éviter les faux positifs sur les modernes (7 chiffres != 9)
            digits = arxiv_id.rsplit("/", 1)[-1]
            if len(digits) == 7:
                found.append((idx, arxiv_id))
    return found


def find_notebooks(workspace: Path, excludes: list[str]) -> list[Path]:
    """Liste tous les *.ipynb du workspace, sauf excludes (sous-chaînes)."""
    notebooks = []
    for nb_path in workspace.rglob("*.ipynb"):
        rel = nb_path.relative_to(workspace).as_posix()
        if any(ex in rel for ex in excludes):
            continue
        notebooks.append(nb_path)
    return sorted(notebooks)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--workspace", default="MyIA.AI.Notebooks", help="Racine du scan")
    ap.add_argument(
        "--exclude",
        default="_archives,.ipynb_checkpoints,.lake/packages",
        help="Sous-chaînes exclues (séparées par virgules)",
    )
    ap.add_argument(
        "--covered",
        default=None,
        help="CSV d'IDs déjà couverts (un ID par ligne) -- calcule le delta non couvert",
    )
    ap.add_argument(
        "--out",
        default=None,
        help="Chemin JSON de sortie (rapport structuré)",
    )
    args = ap.parse_args()
    workspace = Path(args.workspace).resolve()
    excludes = [s.strip() for s in args.exclude.split(",") if s.strip()]
    notebooks = find_notebooks(workspace, excludes)
    print(f"[scan] {len(notebooks)} notebooks sous {workspace}")
    # collecte brute : {arxiv_id: [(nb_path, cell_idx)...]} -- le notebook avec le plus d'occurrences
    # détermine si l'ID est largement cité.
    occurrences: dict[str, list[tuple[Path, int]]] = defaultdict(list)
    notebooks_with_ids = 0
    for nb in notebooks:
        recs = scan_notebook(nb)
        if recs:
            notebooks_with_ids += 1
        for cell_idx, arxiv_id in recs:
            occurrences[arxiv_id].append((nb, cell_idx))
    # charge covered
    covered = set()
    if args.covered:
        cov_path = Path(args.covered)
        if cov_path.exists():
            for line in cov_path.read_text(encoding="utf-8").splitlines():
                line = line.strip()
                if line and not line.startswith("#"):
                    covered.add(line)
    # delta
    not_covered = {k: v for k, v in occurrences.items() if k not in covered}
    # résumé
    summary = {
        "scan_workspace": str(workspace),
        "notebooks_scanned": len(notebooks),
        "notebooks_with_arxiv": notebooks_with_ids,
        "unique_arxiv_ids": len(occurrences),
        "covered_count": sum(1 for k in occurrences if k in covered),
        "not_covered_count": len(not_covered),
        "excludes": excludes,
    }
    print("[scan]", json.dumps(summary, indent=2))
    # top 10 IDs par couverture
    top = sorted(occurrences.items(), key=lambda kv: -len(kv[1]))[:20]
    print(f"[scan] Top 20 IDs les plus cités :")
    for aid, occs in top:
        nb_count = len({nb for nb, _ in occs})
        flag = " (delta)" if aid in not_covered else ""
        print(f"  {aid} : {len(occs)} occurrences, {nb_count} notebooks{flag}")
    if not_covered:
        print(f"[scan] {len(not_covered)} IDs non couverts (delta vs covered) :")
        for aid in sorted(not_covered):
            occs = not_covered[aid]
            nbs = sorted({nb.relative_to(workspace).as_posix() for nb, _ in occs})
            print(f"  arXiv:{aid} -> {len(occs)} occ, {len(nbs)} notebooks")
            for np in nbs[:3]:
                print(f"      {np}")
    # JSON output
    if args.out:
        out_path = Path(args.out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        # Structure complète : chaque ID avec liste d'occurrences (notebook, cell_idx)
        out_data = {
            "summary": summary,
            "covered_used_path": str(cov_path) if args.covered else None,
            "occurrences": {
                aid: [
                    {"notebook": str(nb.relative_to(workspace).as_posix()), "cell_idx": idx}
                    for nb, idx in occs
                ]
                for aid, occs in sorted(occurrences.items())
            },
            "delta_not_covered": sorted(not_covered.keys()),
        }
        out_path.write_text(json.dumps(out_data, indent=2, ensure_ascii=False), encoding="utf-8")
        print(f"[scan] -> {out_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
