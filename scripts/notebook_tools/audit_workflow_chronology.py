#!/usr/bin/env python3
"""Detecte la chronologie de livraison Git dans la prose des carnets (audit de stock).

Issue #14442 (défaut 3) : certaines introductions et conclusions de carnets
justifient leur contenu par la **chronologie de livraison** — renvois à un EPIC,
à une PR/issue, ou au fait qu'un morceau a été « livré » — au lieu de le
justifier **pédagogiquement**. Ce récit de livraison vit dans git, les PR et les
issues, pas dans le carnet que lit l'apprenant.

Ce script est un **audit de stock** (pas un ratchet de diff) : il parcourt les
cellules markdown d'un carnet ou d'une série et signale chaque **marqueur de
chronologie de livraison** présent, avec l'index de la cellule et le texte qui
a matché. Il ne **classe** pas : l'issue impose que chaque occurrence soit
**relue dans son contexte** (un « GT-3b » nu est un pointeur pédagogique vers
un carnet voisin et reste ; un « GT-3b (#12213) » est une référence de
livraison). La classification (PEDAGOGIQUE / PROVENANCE_UTILE /
CHRONOLOGIE_GIT_A_RETIRER) est donc produite par la lecture humaine, consignée
dans le ledger d'accompagnement ; l'organe rend seulement le candidat précis.

Différenciation avec ``check_activity_leak.py`` : celui-ci est un **ratchet sur
les passages AJOUTÉS** d'une PR (densité de récit de cycle) ; ici c'est un
**inventaire des marqueurs PRÉSENTS** dans le stock, pour un balayage ponctuel.
Les deux sont complémentaires.

Marqueurs (taxonomie #14442, focale sur la livraison) :

- ``EPIC #N`` / ``Epic #N``   — renvoi à un EPIC.
- ``PR #N``                   — renvoi à une pull request.
- ``Issue #N``                — renvoi à une issue.
- ``(#NNNN)`` (4-5 chiffres)  — numéro de PR/issue en parenthèse, la forme
  canonique du renvoi de livraison (« GT-3b (#12213) »).
- ``livré / livrée / livrée(s)`` accolé à un numéro ou à ``sur main`` —
  past-participe de livraison.

Faux positifs évités : un pointeur de carnet **sans** numéro (« voir GT-3b »,
« les murs de GT-3b ») ne matche pas ; « promesse livrée à Colonne » (prose
française courante) ne matche pas (pas de numéro accolé). Un carnet qui
**enseigne** git peut citer une issue en exemple : un tel passage se classe
PEDAGOGIQUE à la lecture, il n'est pas supprimé.

Usage :
    python scripts/notebook_tools/audit_workflow_chronology.py <chemin> [--json]

``<chemin>`` est un carnet ``.ipynb`` ou un répertoire (parcours récursif).
Sortie : un rapport par carnet portant ≥ 1 marqueur. Code de sortie : 0 = aucun
marqueur, 1 = marqueur(s) trouvé(s), 2 = erreur (chemin absent, JSON invalide).
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys

# Marqueurs de chronologie de livraison. Le premier groupe (renvois EPIC/PR/
# issue + numéro en parenthèse) est la signature : un carnet pédagogique ne
# cite pas de numéros de PR/issue. Le second groupe (past-participe « livré »)
# n'est retenu que s'il est accolé à un numéro ou à « sur main ».
MARKERS = [
    ("epic", re.compile(r"\bEPIC\s+#\d+", re.IGNORECASE)),
    ("pr", re.compile(r"\bPR\s+#\d+")),
    ("issue", re.compile(r"\bIssue\s+#\d+", re.IGNORECASE)),
    ("pr_paren", re.compile(r"\(#\d{4,5}\)")),
    ("livre", re.compile(r"\blivr\w*\s+(?:#?\d|\bsur\s+main\b)", re.IGNORECASE)),
]

SKIP_DIRS = {"_archive", "archive", ".ipynb_checkpoints", "node_modules"}


def iter_notebooks(path: str):
    """Yield les chemins de carnets .ipynb sous ``path`` (fichier ou répertoire)."""
    if os.path.isfile(path):
        if path.endswith(".ipynb"):
            yield path
        return
    for dirpath, dirnames, filenames in os.walk(path):
        dirnames[:] = [d for d in dirnames if d not in SKIP_DIRS]
        for f in filenames:
            if f.endswith(".ipynb") and not f.endswith("_output.ipynb"):
                yield os.path.join(dirpath, f)


def scan_notebook(path: str):
    """Retourne la liste des (index_cellule, marqueur, texte_matche) d'un carnet."""
    with open(path, encoding="utf-8") as fh:
        nb = json.load(fh)
    hits = []
    for idx, cell in enumerate(nb.get("cells", [])):
        if cell.get("cell_type") != "markdown":
            continue
        text = "".join(cell.get("source", []))
        for name, rx in MARKERS:
            for m in rx.finditer(text):
                start = max(0, m.start() - 24)
                end = min(len(text), m.end() + 24)
                snippet = text[start:end].replace("\n", " ").strip()
                hits.append((idx, name, snippet))
    return hits


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("path", help="carnet .ipynb ou répertoire")
    ap.add_argument("--json", action="store_true", help="sortie JSON")
    args = ap.parse_args(argv)

    if not os.path.exists(args.path):
        print("chemin absent : %s" % args.path, file=sys.stderr)
        return 2

    results = []
    for nbpath in iter_notebooks(args.path):
        rel = nbpath.replace("\\", "/")
        try:
            hits = scan_notebook(nbpath)
        except (json.JSONDecodeError, OSError) as exc:
            print("lecture impossible %s : %s" % (rel, exc), file=sys.stderr)
            return 2
        if hits:
            results.append({"path": rel, "n_hits": len(hits), "hits": hits})

    results.sort(key=lambda r: (r["path"]))

    if args.json:
        print(json.dumps({"n_notebooks_flagged": len(results), "notebooks": results},
                         ensure_ascii=False, indent=1))
    else:
        if not results:
            print("aucun marqueur de chronologie de livraison")
        for r in results:
            print("%s  (%d marqueur%s)" % (r["path"], r["n_hits"], "s" if r["n_hits"] > 1 else ""))
            for idx, name, snippet in r["hits"]:
                print("   cellule %2d  [%s]  …%s…" % (idx, name, snippet))
    return 1 if results else 0


if __name__ == "__main__":
    sys.exit(main())
