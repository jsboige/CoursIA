"""Detecte un denominateur de serie dans l'en-tete d'un carnet (#23678).

Le champ d'en-tete `**Notebook** : 6f/13` porte, apres le numero du carnet, le
**nombre de carnets de la serie**. C'est un compte **derive** : il est perime par
construction des qu'un carnet est ajoute a la racine de la serie, et aucun organe
ne le verifiait. Mesure du 2026-10-31 sur la serie RL : **18 carnets** le
declarent, **tous faux** (16 a `/26` alors que la racine en compte 27 depuis
l'accretion de `RL-06f` le 30/10, 2 a `/13`), et 9 des 27 carnets racine ne le
portent pas du tout -- la forme est minoritaire et non tenue.

La source de verite de l'effectif est le **catalogue genere**
(`COURSE_CATALOG.generated.json`, champs `serie` / `sous_serie`), pas un nombre
recopie dans chaque en-tete. Le repere canonique d'un carnet est son nom de
fichier (prefixe + numero, la lettre signifiant « approfondit ») : le numero seul
suffit a situer le carnet dans le parcours, le denominateur n'ajoute rien et
vieillit mal.

Deux formes coexistent dans les carnets et sont toutes deux detectees :

    **Notebook** : 6f/13      (le gras ferme avant le deux-points)
    **Notebook : 10/26**      (le gras couvre tout le champ)

Usage :

    python scripts/notebook_tools/check_series_denominator.py <chemin>... [--json]

`<chemin>` peut etre un carnet ou un dossier (parcours recursif des `*.ipynb`).
Sortie 0 : aucun denominateur. Sortie 1 : au moins un. Sortie 2 : argument
manquant ou chemin introuvable (un chemin muet ne doit jamais passer pour un
vert).

Portee assumee : l'organe detecte la FORME, pas la justesse du compte -- il
rougit sur un denominateur **correct** aussi, parce que le defaut est de le
declarer, pas de se tromper d'unite. C'est ce qui le rend vrai demain.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

DENOMINATOR_RE = re.compile(r"\*\*Notebook(?:\*\*)?\s*:\s*\d+[a-z]?\s*/\s*\d+(?:\*\*)?")


def iter_notebooks(paths):
    """Rend les chemins de carnets : un fichier est rendu tel quel, un dossier est parcouru."""
    for raw in paths:
        path = Path(raw)
        if path.is_dir():
            yield from sorted(path.rglob("*.ipynb"))
        else:
            yield path


def scan_notebook(path):
    """Rend [(index_cellule, extrait)] des denominateurs trouves dans les cellules markdown."""
    findings = []
    try:
        with open(path, encoding="utf-8") as handle:
            notebook = json.load(handle)
    except (OSError, json.JSONDecodeError) as exc:
        return findings, "illisible (%s)" % exc.__class__.__name__
    for index, cell in enumerate(notebook.get("cells", [])):
        if cell.get("cell_type") != "markdown":
            continue
        source = "".join(cell.get("source", []))
        for match in DENOMINATOR_RE.finditer(source):
            findings.append((index, match.group(0)))
    return findings, None


def collect(paths):
    """Rend la liste des constats, chemin par chemin."""
    report = []
    for notebook in iter_notebooks(paths):
        findings, error = scan_notebook(notebook)
        if error:
            report.append({"path": str(notebook), "cell": None, "match": None, "error": error})
            continue
        for cell, match in findings:
            report.append({"path": str(notebook), "cell": cell, "match": match, "error": None})
    return report


def main(argv=None):
    parser = argparse.ArgumentParser(description="Detecte un denominateur de serie dans les en-tetes.")
    parser.add_argument("paths", nargs="*", help="carnet(s) ou dossier(s) a inspecter")
    parser.add_argument("--json", action="store_true", help="sortie machine")
    args = parser.parse_args(argv)

    if not args.paths:
        print("chemin requis : aucun perimetre inspecte n'est pas un vert", file=sys.stderr)
        return 2
    missing = [raw for raw in args.paths if not Path(raw).exists()]
    if missing:
        print("chemin introuvable : %s" % ", ".join(missing), file=sys.stderr)
        return 2

    report = collect(args.paths)
    if args.json:
        print(json.dumps({"findings": report, "count": len(report)}, ensure_ascii=False, indent=2))
    else:
        for item in report:
            if item["error"]:
                print("%s: %s" % (item["path"], item["error"]))
            else:
                print("%s: cellule %d -- %s" % (item["path"], item["cell"], item["match"]))
        print("%d denominateur(s) de serie declare(s)" % len(report))
    return 1 if report else 0


if __name__ == "__main__":
    sys.exit(main())
