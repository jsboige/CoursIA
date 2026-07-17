#!/usr/bin/env python3
r"""Detecte les cellules .NET qui `display()` un chart SVG mais produisent un output VIDE (figure BLANCHE sur GitHub/nbviewer).

Pourquoi cet outil existe
-------------------------
Le rollout SVG inline (#6927) remplace les graphiques Plotly.js-CDN par du SVG
inline `text/html` qui rend partout. Le canon (ai-01, `svg-6927-canon.md`) pose
deux regles mecaniques pour qu'un notebook converti rende REELLEMENT :

  1. Le SVG doit etre la **derniere expression de cellule** (`execute_result`),
     PAS `display(chart)` -> sous .NET Interactive headless, `display(chartObj)`
     produit frequemment un **output vide** (`outputs: []`) alors meme que la
     cellule s'execute sans erreur (`execution_count` set).
  2. no-cdn + no-comma sont **necessaires PAS suffisantes** : un output vide
     passe les deux detecteurs (`detect_svg_decimal_commas.py` #6959 n'a aucun
     SVG a verifier ; `detect_blank_figures.py` #6918 cible les PNG degenerees,
     pas les outputs text/html manquants). Resultat : **figure BLANCHE sur
     GitHub** alors que CI est verte, code execute, valeurs correctes ->
     invisible a la review de code et a la validation structurelle. Incident
     fondateur : PR #6963 (DecInfer-6, po-2023) -- 4 cellules
     `display(SvgChartHelper.Bar(...))` avec exec_count set mais `outputs: []`,
     0 SVG dans tout le notebook ; base main avait 5 outputs Plotly-CDN, head a
     0 chart = regression nette (Plotly-blanc -> rien du tout).

Portee cluster : tous les workers po-* convergent les notebooks Plotly-CDN vers
SvgChartHelper.cs (#6942) ou des builders inline. Une conversion qui utilise
`display(chart)` au lieu d'une derniere expression peut silencieusement produire
un output vide -> l'objectif explicite de la PR « render on GitHub/nbviewer »
est non atteint. Les 21 PRs soeurs du rollout #6927 sont a risque.

Ce que l'outil DETECTE (DETERMINISTE, zero faux-positif)
-------------------------------------------------------
Pour chaque cellule **code** d'un notebook, flagge si les 3 conditions sont
vraies SIMULTANEMENT :

  1. **`execution_count` est non-null** -- la cellule a reellement execute
     (exclut les cellules non-run, `outputs: []` legitime).
  2. **`outputs == []`** (vide, **pas** de sortie stream/error/display) -- la
     cellule a produit STRICTEMENT rien. Une cellule en erreur aurait un output
     `error` (probleme different, attrape par H.1) ; une cellule qui print a un
     output `stream`. Ici on cible le cas precis ou l'execution reussit
     (`execution_count` set) mais n'emet AUCUN output.
  3. **La source contient un pattern de DISPLAY de chart** -- la cellule a
     l'intention declaree de produire un graphique :
       - `display(SvgChartHelper.`  (canon helper #6942)
       - `display(HTML(`            (wrapper HTML inline, ex GT-3 #6961)
       - `ScatterSvg` / `PlotSvg` / `BuildScatterSvg` (builders inline,
         ex Infer-17 #6946, MGS-15 #6960)

     La combinaison (display-intention + execution reussie + zero output) est la
     **signature exacte** du blanc-sur-GitHub. **Zero faux-positif** : aucune
     cellule legitime n'ecrit `display(SvgChartHelper.Bar(...))` (ou un builder
     SVG) en attendant un output vide -- une cellule qui construit un chart
     sans l'afficher ne contient pas ces patterns de display.

Ce qu'il NE corrige PAS
-----------------------
Il DETECTE, il ne CORRIGE PAS. La correction = faire du chart la **derniere
expression** de la cellule (retirer le `display(...)` et laisser l'objet chart
comme valeur de finalisation -> `execute_result` porte le SVG), OU investiguer
pourquoi le helper n'emet pas sous l'exec headless, puis **re-executer** le
kernel .NET -> l'output committee porte le `<svg>`. Stop&Repair : on repare la
cause et on re-execute, jamais scrubber la sortie a la main (regle
secrets-hygiene 6).

Known blind spots (hors scope par design)
-----------------------------------------
- **Cellule qui `display()` un chart et emet un output SANS svg** (ex un
  stream-only ou un display_data d'un autre type) : non couvert ici (rare ;
  l'echec canonique de #6927 est l'output totalement vide). Le cas "output
  present mais sans svg" est un defeau de logique applicative, pas un blanc
  de display.
- **Notebooks non-.NET** : les patterns (`SvgChartHelper`, `display(HTML(`,
  `ScatterSvg`) sont specifiques au rollout .NET/C# de #6927. Un notebook
  Python matplotlib n'utilise pas ces constructs (ses charts sont des PNG en
  `image/png`, couverts par `detect_blank_figures.py` #6918).
- **Detection base-vs-head** : cet outil scanne un notebook tel-committe (pas
  un diff). Une PR qui SUPPRIME intentionnellement une cellule chart n'est pas
  flaggee (la cellule n'existe plus). Le cas #6963 est detecte car les cellules
  existent toujours (videes de leur output, pas supprimees).

Usage
-----
    python detect_svg_empty_display.py NB.ipynb                 # un notebook
    python detect_svg_empty_display.py --family Probas          # une famille
    python detect_svg_empty_display.py                          # tous les notebooks
    python detect_svg_empty_display.py NB.ipynb --json          # sortie machine
    python detect_svg_empty_display.py NB.ipynb --check         # exit 1 si defauts (CI-ready)

Exit codes
----------
    0 -- aucun defaut (ou mode non --check)
    1 -- un ou plusieurs defauts (--check seulement)
    2 -- erreur (notebook illisible, famille introuvable)

Voir aussi
----------
- `detect_svg_decimal_commas.py` (#6959) -- l'AUTRE defeau de rendu SVG (virgule
  decimale fr-FR -> zigzag). Les deux detecteurs sont complementaires : celui-ci
  attrape le "chart absent", #6959 attrape le "chart present mais casse".
- `detect_blank_figures.py` (#3801/#6918) -- figures PNG degenerees (1x1, 70 o).
- `.github/workflows/svg-decimal-comma-gate.yml` (#6965) -- gate CI per-PR pour
  #6959 ; cet outil est destine a une gate soeur.
- ai-01 canon `svg-6927-canon.md` (points 1 et 2) -- la regle que cet outil
  encode mecaniquement.

Part of #3801 (EPIC SOTA axe-2) + See #6927 (SVG inline rollout).
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

# Pattern de DISPLAY de chart : la cellule a l'intention declaree de produire
# un graphique SVG inline (canon helper #6942, wrapper HTML inline, ou builders
# ScatterSvg/PlotSvg/BuildScatterSvg utilises par Infer-17/MGS-15). Zero-FP :
# aucun code legitime n'ecrit ces constructs sans en attendre un output.
_CHART_DISPLAY_RE = re.compile(
    r"display\s*\(\s*SvgChartHelper\."  # canon: display(SvgChartHelper.Bar(...))
    r"|display\s*\(\s*HTML\s*\("         # wrapper HTML inline (display(HTML(...)))
    r"|ScatterSvg"                        # builder inline (Infer-17 #6946)
    r"|PlotSvg"                           # builder inline (GT-3 #6961)
    r"|BuildScatterSvg",                  # builder inline (MGS-15 #6960)
    re.IGNORECASE,
)

# Un bloc <svg ...> dans un output (preuve qu'un chart a bien ete emis).
_SVG_RE = re.compile(r"<svg\b", re.IGNORECASE)


def _cell_source(cell: dict) -> str:
    src = cell.get("source", "")
    if isinstance(src, list):
        return "".join(src)
    return str(src)


def _output_has_svg(outputs: list) -> bool:
    """True si un des outputs porte un <svg> dans text/html ou image/svg+xml."""
    for out in outputs:
        if not isinstance(out, dict):
            continue
        data = out.get("data", {})
        if not isinstance(data, dict):
            continue
        for payload in data.values():
            txt = "".join(payload) if isinstance(payload, list) else str(payload)
            if _SVG_RE.search(txt):
                return True
    return False


def detect_cell(cell: dict) -> bool:
    """True si la cellule code porte le signature blanc-sur-GitHub.

    3 conditions co-necessaires (zero-FP) :
      1. execution_count non-null (cellule rellement executee)
      2. outputs == [] (strictement vide -- pas d'erreur, pas de stream)
      3. source contient un pattern display(chart) (intention declaree)
    """
    if cell.get("cell_type") != "code":
        return False
    if cell.get("execution_count") is None:  # pas executee -> outputs=[] legit
        return False
    outputs = cell.get("outputs", [])
    if outputs:  # a un output (erreur/stream/display) -> pas le blanc cible
        return False
    if _output_has_svg(outputs):  # defensive (vide -> toujours False)
        return False
    return bool(_CHART_DISPLAY_RE.search(_cell_source(cell)))


def detect_cell_detail(cell: dict) -> dict | None:
    """Return a detail dict if the cell is flagged, else None (for reporting)."""
    if not detect_cell(cell):
        return None
    return {
        "exec_count": cell.get("execution_count"),
        "source_excerpt": _cell_source(cell)[:120].replace("\n", " "),
        "matched_pattern": _matched_pattern(_cell_source(cell)),
    }


def _matched_pattern(src: str) -> str:
    """Human-readable name of the first chart-display pattern matched."""
    s = src
    if re.search(r"display\s*\(\s*SvgChartHelper\.", s, re.IGNORECASE):
        return "display(SvgChartHelper.<chart>)"
    if re.search(r"display\s*\(\s*HTML\s*\(", s, re.IGNORECASE):
        return "display(HTML(<svg>))"
    if re.search(r"ScatterSvg", s, re.IGNORECASE):
        return "ScatterSvg builder"
    if re.search(r"PlotSvg", s, re.IGNORECASE):
        return "PlotSvg builder"
    if re.search(r"BuildScatterSvg", s, re.IGNORECASE):
        return "BuildScatterSvg builder"
    return "chart-display"


def scan_notebook(path: Path) -> dict:
    """Return a result dict for one notebook: path, kernel, hits[], error."""
    try:
        with open(path, encoding="utf-8") as f:
            nb = json.load(f)
    except (OSError, json.JSONDecodeError) as exc:
        return {"path": str(path), "error": str(exc), "hits": []}
    hits = []
    for ci, cell in enumerate(nb.get("cells", [])):
        detail = detect_cell_detail(cell)
        if detail:
            hits.append({"cell_index": ci, **detail})
    kernel = nb.get("metadata", {}).get("kernelspec", {}).get("name", "?")
    return {"path": str(path), "kernel": kernel, "hits": hits, "error": None}


# Dossiers a ignorer (alignes sur detect_svg_decimal_commas.py / detect_blank_figures.py).
SKIP_DIRS = {
    ".lake", ".git", "__pycache__", "_archives", "archive", "_archive",
    ".ipynb_checkpoints", ".pytest_cache", "worktrees",
    "foundry-lib",  # lib vendored tierce, pas a nous a fixer
}
_OUTPUT_SUFFIX = "_output.ipynb"


def _should_skip(rel: Path) -> bool:
    if any(part in SKIP_DIRS for part in rel.parts):
        return True
    return rel.name.endswith(_OUTPUT_SUFFIX)


def _iter_notebooks(root: Path, family: str | None):
    base = root / "MyIA.AI.Notebooks"
    if family:
        base = base / family
    if not base.exists():
        return
    for nb in sorted(base.rglob("*.ipynb")):
        if _should_skip(nb.relative_to(base)):
            continue
        yield nb


def _human_report(results: list[dict]) -> str:
    total_hits = sum(len(r["hits"]) for r in results)
    affected = [r for r in results if r["hits"]]
    errored = [r for r in results if r.get("error")]
    lines = [
        f"Notebooks scanned    : {len(results)}",
        f"Empty-display defects : {total_hits}",
        f"Affected notebooks   : {len(affected)}",
        "",
    ]
    if not affected:
        lines.append(
            "No empty-display defects detected (display(chart) cell with empty output)."
        )
        if errored:
            lines.append("")
            lines.append(f"NOTE: {len(errored)} notebook(s) unreadable (see --json for details).")
        return "\n".join(lines)
    for r in affected:
        short = r["path"].split("MyIA.AI.Notebooks")[-1].lstrip("\\/")
        lines.append(f"## {short}  [{r['kernel']}]")
        for h in r["hits"]:
            lines.append(
                f"  - cell [{h['cell_index']}] exec_count={h['exec_count']} "
                f"outputs=[] {h['matched_pattern']} : {h['source_excerpt']!r}"
            )
        lines.append("")
    lines.append(
        "FIX: make the chart the LAST EXPRESSION of the cell (drop `display(chart)` -> "
        "leave the chart object as the cell's final value -> `execute_result` carries "
        "the <svg>), then re-execute the .NET kernel -- the committed output then carries "
        "the SVG. See ai-01 canon `svg-6927-canon.md` (point 1). "
        "Stop&Repair: fix cause + re-execute, never scrub the output by hand "
        "(secrets-hygiene rule 6)."
    )
    return "\n".join(lines)


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        description=__doc__.split("\n\n")[0],
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("notebook", nargs="?", help="Notebook to scan (default: all pedagogical)")
    parser.add_argument("--family", help="Top-level family under MyIA.AI.Notebooks/ (e.g. Probas)")
    parser.add_argument("--root", default=".", help="Repo root (default: cwd)")
    parser.add_argument("--json", action="store_true", help="Machine-readable JSON output")
    parser.add_argument("--check", action="store_true", help="Exit 1 if any empty-display defect (CI-ready)")
    args = parser.parse_args(argv)

    root = Path(args.root).resolve()
    if args.notebook:
        paths = [Path(args.notebook)]
        if not paths[0].is_absolute():
            paths[0] = root / paths[0]
        if not paths[0].exists():
            print(f"error: notebook not found: {paths[0]}", file=sys.stderr)
            return 2
    else:
        paths = list(_iter_notebooks(root, args.family))
        if args.family and not paths:
            print(f"error: family not found: {args.family}", file=sys.stderr)
            return 2

    results = [scan_notebook(p) for p in paths]
    total_hits = sum(len(r["hits"]) for r in results)

    if args.json:
        payload = {"notebooks_scanned": len(results), "total_hits": total_hits, "results": results}
        print(json.dumps(payload, ensure_ascii=False, indent=2))
    else:
        print(_human_report(results))

    if args.check and total_hits > 0:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
