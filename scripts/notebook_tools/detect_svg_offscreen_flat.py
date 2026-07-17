#!/usr/bin/env python3
r"""Detecte les sorties SVG PLATES dont une geometrie de DONNEES est projetee
tres au-dela du viewBox (>15% de sa hauteur) : barre/ligne/point rendu HORS du
cadre visible = figure amputee, alors que le SVG n'est ni vide, ni a dimension
negative, ni a virgule fr-FR. C'est le trou §5b residuel de la render-suite.

Pourquoi cet outil existe
-------------------------
Le rollout SVG inline (#6927) remplace les graphiques Plotly.js-CDN (BLANC en
static rendering) par du SVG inline. La render-suite mecanique verrouille deja
plusieurs classes de casse :
  - `detect_svg_decimal_commas.py`  (#6959) -- virgule decimale fr-FR
  - `detect_svg_empty_display.py`   (#6971) -- output SVG vide (display sans capture)
  - `detect_svg_broken_geometry.py` (#7008) -- element a DIMENSION NEGATIVE
  - `detect_blank_figures.py`       (#6918) -- figure raster degeneree (1x1, ~70 o)

`detect_svg_broken_geometry.py` (#7008) attrape la classe GroupedBar-logY dont
les `<rect>` ont une `height` NEGATIVE (barres invisibles). Mais son docstring
documente explicitement un **angle mort assume** : un element aux DIMENSIONS
POSITIVES mais projete HORS-CHAMP (un `<rect>` de hauteur positive dont le `y`
est tres negatif, ou une barre qui demarre sous le plancher du plot) n'est PAS
flage par le signal dimension-negative. Ce cas nait du meme bug de fond que
#7007 (layout construit en bornes lineaires alors que la projection `YF` mappe
en log10) mais du cote ou l'arithmetique produit un decalage plutot qu'une
hauteur negative. #7008 le deferait au backstop vision-QA periodique. Cet outil
le rend MECANIQUE et CI-enforceable pour la classe ou il est detectable sans
faux-positif : les SVG PLATS.

Ce que l'outil DETECTE (DETERMINISTE, ZERO faux-positif verifie)
----------------------------------------------------------------
Pour chaque bloc `<svg>` d'un output de cellule code AYANT un `viewBox` :

1. **Filtre anti-FP (le point cle)** : si le SVG contient le moindre groupe a
   transform DEPLACANT (`transform="translate(...)"`, `matrix(...)`, `scale(...)`),
   il est **IGNORE** (defere a la vision). Lire des coordonnees brutes sans
   resoudre la pile de transforms produit de VRAIS faux-positifs : les charts
   matplotlib (python3) et plusieurs emetteurs .NET tracent dans des `<g
   transform="translate(...)">`, ou une coordonnee brute negative est on-screen
   apres transform (cf le rejet argumente dans `detect_svg_broken_geometry.py`).
   Le canon `SvgChartHelper.cs` (l'emetteur .NET ou naissent les bugs §5b logY)
   emet un SVG PLAT en coordonnees ABSOLUES -- seul un `rotate(...)` sur les
   labels texte, jamais de translate de geometrie. C'est exactement la classe
   ou le bound-check est sur.

2. Sur un SVG plat, pour chaque geometrie de DONNEES (`<rect>`, `<line>`,
   `<circle>`) : une coordonnee `y` (rect `y` et `y+height`, line `y1`/`y2`,
   circle `cy`) hors de `[viewBox.minY - 0.15*h, viewBox.minY + h + 0.15*h]`.
   La marge de 15% de la hauteur du viewBox est CONSERVATRICE : un chart sain
   trace tout son contenu DANS `[minY, minY+h]` par construction (verifie : 0
   hit sur 944 notebooks), tandis qu'un decalage §5b est GROSSIER (des centaines
   de px, bien au-dela de 15% -- ex. `y=-893` sur un viewBox de 480). Les
   overshoots benins (tick d'axe depassant de quelques px, `<rect>` de fond
   exactement au bord du viewBox) restent DANS la marge -> pas de flag.

`<text>` est exclu : les labels (ticks, titres pivotes) peuvent legitimement
friser les bords et ne portent pas la geometrie de donnees en cause.

Ce qu'il NE corrige PAS
-----------------------
Il DETECTE, il ne CORRIGE PAS. La correction d'un `logY` decale = construire le
`PlotLayout` en espace log10 (grille log-aware tracant lignes ET labels aux
memes positions de decade, geometrie entierement en log -- cf `GridAndYAxisLog`/
`LogTicks`/`PYy` de `Overlay(logY:true)`, #7006), puis **re-executer** le kernel
.NET. Stop&Repair : reparer la cause et re-executer, jamais scrubber la sortie a
la main (regle secrets-hygiene 6).

Usage
-----
    python detect_svg_offscreen_flat.py NB.ipynb                 # un notebook
    python detect_svg_offscreen_flat.py --family Sudoku          # une famille
    python detect_svg_offscreen_flat.py                          # tous les notebooks
    python detect_svg_offscreen_flat.py NB.ipynb --json          # sortie machine
    python detect_svg_offscreen_flat.py NB.ipynb --check         # exit 1 si defauts (CI-ready)

Exit codes
----------
    0 -- aucun defaut (ou mode non --check)
    1 -- un ou plusieurs defauts (--check seulement)
    2 -- erreur (notebook illisible, famille introuvable)

Voir aussi
----------
- `detect_svg_broken_geometry.py` (#7008) -- frere : dimension NEGATIVE
- `.claude/rules/sota-not-workaround.md` -- Prong-A : vrai outil, pas rendu casse
- PR #7007 / EPIC #6927 -- incident fondateur (logY layout lineaire vs YF log10)

Part of #3801 (EPIC SOTA axe-2) + See #6927 (SVG inline rollout).
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

# MIMEs pouvant porter du SVG inline dans un output de cellule.
_SVG_MIMES = ("image/svg+xml", "text/html")

# Blocs <svg ...>...</svg>.
_SVG_BLOCK_RE = re.compile(r"<svg\b.*?</svg>", re.DOTALL)

# viewBox="minX minY width height" (simples ou doubles quotes).
_VIEWBOX_RE = re.compile(
    r'<svg\b[^>]*\bviewBox\s*=\s*(["\'])\s*'
    r"([-\d.]+)\s+([-\d.]+)\s+([-\d.]+)\s+([-\d.]+)\s*\1"
)

# Transform DEPLACANT la geometrie enfant -> defere a la vision (SVG ignore).
# `rotate` est volontairement absent : il pivote (labels texte), ne translate pas
# la geometrie de donnees hors-champ.
_MOVING_TR_RE = re.compile(r'transform\s*=\s*(["\'])\s*(?:translate|matrix|scale)\b')

# Geometrie de donnees.
_RECT_RE = re.compile(
    r'<rect\b[^>]*\by\s*=\s*(["\'])([-\d.]+)\1'
    r'(?:[^>]*?\bheight\s*=\s*(["\'])([-\d.]+)\3)?[^>]*>'
)
_LINE_RE = re.compile(r"<line\b[^>]*>")
_LINE_Y_RE = re.compile(r'\b(y1|y2)\s*=\s*(["\'])([-\d.]+)\2')
_CIRCLE_RE = re.compile(r'<circle\b[^>]*\bcy\s*=\s*(["\'])([-\d.]+)\1')

# Marge de tolerance (fraction de la hauteur du viewBox).
_MARGIN = 0.15


def _extract_svgs(payload: object) -> list[str]:
    if isinstance(payload, list):
        payload = "".join(payload)
    if not isinstance(payload, str):
        return []
    return _SVG_BLOCK_RE.findall(payload)


def _f(x: str) -> float | None:
    try:
        return float(x)
    except (TypeError, ValueError):
        return None


def detect_svg(svg: str) -> dict | None:
    """Return a finding dict if a FLAT svg projects data geometry far off the
    viewBox, else None. SVGs with moving transforms are skipped (None)."""
    m = _VIEWBOX_RE.search(svg)
    if not m:
        return None
    min_y = _f(m.group(3))
    height = _f(m.group(5))
    if min_y is None or height is None or height <= 0:
        return None
    if _MOVING_TR_RE.search(svg):
        return None  # transform-aware hors scope -> defere a la vision
    lo = min_y - _MARGIN * height
    hi = min_y + height + _MARGIN * height
    offenders: list[dict] = []

    for rm in _RECT_RE.finditer(svg):
        y = _f(rm.group(2))
        if y is None:
            continue
        h = _f(rm.group(4)) if rm.group(4) else 0.0
        h = h if h is not None else 0.0
        top, bot = min(y, y + h), max(y, y + h)
        if top < lo or bot > hi:
            offenders.append({"el": "rect", "y": y, "height": h})

    for lm in _LINE_RE.finditer(svg):
        for ym in _LINE_Y_RE.finditer(lm.group(0)):
            y = _f(ym.group(3))
            if y is not None and (y < lo or y > hi):
                offenders.append({"el": "line", "attr": ym.group(1), "y": y})

    for cm in _CIRCLE_RE.finditer(svg):
        y = _f(cm.group(2))
        if y is not None and (y < lo or y > hi):
            offenders.append({"el": "circle", "y": y})

    if not offenders:
        return None
    return {
        "viewBox_min_y": min_y,
        "viewBox_height": height,
        "bounds": [round(lo, 1), round(hi, 1)],
        "offscreen": {"count": len(offenders), "samples": offenders[:5]},
    }


def _cell_outputs(cell: dict) -> list[dict]:
    return cell.get("outputs", []) or []


def detect_cell(cell: dict) -> list[dict]:
    findings = []
    for oi, out in enumerate(_cell_outputs(cell)):
        data = out.get("data", {}) if isinstance(out, dict) else {}
        for mime in _SVG_MIMES:
            if mime not in data:
                continue
            for markup in _extract_svgs(data[mime]):
                finding = detect_svg(markup)
                if finding:
                    findings.append({"output_index": oi, "mime": mime,
                                     "svg_chars": len(markup), **finding})
    return findings


def _kernel(nb: dict) -> str:
    return nb.get("metadata", {}).get("kernelspec", {}).get("name", "?")


def scan_notebook(path: Path) -> dict:
    try:
        with open(path, encoding="utf-8") as f:
            nb = json.load(f)
    except (OSError, json.JSONDecodeError) as exc:
        return {"path": str(path), "error": str(exc), "hits": []}
    hits = []
    for ci, cell in enumerate(nb.get("cells", [])):
        if cell.get("cell_type") != "code":
            continue
        for finding in detect_cell(cell):
            hits.append({"cell_index": ci, **finding})
    return {"path": str(path), "kernel": _kernel(nb), "hits": hits, "error": None}


# Dossiers a ignorer (alignes sur detect_svg_broken_geometry.py:SKIP_DIRS).
SKIP_DIRS = {
    ".lake", ".git", "__pycache__", "_archives", "archive", "_archive",
    ".ipynb_checkpoints", ".pytest_cache", "worktrees",
    "foundry-lib",
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
        f"Notebooks scanned            : {len(results)}",
        f"SVG offscreen (flat, >15%)   : {total_hits}",
        f"Affected notebooks           : {len(affected)}",
        "",
    ]
    if not affected:
        lines.append("No offscreen-flat-SVG defect detected "
                     "(deterministic viewBox-bounds check on flat SVGs, zero-FP).")
        if errored:
            lines.append("")
            lines.append(f"NOTE: {len(errored)} notebook(s) unreadable (see --json for details).")
        return "\n".join(lines)
    for r in affected:
        short = r["path"].split("MyIA.AI.Notebooks")[-1].lstrip("\\/")
        lines.append(f"## {short}  [{r['kernel']}]")
        for h in r["hits"]:
            off = h["offscreen"]
            eg = off["samples"][0]
            lines.append(
                f"  - cell [{h['cell_index']}] output[{h['output_index']}] "
                f"{h['mime']} ({h['svg_chars']} chars): "
                f"viewBox y in [{h['viewBox_min_y']}, "
                f"{h['viewBox_min_y'] + h['viewBox_height']}] "
                f"bounds{h['bounds']} -> offscreen:{off['count']} "
                f"(e.g. {eg})"
            )
        lines.append("")
    lines.append(
        "FIX: build the PlotLayout in the correct space (e.g. log10 for logY: a "
        "single log-aware grid method drawing gridlines AND labels at the same "
        "decade positions, geometry fully in log space -- cf GridAndYAxisLog/"
        "LogTicks/PYy of Overlay(logY:true), #7006), then RE-EXECUTE the .NET "
        "kernel. Stop&Repair: fix cause + re-execute, never scrub the output by "
        "hand (secrets-hygiene rule 6)."
    )
    return "\n".join(lines)


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        description=__doc__.split("\n\n")[0],
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("notebook", nargs="?", help="Notebook to scan (default: all pedagogical)")
    parser.add_argument("--family", help="Top-level family under MyIA.AI.Notebooks/ (e.g. Sudoku)")
    parser.add_argument("--root", default=".", help="Repo root (default: cwd)")
    parser.add_argument("--json", action="store_true", help="Machine-readable JSON output")
    parser.add_argument("--check", action="store_true", help="Exit 1 if any offscreen defect (CI-ready)")
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
