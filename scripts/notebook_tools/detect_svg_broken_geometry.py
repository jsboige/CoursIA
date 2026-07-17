#!/usr/bin/env python3
r"""Detecte les sorties SVG dont un element a une DIMENSION NEGATIVE : rect/use/
image a `width='-...'` ou `height='-...'` = element invisible (rendu casse).

Pourquoi cet outil existe
-------------------------
Le rollout SVG inline (#6927) remplace les graphiques Plotly.js-CDN (BLANC en
static rendering) par du SVG inline qui rend partout. Les detecteurs freres
`detect_svg_decimal_commas.py` (#6959, virgule fr-FR) et le check no-cdn sont
NECESSAIRES mais PAS SUFFISANTS : un SVG **non vide mais mal projete** passe les
deux (rien a flaguer cote virgule/cdn) tout en etant **visuellement casse**.
C'est exactement le trou par lequel un rendu `logY` bugge a pu etre merge
(#7007) : le `PlotLayout` etait construit en bornes **lineaires** alors que la
fonction de projection `YF` mappait en **log10**. Les valeurs a plus d'une
decade sous le max tombaient **sous le plancher du plot**, produisant des
`<rect>` a `height` NEGATIVE -> barres invisibles. La CI passait au vert
(`out_len>0`, 0 virgule, pas de cdn) pendant que les barres des solveurs rapides
etaient absentes de la figure committee (violation H.1).

Preuve firsthand du trou (Sudoku-18 sur main, GroupedBar logY) :
cell[39] = 15 attributs `height='-893'...'-66'`, cell[55] = 20 attributs
`height='-1017'...` -> rects a hauteur negative = invisibles. Aucun autre
detecteur du rollout ne l'attrape ; ce fichier comble le trou.

Ce que l'outil DETECTE (DETERMINISTE, ZERO faux-positif)
--------------------------------------------------------
Pour chaque bloc `<svg>` d'un output de cellule code : tout attribut
`width='-...'` ou `height='-...'` (valeur negative). Per la spec SVG, une
largeur/hauteur negative est une **erreur** : l'element ne rend pas (rect, use,
image, foreignObject...). AUCUN SVG legitime n'a de dimension negative, et --
contrairement aux coordonnees x/y -- `width`/`height` ne sont **jamais**
deplacees par un `transform` (translate/rotate n'agit que sur la position, pas
sur la taille intrinseque ; seul un `scale` negatif le pourrait, jamais emis par
les generateurs du depot). Donc **zero faux-positif**, quelle que soit la pile de
transforms. Verifie empiriquement sur tout l'arbre : seul Sudoku-18 (le rendu
logY casse) est flage ; les ~60 autres notebooks SVG sains -> 0 hit.

Pourquoi PAS de test "coordonnee hors viewBox"
----------------------------------------------
Evalue puis REJETE : compter les coordonnees `x/y/cx/cy` hors du viewBox parait
seduisant, mais produit de VRAIS faux-positifs. Les charts matplotlib (python3)
et plusieurs emetteurs .NET tracent leur contenu dans des groupes
`<g transform='translate(...)'>` ou via des labels `transform='rotate(-90 ...)'`
: une coordonnee brute **negative** y est **on-screen apres le transform**.
Lire les coords brutes sans resoudre la pile de transforms flague a tort
Infer-5/6/7/8/9, Search-10, etc. Un test transform-aware est hors scope, et le
signal dimension-negative attrape deja la classe GroupedBar-logY de maniere
decisive. L'angle mort residuel -- un element aux dimensions POSITIVES projete
hors-champ (BoxPlot dont les boites partent hors du plot) -- est desormais
couvert MECANIQUEMENT pour les SVG PLATS par le detecteur frere
`detect_svg_offscreen_flat.py` (#7008 suite), qui applique le bound-check
viewBox UNIQUEMENT quand aucun transform deplacant n'est present (le cas ou il
est zero-FP). Reste defere au backstop vision-QA periodique (svg-6927-canon §5)
le seul cas encore non mecanisable : un SVG a transform-groups (matplotlib /
emetteurs .NET a `<g translate>`) dont la geometrie sort apres resolution de la
pile de transforms.

Ce qu'il NE corrige PAS
-----------------------
Il DETECTE, il ne CORRIGE PAS. La correction d'un `logY` casse = construire le
`PlotLayout` en espace log10 (une seule methode de grille log-aware tracant
lignes ET labels aux memes positions de decade, geometrie entierement en log),
comme le fait deja `GridAndYAxisLog`/`LogTicks`/`PYy` de `Overlay(logY:true)`
(#7006). Puis **re-executer** le kernel .NET (Stop&Repair : reparer la cause et
re-executer, jamais scrubber la sortie a la main -- regle secrets-hygiene 6).

Usage
-----
    python detect_svg_broken_geometry.py NB.ipynb                 # un notebook
    python detect_svg_broken_geometry.py --family Sudoku          # une famille
    python detect_svg_broken_geometry.py                          # tous les notebooks
    python detect_svg_broken_geometry.py NB.ipynb --json          # sortie machine
    python detect_svg_broken_geometry.py NB.ipynb --check         # exit 1 si defauts (CI-ready)

Exit codes
----------
    0 -- aucun defaut (ou mode non --check)
    1 -- un ou plusieurs defauts (--check seulement)
    2 -- erreur (notebook illisible, famille introuvable)

Voir aussi
----------
- `detect_svg_decimal_commas.py` (#6959) -- virgule decimale SVG fr-FR
- `detect_svg_empty_display.py` (#6971) -- output SVG vide (display sans capture)
- `detect_svg_offscreen_flat.py` (#7008 suite) -- frere : geometrie hors viewBox (SVG plats)
- `detect_blank_figures.py` (#3801) -- figures PNG degenerees (1x1, 70 o)
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

# Dimension negative sur n'importe quel element (zero-FP : jamais legitime,
# jamais deplacee par un transform). Simples OU doubles quotes ; la
# backreference (\2) referme le meme quote ouvrant.
_NEG_DIM_RE = re.compile(r"\b(width|height)\s*=\s*([\"'])(-[\d.]+)\2")


def _extract_svgs(payload: object) -> list[str]:
    if isinstance(payload, list):
        payload = "".join(payload)
    if not isinstance(payload, str):
        return []
    return _SVG_BLOCK_RE.findall(payload)


def _negative_dims(svg: str) -> list[dict]:
    """Elements with a negative width/height (invalid SVG, invisible)."""
    return [{"attr": m.group(1), "value": m.group(3)} for m in _NEG_DIM_RE.finditer(svg)]


def detect_svg(svg: str) -> dict | None:
    """Return a finding dict if the SVG has a negative-dimension element, else None."""
    neg = _negative_dims(svg)
    if not neg:
        return None
    return {"negative_dims": {"count": len(neg), "samples": neg[:5]}}


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


# Dossiers a ignorer (alignes sur detect_svg_decimal_commas.py:SKIP_DIRS).
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
        f"Notebooks scanned         : {len(results)}",
        f"SVG negative-dim defects  : {total_hits}",
        f"Affected notebooks        : {len(affected)}",
        "",
    ]
    if not affected:
        lines.append("No SVG negative-dimension defects detected "
                     "(deterministic width/height<0 check, zero-FP).")
        if errored:
            lines.append("")
            lines.append(f"NOTE: {len(errored)} notebook(s) unreadable (see --json for details).")
        return "\n".join(lines)
    for r in affected:
        short = r["path"].split("MyIA.AI.Notebooks")[-1].lstrip("\\/")
        lines.append(f"## {short}  [{r['kernel']}]")
        for h in r["hits"]:
            nd = h["negative_dims"]
            eg = nd["samples"][0]
            lines.append(f"  - cell [{h['cell_index']}] output[{h['output_index']}] "
                         f"{h['mime']} ({h['svg_chars']} chars): "
                         f"negative-dims:{nd['count']} (e.g. {eg['attr']}={eg['value']})")
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
    parser.add_argument("--check", action="store_true", help="Exit 1 if any negative-dim defect (CI-ready)")
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
