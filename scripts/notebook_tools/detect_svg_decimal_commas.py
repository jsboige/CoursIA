#!/usr/bin/env python3
r"""Detecte les sorties SVG dont les coordonnees utilisent des virgules decimales (rendu casse sur Chromium/GitHub/nbviewer).

Pourquoi cet outil existe
-------------------------
Le rollout SVG inline (#6927) remplace les graphiques Plotly.js-CDN (`<script>`
externe -> BLANC en static rendering) par du SVG inline `image/svg+xml`/`text/html`
qui rend partout. Une cellule C# qui formate ses coordonnees avec `:F1` / `:F2`
ou `double.ToString()` par defaut emet un **separateur decimal sensible a la
culture** : sur une machine fr-FR, `334.4` devient `334,4`. Or, per la spec SVG,
**la virgule ET l'espace sont tous deux des separateurs de coordonnees**. Chromium
(= le moteur de GitHub/nbviewer) parse donc `points="70,0,334,4 ..."` comme
**4 nombres = 2 points** (70,0)(334,4), pas 1 point (70.0, 334.4). Le chart rend
en **zigzag chaotique** ; les attributs mono-coordonnee (`cx="70,0"`) tombent en
erreur console `Expected length` et **default a 0**. Le but explicite de la PR
"render on GitHub/nbviewer" est alors **non atteint**, alors meme que le XML est
bien forme, le code s'execute et les valeurs MSE sont correctes -> invisible a la
review de code et a la validation structurelle. Incident fondateur : PR #6946
(Infer-17 Kalman, po-2023, machine fr-FR) -- 1485 occurrences de virgule decimale
dans le SVG cell[8] committe, chart rendu en zigzag sur Chromium (prouve firsthand
DOM c.581 : 22 points attendus parses en 44). Le helper canon `SvgChartHelper.cs`
(#6942, #6954) utilise InvariantCulture (points) et rend correctement (0 virgule).

Portee cluster : tous les workers po-* tournent en culture fr-FR -> toute cellule
.NET qui emet du SVG inline avec `:F1`/`:F2`/`ToString()` par defaut produit des
virgules -> rendu casse sur GitHub. Les 21 PRs soeurs du rollout #6927 sont a
risque tant qu'elles n'utilisent pas le helper canon ou InvariantCulture.

Ce que l'outil DETECTE (DETERMINISTE, zero faux-positif)
-------------------------------------------------------
Pour chaque sortie `image/svg+xml` ou SVG inline dans `text/html` d'une cellule
code, il extrait les blocs `<svg>...</svg>` et verifie :

  1. **Attribut `points`** (`<polyline>` / `<polygon>`) : chaque token separe par
     un espace est une paire (x,y). Une paire valide a **exactement 1 virgule**
     (2 parts : "70,334" ou "70.0,334.4"). Un token avec **>2 parts** separees
     par virgule (ex "70,0,334,4" -> 4 parts) est le signature exact de la
     virgule-decimale. Un token integer valide ("70,334") -> 2 parts -> NON flage.
     **Zero faux positif** sur les coordonnees entieres legitimes.
  2. **Attributs mono-coordonnee** (`cx cy x y x1 y1 x2 y2 r rx ry width height
     fx fy`) : une valeur contenant `\d,\d` est invalide (une coordonnee seule ne
     peut pas contenir de virgule) -> flag. Une valeur a point ("70.0") ou entiere
     ("70") -> OK. Les attributs couleur (`fill stroke` rgba()/rgb()) et
     `transform` (translate/rotate avec virgules legitimes) sont EXCLUS du
     whitelist -> pas de faux positif sur le CSS embarque.

Ce qu'il NE corrige PAS
-----------------------
Il DETECTE, il ne CORRIGE PAS. La correction = forcer la culture invariante dans
la cellule source (`xp.ToString("F1", CultureInfo.InvariantCulture)` ou
`FormattableString.Invariant(...)`, ou `CultureInfo.DefaultThreadCurrentCulture =
InvariantCulture` en tete de cellule) puis **re-executer** sur le kernel .NET ->
la sortie committee porte des points. Stop&Repair : on repare la cause et on
re-execute, jamais scrubber la sortie a la main (regle secrets-hygiene 6).

Known blind spots (hors scope par design)
-----------------------------------------
- **Attribut `d` des `<path>`** : les path-data utilisent la virgule comme
  separateur optionnel ET potentiellement comme decimal -- ambiguité. Hors scope :
  l'outil cible polyline/polygon + attributs mono-coord (le cas #6946 exact).
- **SVG sans coordonnees** : un SVG purement decoratif (logo, icone) sans
  `points` ni attr mono-coord n'est pas flage (rien a casser).
- **SVG dans markdown (pas code output)** : on ne scanne que les OUTPUTS de
  cellules code (la source C# est le livrable ; les artefacts papermill
  `*_output.ipynb` sont exclus au profit de la source canonique).

Usage
-----
    python detect_svg_decimal_commas.py NB.ipynb                 # un notebook
    python detect_svg_decimal_commas.py --family Probas          # une famille
    python detect_svg_decimal_commas.py                          # tous les notebooks
    python detect_svg_decimal_commas.py NB.ipynb --json          # sortie machine
    python detect_svg_decimal_commas.py NB.ipynb --check         # exit 1 si defauts (CI-ready)

Exit codes
----------
    0 -- aucun defaut (ou mode non --check)
    1 -- un ou plusieurs defauts (--check seulement)
    2 -- erreur (notebook illisible, famille introuvable)

Voir aussi
----------
- `detect_blank_figures.py` (#3801) -- figures PNG degenerees (1x1, 70 o)
- `detect_ascii_workaround.py` (#3801) -- charts ASCII en lieu de viz
- `.claude/rules/sota-not-workaround.md` -- Prong-A : vrai outil, pas workaround
- PR #6946 / EPIC #6927 -- incident fondateur (decimal-comma SVG fr-FR)

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

# Regex pour extraire les blocs <svg ...>...</svg> (greedy sur le plus grand,
# un output = typiquement un seul <svg> racine).
_SVG_BLOCK_RE = re.compile(r"<svg\b.*?</svg>", re.DOTALL)

# Attribut points (polyline/polygon).
_POINTS_RE = re.compile(r"<(?:polyline|polygon)\b[^>]*\bpoints\s*=\s*\"([^\"]*)\"", re.IGNORECASE)

# Attributs mono-coordonnee dont une virgule est toujours un defaut.
_COORD_ATTRS = ("cx", "cy", "x", "y", "x1", "y1", "x2", "y2", "r", "rx", "ry",
                "width", "height", "fx", "fy")
_COORD_ATTR_RE = {
    a: re.compile(rf"\b{a}\s*=\s*\"([^\"]*)\"")
    for a in _COORD_ATTRS
}
# Signature d'une virgule decimale dans une valeur mono-coord : digit,virgule,digit.
_DECIMAL_COMMA_RE = re.compile(r"\d,\d")


def _extract_svgs(payload: object) -> list[str]:
    """Return the list of <svg>...</svg> markup strings found in a notebook
    output payload (str or list[str])."""
    if isinstance(payload, list):
        payload = "".join(payload)
    if not isinstance(payload, str):
        return []
    return _SVG_BLOCK_RE.findall(payload)


def _points_tokens_with_bug(points_value: str) -> list[str]:
    """Return the whitespace-tokens of a `points` attribute that carry a
    decimal-comma (tokens with >2 comma-separated parts). A valid (x,y) pair
    has exactly 2 parts; >2 parts is the decimal-comma signature (zero FP)."""
    buggy = []
    for token in points_value.split():
        # skip empty
        if not token:
            continue
        parts = token.split(",")
        # 2 parts = paire valide (entiere "70,334" ou decimale "70.0,334.4").
        # >2 parts = virgule-decimale (ex "70,0,334,4" -> 4 parts).
        if len(parts) > 2:
            buggy.append(token)
    return buggy


def _coord_attr_commas(svg: str) -> list[dict]:
    """Return [{attr, value}] for mono-coord attributes whose value contains a
    decimal comma (invalid SVG -- a single coord cannot hold a comma)."""
    findings = []
    for attr, rx in _COORD_ATTR_RE.items():
        for m in rx.finditer(svg):
            value = m.group(1)
            if _DECIMAL_COMMA_RE.search(value):
                findings.append({"attr": attr, "value": value})
    return findings


def detect_svg(svg: str) -> dict | None:
    """Return a finding dict if the SVG block has decimal-comma defects, else None."""
    # 1. points attribute (polyline/polygon)
    points_bugs = []
    for m in _POINTS_RE.finditer(svg):
        buggy = _points_tokens_with_bug(m.group(1))
        if buggy:
            points_bugs.append({"sample_tokens": buggy[:5], "count": len(buggy)})
    # 2. mono-coord attributes
    coord_bugs = _coord_attr_commas(svg)
    if not points_bugs and not coord_bugs:
        return None
    return {"points_tokens": points_bugs, "coord_attrs": coord_bugs}


def _cell_outputs(cell: dict) -> list[dict]:
    return cell.get("outputs", []) or []


def detect_cell(cell: dict) -> list[dict]:
    """Return findings (one per SVG-bearing output with defects) for a code cell."""
    findings = []
    for oi, out in enumerate(_cell_outputs(cell)):
        data = out.get("data", {}) if isinstance(out, dict) else {}
        svgs: list[tuple[str, str]] = []  # (mime, markup)
        for mime in _SVG_MIMES:
            if mime in data:
                for markup in _extract_svgs(data[mime]):
                    svgs.append((mime, markup))
        for mime, markup in svgs:
            finding = detect_svg(markup)
            if finding:
                findings.append({"output_index": oi, "mime": mime, "svg_chars": len(markup), **finding})
    return findings


def _kernel(nb: dict) -> str:
    return nb.get("metadata", {}).get("kernelspec", {}).get("name", "?")


def scan_notebook(path: Path) -> dict:
    """Return a result dict for one notebook: path, kernel, hits[], error."""
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


# Dossiers a ignorer (alignes sur detect_blank_figures.py:SKIP_DIRS).
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
        f"SVG decimal-comma defects : {total_hits}",
        f"Affected notebooks   : {len(affected)}",
        "",
    ]
    if not affected:
        lines.append("No SVG decimal-comma defects detected (deterministic point/coord-attr check).")
        if errored:
            lines.append("")
            lines.append(f"NOTE: {len(errored)} notebook(s) unreadable (see --json for details).")
        return "\n".join(lines)
    for r in affected:
        short = r["path"].split("MyIA.AI.Notebooks")[-1].lstrip("\\/")
        lines.append(f"## {short}  [{r['kernel']}]")
        for h in r["hits"]:
            tags = []
            if h.get("points_tokens"):
                n = sum(p["count"] for p in h["points_tokens"])
                tags.append(f"points-tokens:{n}")
            if h.get("coord_attrs"):
                tags.append(f"coord-attrs:{len(h['coord_attrs'])}")
            lines.append(f"  - cell [{h['cell_index']}] output[{h['output_index']}] {h['mime']} ({h['svg_chars']} chars): {', '.join(tags)}")
        lines.append("")
    lines.append(
        "FIX: force InvariantCulture in the cell source "
        "(xp.ToString(\"F1\", CultureInfo.InvariantCulture) or "
        "FormattableString.Invariant, or CultureInfo.DefaultThreadCurrentCulture = "
        "InvariantCulture at cell top) then re-execute the .NET kernel -- the "
        "committed output then carries dot-decimals. Or reuse the canon "
        "SvgChartHelper.cs (#6942) which already formats with dots. "
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
    parser.add_argument("--check", action="store_true", help="Exit 1 if any SVG decimal-comma defect (CI-ready)")
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
