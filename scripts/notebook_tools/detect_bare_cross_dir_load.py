#!/usr/bin/env python3
r"""Detecte un `#load "X.cs"` **bare** (nom de fichier nu, sans separateur) dont le `.cs` n'existe PAS dans le dossier du notebook.

Pourquoi cet outil existe
-------------------------
Le rollout SVG inline (#6927) fait converger des dizaines de notebooks .NET vers
le helper partage `SvgChartHelper.cs` (qui vit dans `MyIA.AI.Notebooks/Probas/Infer/`,
0 copie ailleurs). Le kernel `dotnet-interactive` resout un `#load "X"` **relativement
au dossier du notebook** (son cwd reel a l'exec headless). Donc un
`#load "SvgChartHelper.cs"` **bare** ne resout QUE si `SvgChartHelper.cs` est
co-localise avec le notebook. Un notebook d'une AUTRE famille (ex `GameTheory/`)
qui charge le helper via un `#load "SvgChartHelper.cs"` bare casse en re-exec
propre : **CS1504 -- source file not found**. Ces cellules rendent aujourd'hui
uniquement parce que le kernel tournait avec un cwd qui trouvait le fichier ;
en re-exec headless depuis le dossier du notebook, elles cassent silencieusement.

Meme classe de defaut que le batch DecInfer/portability (`FactorGraphHelper.cs` /
`SvgChartHelper.cs`, 10+ PR deja mergees) -- mais **cross-family** (le `.cs` vit
dans un dossier different de celui du notebook). Le correctif canonique
(design-gate tranche ai-01 2026-07-17, issue #7050) = **path relatif explicite**
`#load "../Probas/Infer/SvgChartHelper.cs"` (rejete : copier le helper = 4 copies
divergentes DRY-violation ; rejete : refactor centralise = sur-ingenierie). Ce
gate ferme la classe et previent la regression apres que les 4 notebooks
residuels (GameTheory-4c/8c/15c/17) auront ete corriges (#7052 / #7049).

Ce que l'outil DETECTE (DETERMINISTE, zero faux-positif)
-------------------------------------------------------
Pour chaque cellule **code**, pour chaque directive `#load "<cible>"` :

  1. La `<cible>` est **BARE** -- aucun separateur de chemin (`/` ni `\`). Un
     chemin explicite (`../Probas/Infer/SvgChartHelper.cs`, `helpers/Foo.cs`,
     absolu) est HORS scope : il porte l'intention de resolution d'un humain et
     le valider entierement demanderait des hypotheses de cwd (source de FP).
     Le correctif recommande (`../Probas/Infer/SvgChartHelper.cs`) contient des
     separateurs -> il **PASSE** ce gate, par construction.
  2. La `<cible>` est un fichier **source .NET** (`.cs`, `.csx`, `.fsx`) -- pas
     un `#r "nuget:..."` (reference de package, jamais un `#load`) ni un `.dll`.
  3. Le fichier `<dossier_du_notebook>/<cible>` **n'existe PAS** (verification
     disque, insensible a la casse pour ne pas FP sur un notebook Windows dont
     le fichier co-localise a une casse differente). Un `#load "Foo.cs"` bare
     dont `Foo.cs` est **co-localise** resout parfaitement en headless -> il
     n'est **PAS** flagge (c'est le cas legitime intra-dossier).

La combinaison (bare + source .cs + absent du dossier) est la **signature exacte**
du cross-dir load casse. **Zero faux-positif** : un `#load` bare co-localise
resout ; un `#load` avec chemin explicite est hors scope ; un `#r`/nuget n'est
pas un `#load`.

Ce qu'il NE corrige PAS
-----------------------
Il DETECTE, il ne CORRIGE PAS. La correction (issue #7050, design-gate tranche) =
remplacer `#load "SvgChartHelper.cs"` par le **path relatif explicite** qui
atteint le helper depuis le dossier du notebook (ex `#load "../Probas/Infer/SvgChartHelper.cs"`).
Fix **source-only** : la ligne `#load` change ; `execution_count`/`outputs`
restent inchanges (la re-exec de verification -- `dotnet_executor` ContentRoot =
dossier du notebook, 0 erreur -- se fait separement, PAS committee ; lecon
banner-leak). Stop&Repair : on repare la cause + re-execute pour verifier, on ne
scrubbe jamais la sortie a la main (secrets-hygiene regle 6).

Known blind spots (hors scope par design)
-----------------------------------------
- **Chemin relatif explicite qui ne resout pas** (`#load "../mauvais/chemin.cs"`) :
  hors scope. Valider qu'un chemin relatif atteint sa cible demande de connaitre
  le cwd d'exec reel du kernel (source de FP). L'outil cible UNIQUEMENT le cas
  bare-non-co-localise, deterministe et zero-FP.
- **`#load` d'un `.cs` co-localise mais absent a l'exec** (fichier genere a la
  volee) : rare ; le fichier existe sur disque au commit -> non flagge (correct).
- **Notebooks non-.NET** : `#load` est une directive C#/F# script. Un notebook
  Python n'en contient pas -> jamais flagge.

Usage
-----
    python detect_bare_cross_dir_load.py NB.ipynb                 # un notebook
    python detect_bare_cross_dir_load.py --family GameTheory      # une famille
    python detect_bare_cross_dir_load.py                          # tous les notebooks
    python detect_bare_cross_dir_load.py NB.ipynb --json          # sortie machine
    python detect_bare_cross_dir_load.py NB.ipynb --check         # exit 1 si defauts (CI-ready)

Exit codes
----------
    0 -- aucun defaut (ou mode non --check)
    1 -- un ou plusieurs defauts (--check seulement)
    2 -- erreur (notebook illisible, famille introuvable)

Voir aussi
----------
- `detect_svg_empty_display.py` (#6971) -- l'AUTRE face du meme pitfall : quand
  le `#load` du helper ne resout pas, la cellule emet un output VIDE (figure
  blanche). Celui-ci attrape la cause a la SOURCE (le `#load` bare cross-dir) ;
  #6971 attrape le SYMPTOME dans l'output (blanc). Complementaires.
- `.github/workflows/bare-cross-dir-load-gate.yml` -- gate CI per-PR pour cet outil.
- issue #7050 (design-gate tranche ai-01 : path relatif explicite canonique) --
  la regle que cet outil encode mecaniquement + la classe qu'il ferme.

See #7050 (suivi optionnel : detecteur CI de la classe #load cross-family).
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

# Directive #load avec une cible entre guillemets doubles (dotnet-interactive).
# Gere le prefixe optionnel @ (`#load @"..."`). Ignore #r (reference de package/dll,
# jamais un #load de fichier source).
_LOAD_RE = re.compile(r'#load\s+@?"([^"]+)"')

# Extensions de fichier source .NET script chargeables par #load.
_SOURCE_EXTS = (".cs", ".csx", ".fsx")


def _cell_source(cell: dict) -> str:
    src = cell.get("source", "")
    if isinstance(src, list):
        return "".join(src)
    return str(src)


def _is_bare(target: str) -> bool:
    """True si la cible est un nom de fichier nu (aucun separateur de chemin)."""
    return "/" not in target and "\\" not in target


def _colocated(nb_dir: Path, target: str) -> bool:
    """True si `target` existe dans `nb_dir` (insensible a la casse -> pas de FP
    sur un fichier co-localise a casse differente, qui resout sur le FS d'exec)."""
    direct = nb_dir / target
    if direct.exists():
        return True
    tl = target.lower()
    try:
        for entry in nb_dir.iterdir():
            if entry.is_file() and entry.name.lower() == tl:
                return True
    except OSError:
        pass
    return False


def detect_cell(cell: dict, nb_dir: Path) -> list[dict]:
    """Retourne la liste des defauts (une entree par directive #load bare cassee)."""
    if cell.get("cell_type") != "code":
        return []
    hits = []
    src = _cell_source(cell)
    for m in _LOAD_RE.finditer(src):
        target = m.group(1)
        if not target.lower().endswith(_SOURCE_EXTS):
            continue  # pas un fichier source .NET (ex .dll) -> hors scope
        if not _is_bare(target):
            continue  # chemin explicite -> hors scope (assume intentionnel)
        if _colocated(nb_dir, target):
            continue  # co-localise -> resout en headless -> legitime
        hits.append({
            "target": target,
            "directive": m.group(0),
        })
    return hits


# Dossiers a ignorer (alignes sur detect_svg_empty_display.py / detect_blank_figures.py).
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


def scan_notebook(path: Path) -> dict:
    """Return a result dict for one notebook: path, kernel, hits[], error."""
    try:
        with open(path, encoding="utf-8") as f:
            nb = json.load(f)
    except (OSError, json.JSONDecodeError) as exc:
        return {"path": str(path), "error": str(exc), "hits": []}
    nb_dir = path.parent
    hits = []
    for ci, cell in enumerate(nb.get("cells", [])):
        for detail in detect_cell(cell, nb_dir):
            hits.append({"cell_index": ci, **detail})
    kernel = nb.get("metadata", {}).get("kernelspec", {}).get("name", "?")
    return {"path": str(path), "kernel": kernel, "hits": hits, "error": None}


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
        f"Bare cross-dir #load hits : {total_hits}",
        f"Affected notebooks        : {len(affected)}",
        "",
    ]
    if not affected:
        lines.append(
            'No bare cross-dir `#load "X.cs"` detected (bare filename not present in '
            "the notebook's own directory)."
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
                f"  - cell [{h['cell_index']}] bare `{h['directive']}` "
                f"-> `{h['target']}` NOT in notebook dir (breaks headless re-exec, CS1504)"
            )
        lines.append("")
    lines.append(
        'FIX: replace the bare `#load "X.cs"` with an EXPLICIT relative path that '
        "reaches the source file from the notebook's directory "
        '(e.g. `#load "../Probas/Infer/SvgChartHelper.cs"` -- the single '
        "SvgChartHelper.cs lives in MyIA.AI.Notebooks/Probas/Infer/). Design-gate "
        "tranched by ai-01 (issue #7050): explicit relative path is canonical "
        "(copying the helper = DRY-violating divergent copies; centralised refactor "
        "= over-engineering, both rejected). Source-only fix (the `#load` line "
        "only; execution_count/outputs unchanged -- run a separate verification "
        "re-exec with the notebook dir as cwd, do NOT commit it). Stop&Repair: fix "
        "the cause + re-execute to verify, never scrub the output by hand "
        "(secrets-hygiene rule 6)."
    )
    return "\n".join(lines)


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        description=__doc__.split("\n\n")[0],
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("notebook", nargs="?", help="Notebook to scan (default: all pedagogical)")
    parser.add_argument("--family", help="Top-level family under MyIA.AI.Notebooks/ (e.g. GameTheory)")
    parser.add_argument("--root", default=".", help="Repo root (default: cwd)")
    parser.add_argument("--json", action="store_true", help="Machine-readable JSON output")
    parser.add_argument("--check", action="store_true", help="Exit 1 if any bare cross-dir #load (CI-ready)")
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
