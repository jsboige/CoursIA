#!/usr/bin/env python3
"""Detecte les regles mermaid `style`/`classDef` portant `fill:` sans `color:` (#15022).

Pourquoi cet outil existe
-------------------------
Defect fondateur #15022 (signale par le user, fix PR #15502) : dans un bloc
mermaid, une regle `style`/`classDef` qui force un `fill:` clair SANS `color:`
explicite laisse le libelle heriter la couleur de TEXTE du theme. En mode
sombre GitHub, texte clair du theme sur fond clair force = illisible
(clair-sur-clair). Le README Probas portait 10 regles dans cet etat sur 3
blocs ; la verification « 0 regle fill: sans color: » avait ete faite A LA MAIN
dans #15502 -- rien n'empechait la recidive (review NanoClaw : « le motif peut
revenir, sur ce fichier comme sur les 24 autres .md du depot »).

Ce detecteur formalise cette verification : une ligne `style <id> ...` ou
`classDef <name> ...` a l'interieur d'une fence ```mermaid est un FINDING si
elle porte `fill:` mais pas `color:`. La correction est l'ajout d'un `color:`
explicite (ton fonce, cf. la garde `%%` posee par #15502 : le ton peut
deliberement s'ecarter du `stroke` -- ne pas harmoniser aveuglement).

Scope : fichiers `.md` trackes + cellules markdown des `.ipynb` (le defect vit
dans les README de series ; les notebooks peuvent porter les memes blocs).
Il DETECTE, il ne CORRIGE PAS.

Mesure fleet sur origin/main (2026-09-11) : **25 fichiers / 90 regles fautives**
sur 204 regles `fill:` totales (114 avec `color:`). Ground truth : le README
Probas porte exactement les 10 regles recomptees a la main par la review
NanoClaw sur #15502 -- le detecteur les retrouve toutes (precision et rappel
prouves sur ce cas). Le residuel fait l'objet d'une issue de suivi nommee dans
le body PR (advisory = pas de cascade sur le pre-existant).

Usage
-----
    python detect_mermaid_fill_without_color.py                  # fleet (git ls-files *.md + notebooks)
    python detect_mermaid_fill_without_color.py README.md        # un fichier
    python detect_mermaid_fill_without_color.py --json           # sortie machine
    python detect_mermaid_fill_without_color.py --check          # exit 1 si finding (CI-ready)
    python detect_mermaid_fill_without_color.py --self-test      # prouve que le detecteur tire
    git diff --name-only ... | python detect_mermaid_fill_without_color.py --stdin --json

Exit codes
----------
    0 -- aucun finding (ou mode non --check)
    1 -- un ou plusieurs findings (--check seulement)
    2 -- erreur (fichier illisible / introuvable)

Voir aussi
----------
- `.github/workflows/mermaid-fill-color-advisory.yml` -- cablage advisory (label)
- `detect_cjk_residue.py` (#8428), `detect_paragraph_length.py` (#15405) -- pattern detect_*
- #15022 (defect fondateur), #15502 (fix + garde %%), issue de suivi sweep corpus

See #15022, #15502.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

# Ouverture de fence code (``` ou ~~~), avec tag de langage optionnel.
_FENCE_OPEN_RE = re.compile(r"^\s*(`{3,}|~{3,})\s*(\S*)")

# Ligne de regle de style mermaid : `style <id> <props>` ou `classDef <name> <props>`.
# On ne juge QUE ces deux formes : ce sont les seules qui portent un `fill:` de
# fond dans la grammaire mermaid (les `class x foo` appliquent, ne definissent pas).
_STYLE_LINE_RE = re.compile(r"^\s*(style|classDef)\s+\S+\s+\S")

_FILL_RE = re.compile(r"\bfill\s*:")
_COLOR_RE = re.compile(r"\bcolor\s*:")

# Allowlist : chemins (substring) ou le pattern est un FIXTURE DE TEST positif --
# le detecteur doit pouvoir prouver qu'il tire sur un cas volontaire.
ALLOWED: dict[str, str] = {
    "scripts/notebook_tools/tests/fixtures/mermaid_fill_no_color":
        "fixture de test positif (pattern volontaire pour piner le contrat)",
}


def classify_mermaid_fill_rules(text: str) -> tuple[list[dict], int, int]:
    """Return ``(findings, n_style_rules, n_with_color)`` for ``text`` (markdown).

    Un finding = ligne ``style``/``classDef`` d'une fence mermaid portant
    ``fill:`` sans ``color:``. ``n_style_rules`` compte les regles style/
    classDef avec ``fill:`` (denominateur), ``n_with_color`` celles qui portent
    aussi ``color:`` -- la paire documente l'etat du fichier sans finding.
    """
    findings: list[dict] = []
    n_style_rules = 0
    n_with_color = 0
    in_fence = False
    fence_is_mermaid = False
    fence_marker = ""
    for lineno, line in enumerate(text.split("\n"), start=1):
        m = _FENCE_OPEN_RE.match(line)
        if m:
            marker, tag = m.group(1), (m.group(2) or "").lower()
            if not in_fence:
                in_fence = True
                fence_marker = marker[0] * 3
                fence_is_mermaid = tag == "mermaid"
            elif line.strip().startswith(fence_marker) and not tag:
                # Fermeture : meme famille de marqueur, pas de tag de langage.
                in_fence = False
                fence_is_mermaid = False
            continue
        if not (in_fence and fence_is_mermaid):
            continue
        if not _STYLE_LINE_RE.match(line):
            continue
        stripped = line.strip()
        if stripped.startswith("%%"):
            continue  # commentaire mermaid, pas une regle
        if not _FILL_RE.search(line):
            continue
        n_style_rules += 1
        if _COLOR_RE.search(line):
            n_with_color += 1
            continue
        rule_type = stripped.split()[0]
        target = stripped.split()[1] if len(stripped.split()) > 1 else "?"
        findings.append({
            "lineno": lineno,
            "rule": rule_type,
            "target": target,
            "context": stripped[:90],
            "reason": "fill: sans color: -- libelle herite la couleur de texte du theme (clair-sur-clair en mode sombre, #15022)",
        })
    return findings, n_style_rules, n_with_color


def _cell_source(cell: dict) -> str:
    src = cell.get("source", "")
    if isinstance(src, list):
        return "".join(src)
    return src or ""


def _is_allowed(rel_path: str) -> str | None:
    for needle, reason in ALLOWED.items():
        if needle in rel_path:
            return reason
    return None


def scan_markdown_file(path: Path, root: Path) -> dict:
    """Scan un .md : findings par ligne (lineno dans le fichier)."""
    try:
        rel = str(path.relative_to(root)).replace("\\", "/")
    except ValueError:
        rel = str(path).replace("\\", "/")
    allowed_reason = _is_allowed(rel)
    if allowed_reason:
        return {"path": rel, "allowed": allowed_reason, "hits": [], "stats": None, "error": None}
    try:
        text = path.read_text(encoding="utf-8", errors="replace")
    except OSError as exc:
        return {"path": rel, "allowed": None, "hits": [], "stats": None, "error": str(exc)}
    findings, n_rules, n_color = classify_mermaid_fill_rules(text)
    return {
        "path": rel, "allowed": None, "hits": findings,
        "stats": {"fill_rules": n_rules, "with_color": n_color},
        "error": None,
    }


def scan_notebook(path: Path, root: Path) -> dict:
    """Scan un .ipynb : findings par cellule markdown (cell_index)."""
    try:
        rel = str(path.relative_to(root)).replace("\\", "/")
    except ValueError:
        rel = str(path).replace("\\", "/")
    allowed_reason = _is_allowed(rel)
    if allowed_reason:
        return {"path": rel, "allowed": allowed_reason, "hits": [], "stats": None, "error": None}
    try:
        with open(path, encoding="utf-8") as f:
            nb = json.load(f)
    except (OSError, json.JSONDecodeError) as exc:
        return {"path": rel, "allowed": None, "hits": [], "stats": None, "error": str(exc)}
    hits: list[dict] = []
    n_rules = n_color = 0
    for ci, cell in enumerate(nb.get("cells", [])):
        if cell.get("cell_type") != "markdown":
            continue
        findings, r, c = classify_mermaid_fill_rules(_cell_source(cell))
        n_rules += r
        n_color += c
        for fd in findings:
            hits.append({"cell_index": ci, "cell_type": "markdown", **fd})
    return {
        "path": rel, "allowed": None, "hits": hits,
        "stats": {"fill_rules": n_rules, "with_color": n_color},
        "error": None,
    }


# Marcheur + SKIP_DIRS canonique centralises dans notebook_walk (#8650).
from notebook_walk import SKIP_DIRS, iter_notebooks  # noqa: E402


def _iter_tracked_md(root: Path) -> list[Path]:
    """Fichiers .md trackes (git ls-files = source de verite, drop gitignore
    et contenu de submodules), hors SKIP_DIRS."""
    try:
        result = subprocess.run(
            ["git", "ls-files", "-z", "--", "*.md"],
            cwd=str(root), capture_output=True, text=False, timeout=180,
        )
    except (FileNotFoundError, OSError):
        return []
    if result.returncode != 0:
        return []
    out: list[Path] = []
    for e in result.stdout.decode("utf-8", "replace").strip("\x00").split("\x00"):
        if not e:
            continue
        rel = e.replace("\\", "/")
        if any(part in SKIP_DIRS for part in rel.split("/")):
            continue
        out.append(root / rel)
    return out


def _scan_one(path: Path, root: Path) -> dict:
    if path.suffix == ".ipynb":
        return scan_notebook(path, root)
    return scan_markdown_file(path, root)


def _human_report(results: list[dict]) -> str:
    scanned = [r for r in results if r["allowed"] is None and r["error"] is None]
    allowed = [r for r in results if r["allowed"]]
    errors = [r for r in results if r["error"]]
    affected = [r for r in scanned if r["hits"]]
    total_hits = sum(len(r["hits"]) for r in scanned)
    total_rules = sum((r["stats"] or {}).get("fill_rules", 0) for r in scanned)
    total_color = sum((r["stats"] or {}).get("with_color", 0) for r in scanned)
    lines = [
        f"Files scanned : {len(scanned)}",
        f"Mermaid fill: rules : {total_rules} (with color: {total_color})",
        f"Findings (fill: sans color:) : {total_hits} in {len(affected)} file(s)",
        f"Allowed (skipped) : {len(allowed)}",
        "",
    ]
    if errors:
        lines.append(f"Read errors : {len(errors)}")
        for r in errors:
            lines.append(f"  - {r['path']}: {r['error']}")
        lines.append("")
    if not affected:
        lines.append("No fill-without-color rule detected (vs #15022).")
        return "\n".join(lines)
    for r in affected:
        lines.append(f"## {r['path']}")
        for h in r["hits"]:
            loc = (f"cell [{h['cell_index']}]" if "cell_index" in h
                   else f"line {h['lineno']}")
            lines.append(f"  - {loc}: {h['rule']} {h['target']} | {h['context']}")
        lines.append("")
    lines.append(
        "NOTE: corriger en ajoutant un `color:` explicite (ton fonce ; peut\n"
        "s'ecarter deliberement du `stroke` -- cf garde %% #15502, ne pas\n"
        "harmoniser aveuglement). Verifier chaque finding firsthand."
    )
    return "\n".join(lines)


def _self_test() -> int:
    """Prouve que le detecteur tire : un bloc fautif DOIT produire un finding,
    son corrige (color: ajoute) DOIT n'en produire aucun."""
    bad = (
        "```mermaid\n"
        "flowchart LR\n"
        "    A --> B\n"
        "    classDef dist fill:#d1ecf1,stroke:#0c5460,stroke-width:2px;\n"
        "    class A,B dist;\n"
        "```\n"
    )
    good = (
        "```mermaid\n"
        "flowchart LR\n"
        "    A --> B\n"
        "    classDef dist fill:#d1ecf1,stroke:#0c5460,stroke-width:2px,color:#0c5460;\n"
        "    class A,B dist;\n"
        "```\n"
    )
    outside = (
        "```\n"
        "classDef dist fill:#d1ecf1,stroke:#0c5460;\n"  # fence non-mermaid : ignore
        "```\n"
    )
    f_bad, n_bad, c_bad = classify_mermaid_fill_rules(bad)
    f_good, n_good, c_good = classify_mermaid_fill_rules(good)
    f_out, _, _ = classify_mermaid_fill_rules(outside)
    assert len(f_bad) == 1 and f_bad[0]["rule"] == "classDef", f"self-test FAIL: bad={f_bad}"
    assert n_bad == 1 and c_bad == 0, f"self-test FAIL: stats bad=({n_bad},{c_bad})"
    assert f_good == [] and n_good == 1 and c_good == 1, f"self-test FAIL: good={f_good}"
    assert f_out == [], f"self-test FAIL: non-mermaid fence judged: {f_out}"
    print("self-test: 3/3 pass (finding on fill-without-color, clean on color:, ignore non-mermaid fence)")
    return 0


_SCANNABLE_EXT = {".ipynb", ".md"}


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        description=__doc__.split("\n\n")[0],
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("target", nargs="?", help="Fichier .md ou .ipynb a scanner (defaut: fleet)")
    parser.add_argument("--root", default=".", help="Repo root (defaut: cwd)")
    parser.add_argument("--json", action="store_true", help="Sortie machine JSON")
    parser.add_argument("--check", action="store_true", help="Exit 1 si finding (CI-ready)")
    parser.add_argument("--self-test", action="store_true", help="Prouve que le detecteur tire")
    parser.add_argument(
        "--stdin", action="store_true",
        help="Lire les chemins a scanner sur stdin (un par ligne, sortie de "
             "`git diff --name-only`) : verdict sur exactement les fichiers "
             "touches par la PR, pas la fleet entiere.",
    )
    args = parser.parse_args(argv)

    if args.self_test:
        return _self_test()

    root = Path(args.root).resolve()
    if args.stdin:
        results = []
        for line in sys.stdin:
            line = line.strip()
            if not line:
                continue
            p = Path(line)
            if not p.is_absolute():
                p = root / p
            if p.suffix not in _SCANNABLE_EXT or not p.exists():
                continue
            try:
                rel_parts = p.relative_to(root).parts
            except ValueError:
                rel_parts = p.parts
            if any(part in SKIP_DIRS for part in rel_parts):
                continue
            results.append(_scan_one(p, root))
    elif args.target:
        p = Path(args.target)
        if not p.is_absolute():
            p = root / p
        if not p.exists():
            print(f"error: target not found: {p}", file=sys.stderr)
            return 2
        results = [_scan_one(p, root)]
    else:
        nb_paths = list(iter_notebooks(root / "MyIA.AI.Notebooks"))
        md_paths = _iter_tracked_md(root)
        results = [scan_notebook(p, root) for p in nb_paths] + [
            scan_markdown_file(p, root) for p in md_paths
        ]

    scanned = [r for r in results if r["allowed"] is None and r["error"] is None]
    errors = [r for r in results if r["error"]]
    total_hits = sum(len(r["hits"]) for r in scanned)

    if args.json:
        payload = {
            "scanned": len(scanned),
            "flagged_count": len([r for r in scanned if r["hits"]]),
            "total_hits": total_hits,
            "error_count": len(errors),
            "results": results,
        }
        print(json.dumps(payload, ensure_ascii=False, indent=2))
    else:
        print(_human_report(results))

    if args.check and total_hits > 0:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
