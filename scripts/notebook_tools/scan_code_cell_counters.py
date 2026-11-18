"""Scan des compteurs quantitatifs dans les commentaires de cellules code.

Contexte : issue #18493 (compteurs litteraux dans commentaires de cellules code,
hors prose markdown). Complement de `check_prose_quantitative_claims.py` qui
cible la prose markdown (#9377 + #9434) -- la classe commentaire-code echappe
au garde prose-counts mais releve de la meme hygiene de mesure d'artefact.

Ces compteurs sont particulierement pieges parce qu'ils sont :
  - invisibles au scan prose markdown (pas une cellule markdown)
  - dans du code execute (un `1/0` ou un commentaire `~1500 fichiers` se voit)
  - bloques contre la regeneration par byte-identite : toute edition de la
    cellule exige une re-execution Papermill complete (C.2) -- ce n'est pas
    un relais md-only.

Trois formes acceptables de commentaires-code avec quantitatif :

  1. **Approximatif** : `# NOTE: ~1500 fichiers de la stdlib`
  2. **Parenthese** : `# Code source : (302 lignes)`
  3. **Nombre + unite** : `# 109 fichiers Lean / 44 297 LOC / 2079 sorry`

Le pattern exclut strictement les comparaisons logiques (`if x > 30`) en
exigeant que la ligne commence par un commentaire `#` ou `//`, et que le
quantitatif soit directement precede d'un nombre (pas d'un mot comme "test").

Le scan produit un verdict par candidat :
  - KEEP            : constante metier, parametre code, reference datee a un
                      snapshot (audit dates d'incident / todo / archivelined).
  - REVIEW          : necessite un jugement humain (snippet de code ambigu).

Usage :
  python scripts/notebook_tools/scan_code_cell_counters.py
      [--root MyIA.AI.Notebooks]
      [--json-out path]
      [--only REVIEW]   # filtre de classe pour triage humain

Pure parsing JSON. Zero execution de notebook.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

# Force UTF-8 sur stdout pour caracteres non-ASCII (grec, accents casses, etc.)
try:
    sys.stdout.reconfigure(encoding="utf-8")
except Exception:
    pass

EXCLUDE_DIRS = {
    "_archive_obsoletes",
    "_archives",
    "_old",
    "TrashBin",
    "trashbin",
    ".ipynb_checkpoints",
    "node_modules",
}

ARTIFACT_SUFFIXES = ("_output.ipynb",)


COMMENT_PREFIX_RE = re.compile(r"^\s*(?:#|//)")

# Pattern A : tilde + nombre + espace? + unite documentaire
PAT_APPROX = re.compile(
    r"~\s*\d+\s+(?:lignes?|fichiers|theoremes|cells?|notebooks?|tests?|modules?|loc)\b",
    re.IGNORECASE,
)
# Pattern B : parentheses (nombre + unite)
PAT_PAREN = re.compile(
    r"\(\s*\d+\s+(?:lignes?|fichiers|theoremes|cells?|notebooks?|tests?|modules?|loc)\s*\)",
    re.IGNORECASE,
)
# Pattern C : "109 fichiers", "2079 sorry" -- nombre directement suivi de l'unite
PAT_N_UNIT = re.compile(
    r"\b\d{2,}\s+(?:lignes|fichiers|theoremes|cells|notebooks|modules)\b",
    re.IGNORECASE,
)
# Pattern D : "(60 lignes)" -- le nombre est entre parentheses
PAT_BARE_PAREN = re.compile(
    r"\(\s*\d+\s+(?:lignes?|fichiers|theoremes|cells?|notebooks?)\s*\)",
    re.IGNORECASE,
)


def is_counter_comment(line: str) -> bool:
    """Verifie qu'une ligne est un commentaire Python ou C# (apres strip)."""
    stripped = line.lstrip()
    return bool(COMMENT_PREFIX_RE.match(stripped))


def has_counter(line: str) -> bool:
    """Vrai si la ligne contient un compteur documentaire (un des 4 patterns)."""
    return bool(
        PAT_APPROX.search(line)
        or PAT_PAREN.search(line)
        or PAT_N_UNIT.search(line)
        or PAT_BARE_PAREN.search(line)
    )


def classify_counter(line: str) -> str:
    """Classifie un compteur en KEEP (constante/snapshot/parametre) ou REVIEW.

    Heuristique volontairement permissive : REVIEW par defaut. Un triage
    humain distingue les cas ambigus.
    """
    # 1. Pattern A : tilde+nombre -- souvent une borne indicative ou
    #    une mesure d'un fait connu (taille de la stdlib, etc.) -> KEEP
    if PAT_APPROX.search(line):
        return "KEEP"

    # 2. Pattern B : "(60 lignes)" entre parentheses -- commentaire de taille
    #    documentaire -> KEEP (commentaire informatif, pas une mesure
    #    reproductible d'artefact vivant).
    if PAT_BARE_PAREN.search(line):
        return "KEEP"

    # 3. Pattern C : "109 fichiers Lean / 2079 sorry" -- snapshot documente
    #    -> KEEP (mesure d'un fait passe, comparable aux mesures
    #    figees dans les recits incidents de #9377).
    if PAT_N_UNIT.search(line):
        return "KEEP"

    return "REVIEW"


def scan_notebook(path: Path) -> list[dict]:
    """Scan un notebook pour les compteurs dans les commentaires de cellules code."""
    try:
        with open(path, "r", encoding="utf-8") as f:
            nb = json.load(f)
    except (json.JSONDecodeError, UnicodeDecodeError, OSError) as e:
        return [{"path": str(path), "error": str(e), "class": "PARSE_ERROR"}]

    found: list[dict] = []
    cells = nb.get("cells", [])
    for i, c in enumerate(cells):
        if c.get("cell_type") != "code":
            continue
        src = c.get("source", [])
        if isinstance(src, list):
            src_text = "".join(src)
        else:
            src_text = src
        for line_no, line in enumerate(src_text.split("\n"), 1):
            if not is_counter_comment(line):
                continue
            if not has_counter(line):
                continue
            cls = classify_counter(line)
            found.append({
                "path": str(path),
                "cell_index": i,
                "line_no": line_no,
                "text": line.strip()[:200],
                "class": cls,
            })
    return found


def collect_notebooks(root: Path) -> list[Path]:
    """Collecte les .ipynb non archive, non Papermill-artifact."""
    out: list[Path] = []
    for p in root.rglob("*.ipynb"):
        parts = set(p.parts)
        if parts & EXCLUDE_DIRS:
            continue
        if p.name.endswith(ARTIFACT_SUFFIXES):
            continue
        out.append(p)
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument("--root", default="MyIA.AI.Notebooks", type=Path)
    parser.add_argument("--json-out", default=None, type=Path)
    parser.add_argument(
        "--only",
        choices=("KEEP", "REVIEW"),
        default=None,
        help="Filtre de classe pour triage humain.",
    )
    args = parser.parse_args(argv)

    if not args.root.exists():
        print(f"::error::Root does not exist: {args.root}", file=sys.stderr)
        return 2

    notebooks = collect_notebooks(args.root)
    all_findings: list[dict] = []
    for nb_path in notebooks:
        all_findings.extend(scan_notebook(nb_path))

    if args.only:
        all_findings = [f for f in all_findings if f.get("class") == args.only]

    # Sortie JSON
    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        with open(args.json_out, "w", encoding="utf-8") as f:
            json.dump(all_findings, f, indent=2, ensure_ascii=False)

    # Resume stdout
    counts: dict[str, int] = {}
    for f in all_findings:
        cls = f.get("class", "?")
        counts[cls] = counts.get(cls, 0) + 1

    print(f"== Scan compteurs commentaires code ({args.root}) ==")
    print(f"Notebooks scannes : {len(notebooks)}")
    print(f"Total compteurs : {len(all_findings)}")
    for cls in ("KEEP", "REVIEW"):
        n = counts.get(cls, 0)
        print(f"  {cls:8s} : {n}")
    print()
    if not args.json_out:
        # mode texte pour stdout
        for f in all_findings[:30]:
            print(f"  [{f.get('class','?'):6s}] {f['path']}:c{f['cell_index']}:l{f['line_no']}")
            print(f"           > {f['text']}")
        if len(all_findings) > 30:
            print(f"  ... ({len(all_findings) - 30} autres, voir --json-out)")

    return 0


if __name__ == "__main__":
    sys.exit(main())