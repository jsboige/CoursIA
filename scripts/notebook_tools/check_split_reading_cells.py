#!/usr/bin/env python3
"""Recensement des cellules de lecture scindees « Lecture » puis « Lecture chiffree ».

Demande user (nit #16554, 2026-09-17, parapluie #16762) : quand un notebook
porte deja une cellule « Lecture », la tranche de densite suivante ajoute une
seconde cellule d'interpretation -- « Lecture chiffree » -- au lieu de
fusionner. Resultat : deux cellules d'interpretation consecutives avec
recouvrement PARTIEL de contenu, l'une derriere l'autre. Ce n'est pas un
doublon franc (les deux cellules disent des choses differentes ET se
repetent en partie) : un detecteur de duplication verbatim ne le voit pas,
et pedagogiquement le lecteur ne sait plus laquelle fait foi.

Ce script fait le RECENSEMENT structurel + la mesure de recouvrement :

  1. Signal structurel : paires de cellules markdown CONSECUTIVES dont les
     titres sont des en-tetes d'interpretation (Lecture / Lecture chiffree /
     Interpretation / Analyse). Sous-classes :
       - ``named_split``   : « Lecture ... » puis « Lecture chiffree ... » --
                             le defaut nomme par le user ;
       - ``generic_pair``  : autre couple d'en-tetes d'interpretation consecutifs.
  2. Mesure de recouvrement entre les deux cellules : Jaccard sur les mots
     pleins + containment des mots rares intra-notebook (df <= 4, meme
     mecanique que detect_repeated_prose.py signal B, reutilise par import).

Variante secondaire ``separated_by_code`` : meme couple d'en-tetes separe par
UNE cellule de code (la lecture chiffree interprete la sortie) -- signale
separement, le defaut user est la paire consecutive.

Le seuil de recouvrement N'EST PAS un verdict de fusion : la fusion est une
decision pedagogique par notebook (acceptance #16762). Le recensement dit
ou regarder ; il ne dit pas quoi couper.

Codes de retour : 0 = aucun finding ; 1 = fichier illisible ; 2 = findings
(avec --fail-on-findings).
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import unicodedata
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from detect_repeated_prose import content_words, markdown_cells  # noqa: E402

REPO_ROOT = Path(__file__).resolve().parents[2]
MAX_DF = 4  # un mot "rare" apparait dans <= 4 cellules du notebook

TITLE_STRIP_RE = re.compile(r"^[#*\-\s`>]+|[#*\s`>:]+$")
INTERPRETATION_RE = re.compile(
    r"^(lecture|interpre|interpret|analyse)\b", re.IGNORECASE
)
NAMED_SECOND_RE = re.compile(r"^lecture\s+chiffr", re.IGNORECASE)
NAMED_FIRST_RE = re.compile(r"^lecture\b", re.IGNORECASE)


def deaccent(s: str) -> str:
    return "".join(
        c for c in unicodedata.normalize("NFKD", s) if not unicodedata.combining(c)
    )


def cell_title(src: str) -> str:
    """Premiere ligne non vide, nettoyee des marques markdown."""
    for line in src.splitlines():
        line = line.strip()
        if not line:
            continue
        return TITLE_STRIP_RE.sub("", line).strip()
    return ""


def is_interpretation_title(title: str) -> bool:
    return bool(INTERPRETATION_RE.match(deaccent(title).lower()))


def is_named_second(title: str) -> bool:
    return bool(NAMED_SECOND_RE.match(deaccent(title).lower()))


def overlap_metrics(nb: dict, i: int, j: int) -> dict:
    """Jaccard mots pleins + containment mots rares entre cellules i et j."""
    words = {ci: content_words(t) for ci, t in markdown_cells(nb)}
    df: Counter[str] = Counter()
    for ws in words.values():
        df.update(ws)
    wi, wj = words.get(i, set()), words.get(j, set())
    union = wi | wj
    jaccard = round(len(wi & wj) / len(union), 3) if union else 0.0
    rare_i = {w for w in wi if df[w] <= MAX_DF}
    rare_shared = rare_i & wj
    containment = round(len(rare_shared) / len(rare_i), 3) if rare_i else 0.0
    return {
        "jaccard": jaccard,
        "rare_containment": containment,
        "shared_rare_words": len(rare_shared),
        "shared_rare_sample": sorted(rare_shared)[:8],
    }


def detect(nb: dict) -> list[dict]:
    cells = nb.get("cells", [])
    titles = {
        i: cell_title(
            "".join(c["source"]) if isinstance(c.get("source"), list)
            else c.get("source", "")
        )
        for i, c in enumerate(cells)
    }
    findings: list[dict] = []
    for i in range(len(cells) - 1):
        a, b = cells[i], cells[i + 1]
        if a.get("cell_type") != "markdown" or b.get("cell_type") != "markdown":
            continue
        ta, tb = titles[i], titles[i + 1]
        if not (is_interpretation_title(ta) and is_interpretation_title(tb)):
            continue
        kind = (
            "named_split"
            if NAMED_FIRST_RE.match(deaccent(ta).lower()) and is_named_second(tb)
            else "generic_pair"
        )
        findings.append({
            "type": kind,
            "cells": [i, i + 1],
            "titles": [ta[:70], tb[:70]],
            **overlap_metrics(nb, i, i + 1),
        })
    # Variante secondaire : meme couple separe par UNE cellule de code.
    for i in range(len(cells) - 2):
        a, mid, b = cells[i], cells[i + 1], cells[i + 2]
        if mid.get("cell_type") != "code":
            continue
        if a.get("cell_type") != "markdown" or b.get("cell_type") != "markdown":
            continue
        ta, tb = titles[i], titles[i + 2]
        if not (is_interpretation_title(ta) and is_named_second(tb)):
            continue
        # Ne pas doubler un named_split deja compte (cas impossible ici :
        # la cellule du milieu est du code), garder pour la lisibilite.
        findings.append({
            "type": "separated_by_code",
            "cells": [i, i + 2],
            "titles": [ta[:70], tb[:70]],
            **overlap_metrics(nb, i, i + 2),
        })
    return findings


def iter_notebooks(root: Path) -> list[Path]:
    skip_parts = {".lake", "_output", ".ipynb_checkpoints", "node_modules", "_peters"}
    return sorted(
        p for p in root.rglob("*.ipynb")
        if not (skip_parts & set(p.parts))
    )


def scan_root(root: Path, as_json: bool) -> int:
    total = 0
    per_kind: Counter[str] = Counter()
    rows = []
    for path in iter_notebooks(root):
        try:
            nb = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as e:
            print(f"ERREUR lecture {path}: {e}", file=sys.stderr)
            return 1
        for f in detect(nb):
            total += 1
            per_kind[f["type"]] += 1
            rel = path.relative_to(root)
            rows.append({"file": str(rel), **f})
    if as_json:
        print(json.dumps(rows, ensure_ascii=False, indent=1))
    else:
        for r in rows:
            print(
                f"{r['type']:18s} {r['file']}  cellules {r['cells']}  "
                f"J={r['jaccard']:.2f} C={r['rare_containment']:.2f} "
                f"rare={r['shared_rare_words']}  «{r['titles'][0]}» + «{r['titles'][1]}»"
            )
        print(f"\nTotal : {total} ({dict(per_kind)})")
    return 0


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("path", nargs="?", default=str(REPO_ROOT / "MyIA.AI.Notebooks"),
                    help="notebook ou dossier a scanner")
    ap.add_argument("--json", action="store_true", dest="as_json")
    ap.add_argument("--fail-on-findings", action="store_true")
    args = ap.parse_args(argv)
    target = Path(args.path)
    if not target.exists():
        print(f"introuvable : {target}", file=sys.stderr)
        return 1
    if target.is_file():
        nb = json.loads(target.read_text(encoding="utf-8"))
        findings = detect(nb)
        print(json.dumps(findings, ensure_ascii=False, indent=1)
              if args.as_json else "\n".join(
                  f"{f['type']} cellules {f['cells']} J={f['jaccard']} "
                  f"C={f['rare_containment']} «{f['titles'][0]}» + «{f['titles'][1]}»"
                  for f in findings) or "clean")
        return 2 if (args.fail_on_findings and findings) else 0
    rc = scan_root(target, args.as_json)
    return rc


if __name__ == "__main__":
    sys.exit(main())
