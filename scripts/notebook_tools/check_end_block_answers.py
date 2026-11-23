#!/usr/bin/env python3
"""Detecte les carnets dont le bloc « Verifiez votre comprehension » n'a pas de reponse.

Pourquoi cet outil existe
-------------------------
Issue #27611 (volet GameTheory de #19297). Le mainteneur a pose sur la PR #27049
(commentaire 6943057003) la constatation suivante : le bloc « Verifiez votre
comprehension » porte la meilleure valeur pedagogique d'un carnet -- et il ne
porte cette valeur que si les **reponses sont la**. Les exercices, eux, restent
volontairement sans reponse : c'est la convention du depot.

Le premier recensement etait **trop large** : il comptait les blocs « Exercices »
comme des blocs sans reponse, et surestimait la dette. D'ou la necessite d'un
detecteur **resserre** qui distingue les deux formats :

- « Verifiez votre comprehension » -> doit porter des reponses repliees ;
- « Exercices » -> sans reponse, par convention, jamais signale.

Ce que l'outil signale
----------------------
Un carnet dont le bloc canonique « Verifiez votre comprehension » ne contient
**pas** de reponses repliees. La reponse repliee est un bloc HTML ``<details>``
dont le ``<summary>`` porte la mention « reponse » (forme de reference livree par
la PR #27049) :

    <details>
    <summary>Elements de reponse</summary>

    1. ...

    </details>

La detection est **insensible aux accents** et tolere les variantes de titre.

Portee
------
``MyIA.AI.Notebooks/**/*.ipynb``, hors ``_archive/``, ``_output/`` et
``.ipynb_checkpoints/``. Les carnets sans bloc « Verifiez votre comprehension »
ne sont **jamais** signales : l'absence du bloc n'est pas le defaut vise.

Usage
-----
    python scripts/notebook_tools/check_end_block_answers.py [--json] [--fail]
    python scripts/notebook_tools/check_end_block_answers.py --series GameTheory
    python scripts/notebook_tools/check_end_block_answers.py --self-test
"""

from __future__ import annotations

import argparse
import io
import json
import os
import re
import sys
import unicodedata
from typing import Any, Dict, List, Optional, Tuple

REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
NOTEBOOK_ROOT = os.path.join(REPO_ROOT, "MyIA.AI.Notebooks")

EXCLUDED_DIRS = ("_archive", "_output", ".ipynb_checkpoints")

HEADING_RE = re.compile(r"^(#{1,6})\s+(.*)$")
DETAILS_RE = re.compile(r"<details\b", re.IGNORECASE)

CANONICAL_TITLE = "verifiez votre comprehension"
ANSWER_MARKER = "reponse"


def strip_accents(text: str) -> str:
    """Renvoie le texte sans accents, en minuscules (comparaison robuste)."""
    folded = unicodedata.normalize("NFD", text)
    return "".join(c for c in folded if not unicodedata.combining(c)).lower()


def cell_text(cell: Dict[str, Any]) -> str:
    """Concatene le source d'une cellule (liste ou chaine)."""
    src = cell.get("source", "")
    if isinstance(src, list):
        return "".join(src)
    return str(src)


def find_end_block(cells: List[Dict[str, Any]]) -> Optional[Tuple[int, int, int]]:
    """Renvoie (index de cellule, niveau du titre, numero de ligne) du bloc."""
    for index, cell in enumerate(cells):
        if cell.get("cell_type") != "markdown":
            continue
        for lineno, line in enumerate(cell_text(cell).splitlines()):
            match = HEADING_RE.match(line.strip())
            if not match:
                continue
            level = len(match.group(1))
            title = strip_accents(match.group(2)).strip()
            if title.startswith(CANONICAL_TITLE) and level <= 3:
                return index, level, lineno
    return None


def block_text(cells: List[Dict[str, Any]], start: int, level: int, title_line: int) -> str:
    """Texte du bloc canonique, titre exclu, section suivante exclue.

    Les sections d'un meme carnet tiennent souvent dans UNE SEULE cellule
    markdown (« A retenir », « Verifiez votre comprehension », « Pour aller plus
    loin »). La coupure doit donc s'appliquer aussi a l'interieur de la cellule
    de depart.
    """
    parts: List[str] = []
    for offset, cell in enumerate(cells[start:]):
        text = cell_text(cell)
        lines = text.splitlines(True)
        if offset == 0:
            lines = lines[title_line + 1:]
        kept: List[str] = []
        for line in lines:
            match = HEADING_RE.match(line.strip())
            if match and len(match.group(1)) <= level:
                parts.append("".join(kept))
                return "\n".join(parts)
            kept.append(line)
        parts.append("".join(kept))
    return "\n".join(parts)


def has_answers(text: str) -> bool:
    """Vrai si le texte porte un bloc <details> de reponses repliees.

    Deux formats sont reconnus, tous deux en usage dans le corpus :

    - la forme de reference (#27049) : un seul ``<details>`` dont le
      ``<summary>`` porte « Elements de reponse » ;
    - la forme par question : un ``<details>`` par question, dont le resume
      porte la question (« Q1 -- ... ») et dont le corps porte « Reponse ».
    """
    for region in DETAILS_RE.finditer(text):
        end = text.find("</details>", region.start())
        chunk = text[region.start(): end if end != -1 else len(text)]
        if ANSWER_MARKER in strip_accents(chunk):
            return True
    return False


def scan_notebook(path: str) -> Optional[Dict[str, Any]]:
    """Analyse un carnet. Renvoie le constat, ou None si rien a signaler."""
    try:
        with io.open(path, encoding="utf-8") as handle:
            notebook = json.load(handle)
    except (OSError, ValueError) as exc:
        return {"path": path, "error": str(exc)}
    cells = notebook.get("cells", [])
    found = find_end_block(cells)
    if found is None:
        return None
    index, level, title_line = found
    window = block_text(cells, index, level, title_line)
    if has_answers(window):
        return None
    return {
        "path": path,
        "cell_index": index,
        "heading_level": level,
        "questions": count_questions(window),
    }


def count_questions(text: str) -> int:
    """Nombre de questions du bloc.

    Deux formes : les listes numerotees (« 1. ... ») et les resumes de la
    forme par question (« Q1 -- ... »).
    """
    count = 0
    for line in text.splitlines():
        if re.match(r"^\s*\d+\.\s+\S", line):
            count += 1
        elif re.match(r"^\s*Q\d+\b", line):
            count += 1
    return count


def iter_notebooks(root: str) -> List[str]:
    """Liste les carnets du corpus, hors repertoires exclus."""
    paths = []
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d not in EXCLUDED_DIRS]
        for name in sorted(filenames):
            if name.endswith(".ipynb"):
                paths.append(os.path.join(dirpath, name))
    return sorted(paths)


def series_of(path: str) -> str:
    """Nom de serie : premier segment du chemin sous ``MyIA.AI.Notebooks``."""
    relative = os.path.relpath(path, NOTEBOOK_ROOT)
    parts = relative.split(os.sep)
    return parts[0] if len(parts) > 1 else "(racine)"


def scan_corpus(root: str, series: Optional[str] = None) -> List[Dict[str, Any]]:
    """Balaye le corpus et renvoie les constats, series comprises."""
    findings = []
    for path in iter_notebooks(root):
        if series and series_of(path) != series:
            continue
        result = scan_notebook(path)
        if result is not None:
            result["series"] = series_of(path)
            findings.append(result)
    return findings


def report(findings: List[Dict[str, Any]]) -> str:
    """Rendu texte du recensement, groupe par serie."""
    lines = []
    by_series: Dict[str, List[Dict[str, Any]]] = {}
    for finding in findings:
        by_series.setdefault(finding.get("series", "?"), []).append(finding)
    total = len(findings)
    lines.append(
        "Bloc « Verifiez votre comprehension » sans reponses repliees -- "
        "%d carnet(s)" % total
    )
    for series in sorted(by_series):
        items = by_series[series]
        lines.append("")
        lines.append("%s (%d)" % (series, len(items)))
        for item in items:
            relative = os.path.relpath(item["path"], REPO_ROOT).replace(os.sep, "/")
            lines.append(
                "  - %s (cellule %s, %s question(s))"
                % (relative, item.get("cell_index"), item.get("questions"))
            )
    return "\n".join(lines)


def self_test() -> int:
    """Controle interne : cas synthetiques, sans dependance au corpus."""
    def md(source: str) -> Dict[str, Any]:
        return {"cell_type": "markdown", "source": source.splitlines(True)}

    with_answers = [
        md("## Verifiez votre comprehension\n\n1. Question ?\n"),
        md(
            "<details>\n<summary>Elements de reponse</summary>\n\n"
            "1. Une reponse.\n\n</details>\n"
        ),
    ]
    without_answers = [md("## Verifiez votre comprehension\n\n1. Question ?\n2. Autre ?\n")]
    accents = [
        md("## Verifiez votre comprehension\n\n1. Question ?\n"),
        md("<details>\n<summary>Éléments de réponse</summary>\n\n1. ok\n\n</details>\n"),
    ]
    exercises_only = [md("## Exercices\n\n1. A faire\n")]
    variant = [md("### Verifiez votre comprehension !\n\n1. Question ?\n")]
    outside_window = [
        md("## Verifiez votre comprehension\n\n1. Question ?\n"),
        md("## Pour aller plus loin\n\n<details>\n<summary>Elements de reponse</summary>\n\n1. ok\n\n</details>\n"),
    ]
    cases = [
        ("avec reponses", with_answers, None),
        ("sans reponses", without_answers, "cellule 0"),
        ("accents", accents, None),
        ("exercices seuls", exercises_only, None),
        ("variante de titre", variant, "cellule 0"),
        ("reponses hors fenetre", outside_window, "cellule 0"),
    ]
    failures = []
    for label, cells, expected in cases:
        found = find_end_block(cells)
        flagged = None
        if found is not None:
            index, level, title_line = found
            if not has_answers(block_text(cells, index, level, title_line)):
                flagged = "cellule %d" % index
        if flagged != expected:
            failures.append("%s : attendu %r, obtenu %r" % (label, expected, flagged))
    if failures:
        for failure in failures:
            sys.stderr.write("ECHEC %s\n" % failure)
        return 1
    sys.stdout.write("self-test OK (%d cas)\n" % len(cases))
    return 0


def main(argv: Optional[List[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="sortie structuree")
    parser.add_argument("--fail", action="store_true", help="code de sortie 1 si constat")
    parser.add_argument("--series", help="restreint le balayage a une serie")
    parser.add_argument("--root", default=NOTEBOOK_ROOT, help="racine du corpus")
    parser.add_argument("--self-test", action="store_true", help="controle interne")
    args = parser.parse_args(argv)

    if args.self_test:
        return self_test()

    findings = scan_corpus(args.root, args.series)
    if args.json:
        payload = {
            "count": len(findings),
            "by_series": {},
            "findings": findings,
        }
        for finding in findings:
            payload["by_series"].setdefault(finding["series"], []).append(
                os.path.relpath(finding["path"], REPO_ROOT).replace(os.sep, "/")
            )
        sys.stdout.write(json.dumps(payload, ensure_ascii=False, indent=1) + "\n")
    else:
        sys.stdout.write(report(findings) + "\n")
    if args.fail and findings:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
