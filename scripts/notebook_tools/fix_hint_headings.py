#!/usr/bin/env python3
"""Repare la regle ``heading_in_list`` de ``detect_markdown_rendering.py``.

Le defaut
---------
Une ligne de commentaire Python recopiee telle quelle dans une cellule
**markdown**, sous une puce, est un titre ATX pour CommonMark :

    - # Indice : cout = (input_tokens/1000) * prix_in

rend un ``<h1>`` a 29 px **a l'interieur d'une puce**. Mesure du 2026-08-21 sur
``QC-Py-26-LLM-Trading-Signals.ipynb`` (rendu GitHub, ``getComputedStyle``) :
6 titres H1 a ``29.0304px``, la plus grosse police de la page, pour des
commentaires d'exercice. Le meme notebook ecrit ailleurs la forme correcte --
``- `# Indice` : ...`` -- ce qui rend l'incoherence interne au fichier.

La reparation
-------------
Entourer le marqueur de backticks : le ``#`` cesse d'ouvrir un titre et la ligne
rend en ``<code>``, taille du corps de texte. C'est la forme deja employee par
les cellules saines du corpus, pas une invention de ce script.

    - # Indice : X      ->      - `# Indice` : X

**Invariant de round-trip** : le script n'INSERE que des backticks. Aucun
caractere n'est supprime ni reordonne ; le contenu prive de backticks est
byte-identique avant et apres. Cet invariant est verifie systematiquement sur
chaque cellule touchee -- il n'y a pas de drapeau a passer -- et le script
refuse d'ecrire s'il est viole.

Ce que le script NE fait PAS
---------------------------
Il ne touche pas ``oversized_hint``. Cette regle-la matche aussi des titres de
section legitimes -- ``### Indices`` dans ``QC-Py-02-Platform-Fundamentals``
est une vraie section (Principe / Objectif / Indices), pas un commentaire fuite.
Reparer les deux avec le meme geste casserait le second cas.

Usage
-----
    python scripts/notebook_tools/fix_hint_headings.py --scan  <notebook|dir>
    python scripts/notebook_tools/fix_hint_headings.py --apply <notebook|dir>
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

# Un titre ATX imbrique dans une puce ou une citation : "- # X", "* ## X",
# "1. # X", "> # X". Le groupe 1 est le conteneur, 2 les diese, 3 le texte.
CONTAINER_HEADING = re.compile(r"^(\s{0,3}(?:[-*+]\s+|\d+[.)]\s+|>\s+)+)(#{1,6})\s+(.+?)\s*$")

# Le marqueur a proteger : le premier segment avant " : " ou ", " s'il ressemble
# a un marqueur d'exercice. Sinon on protege le mot-cle seul.
MARKER = re.compile(
    r"^(Indice|Indices|Astuce|Hint|TODO|Note|Etape|Étape|Step|Solution)"
    r"(\s+\d+)?\s*$",
    re.IGNORECASE,
)


def _fix_line(line: str) -> str | None:
    """Rend la ligne reparee, ou None si la ligne n'est pas concernee."""
    m = CONTAINER_HEADING.match(line)
    if not m:
        return None
    container, hashes, text = m.group(1), m.group(2), m.group(3)
    # Deja protege ? (" - `# Indice` : ..." ne matche pas CONTAINER_HEADING,
    # mais on reste defensif si le texte contient deja des backticks en tete.)
    if text.startswith("`"):
        return None
    # Couper au premier " : " -- le marqueur est a gauche, le corps a droite.
    parts = re.split(r"\s*:\s*", text, maxsplit=1)
    head = parts[0]
    rest = parts[1] if len(parts) > 1 else None
    if not MARKER.match(head):
        # Pas un marqueur d'exercice reconnu : on ne devine pas. Le titre
        # imbrique est peut-etre intentionnel -- le signaler, ne pas le corriger.
        return None
    fixed_head = "`" + hashes + " " + head + "`"
    return container + fixed_head + (" : " + rest if rest is not None else "")


def _strip_backticks(s: str) -> str:
    return s.replace("`", "")


def scan_cell(src: str) -> list[tuple[int, str, str]]:
    out = []
    for i, line in enumerate(src.split("\n")):
        fixed = _fix_line(line)
        if fixed is not None:
            out.append((i, line, fixed))
    return out


def process(path: Path, apply: bool) -> tuple[int, list[str]]:
    nb = json.loads(path.read_text(encoding="utf-8"))
    report: list[str] = []
    n = 0
    changed = False
    for ci, cell in enumerate(nb.get("cells", [])):
        if cell.get("cell_type") != "markdown":
            continue
        src = "".join(cell["source"])
        hits = scan_cell(src)
        if not hits:
            continue
        lines = src.split("\n")
        for idx, before, after in hits:
            lines[idx] = after
            report.append("  %s cell#%-3d %s" % (path.name, ci, before.strip()[:88]))
            n += 1
        new_src = "\n".join(lines)
        # Invariant de round-trip : seuls des backticks ont ete inseres.
        if _strip_backticks(new_src) != _strip_backticks(src):
            raise SystemExit(
                "INVARIANT VIOLE sur %s cell#%d : le contenu a change au-dela des backticks"
                % (path, ci)
            )
        if apply:
            parts = new_src.split("\n")
            if parts and parts[-1] == "":
                # la cellule se terminait par un saut de ligne : ne pas
                # fabriquer un element "" final que nbformat n'ecrit jamais
                cell["source"] = [l + "\n" for l in parts[:-1]]
            else:
                cell["source"] = [l + "\n" for l in parts[:-1]] + [parts[-1]]
            changed = True
    if apply and changed:
        path.write_text(json.dumps(nb, ensure_ascii=False, indent=1) + "\n", encoding="utf-8")
    return n, report


# --- controle positif : le detecteur DOIT tirer sur le connu-mauvais ---------
_CTRL_BAD = "- # Indice : calculez X"
_CTRL_OK = "- `# Indice` : calculez X"
_CTRL_SECTION = "### Indices"
assert _fix_line(_CTRL_BAD) == "- `# Indice` : calculez X", "CONTROLE: aveugle au connu-mauvais"
assert _fix_line(_CTRL_OK) is None, "CONTROLE: tire sur la forme deja saine"
assert _fix_line(_CTRL_SECTION) is None, "CONTROLE: tire sur un titre de section legitime"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("targets", nargs="+", type=Path)
    g = ap.add_mutually_exclusive_group()
    g.add_argument("--scan", action="store_true", help="rapporter sans ecrire (defaut)")
    g.add_argument("--apply", action="store_true", help="ecrire les corrections")
    args = ap.parse_args()

    files: list[Path] = []
    for t in args.targets:
        files.extend(sorted(t.rglob("*.ipynb")) if t.is_dir() else [t])

    total = 0
    for f in files:
        try:
            n, rep = process(f, args.apply)
        except json.JSONDecodeError as exc:
            print("  SKIP %s (json: %s)" % (f, exc), file=sys.stderr)
            continue
        if n:
            print("\n".join(rep))
            total += n
    verb = "corrigee(s)" if args.apply else "trouvee(s) (utiliser --apply)"
    print("\n%d occurrence(s) %s dans %d fichier(s)" % (total, verb, len(files)))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
