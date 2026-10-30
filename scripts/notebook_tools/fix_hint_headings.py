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
    # Indice : X        ->      `# Indice` : X

Deux formes sont couvertes : le titre **imbrique** dans une puce ou une citation
(``- # Indice``), et le titre **nu** hors de tout conteneur (``# Indice``). Pour
la forme nue, deux conditions separent un commentaire d'exercice recopie d'une
vraie section : le **deux-points** (marqueur + corps), et le **niveau h1**. Le
niveau est indispensable -- mesure du 2026-10-25 : sur 142 candidats nus, les 20
de niveau h2-h4 sont tous de vraies sections (``### Solution : Plugins``,
``## Step 1: Load USDCAD Price Data``), et les backticker casserait le rendu.

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

Il ne touche pas non plus un titre de marqueur **de niveau h2-h4**
(``### Solution : ...``, ``### Note : ...``) : a ce niveau le marqueur introduit
une section, pas une ligne d'indice.

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

# Un titre de marqueur NU, hors de tout conteneur (#22477) : la ligne commence
# directement par les dieses. Deux conditions, et la seconde a ete mesuree.
#
# 1. Le **deux-points** separe ``# Indice : X`` (marqueur + corps) de
#    ``### Indices`` -- la section legitime de ``QC-Py-02-Platform-Fundamentals``
#    (Principe / Objectif / Indices) que ce script ne touche pas.
#
# 2. Le **niveau h1 seulement**. Le deux-points seul ne suffit pas : mesure du
#    2026-10-25 sur 1648 carnets, 142 titres de marqueur nus candidats, dont 20
#    de niveau h2-h4 -- et ces 20 sont TOUS de vraies sections
#    (``#### Etape 1 : creer un fichier Lean`` dans ``Lean-01-Setup-Lean``,
#    ``### Solution : Plugins`` dans ``Lean-09-SK-Multi-Agents``, ``### Solution :
#    Shrinkage (Ledoit-Wolf)`` dans ``QC-Py-21``, ``## Step 1: Load USDCAD Price
#    Data`` dans le quantbook ``research.ipynb``, ``### Note : mode batch`` dans
#    ``fort-boyard-python`` et son sibling ``_en``). Les backticker transformerait
#    un titre de section en ligne de code : une regression de rendu, pas une
#    reparation. Les 122 restants sont tous de niveau h1 et forment des blocs
#    consecutifs d'indices/etapes dans une cellule d'exercice -- la signature
#    exacte du commentaire Python recopie (defaut #22446).
NAKED_MARKER_HEADING = re.compile(r"^(#\s+)(.+?)(\s*):(.*)$")


def _fix_naked(line: str) -> str | None:
    """Titre de marqueur nu : ``# Indice : X`` -> ``` `# Indice` : X ```.

    Seul le marqueur recoit des backticks ; le corps de la ligne est rendu tel
    quel (invariant de round-trip : retirer les backticks redonne la ligne
    d'origine a l'identique).
    """
    m = NAKED_MARKER_HEADING.match(line)
    if not m:
        return None
    open_hashes, head, before_colon, rest = m.groups()
    if head.startswith("`"):
        return None
    if not MARKER.match(head):
        return None
    return "`" + open_hashes + head + "`" + before_colon + ":" + rest



def _fix_line(line: str) -> str | None:
    """Rend la ligne reparee, ou None si la ligne n'est pas concernee."""
    m = CONTAINER_HEADING.match(line)
    if not m:
        return _fix_naked(line)
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
        # ``newline="\\n"`` n'est pas cosmetique : sans lui, ``write_text`` traduit
        # chaque ``\n`` en ``os.linesep`` et reecrit TOUT le fichier en CRLF sur
        # Windows (mesure du 2026-10-25 : 1955 lignes remplacees pour 4 lignes
        # reparees). Le depot est en LF ; un diff de 2000 lignes noierait le fix
        # et le fichier partirait en CRLF. Avec cette option le rendu
        # ``json.dumps(indent=1)`` est byte-identique a la forme du corpus.
        path.write_text(json.dumps(nb, ensure_ascii=False, indent=1) + "\n",
                        encoding="utf-8", newline="\n")
    return n, report


# --- controle positif : le detecteur DOIT tirer sur le connu-mauvais ---------
_CTRL_BAD = "- # Indice : calculez X"
_CTRL_OK = "- `# Indice` : calculez X"
_CTRL_SECTION = "### Indices"
assert _fix_line(_CTRL_BAD) == "- `# Indice` : calculez X", "CONTROLE: aveugle au connu-mauvais"
assert _fix_line(_CTRL_OK) is None, "CONTROLE: tire sur la forme deja saine"
assert _fix_line(_CTRL_SECTION) is None, "CONTROLE: tire sur un titre de section legitime"

# #22477 : le meme marqueur, ecrit NU (hors conteneur). Le niveau h1 est requis
# (cf. le commentaire de NAKED_MARKER_HEADING) : les controles ci-dessous
# pinnent les deux bords -- ce qui doit tomber, et ce qu'une regle trop large
# casserait.
_CTRL_NAKED_BAD = "# Indice : calculez X"
_CTRL_NAKED_STEP = "# Etape 1 : ouvrir le fichier"
_CTRL_NAKED_SECTION = "# Introduction : vue d'ensemble du probleme"
# Les 20 sections legitimes mesurees au niveau h2-h4 : elles doivent rester des
# titres. Ce sont les faux positifs qu'une regle « deux-points seul » produirait.
_CTRL_LEGIT_SECTIONS = (
    "#### Etape 1 : creer un fichier Lean",
    "### Solution : Plugins",
    "### Solution : Shrinkage (Ledoit-Wolf)",
    "## Step 1: Load USDCAD Price Data",
    "### Note : mode batch",
    "### Note: batch mode",
)
assert _fix_line(_CTRL_NAKED_BAD) == "`# Indice` : calculez X", "CONTROLE: aveugle au marqueur NU"
assert _fix_line(_CTRL_NAKED_STEP) == "`# Etape 1` : ouvrir le fichier", "CONTROLE: nu, marqueur numerote"
assert _fix_line("`# Indice` : calculez X") is None, "CONTROLE: nu deja protege"
# Un titre NU non-marqueur garde son role de section : le deux-points seul ne
# suffit pas, il faut AUSSI que le segment soit un marqueur d'exercice.
assert _fix_line(_CTRL_NAKED_SECTION) is None, "CONTROLE: tire sur une section nue non-marqueur"
for _s in _CTRL_LEGIT_SECTIONS:
    assert _fix_line(_s) is None, "CONTROLE: backticke une section legitime h2-h4 : %r" % _s


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
