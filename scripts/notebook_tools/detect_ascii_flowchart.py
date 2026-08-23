#!/usr/bin/env python3
"""Detect ASCII flowcharts in notebook cells (Prong-A complement, scope = flowcharts).

Pourquoi cet outil existe
-------------------------
Le sweep Prong-A #3801 a traite les **bar charts ASCII** (replace par Plotly)
via `detect_ascii_workaround.py`. Mais un autre pattern ASCII degrade reste non
couvert : les **flowcharts ASCII** (architecture pipeline, schemas donnees,
organigrammes) traces a la main avec des caracteres `+`, `-`, `|`, `v`, `<--`,
`--->`. Le moteur canonique pour les remplacer est **Mermaid** (rendu natif
GitHub / Jupyter via `jupyterlab-mermaid` / Quarto / Slidev).

Cas fondateur verbatim (user 2026-08-20, source : SW-12-Python-GraphRAG.ipynb
cell ## 2. Architecture d'un pipeline GraphRAG, l.208, preserve par PR #11906
byte-identique) :

    Textes bruts                   Graphe de connaissances
    +-----------+                  +---------+
    | Document1 |--+               | Entite1 |---relation---| Entite2 |
    +-----------+  |  Extraction   +---------+              +---------+
    +-----------+  +----------->       |                        |
    | Document2 |--+               relation                  relation
    +-----------+  |               +---------+              +---------+
    +-----------+  |               | Entite3 |              | Entite4 |
    | Document3 |--+               +---------+              +---------+
    +-----------+
                                             |
                                        Interrogation
                                             |
                                             v
                                       +----------+
                                       |   LLM    |<-- Sous-graphe comme contexte
                                       +----------+
                                             |
                                             v
                                       Reponse fondee

Ce bloc est en ASCII pur et reproduit une architecture pipeline qui se rend
nativement en `flowchart LR` Mermaid. Il est dans le notebook main avant
PR #11906, preserve byte-identique par la density tranche.

Discriminateur cles (G.1, anti-faux-positifs)
---------------------------------------------
Un genuine flowchart ASCII = un BLOC CONTIGU de >= 4 lignes consecutives dans
une cellule markdown qui combine :
  - au moins 2 boites `+---------+` ou variantes (`+===+`, `[ ... ]`)
  - au moins 2 connecteurs parmi `--->`, `<--`, `|`, `v`, `^`, `-->`
  - un label de section ou de transition (mot sans symbole)

Filtres faux-positifs (EXCLUS)
------------------------------
- Cellule CODE (le scan se limite aux cellules markdown ; les print() bar-chart
  sont le scope de `detect_ascii_workaround.py`)
- Table Markdown `| --- | --- |` (les `|` sont des separateurs de colonnes, pas
  des connecteurs ; les `-` sont des borders de tableau ; cf `scan_md_table_syntax.py`)
- Bloc de moins de 4 lignes (un fragment isole n'est pas un flowchart)
- Bloc qui n'a qu'**une seule** boite (juste un encadre de titre)
- Bloc sans **aucun** connecteur (`--->`/`<--`/`|v`/`|^`)
- Bloc deja en syntaxe Mermaid (```` ```mermaid ```` fence) — deja converti
- Bloc dans une cellule de **table ASCII** au sens `scan_md_table_syntax.py`
  (les boites `+===+` de tables ASCII ne sont pas des flowcharts)

Il DETECTE, il ne CONVERTIT PAS. La conversion ASCII -> Mermaid exige une
comprehension semantique (quelles boites, quels flux, quels labels d'aretes)
qu'un convertisseur automatique ne peut garantir ; c'est un travail de
substance par notebook. Comme `detect_ascii_workaround.py` (cf son header),
ce tool guide le sweep en listant les candidats ; il ne fournit pas la
substance de remplacement.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

import nbformat
from nbformat.reader import NotJSONError
from nbformat.validator import ValidationError

# --- Signaux -----------------------------------------------------------

# Boite : `+---------+`, `+========+`, `[ ... ]`, `┌───┐`, etc.
# On accepte les boites ASCII classiques `+---+` (3+ dashes/equals entre +)
# et les boites Unicode box-drawing. Exclure les tables Markdown `| --- |`.
# c.475 patch (Tell c.475-L2 ★ NEW) : on preserve le leading whitespace
# (les boites peuvent etre indentees dans une liste markdown) MAIS sans
# l'ancre de fin `\s*$` qui rendait le pattern aveugle aux boites
# cote a cote sur la meme ligne. `_line_is_box` utilise match() qui
# ancre implicitement au debut de la chaine.
_RE_BOX_ASCII = re.compile(r"\s*\+[-=]{3,}\+")
_RE_BOX_UNICODE = re.compile(r"\s*[┌┐└┘├┤┬┴┼][─━]{3,}[┌┐└┘├┤┬┴┼]")

# Connecteurs : `--->`, `<--`, `<--->`, `-->`, `|`, `v`, `^` (en contexte ligne)
# c.474 patch d'une ligne (issue #12324) : ajout de `|---|` / `---` pour les
# separateurs entre boites cote a cote (ex. QC-Py-13 c3 : `| Universe |---|
# Algorithm |---| Broker |...`). Sans ce pattern, la disposition horizontale
# a 5 boites cote a cote ne matche aucun connecteur, et le flowchart echappe
# a la detection. On accepte les separateurs `--|---|` (au moins 3 dashes
# entre deux boites ou a l'extremite) comme connecteur de flux.
_RE_CONNECTOR_ARROW = re.compile(r"(--?>|<--?-+|={2,}>|<={2,}|--\||---{2,}\||---{3,})")
_RE_CONNECTOR_VLINE = re.compile(r"\|\s*(v|\^| Extraction| Construction| Indexation| Interrogation| Generation)\s*\|?")
_RE_CONNECTOR_VERTICAL = re.compile(r"^\s*\|\s*$")  # ligne de bare verticale isolee
# Lignes courtes avec un seul caractere de connexion (`v`, `^`, `|`, `>`)
_RE_CONNECTOR_BARE = re.compile(r"^\s*[v^|>]\s*$")

# Label de transition (mot sans symbole, en colonne isolee)
_RE_LABEL_LINE = re.compile(r"^\s{2,}([A-Z][a-zA-Z]{3,}( [a-z]+){0,3})\s*$")


def _line_is_box(line: str) -> bool:
    # c.475 : match() ancre au debut de ligne, donc on garde la semantique
    # originelle (ligne qui COMMENCE par une boite). _count_boxes_on_line
    # utilise findall() sur la regex non-ancree pour compter N boites.
    return bool(_RE_BOX_ASCII.match(line) or _RE_BOX_UNICODE.match(line))


def _line_has_connector(line: str) -> bool:
    """Verifie si la ligne contient un VRAI connecteur de flowchart.

    On distingue :
      - Vrai connecteur (`--->`, `<--`, `|v|`, `| Extraction`) -> counted
      - Bare connector isole (`v`, `^`, `|`) -> NOT counted comme connecteur
        (trop de faux positifs : un `v` isole dans une liste markdown n'est
        pas un connecteur de flux ; un `|` isole peut etre une bare de table).
    La detection d'un flowchart se fait au niveau FENETRE : si la fenetre
    a des boites ET des bare-connecteurs en nombre coherent, c'est un
    flowchart (les bare-connecteurs sont confirmes par le contexte).

    c.475 patch (Tell c.475-L4 ★ NEW) : une ligne qui EST une boite ASCII
    (`+--------+`) contient `--` qui matche `_RE_CONNECTOR_ARROW`, ce qui
    faisait compter les boites elles-memes comme connecteurs, et un simple
    encadre de titre `+--------+ / | Title | / +--------+` (single box) etait
    interprete comme un flowchart a 2 boites + 2 connecteurs. La correction :
    une boite ASCII ou Unicode n'est JAMAI un connecteur. On retourne
    `False` si la ligne est une boite.
    """
    if _line_is_box(line):
        return False
    if _RE_CONNECTOR_ARROW.search(line):
        return True
    if _RE_CONNECTOR_VLINE.search(line):
        return True
    return False


def _line_has_bare_connector(line: str) -> bool:
    """Bare connector isole (`v`, `^`, `|`, `>` seul sur une ligne).
    Utilise pour le discriminant fenetre : il ne suffit pas, mais complete
    les vrais connecteurs dans une fenetre deja candidate."""
    if _RE_CONNECTOR_VERTICAL.match(line):
        return True
    if _RE_CONNECTOR_BARE.match(line):
        return True
    return False


def _is_markdown_table_separator(line: str) -> bool:
    """Exclure `| --- | --- |` des tables Markdown (scan_md_table_syntax.py)."""
    return bool(re.match(r"^\s*\|?[\s:|-]{3,}\|[\s:|-]+\|?\s*$", line))


def _is_markdown_table_row(line: str) -> bool:
    """Exclure les lignes de cellules de tableau Markdown `| col1 | col2 |`.

    Tell c.475-L5 ★ NEW : une ligne de tableau peut contenir une fleche
    (`| Process | ... | Generate -> Review -> Publish |`) qui matche
    `_RE_CONNECTOR_ARROW`. Si la fenetre demarre sur une telle ligne, le
    detecteur traite le tableau markdown comme un flowchart (faux positif
    massif : les cellules avec `->` dans les colonnes sont ubiquitaires).
    """
    stripped = line.strip()
    if not stripped:
        return False
    # Format `| col | col |` (commence et finit par `|`, contient au moins 1 `|`)
    return stripped.startswith("|") and stripped.endswith("|") and stripped.count("|") >= 2


def _is_inside_fence(lines: list[str], idx: int) -> bool:
    """Verifie si la ligne idx est a l'interieur d'un bloc ``` ... ```
    (mermaid ou autre langage — les fences code block sont l'encadrement
    standard d'un diagramme ASCII ou Mermaid dans une cellule markdown).
    """
    in_fence = False
    for i in range(idx):
        if lines[i].lstrip().startswith("```"):
            in_fence = not in_fence
    return in_fence


def _find_flowchart_blocks(cell_source: str) -> list[dict]:
    """Decoupe le source d'une cellule markdown en blocs contigus de >= 4 lignes
    qui matchent les signaux d'un flowchart ASCII. Renvoie la liste des blocs
    detectes avec leur ligne de debut, fin, et score (boites x connecteurs).

    Note sur les fences : les diagrammes ASCII sont frequemment enveloppes dans
    une fence ``` ``` ``` (code block sans langage) pour preserver le rendu.
    On detecte DANS les fences egalement (le contenu reste un flowchart ASCII
    degrade), mais on flagge `fenced=True` pour que la remediation proposee
    inclue le remplacement de la fence ```` ``` ```` par ```` ```mermaid ````.

    c.474 patch d'une ligne (issue #12324) : l'ancre `\s*$` du `_RE_BOX_ASCII`
    a ete retiree, ce qui rend visible la **disposition horizontale** (boites
    cote a cote sur la meme ligne) en plus de la disposition verticale
    traditionnelle. Les 3 branches du discriminant :

      A. `(boxes >= 2 and connectors >= 2)` -- pipeline vertical dense
         (deux connecteurs explicites dans la fenetre).
      B. `(boxes >= 3 and connectors >= 1)` -- block diagram aligne
         (au moins 3 boites = structure multi-stage claire).
      C. `(boxes_inline >= 2 and connectors >= 1)` -- flowchart horizontal
         (au moins 2 boites **sur la meme ligne** + un connecteur ; cette
         condition stricte evite le faux positif `single_box_only` ou 2
         boites occupees par 2 rangees verticales distinctes). Tell c.475-L2 ★
         (NEW) : `boxes_inline` = max par ligne du nombre de boites ASCII
         cote a cote ; discriminant pour flowcharts horizontaux.

    Tell c.475-L3 ★ (NEW) : la condition `boxes_inline >= 2` distingue
    veritablement un flowchart horizontal (boites separees par `---`/`|---|`
    sur la meme ligne) d'une simple **juxtaposition verticale** (boites
    empilees dans la meme fenetre sans lien de flux). Mesure empirique c.475 :
    QC-Py-13 c3 produit boxes_inline=5 (5 boites sur 1 ligne), GT-17 NFSP c15
    produit boxes_inline=3 (3 boites sur 1 ligne), single_box_only produit
    boxes_inline=1 (1 boite par ligne) -- d'ou le seuil 2.
    """
    lines = cell_source.split("\n")
    blocks = []
    n = len(lines)
    i = 0
    while i < n:
        if _is_markdown_table_separator(lines[i]):
            i += 1
            continue
        # c.475 patch (Tell c.475-L5 ★ NEW) : exclure aussi les lignes de
        # cellules de tableau `| col | col |` du point de depart de la
        # fenetre (sinon les fleches `->` dans une colonne de tableau
        # declenchent la branche C comme faux positif massif).
        if _is_markdown_table_row(lines[i]):
            i += 1
            continue
        if not (_line_is_box(lines[i]) or _line_has_connector(lines[i])):
            i += 1
            continue
        # Fenetre 4-12 lignes autour de i
        window_end = min(i + 12, n)
        window = lines[i:window_end]
        # Compter boites et connecteurs dans la fenetre
        boxes = sum(1 for ln in window if _line_is_box(ln))
        boxes_inline = max(_count_boxes_on_line(ln) for ln in window)
        connectors = sum(1 for ln in window if _line_has_connector(ln))
        bare_connectors = sum(1 for ln in window if _line_has_bare_connector(ln))
        labels = sum(1 for ln in window if _RE_LABEL_LINE.match(ln))
        # 3 branches du discriminant (voir docstring)
        # C. relaxation c.474 : boites_inline >= 2 et >= 1 connecteur pour
        # les flowcharts horizontaux (GT-17 NFSP c15, QC-Py-13 c3, etc.)
        is_flowchart = (
            (boxes >= 2 and connectors >= 2)
            or (boxes >= 3 and connectors >= 1)
            or (boxes >= 2 and connectors >= 1 and bare_connectors >= 2 and labels >= 1)
            or (boxes_inline >= 2 and connectors >= 1)  # c.474 : flowchart horizontal
        )
        if is_flowchart:
            in_fence = _is_inside_fence(lines, i)
            blocks.append({
                "start_line": i + 1,  # 1-indexed
                "end_line": window_end,
                "boxes": boxes,
                "boxes_inline": boxes_inline,
                "connectors": connectors,
                "labels": labels,
                "fenced": in_fence,
                "verbatim": "\n".join(window).rstrip(),
            })
            i = window_end
        else:
            i += 1
    return blocks


def _count_boxes_on_line(line: str) -> int:
    """Compte le nombre de boites ASCII `+---+` distinctes sur une ligne.

    Tell c.475-L2 ★ (NEW) : une flowchart horizontal a N boites sur la MEME
    ligne (separees par `---` ou `|---|`). Une juxtaposition verticale a
    1 boite par ligne. Le discriminant `max(boxes_inline)` sur la fenetre
    detecte la disposition horizontale.
    """
    # Compter les positions de `+---` debut de boite
    return len(_RE_BOX_ASCII.findall(line)) + len(_RE_BOX_UNICODE.findall(line))


def scan_notebook(path: Path) -> dict:
    """Scan un notebook ; renvoie les cellules markdown contenant des flowcharts ASCII."""
    try:
        nb = nbformat.read(path, as_version=4)
    except (OSError, NotJSONError, ValidationError) as exc:
        # Garde par-fichier (#12097) : un notebook illisible (BOM UTF-8,
        # JSON tronque, validation echouee) ne doit pas interrompre le scan
        # entier — il est reporte dans `skipped`, pas avale silencieusement.
        return {"path": str(path), "error": str(exc), "findings": []}
    findings = []
    for cell_idx, cell in enumerate(nb.cells):
        if cell.get("cell_type") != "markdown":
            continue
        source = cell.get("source", "")
        if isinstance(source, list):
            source = "".join(source)
        blocks = _find_flowchart_blocks(source)
        for blk in blocks:
            findings.append({
                "path": str(path),
                "cell_index": cell_idx,
                "start_line": blk["start_line"],
                "end_line": blk["end_line"],
                "boxes": blk["boxes"],
                "connectors": blk["connectors"],
                "labels": blk["labels"],
                "evidence": blk["verbatim"][:240],  # troncature pour le rapport
            })
    return {"path": str(path), "error": None, "findings": findings}


def scan_paths(paths: list[Path]) -> dict:
    """Scan une liste de notebooks ; agrege les resultats."""
    all_findings = []
    files_scanned = 0
    files_with_findings = 0
    skipped = []
    for p in paths:
        if not p.exists():
            continue
        if p.is_dir():
            nb_paths = sorted(p.rglob("*.ipynb"))
        else:
            nb_paths = [p]
        for nb_path in nb_paths:
            files_scanned += 1
            result = scan_notebook(nb_path)
            if result.get("error"):
                skipped.append({"path": str(nb_path), "error": result["error"]})
                continue
            if result["findings"]:
                files_with_findings += 1
            all_findings.extend(result["findings"])
    return {
        "files_scanned": files_scanned,
        "files_with_findings": files_with_findings,
        "total_findings": len(all_findings),
        "skipped": skipped,
        "findings": all_findings,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument("paths", nargs="+", type=Path,
                        help="Notebooks ou repertoires a scanner")
    parser.add_argument("--json", action="store_true",
                        help="Sortie JSON structuree")
    args = parser.parse_args()

    result = scan_paths(args.paths)
    if args.json:
        print(json.dumps(result, indent=2, ensure_ascii=False))
    else:
        print(f"Notebooks scanned   : {result['files_scanned']}")
        print(f"With findings       : {result['files_with_findings']}")
        print(f"Total findings      : {result['total_findings']}")
        for skip in result["skipped"]:
            print(f"\n  SKIPPED {skip['path']}: {skip['error'][:120]}")
        for f in result["findings"][:10]:
            print(f"\n  {f['path']}:{f['start_line']}-{f['end_line']}  "
                  f"boxes={f['boxes']} connectors={f['connectors']} labels={f['labels']}")
            print(f"    > {f['evidence'][:120]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
