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
_RE_BOX_ASCII = re.compile(r"^\s*\+[-=]{3,}\+\s*$")
_RE_BOX_UNICODE = re.compile(r"^\s*[┌┐└┘├┤┬┴┼][─━]{3,}[┌┐└┘├┤┬┴┼]")

# Connecteurs : `--->`, `<--`, `<--->`, `-->`, `|`, `v`, `^` (en contexte ligne)
_RE_CONNECTOR_ARROW = re.compile(r"(--?>|<--?-+|={2,}>|<={2,})")
_RE_CONNECTOR_VLINE = re.compile(r"\|\s*(v|\^| Extraction| Construction| Indexation| Interrogation| Generation)\s*\|?")
_RE_CONNECTOR_VERTICAL = re.compile(r"^\s*\|\s*$")  # ligne de bare verticale isolee
# Lignes courtes avec un seul caractere de connexion (`v`, `^`, `|`, `>`)
_RE_CONNECTOR_BARE = re.compile(r"^\s*[v^|>]\s*$")

# Label de transition (mot sans symbole, en colonne isolee)
_RE_LABEL_LINE = re.compile(r"^\s{2,}([A-Z][a-zA-Z]{3,}( [a-z]+){0,3})\s*$")


def _line_is_box(line: str) -> bool:
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
    """
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
    """
    lines = cell_source.split("\n")
    blocks = []
    n = len(lines)
    i = 0
    while i < n:
        if _is_markdown_table_separator(lines[i]):
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
        connectors = sum(1 for ln in window if _line_has_connector(ln))
        bare_connectors = sum(1 for ln in window if _line_has_bare_connector(ln))
        labels = sum(1 for ln in window if _RE_LABEL_LINE.match(ln))
        # Critere : >= 2 boites ET >= 2 vrais connecteurs (les v/^/| isoles
        # sont trop generiques, on les accepte SEULEMENT en complement dans
        # une fenetre deja candidate).
        # OU : >= 2 boites ET >= 1 vrai connecteur ET >= 2 bare-connecteurs
        # (pipeline vertical : `Box | v Box | v Box`).
        # OU : >= 3 boites ET >= 1 vrai connecteur (block diagramme aligne).
        is_flowchart = (
            (boxes >= 2 and connectors >= 2)
            or (boxes >= 3 and connectors >= 1)
            or (boxes >= 2 and connectors >= 1 and bare_connectors >= 2 and labels >= 1)
        )
        if is_flowchart:
            in_fence = _is_inside_fence(lines, i)
            blocks.append({
                "start_line": i + 1,  # 1-indexed
                "end_line": window_end,
                "boxes": boxes,
                "connectors": connectors,
                "labels": labels,
                "fenced": in_fence,
                "verbatim": "\n".join(window).rstrip(),
            })
            i = window_end
        else:
            i += 1
    return blocks


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
