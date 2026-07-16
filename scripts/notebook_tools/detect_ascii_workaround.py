#!/usr/bin/env python3
"""Detecte les visualisations ASCII workaround (Prong-A, registre #3801).

Pourquoi cet outil existe
-------------------------
Le registre #3801 (SOTA axe-2, Prong-A) accumule des corrections manuelles de
visualisations ASCII degenerees remplacees par le vrai outil (matplotlib/Plotly) :
#6603 (App-7-Wordle bar), #6659 (PyMC-12 shrinkage bar), #6826 (App-8 MiniZinc
bars), #6829 (GT-4c Nash simplex trajectory), #6834 (PyMC-17 Kalman trajectory),
#6837 (Search-11b ABC limit-sweep). Chaque defaut est decouvert a la main, ad-hoc,
par le worker qui tombe dessus. Plusieurs scans systematiques (po-2025 c.542/c.543)
ont MANQUE des defauts connus (PyMC-12, App-7-Wordle) parce que les patterns de
commentaires varient. Ce tool formalise la moitie DETECTION du sweep Prong-A :
il liste les cellules code qui dessinent des charts/bars/trajectoires en ASCII
alors qu'un vrai outil de charting est invocable.

Il DETECTE, il ne CONVERTIT PAS. La conversion (ASCII -> matplotlib/Plotly) est
un travail de substance par notebook (re-exec, fidelite des donnees, C548-L2 pour
.NET) qui reste manuel. Cet outil guide le sweep en listant les candidats.

Discriminateur cles (G.1, lecons des faux positifs)
---------------------------------------------------
Un genuine Prong-A defect = une cellule code qui produit une visualisation
QUANTITATIVE (bar chart d'une valeur scalaire, trajectoire de donnees,
distribution) en ASCII via la multiplication d'un caractere par une LONGUEUR
CALCULEE depuis un scalaire de donnees. Ex canonique (PyMC-17 cell6) :

    def bar(v, c):
        n = int(round((v - lo) / (hi - lo) * W))   # longueur calculee depuis un scalaire
        return c * n                                # caractere * longueur
    print(f"VRAI {bar(trueState[t], '|')}")         # data serie rendue en barres

Le discriminateur vs une viz legitime (grille/plateau/board) : la viz legitime
itere une MATRICE 2D d'etats discrets et choisit un caractere PAR ETAT (boucle
imbriquee `for row in grid: for cell in row: print(state_char(cell))`). La viz
defect multiplie un caractere par une LONGUEUR DERIVEE D'UN SCALAIRE (bar chart).
Un board Sudoku / un plateau Demineur / un chemin sur grille = etat discret =
ASCII legitime. Un histogramme de scores / une trajectoire Kalman / des bars de
comparaison = donnees quantitatives = defect si pas de vrai chart.

Filtres faux-positifs (EXCLUS)
-----------------------------
- Cellule QUI utilise un vrai charting lib (matplotlib/pyplot/plt./plotly/altair/
  seaborn/bokeh/Formatter.Register(PlotlyHtml)) -> pas un workaround, meme si un
  companion ASCII quick-check existe (pattern ICT-16 cell10+11, #5736).
- Cellule purement markdown (ASCII art de decoration, tables ASCII).
- Viz d'ETAT discret (grille/plateau/board/maze/labyrinthe/carte) : la signature
  est une boucle sur une matrice d'etats, pas une bar-length depuis un scalaire.
- ASCII art de TITRE / box-drawing de decoration sans donnees.
- TABLE SEPARATORS : `print("-" * 50)`, `print("=" * len(header))`,
  `"  ".join("-" * width for width in w)` (SL-6 row border loop) -- le caractere
  est un SEPARATEUR (- = + . _) et/ou la longueur est une constante / une largeur
  de colonne, pas un scalaire de donnees. Seuls les caracteres de REMPLISSAGE de
  barre (# * | et blocs █▓░) multiplies par une variable de donnees sont retenus.
- HELPERS MATH : `return a * b`, `return slope*time+intercept` (regression),
  `return K*np.exp(...)` (Black-Scholes), `return A*n+np.sum(...)` (Ackley) -- ils
  multiplient des VARIABLES, jamais un caractere de dessin. La presence d'un
  litteral-caractere multiplie est ce qui distingue une barre ASCII d'un calcul.

L'outil est CONSERVATEUR : il prefer la precision au rappel. Un hit rapporte est
fortement suspect d'etre un genuine defect. La baseline validee c.543 sur 935
notebooks pedagogiques = **1 genuine defect** (PyMC-17 cell6, #6834 OPEN). Les
defects subtils hors-scope (voir "Known blind spots") echappent a l'outil mais
sont documentes pour investigation manuelle.

Known blind spots (valides c.543, a completer au fil des rencontres)
-------------------------------------------------------------------
- TABLES DE NOMBRES : une cellule qui imprime des resultats numeriques en tableau
  texte (`limit | f moyen | std`) alors qu'un line-chart serait plus lisible
  (#6837 Search-11b sweep). Ce n'est PAS le pattern bar/char-repeat -- c'est un
  jugement pedagogique plus large et bien plus bruite (la plupart des tables de
  resultats sont legitimes). Hors scope par design.
- FORMES HELPER C# : `new string('-', n)`, methodes .NET repetant un char. Le
  detecteur helper-call couvre le `def` Python ; les idiom C# (.NET Interactive)
  ne sont pas reconnus. La majorite des defects C# connus (#6826 App-8, #6829
  GT-4c) sont deja fixes ; le residuel est a verifier manuellement.
- CARACTERE VIA VARIABLE : `c = '#'; print(c * n)` (le char est une variable, pas
  un litteral a l'endroit de la multiplication) -- rate. Pattern rare.
- BARRES EN CARACTERE SEPARATEUR : un vrai histogramme dessine en `-` ou `=`
  (rare ; la convention est `#`/`*`/blocks) -- exclu par le filtre separateur.
- Trajectoires sur grille 2D (Nash simplex) : risque de FP si la grille est un
  vrai board de jeu, OU de faux-negatif si la trajectoire n'utilise pas le
  pattern bar-helper.

Comment ca marche
-----------------
Pour chaque cellule code, l'outil cherche un CARACTERE DE REMPLISSAGE DE BARRE
(# * | blocs) repete par une longueur DERIVEE DE DONNEES, sous 3 formes :
  (1) inline : `'#' * score` / `'|' * n` (litteral-char de donnees * variable) ;
  (2) helper literal : `return '#' * n` (renvoie un litteral-char repete) ;
  (3) helper-call : `def bar(v,c): return c*n` appele `bar(x, '|')` (analyses au
      niveau fonction -- relie le char du call-site au parametre retourne, forme
      canonique PyMC-17 cell6) ;
  ET (4) la cellule n'utilise PAS un charting lib ;
  ET (5) la cellule n'est PAS une viz d'etat discret dominante.
Chaque hit est rapporte avec index de cellule, signature detectee, et la ligne
de contexte. L'outil ne touche pas les notebooks : lecture seule.

Usage
-----
    python detect_ascii_workaround.py NB.ipynb                 # un notebook
    python detect_ascii_workaround.py --family Probas          # une famille
    python detect_ascii_workaround.py                           # tous les notebooks
    python detect_ascii_workaround.py NB.ipynb --json          # sortie machine
    python detect_ascii_workaround.py NB.ipynb --check         # exit 1 si hits (CI-ready)

Exit codes
----------
    0 -- aucun defect detecte (ou mode non --check)
    1 -- un ou plusieurs hits detectes (--check seulement)
    2 -- erreur (notebook illisible, famille introuvable)

Voir aussi
----------
- `detect_accent_stripping.py` (#6806) -- pattern de detecteur read-only + baseline
- `check_notebook_navlinks.py` (#6813) -- baseline honnete + filtres FP
- docs/ledgers/3801-sota-axe2.md -- registre Prong-A (verdicts SOTA)
- .claude/rules/sota-not-workaround.md -- Prong-A : vrai outil SOTA, pas workaround

Part of #3801 (EPIC SOTA axe-2).
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

# --- Charting libs (présence -> pas un workaround, même si ASCII companion) ---
CHARTING_LIB_RE = re.compile(
    r"\b(matplotlib|pyplot|plotly|altair|seaborn|bokeh|ggplot|chart\.js|d3)\b|"
    r"\bplt\.(show|subplots|figure|plot|scatter|bar|hist|imshow)|"
    r"Formatter\.Register\s*\(\s*typeof\s*\(\s*PlotlyHtml|"
    r"Plotly\.(newPlot|react|plot)|"
    r"<script[^>]*plotly|cdn\.plot\.ly|"
    r"\bgo\.(Figure|Scatter|Bar)\b",  # plotly.graph_objects
    re.IGNORECASE,
)

# --- Bar-char-multiplied-by-computed-length (BAR CHART semantics) ---
# Two alphabets: DATA-BAR FILL chars (hashes/stars/pipes/blocks = a filled bar
# representing a quantity) vs SEPARATOR chars (- = + . _ = table borders, axis
# lines, dividers). A `print("-" * width for width in w)` is a TABLE BORDER loop,
# not a data bar -- so the decisive signals use DATA_BAR_CHAR only.
BAR_CHAR = r"[#*=|._▀-▟\-+@]"          # broad drawing alphabet (reference)
DATA_BAR_CHAR = r"[#*|@█▓░▀-▟]"         # bar FILL chars (excludes separators)
# Builtins that, as a multiplier, mean FORMATTING (table border / cast), not data:
#   '-' * len(header)  /  '.' * int(x)  /  '#' * str(n)   -> separators, not bars.
_BUILTIN_MULT = r"(?:len|int|round|str|abs|min|max|sum|range|ord|chr)\b"
# (a) helper RETURNING a literal data-bar char repeated:  return '#' * n
#     Requires the char to be a STRING LITERAL -- math helpers (`return a * b`,
#     `return slope*time+intercept`, Black-Scholes, Ackley) multiply VARIABLES,
#     never a drawing-character literal. This is what tells a bar helper from math.
BAR_HELPER_RE = re.compile(
    rf"return\s+['\"]{DATA_BAR_CHAR}['\"]\s*\*\s*\w+", re.IGNORECASE
)
# (b) inline literal data-bar char * DATA variable (inside print/f-string):
#       '#' * score ,  '|' * n
#     EXCLUDES constant-width table separators ('-' * 50), len()-width borders
#     ('-' * len(header)), cast wrappers ('.' * int(x)) AND separator-char border
#     loops ('-' * width for width in w): the char must be a DATA-BAR fill, and the
#     multiplier a bare data variable (not a literal, not a builtin).
INLINE_BAR_RE = re.compile(
    rf"""['"]{DATA_BAR_CHAR}['"]\s*\*\s*(?!{_BUILTIN_MULT})(?!\d)[A-Za-z_]\w*""",
    re.IGNORECASE,
)
# (c) computed bar length from a scalar:  int(round(v * W))  or  * W / * width
#     ALONE this is weak (normalization `* scale`, regression slope use it too);
#     it is only actionable paired with (d) a bar char actually printed.
BAR_LENGTH_FROM_SCALAR_RE = re.compile(
    r"int\s*\(\s*round\s*\([^)]*\*\s*\w+\s*\)\s*\)|"   # int(round(v * W))
    r"\*\s*(W|width|scale|n_cols|cols|max_w)\b",         # * W / * width
    re.IGNORECASE,
)
# (d) The bar-HELPER-CALL form (canonical PyMC-17 cell6) is detected at function
#     level by `_bar_helper_call` below, not by a flat regex: a flat "char as a call
#     arg" pattern matches C# `new string('=', 60)` (constant separator), Python
#     `grid.get(nxt, "#")` (dict default) and dynamic-width borders -- none are data
#     bars. The real signal ties the call-site char literal to a function whose body
#     repeats a parameter: `def bar(v,c): return c * n` called as `bar(x, '|')`.

# --- ASCII-viz comment + quantitative context ---
ASCII_COMMENT_RE = re.compile(
    r"#.*\b(ascii|visualisation\s+(textuelle|ascii)|affichage\s+(textuel|ascii)|"
    r"tracer\s+ascii|dessin\s+ascii|graphe\s+ascii)\b",
    re.IGNORECASE,
)
QUANT_CONTEXT_RE = re.compile(
    r"\b(bar|bars|score|scores|trajectoir|trajectory|histogram|histogramme|"
    r"distribution|compar|comparaison|convergence|courbe|metric|metrique|"
    r"result|valeur|value|count|frequence|frequence|proportion|ratio|"
    r"shrinkage|gain|loss|reward|fitness|erreur|error|residu)\b",
    re.IGNORECASE,
)

# --- Discrete-state viz (LEGITIMATE ASCII) ---
# Nested loop over a grid/board matrix, char chosen by state (not bar-length).
GRID_BOARD_KEYWORD_RE = re.compile(
    r"\b(grille|plateau|board|sudoku|demineur|minesweeper|grid|maze|labyrinthe|"
    r"carte|map|chess|echiquier|damier|tetris| cellular|automate|cells?\s+state)\b",
    re.IGNORECASE,
)
# nested-loop printing per-cell state:  for row in X: for cell in row: ... print
NESTED_GRID_LOOP_RE = re.compile(
    r"for\s+\w+\s+in\s+\w+.*:\s*\n\s*for\s+\w+\s+in\s+\w+.*:",
    re.IGNORECASE | re.DOTALL,
)


def _cell_source(cell: dict) -> str:
    src = cell.get("source", "")
    if isinstance(src, list):
        return "".join(src)
    return src or ""


def _uses_charting_lib(src: str) -> bool:
    return bool(CHARTING_LIB_RE.search(src))


def _is_discrete_state_viz(src: str) -> bool:
    """Legitimate ASCII grid/board: nested loop over states, not bar-length-from-scalar."""
    has_grid_kw = bool(GRID_BOARD_KEYWORD_RE.search(src))
    has_nested_loop = bool(NESTED_GRID_LOOP_RE.search(src))
    # bar-length-from-scalar present -> leans data-viz even with grid kw
    has_bar_scalar = bool(BAR_LENGTH_FROM_SCALAR_RE.search(src))
    # Strong state-viz signal: grid keyword + nested loop + NO bar-scalar
    return has_grid_kw and has_nested_loop and not has_bar_scalar


def _bar_helper_call(src: str) -> str | None:
    """Detect the canonical ASCII bar-helper form (PyMC-17 cell6, #6834).

    A Python `def NAME(...params...): ... return <param> * <expr>` where `<param>`
    is a short identifier (c / ch / sym / char -- the drawing char) AND `NAME` is
    called somewhere with a STANDALONE bar-char-literal argument. The function's
    job is to repeat the char; that is what distinguishes it from math.

    Returns the matched param name, or None. Precisely excludes:
      - `new string('=', 60)` (C# constant separator -- not a Python def)
      - `grid.get(nxt, "#")` (dict default -- get() does not repeat a param)
      - math helpers `def ev(belief, r): return belief * r` -- `belief` is > 4 chars
        and ev() is never called with a char literal anyway.
    """
    for m in re.finditer(r"def\s+(\w+)\s*\(([^)]*)\)\s*:", src):
        name = m.group(1)
        params = []
        for p in m.group(2).split(","):
            p = p.strip().split("=")[0].split(":")[0].strip()
            if p and re.fullmatch(r"[A-Za-z_]\w{0,3}", p):  # 1-4 char ident (c/ch/sym/char)
                params.append(p)
        if not params:
            continue
        body = src[m.end(): m.end() + 800]
        call_re = re.compile(
            rf"\b{re.escape(name)}\s*\([^)]*[(,]\s*['\"]{DATA_BAR_CHAR}['\"]\s*[,)]"
        )
        if not call_re.search(src):
            continue
        for p in params:
            if re.search(rf"\breturn\s+{re.escape(p)}\s*\*", body):
                return p
    return None


def detect_cell(src: str) -> dict | None:
    """Return a finding dict if `src` (code cell) is a genuine Prong-A candidate, else None."""
    if not src.strip():
        return None
    if _uses_charting_lib(src):
        return None  # real charting lib present -> not a workaround
    if _is_discrete_state_viz(src):
        return None  # legitimate discrete-state grid/board

    signatures = []
    has_bar_helper = bool(BAR_HELPER_RE.search(src))      # return '#' * n (literal)
    has_inline_bar = bool(INLINE_BAR_RE.search(src))       # '#' * score (literal*var)
    has_bar_scalar = bool(BAR_LENGTH_FROM_SCALAR_RE.search(src))  # int(round(v*W)) / * W
    bar_param = _bar_helper_call(src)                       # def bar(v,c): return c*n; bar(x,'|')
    ascii_comment = bool(ASCII_COMMENT_RE.search(src))
    quant_context = bool(QUANT_CONTEXT_RE.search(src))

    # Decision (precision-first). The discriminator vs math/code is ALWAYS a
    # DRAWING-CHARACTER LITERAL repeated by a data-derived length: math multiplies
    # variables, an ASCII bar repeats a char. Three unambiguous forms:
    #   - inline literal:   '#' * score, '|' * n, '-' * width    (INLINE_BAR_RE)
    #   - helper literal:   return '#' * n                        (BAR_HELPER_RE)
    #   - helper-call:      def bar(v,c): return c*n; bar(x,'|')  (_bar_helper_call)
    # bar_length_from_scalar alone is NOT decisive (regression/normalization share
    # `* scale`), so it is reported as a flag, not gated on.
    is_defect = False
    if has_inline_bar:
        is_defect = True
        signatures.append("inline_bar_multiplication")
    if has_bar_helper:
        is_defect = True
        signatures.append("bar_helper_literal_return")
    if bar_param:
        is_defect = True
        signatures.append(f"bar_helper_call(param={bar_param})")

    if not is_defect:
        return None

    # Context line: first line carrying a bar signature for the report
    context = ""
    for line in src.splitlines():
        if (INLINE_BAR_RE.search(line) or BAR_HELPER_RE.search(line)
                or ASCII_COMMENT_RE.search(line)):
            context = line.strip()[:100]
            break
    return {
        "signatures": sorted(set(signatures)),
        "ascii_comment": ascii_comment,
        "quant_context": quant_context,
        "scalar_length": has_bar_scalar,
        "context": context,
    }


def scan_notebook(path: Path) -> dict:
    """Return a result dict for one notebook: path, hits[], error."""
    try:
        with open(path, encoding="utf-8") as f:
            nb = json.load(f)
    except (OSError, json.JSONDecodeError) as exc:
        return {"path": str(path), "error": str(exc), "hits": []}

    hits = []
    for ci, cell in enumerate(nb.get("cells", [])):
        if cell.get("cell_type") != "code":
            continue
        src = _cell_source(cell)
        finding = detect_cell(src)
        if finding:
            hits.append({"cell_index": ci, **finding})
    return {"path": str(path), "kernel": _kernel(nb), "hits": hits, "error": None}


def _kernel(nb: dict) -> str:
    return nb.get("metadata", {}).get("kernelspec", {}).get("name", "?")


def _iter_notebooks(root: Path, family: str | None):
    base = root / "MyIA.AI.Notebooks"
    if family:
        base = base / family
    if not base.exists():
        return
    yield from sorted(base.rglob("*.ipynb"))


def _human_report(results: list[dict]) -> str:
    total_hits = sum(len(r["hits"]) for r in results)
    affected = [r for r in results if r["hits"]]
    lines = [
        f"Notebooks scanned : {len(results)}",
        f"Cells with Prong-A ASCII candidates : {total_hits}",
        f"Affected notebooks : {len(affected)}",
        "",
    ]
    if not affected:
        lines.append("No ASCII-workaround candidates detected (conservative heuristic).")
        return "\n".join(lines)
    for r in affected:
        short = r["path"].split("MyIA.AI.Notebooks")[-1].lstrip("\\/")
        lines.append(f"## {short}  [{r['kernel']}]")
        for h in r["hits"]:
            sig = ", ".join(h["signatures"])
            flags = []
            if h["ascii_comment"]:
                flags.append("ascii-comment")
            if h["quant_context"]:
                flags.append("quant-ctx")
            flagstr = f" ({', '.join(flags)})" if flags else ""
            ctx = f"  | {h['context']}" if h["context"] else ""
            lines.append(f"  - cell [{h['cell_index']}]: {sig}{flagstr}{ctx}")
        lines.append("")
    lines.append(
        "NOTE: conservative heuristic (precision > recall). Verify each candidate "
        "firsthand before fixing -- legitimate discrete-state grids/boards and "
        "matplotlib companions are filtered, but subtle cases need human judgment."
    )
    return "\n".join(lines)


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        description=__doc__.split("\n\n")[0],
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("notebook", nargs="?", help="Notebook to scan (default: all pedagogical)")
    parser.add_argument("--family", help="Top-level family under MyIA.AI.Notebooks/ (e.g. Probas, ML)")
    parser.add_argument("--root", default=".", help="Repo root (default: cwd)")
    parser.add_argument("--json", action="store_true", help="Machine-readable JSON output")
    parser.add_argument("--check", action="store_true", help="Exit 1 if any hit (CI-ready)")
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
