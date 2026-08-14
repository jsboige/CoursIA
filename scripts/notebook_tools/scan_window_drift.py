#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Detecteur advisory de la derive de fenetre QC (forme de la borne, D2 #9768).

Classe un notebook (ou un arbre) en ``DRIFT`` / ``PINNED`` / ``INDÉTERMINÉ``
/ ``N-A`` :

  N-A          : aucune API QC dans le code (``set_end_date`` non-applicable).
  DRIFT        : la fenetre de donnees bouge avec l'horloge murale.
  PINNED       : bornes litterales ou ``set_end_date`` present -> fenetre figee.
  INDÉTERMINÉ  : API QC presente mais forme de la borne ambigue.

Quatre formes distinctes produisent le drift, et **une seule** se corrige par
``set_end_date`` (cf #10230) :

  T  ``history(sym, timedelta(...), ...)``   fenetre relative depuis NOW
  L  ``history(sym, N, Resolution)``         N barres depuis NOW
  N  ``datetime.now()`` / ``date.today()``   borne ancrée sur l'horloge
  S  ``set_start_date`` sans ``set_end_date`` fenetre ouverte à droite

Le detecteur cherche la **forme de la borne**, jamais la presence d'un nom de
methode : une borne litterale (``datetime(2015, 1, 1)``) passee a ``history``
est figee meme sans ``set_end_date``. Lit les cellules **code** uniquement
(une date en prose ne fige rien).

Pourquoi les snippets de reference ``class Foo(QCAlgorithm)`` sont ecartes :
dans un ``QCAlgorithm``, ``self.History(symbol, N)`` s'ancre sur ``self.Time``,
l'heure COURANTE de la boucle de backtest -- le lookback glissant y est l'effet
voulu. Seul le ``QuantBook`` de recherche derive. Compter le
``self.SetStartDate(...)`` d'un snippet a copier dans ``main.py`` contaminerait
le verdict des cellules ``QuantBook`` voisines (cas mesure : QC-Py-04, #8765).

Advisory : ``exit 0`` toujours, le signal est le rapport. ``--json`` pour la
CI ulterieure, ``--check`` pour un echec bloquant.

See #10230 (grain), #9772 (probe precedant), #9768 (EPIC D2), #1621.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
DEFAULT_ROOT = REPO_ROOT / "MyIA.AI.Notebooks"

# --- Marqueurs d'API QC --------------------------------------------------
# Presence d'AU MOINS UN => le notebook parle a QuantConnect => set_end_date est
# applicable. L'absence de tous => N-A (ajouter set_end_date serait un no-op ou
# un NameError). Cohérent avec le grep de cadrage de #10230.
RE_QC_API = re.compile(
    r"\bQuantBook\b"
    r"|\bQCAlgorithm\b"
    r"|\bset_start_date\b"
    r"|\bset_end_date\b"
    r"|\bSetStartDate\b"
    r"|\bSetEndDate\b"
    r"|\badd_(?:equity|crypto|forex|security|option|future|cfd)s?\b",
    re.IGNORECASE,
)

# set_start_date / set_end_date, tolerants a la casse et au separateur
# (SetStartDate, set_start_date, SETENDDATE). Reutilise l'idiome de
# scan_d2_window_openness.py.
RE_SET_START = re.compile(
    r"[Ss][Ee][Tt][_]?[Ss][Tt][Aa][Rr][Tt][_]?[Dd][Aa][Tt][Ee]\s*\("
)
RE_SET_END = re.compile(
    r"[Ss][Ee][Tt][_]?[Ee][Nn][Dd][_]?[Dd][Aa][Tt][Ee]\s*\("
)

# Borne ancrée sur l'horloge murale : datetime.now(), date.today(),
# datetime.utcnow(), pd.Timestamp.now(). Forme N = la borne de la fenetre de
# DONNEES derive avec l'horloge. Discrimine par CONTEXTE (pas le pattern seul) :
# ne compte que ``now()/today()`` qui est (a) assigne a une variable-borne, ou
# (b) passe en argument a history()/set_*date(). Un ``now()`` dans un en-tete
# de log ``print(f"...{datetime.now().strftime()}")`` n'est PAS une borne -> FP
# evite (QC-Py-40/41, #10230). Une variable-borne = nom de date de fin/right.
RE_NOW = re.compile(
    r"\b(?:datetime|date|pd\.Timestamp|pd\.DatetimeIndex)\s*\.\s*"
    r"(?:now|utcnow|today)\s*\("
)
# ``<var> = ... datetime.now()/today()`` ou var est un nom de borne (end/stop/
# to/right/finish). Le ``=`` distingue l'affectation d'une borne d'un print.
RE_NOW_ASSIGN = re.compile(
    r"^[ \t]*(?:end|end_date|enddate|to|to_date|todate|stop|stop_date|"
    r"finish|right|right_edge|back_end|date_end|final)\w*\s*=\s*=?"
    r"[^\n]*\b(?:datetime|date|pd\.Timestamp)\s*\.\s*(?:now|utcnow|today)\s*\(",
    re.MULTILINE,
)

# Argument entier (lookback en barres) : 2520, 365*5, 252 * 12, etc.
# Reutilise RE_INT_ARG de detect_quantbook_window_divergence.py (#8772).
RE_INT_ARG = re.compile(r"^(?=.*\d)[\d\s*+/()-]+$")

# Borne litterale concrete : datetime(2015, 1, 1), date(2020, 6, 30). Une telle
# borne passee a history FIGE la fenetre (PINNED) meme sans set_end_date.
RE_LITERAL_DATE = re.compile(r"\b(?:datetime|date)\s*\(\s*\d{4}\s*,")

# Affectation d'une variable a une date litterale concrete : ``start = datetime(
# 2015, 1, 1)``, ``end_date = date(2020, 6, 30)``. Permet de resoudre le data-
# flow elementaire : ``qb.History(sym, start, end)`` ou ``start``/``end`` sont
# des variables-borne litterales -> fenetre FIGEE (PINNED), pas INDÉTERMINÉ.
RE_DATE_VAR_ASSIGN = re.compile(
    r"^[ \t]*(\w+)\s*=\s*(?:datetime|date)\s*\(\s*\d{4}\s*,",
    re.MULTILINE,
)


def _split_call_args(text: str, open_paren: int) -> tuple[list[str], int] | None:
    """Decoupe les arguments d'un appel dont la parenthese ouvrante est a
    ``open_paren``, en respectant l'imbrication des ``()[]{}`` et les chaines.

    Retourne ``(args, index_de_la_parenthese_fermante)`` ou ``None`` si l'appel
    n'est pas clos (source tronquee). Ecrit a la main plutot qu'en regex : une
    classe ``[^)]`` casse sur ``list(symbols.values())`` (#8772). Reutilise tel
    quel depuis detect_quantbook_window_divergence.py.
    """
    depth = 0
    quote: str | None = None
    args: list[str] = []
    current: list[str] = []
    i = open_paren
    while i < len(text):
        ch = text[i]
        if quote is not None:
            current.append(ch)
            if ch == "\\":
                if i + 1 < len(text):
                    current.append(text[i + 1])
                    i += 2
                    continue
            elif ch == quote:
                quote = None
            i += 1
            continue
        if ch in "\"'":
            quote = ch
            current.append(ch)
        elif ch in "([{":
            depth += 1
            if depth > 1:
                current.append(ch)
        elif ch in ")]}":
            depth -= 1
            if depth == 0:
                args.append("".join(current))
                return [a.strip() for a in args], i
            current.append(ch)
        elif ch == "," and depth == 1:
            args.append("".join(current))
            current = []
        else:
            current.append(ch)
        i += 1
    return None


def _history_calls(source: str) -> list[dict]:
    """Retourne les appels ``<receiver>.History(...)`` / ``.history(...)`` dont
    le receiver n'est pas ``self`` (sémantique QCAlgorithm, non-defaut), avec le
    2e argument positionnel et l'expression de l'appel.
    """
    hits: list[dict] = []
    for m in re.finditer(r"(\w+)\s*\.\s*[Hh]istory\s*\(", source):
        if m.group(1) == "self":
            continue
        open_paren = m.end() - 1
        parsed = _split_call_args(source, open_paren)
        if parsed is None:
            continue
        args, close = parsed
        # expression complete de l'appel (receiver.history(...))
        expr = source[m.start():close + 1]
        hits.append({
            "receiver": m.group(1),
            "args": args,
            "expr": expr,
            "start": m.start(),
        })
    return hits


def _line_no(source: str, offset: int) -> int:
    """Numero de ligne (1-indexe) d'un offset dans une source multi-lignes."""
    return source.count("\n", 0, offset) + 1


def _snippet_of(src: str, line: int) -> str:
    lines = src.splitlines()
    return lines[line - 1].strip() if 0 < line <= len(lines) else src.strip()


def classify_notebook(path: Path) -> dict[str, Any]:
    """Classifie un notebook selon le verdict D2 de forme de fenetre.

    Lit les cellules **code** uniquement (une date en prose ne fige rien). Les
    formes de drift se detectent sur TOUT le code :

    - Forme S (``set_start_date`` sans ``set_end_date``) s'applique y compris au
      code ``QCAlgorithm`` : un backtest d'algorithme dont la fin n'est pas
      figee derive comme une fenetre de recherche (cas QC-Py-Cloud-03, #10230).
    - Formes L/T (``history(..., N/timedelta, ...)``) : le ``self.History`` d'un
      ``QCAlgorithm`` s'ancre sur l'heure COURANTE de la boucle de backtest
      (effet voulu) -> exclu via le receiver ``self``, pas via la cellule.
    """
    rec: dict[str, Any] = {
        "path": _rel(path),
        "verdict": None,
        "forms": [],
        "markers": [],
        "has_qc_api": False,
        "has_set_end": False,
        "error": None,
    }
    try:
        nb = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        rec["error"] = f"{type(exc).__name__}: {exc}"
        rec["verdict"] = "ERREUR"
        return rec

    cells = nb.get("cells", []) or []
    code_cells = []
    for i, c in enumerate(cells):
        if c.get("cell_type") != "code":
            continue
        src = c.get("source")
        # Defensive: tolerate `source: None` (one source-like field was None) and
        # `source: [None, "x = 1\n"]` (list with None entries). nbformat spec
        # says source is a string OR a list of strings; some notebooks produced
        # by older tooling violate it. Without this guard the tree-scan
        # crashes on a TypeError, masking the whole tree (#10230 follow-up).
        if src is None:
            src_text = ""
        elif isinstance(src, list):
            src_text = "".join(s for s in src if isinstance(s, str))
        else:
            src_text = src if isinstance(src, str) else ""
        code_cells.append((i, src_text))
    full_code = "\n".join(src for _, src in code_cells)

    has_qc_api = bool(RE_QC_API.search(full_code))
    rec["has_qc_api"] = has_qc_api
    if not has_qc_api:
        rec["verdict"] = "N-A"
        return rec

    has_set_start = bool(RE_SET_START.search(full_code))
    has_set_end = bool(RE_SET_END.search(full_code))
    rec["has_set_end"] = has_set_end

    forms: dict[str, list[dict]] = {}

    # Forme S : set_start_date sans set_end_date (fenetre ouverte a droite).
    # C'est la SEULE forme que set_end_date corrige. Evaluee sur tout le code,
    # QCAlgorithm inclus (backtest a fin ouverte = drift).
    if has_set_start and not has_set_end:
        for idx, src in code_cells:
            m = RE_SET_START.search(src)
            if m:
                ln = _line_no(src, m.start())
                forms.setdefault("S", []).append(
                    {"cell_index": idx, "line": ln, "snippet": _snippet_of(src, ln)}
                )
                break

    # Forme N : now()/today() assigne a une variable-borne (end/stop/to/...).
    # Le ``=`` distingue l'affectation d'une borne d'un simple print de log
    # (QC-Py-40/41 impriment ``datetime.now()`` dans un en-tete -> pas une borne).
    for m in RE_NOW_ASSIGN.finditer(full_code):
        # retrouve la cellule + ligne de l'offset dans full_code.
        offset = m.start()
        idx, ln = _locate(code_cells, offset)
        forms.setdefault("N", []).append(
            {"cell_index": idx, "line": ln, "snippet": _snippet_of(_cell_src(code_cells, idx), ln)}
        )

    # Variables-borne litterales : ``start = datetime(2015,1,1)`` etc. Permet de
    # resoudre ``qb.History(sym, start, end)`` (args nus) vers PINNED.
    literal_date_vars: set[str] = set()
    for m in RE_DATE_VAR_ASSIGN.finditer(full_code):
        literal_date_vars.add(m.group(1))

    # Formes T / L / N-arg : arguments de <receiver>.history(...), receiver != self.
    history_literal_pinned = False
    history_calls_seen = False
    for idx, src in code_cells:
        for call in _history_calls(src):
            history_calls_seen = True
            args = call["args"]
            if len(args) < 2:
                continue
            second = args[1]
            line = _line_no(src, call["start"])
            snippet = _snippet_of(src, line)
            # Forme N directe : now()/today() passe en argument a history(...).
            if RE_NOW.search(second):
                forms.setdefault("N", []).append(
                    {"cell_index": idx, "line": line, "snippet": snippet}
                )
            elif "timedelta" in second:
                forms.setdefault("T", []).append(
                    {"cell_index": idx, "line": line, "snippet": snippet}
                )
            elif RE_INT_ARG.match(second):
                forms.setdefault("L", []).append(
                    {"cell_index": idx, "line": line, "snippet": snippet, "lookback": second}
                )
            elif RE_LITERAL_DATE.search(second) or second.split("[")[0].strip() in literal_date_vars:
                # borne litterale concrete (ou variable litterale resolue) ->
                # fenetre FIGEE, pas du drift.
                history_literal_pinned = True

    rec["forms"] = sorted(forms.keys())
    for f in sorted(forms.keys()):
        rec["markers"].append({"form": f, "hits": forms[f]})

    if forms:
        rec["verdict"] = "DRIFT"
    elif has_set_end:
        rec["verdict"] = "PINNED"
    elif history_literal_pinned:
        rec["verdict"] = "PINNED"
    else:
        rec["verdict"] = "INDÉTERMINÉ"
    return rec


def _locate(code_cells: list[tuple[int, str]], offset: int) -> tuple[int, int]:
    """Mappe un offset dans full_code vers (cell_index, ligne_dans_la_cellule)."""
    running = 0
    for idx, src in code_cells:
        cell_len = len(src) + 1  # +1 pour le '\n' de jonction
        if offset < running + cell_len:
            return idx, full_code_offset_to_line(src, offset - running)
        running += cell_len
    return code_cells[-1][0], 1


def full_code_offset_to_line(src: str, offset: int) -> int:
    if offset < 0:
        offset = 0
    return src.count("\n", 0, min(offset, len(src))) + 1


def _cell_src(code_cells: list[tuple[int, str]], idx: int) -> str:
    for i, src in code_cells:
        if i == idx:
            return src
    return ""


def _rel(path: Path) -> str:
    try:
        return str(path.relative_to(REPO_ROOT))
    except ValueError:
        return str(path)


def _iter_notebooks(root: Path, family: str | None):
    base = root / "MyIA.AI.Notebooks" if (root / "MyIA.AI.Notebooks").is_dir() else root
    top = base / family if family else base
    if not top.is_dir():
        return
    for p in sorted(top.rglob("*.ipynb")):
        if ".ipynb_checkpoints" in p.parts:
            continue
        yield p


def _human_report(records: list[dict]) -> str:
    by_verdict: dict[str, list[dict]] = {}
    for r in records:
        by_verdict.setdefault(r["verdict"], []).append(r)
    total = len(records)
    lines = [f"=== scan_window_drift : {total} notebook(s) ==="]
    order = ["DRIFT", "PINNED", "INDÉTERMINÉ", "N-A", "ERREUR"]
    for v in order:
        bucket = by_verdict.get(v, [])
        if not bucket:
            continue
        lines.append(f"\n--- {v} : {len(bucket)} ---")
        for r in bucket:
            lines.append(f"  {_rel(Path(r['path']))}")
            for marker in r.get("markers", []):
                for hit in marker["hits"]:
                    lines.append(
                        f"      [{marker['form']}] c{hit['cell_index']} L{hit['line']}: {hit['snippet'][:90]}"
                    )
    # cross-tab
    lines.append("\n=== Répartition ===")
    for v in order:
        c = len(by_verdict.get(v, []))
        if c:
            lines.append(f"  {v:<13}: {c}")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=__doc__.splitlines()[0] if __doc__ else None,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("notebook", nargs="?", help="Notebook à classer (défaut: arbre QC entier)")
    parser.add_argument("--family", default="QuantConnect", help="Famille sous MyIA.AI.Notebooks/ (défaut: QuantConnect)")
    parser.add_argument("--root", default=str(REPO_ROOT), help="Racine du dépôt")
    parser.add_argument("--json", action="store_true", help="Sortie JSON machine-readable")
    parser.add_argument("--check", action="store_true", help="Exit 1 si au moins un DRIFT (CI-ready)")
    args = parser.parse_args(argv)

    root = Path(args.root)

    if args.notebook:
        nb_path = Path(args.notebook)
        if not nb_path.is_absolute():
            nb_path = root / args.notebook
        if nb_path.is_dir():
            # Acceptance #10230 : « lancer sur l'arbre QC entier ». Un chemin de
            # répertoire scanne tous les .ipynb qu'il contient (hors checkpoints),
            # au lieu de crasher en ERREUR (read_text sur un dir).
            paths = [p for p in sorted(nb_path.rglob("*.ipynb"))
                     if ".ipynb_checkpoints" not in p.parts]
            if not paths:
                print(f"[scan_window_drift] aucun notebook sous {nb_path}", file=sys.stderr)
                return 2
            records = [classify_notebook(p) for p in paths]
        else:
            records = [classify_notebook(nb_path)]
    else:
        paths = list(_iter_notebooks(root, args.family))
        if not paths:
            print(f"[scan_window_drift] aucun notebook sous {root}/{args.family}", file=sys.stderr)
            return 2
        records = [classify_notebook(p) for p in paths]

    if args.json:
        payload = {"records": records}
        print(json.dumps(payload, ensure_ascii=False, indent=2))
    else:
        print(_human_report(records))

    if args.check and any(r["verdict"] == "DRIFT" for r in records):
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
