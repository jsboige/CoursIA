#!/usr/bin/env python3
"""Detecte les quantbooks qui annoncent une periode d'analyse qu'ils ne calculent pas (#8772).

Pourquoi cet outil existe
-------------------------
Six quantbooks QuantConnect impriment `Periode: 2020-01-01 a 2024-12-31` puis
calculent leurs metriques sur une toute autre fenetre. Ce n'est pas un defaut de
donnees -- les barres sont reelles -- c'est un defaut d'honnetete documentaire
(classe #8052/#8364) : l'etudiant lit une periode et regarde des chiffres qui
n'en viennent pas.

Deux mecanismes distincts produisent la meme divergence.

**Mecanisme A -- le lookback entier recule depuis `StartDate`.**
`qb.History(symbols, 365*5, Resolution.Daily)` ancre sa fenetre sur `qb.Time`,
qui vaut `StartDate` dans un QuantBook frais. Les « 5 ans » demandes sont donc
les 5 ans **qui precedent** la periode declaree, pas les 5 ans declares. Mesure
#8772 sur `ML-DeepLearning` : declare 2020-01-01 -> 2024-12-31, calcule sur
2012-09-28 -> 2019-12-31 (soit ni le COVID ni le drawdown 2022, exactement les
regimes qu'un lecteur s'attend a voir).

**Mecanisme B -- les sorties committees viennent du chemin de repli local.**
Quand `QuantBook()` leve `NameError`, le `try/except` de repli bascule sur
yfinance, dont la fenetre s'ancre a **l'heure d'execution**. Le `SetStartDate`
etait dans le `try:` qui a echoue : il n'a jamais pris effet. Mesure #8772 sur
`Alpha-Correlation-Analysis` : declare 2020-2024, sorties committees sur
2021-06-01 -> 2026-05-29. La donnee externe n'est pas le probleme (elle est
legitime, cf #7066) -- la substitution **silencieuse** l'est.

Ce que cet outil NE dit PAS
---------------------------
Il ne dit pas qu'une fenetre reculee est fausse. Elle est souvent la seule
disponible : #8734 etablit que les donnees equity locales s'arretent au
2021-03-31 et que Lean les prolonge en constante via `fillDataForward=True`.
Re-fenetrer sur la periode declaree aujourd'hui echangerait un defaut de
documentation contre un defaut de donnees (c'est l'artefact qui a produit les
100 % de direction accuracy de #8719). **Le correctif attendu est de divulguer,
pas de re-fenetrer** -- sur le modele de #8770 :

    print(f"Fenetre effective: {closes.index[0].date()} a {closes.index[-1].date()}")

Il DETECTE, il ne CORRIGE PAS : imprimer la fenetre reelle suppose une
re-execution du notebook (C.2/H.1). JAMAIS retoucher une sortie committee a la
main (Stop&Repair, secrets-hygiene regle 6).

Ce qui est flagge (DETERMINISTE)
--------------------------------
Signal A -- `history_int_lookback_undisclosed` :
  le notebook instancie un `QuantBook()` **et** appelle `SetStartDate` **et**
  passe un lookback ENTIER en 2e argument positionnel de `<qb>.History(...)`
  **et** n'imprime nulle part la fenetre reellement obtenue. Les quatre
  conditions sont requises : un notebook qui divulgue (`Fenetre effective:`,
  `closes.index[0]`, ...) est conforme et n'est pas flagge -- c'est l'etat
  cible, pas un defaut.

Signal B -- `declared_period_in_dead_fallback_branch` :
  une sortie committee porte un marqueur de repli hors-QuantBook (« local
  environment », « yfinance will be used ») **alors que** le notebook declare
  une periode. Le repli n'est pas le defaut -- yfinance est une donnee externe
  legitime (#7066) et un notebook qui l'annonce sans rien declarer est conforme.
  Le defaut est la CONJONCTION : un `SetStartDate` place dans le `try:` qui a
  echoue, donc annonce puis jamais applique. Le fait est lu dans les `outputs`,
  pas devine depuis la source : c'est ce que le notebook a reellement imprime.

Ce qui n'est JAMAIS flagge (faux positifs mesures avant livraison)
------------------------------------------------------------------
Une premiere version rendait 42 hits sur 22 notebooks la ou 5 seulement etaient
reels. Un faux positif accuse un auteur conforme et le signal cesse d'etre cru
des la premiere fausse accusation (lecon #8765) -- quatre exclusions, chacune
verrouillee par un test :

  1. **Cellules de reference `class X(QCAlgorithm)`** (« code a copier dans
     main.py », non executable ici). Dans un QCAlgorithm, `self.History(sym, N)`
     s'ancre sur l'heure COURANTE de la boucle de backtest : le lookback
     glissant y est l'effet VOULU. Ces cellules sont ecartees DE BOUT EN BOUT,
     y compris de la detection de `SetStartDate` -- leur declaration configure
     un backtest, elle n'annonce pas la periode de la recherche voisine
     (cas mesure : QC-Py-04).
  2. **Appels sur `self`** -- meme raison, sans dependre du marqueur de classe.
  3. **Arguments ambigus** : seul un entier litteral ou arithmetique (`365*5`,
     `252`) compte comme lookback. Un identifiant nu (`start`) peut porter un
     `datetime` -- faux negatif assume plutot que fausse accusation.
  4. **Repli local annonce sans periode declaree** (forme
     `Research-Executor/research_*.ipynb`).

Limite assumee : ML-EnhancedPairs imprime bien sa fenetre effective, sous un
libelle `Periode:` identique a celui de la periode declaree. Le detecteur le
tient pour conforme. Ce residu est un defaut de **libelle**, porte par le
critere 2 de #8772 -- l'outil ne revendique pas plus qu'il ne mesure.

Les arguments de `History(` sont decoupes par un scanner a parentheses
equilibrees, PAS par une regex. Une regex `\\([^)]*\\)` casse sur
`History(list(symbols.values()), 365*5, ...)` -- la parenthese de `list(` ferme
la classe de caracteres et l'appel est silencieusement manque. Ce faux negatif
a sous-compte le scan initial de 7 hits sur 9 (#8772).

Usage
-----
    python scripts/notebook_tools/detect_quantbook_window_divergence.py --family QuantConnect
    python scripts/notebook_tools/detect_quantbook_window_divergence.py <notebook> --json
    python scripts/notebook_tools/detect_quantbook_window_divergence.py --family QuantConnect --check
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

# Marcheur + SKIP_DIRS canonique centralises dans notebook_walk (#8650).
from notebook_walk import iter_notebooks  # noqa: E402

# `SetStartDate(...)` / `set_start_date(...)` -- le notebook declare une periode.
RE_SET_START = re.compile(r"\b[Ss]et_?[Ss]tart_?[Dd]ate\s*\(")

# Marqueurs de divulgation de la fenetre reellement obtenue. La presence d'UN
# seul suffit : le notebook est conforme (modele #8770).
RE_DISCLOSURE = re.compile(
    r"(?:[Ff]en[eê]tre\s+effective"          # "Fenetre effective:" (#8770)
    r"|effective\s+window"
    r"|\.index\[0\]"                          # print(f"... {closes.index[0].date()} ...")
    r"|\.index\[-1\]"
    r"|\.index\.min\(\)"
    r"|\.index\.max\(\))"
)

# Marqueurs de repli hors-QuantBook, lus dans les SORTIES committees.
RE_LOCAL_FALLBACK = re.compile(
    r"(?:[Ll]ocal environment"
    r"|yfinance will be used"
    r"|\(local environment\))"
)

# Un 2e argument ENTIER : litteral ou arithmetique de litteraux (`365*5`, `252`,
# `1825`). Volontairement STRICT -- un identifiant nu (`start`, `lookback`) est
# AMBIGU (il peut porter un `datetime`) et n'est donc PAS flagge. Faux negatif
# assume : un faux positif accuse un auteur conforme et le signal cesse d'etre
# croyable des la premiere fausse accusation (lecon #8765).
RE_INT_ARG = re.compile(r"^(?=.*\d)[\d\s*+/()-]+$")

# Cellule de reference `QCAlgorithm` -> semantique DIFFERENTE, jamais un defaut.
# Dans un QCAlgorithm, `self.History(symbol, N)` s'ancre sur `self.Time`, l'heure
# COURANTE de la boucle de backtest : le lookback glissant est exactement l'effet
# voulu. Seul le QuantBook de recherche, dont `qb.Time` est fige a `StartDate`,
# produit la divergence. Les deux se distinguent textuellement.
RE_QCALGORITHM = re.compile(r"\bQCAlgorithm\b")

# Le notebook doit reellement instancier un QuantBook de recherche.
RE_QUANTBOOK = re.compile(r"\bQuantBook\s*\(")


def _split_call_args(text: str, open_paren: int) -> tuple[list[str], int] | None:
    """Decoupe les arguments d'un appel dont la parenthese ouvrante est a
    ``open_paren``, en respectant l'imbrication des ``()[]{}`` et les chaines.

    Retourne ``(args, index_de_la_parenthese_fermante)`` ou ``None`` si l'appel
    n'est pas clos (source tronquee). Ecrit a la main plutot qu'en regex : une
    classe ``[^)]`` casse sur ``list(symbols.values())`` (#8772).
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


def find_int_lookback_calls(source: str) -> list[dict]:
    """Retourne les appels ``History(...)`` dont le 2e argument positionnel est
    un lookback ENTIER (donc ancre sur ``qb.Time``), avec l'expression trouvee.

    Les appels sur ``self`` sont ignores : dans un ``QCAlgorithm``,
    ``self.History(symbol, N)`` s'ancre sur l'heure COURANTE de la boucle de
    backtest -- le lookback glissant y est l'effet voulu, pas un defaut.
    """
    hits: list[dict] = []
    for m in re.finditer(r"(\w+)\s*\.\s*[Hh]istory\s*\(", source):
        if m.group(1) == "self":
            continue
        parsed = _split_call_args(source, m.end() - 1)
        if parsed is None:
            continue
        args, _ = parsed
        if len(args) < 2:
            continue
        second = args[1]
        if not second or not RE_INT_ARG.match(second):
            continue
        hits.append({"receiver": m.group(1), "lookback": second})
    return hits


def _cell_output_text(cell: dict) -> str:
    parts: list[str] = []
    for out in cell.get("outputs", []) or []:
        if "text" in out:
            parts.append("".join(out["text"]))
        data = out.get("data") or {}
        for key in ("text/plain", "text/html"):
            if key in data:
                parts.append("".join(data[key]))
    return "\n".join(parts)


def scan_notebook(path: Path) -> dict:
    result = {"path": str(path), "hits": [], "error": None}
    try:
        nb = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        result["error"] = f"{type(exc).__name__}: {exc}"
        return result

    cells = nb.get("cells", []) or []
    code_cells = [(i, c) for i, c in enumerate(cells) if c.get("cell_type") == "code"]

    # Les cellules de reference `class X(QCAlgorithm)` -- « code a copier dans
    # main.py », non executable ici -- sont ECARTEES DE BOUT EN BOUT, pas
    # seulement de la recherche d'appels. Leur `self.SetStartDate(2015, 1, 1)`
    # configure un backtest, il ne declare PAS la periode de la recherche : le
    # compter contaminerait le verdict des cellules QuantBook voisines. Cas
    # mesure : QC-Py-04, dont la seule declaration vit dans un snippet de
    # reference alors que la recherche, elle, n'annonce aucune periode.
    research_cells = [
        (i, c) for i, c in code_cells
        if not RE_QCALGORITHM.search("".join(c.get("source", [])))
    ]
    full_source = "\n".join("".join(c.get("source", [])) for _, c in research_cells)

    declares_period = bool(RE_SET_START.search(full_source))
    discloses = bool(RE_DISCLOSURE.search(full_source))
    is_quantbook = bool(RE_QUANTBOOK.search(full_source))

    # -- Signal A : lookback entier non divulgue -----------------------------
    # Trois conditions cumulees : le notebook est bien un QuantBook de recherche,
    # il declare une periode, et il ne divulgue jamais la fenetre obtenue.
    if is_quantbook and declares_period and not discloses:
        for idx, cell in research_cells:
            src = "".join(cell.get("source", []))
            for call in find_int_lookback_calls(src):
                result["hits"].append({
                    "cell_index": idx,
                    "signal": "history_int_lookback_undisclosed",
                    "lookback": call["lookback"],
                    "detail": (
                        f"{call['receiver']}.History(..., {call['lookback']}, ...) s'ancre sur "
                        "qb.Time=StartDate -> la fenetre RECULE depuis la periode declaree ; "
                        "aucune ligne n'imprime la fenetre reellement obtenue"
                    ),
                })

    # -- Signal B : periode declaree dans une branche morte -------------------
    # Le repli yfinance n'est PAS le defaut : c'est une donnee externe legitime
    # (#7066), et un notebook qui l'annonce sans rien declarer est conforme --
    # les trois `Research-Executor/research_*.ipynb` impriment « Local
    # environment - using yfinance fallback » et ne declarent aucune periode :
    # rien n'y diverge. Le defaut est la CONJONCTION : un `SetStartDate` place
    # dans le `try:` qui a echoue, donc annonce puis jamais applique, pendant
    # que la fenetre reelle s'ancre a l'heure d'execution.
    if declares_period:
        for idx, cell in code_cells:
            text = _cell_output_text(cell)
            if text and RE_LOCAL_FALLBACK.search(text):
                result["hits"].append({
                    "cell_index": idx,
                    "signal": "declared_period_in_dead_fallback_branch",
                    "detail": (
                        "sortie committee produite HORS QuantBook (repli local) alors que le "
                        "notebook declare une periode : le SetStartDate n'a jamais pris effet, "
                        "la fenetre reelle est ancree a l'heure d'execution"
                    ),
                })
                break  # un marqueur suffit a qualifier le notebook

    return result


def _iter_notebooks(root: Path, family: str | None):
    yield from iter_notebooks(root / "MyIA.AI.Notebooks", family=family)


def _human_report(results: list[dict]) -> str:
    affected = [r for r in results if r["hits"]]
    errored = [r for r in results if r.get("error")]
    total_hits = sum(len(r["hits"]) for r in results)
    lines = [
        f"Notebooks scanned      : {len(results)}",
        f"Window divergences     : {total_hits}",
        f"Affected notebooks     : {len(affected)}",
        "",
    ]
    if not affected:
        lines.append("No declared-vs-effective window divergence detected.")
        if errored:
            lines.append("")
            lines.append(f"NOTE: {len(errored)} notebook(s) unreadable (see --json for details).")
        return "\n".join(lines)
    for r in affected:
        short = r["path"].split("MyIA.AI.Notebooks")[-1].lstrip("\\/")
        lines.append(f"## {short}")
        for h in r["hits"]:
            extra = f" ({h['lookback']})" if "lookback" in h else ""
            lines.append(f"  - cell [{h['cell_index']}] {h['signal']}{extra}")
            lines.append(f"      {h['detail']}")
        lines.append("")
    lines.append(
        "FIX (#8772) : DIVULGUER la fenetre reellement calculee -- "
        "print(f\"Fenetre effective: {closes.index[0].date()} a {closes.index[-1].date()}\") -- "
        "puis re-executer (C.2/H.1). NE PAS re-fenetrer sur la periode declaree tant que "
        "#8734 n'est pas resolue : les donnees locales s'arretent au 2021-03-31 et Lean "
        "prolonge en constante, ce qui echangerait un defaut de doc contre un defaut de donnees."
    )
    return "\n".join(lines)


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        description=__doc__.split("\n\n")[0],
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("notebook", nargs="?", help="Notebook to scan (default: all pedagogical)")
    parser.add_argument("--family", help="Top-level family under MyIA.AI.Notebooks/ (e.g. QuantConnect)")
    parser.add_argument("--root", default=".", help="Repo root (default: cwd)")
    parser.add_argument("--json", action="store_true", help="Machine-readable JSON output")
    parser.add_argument("--check", action="store_true", help="Exit 1 if any divergence (CI-ready)")
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
