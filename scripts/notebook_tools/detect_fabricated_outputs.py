#!/usr/bin/env python3
"""Detecte les sorties textuelles FABRIQUEES committes comme resultats d'execution (Prong-A, registre #3801).

Pourquoi cet outil existe
-------------------------
Le sweep Prong-A (#3801) traque les sorties FABRIQUEES : une cellule code qui
pretend avoir execute mais commit un placeholder textuel en lieu et place du
vrai resultat. `detect_blank_figures.py` couvre les images degeneres (axe 1 :
le PNG 1x1 de 70 octets emis par matplotlib quand la figure est vide).
Cet outil couvre l'AXE 2 : les sorties TEXTUELLES fabriquees -- dataframes de
backtest avec stats a 0.0 simulant un backtest qui n'a pas tourne, lignes
`Row N` placeholders, listes d'allocations vides.

Incident fondateur #6891 : 8 quantbook.ipynb QuantConnect committes chacun avec
(a) un unique PNG 1x1 de 70 octets (axe 1, deja couvert par detect_blank_figures)
ET (b) des sorties textuelles fabriquees -- `Row N` placeholders simulant un
tableau de resultats (axe 2, ce detecteur). Distribution observee sur les 8 :

    AllWeather       9 lignes "Row N"     + 1 dataframe stats 0.0
    DualMomentum     3 lignes "Row N"
    EMA-Cross-Alpha  0 (uniquement axe 1, blank PNG)
    FuturesTrend    15 lignes "Row N"
    MomentumStrategy 3 lignes "Row N"
    RiskParity      11 lignes "Row N"     + 1 dataframe stats 0.0
    SectorMomentum   3 lignes "Row N"
    TurnOfMonth     16 lignes "Row N"     + 4 dataframes stats 0.0

La fabrication textuelle est un signal complementaire au blank-PNG : un notebook
peut avoir des images legitimes ET du texte fabrique (cas rare mais possible),
ou uniquement du texte fabrique (cas frequent quand le kernel est juste non
disponible et que l'auteur a rempli `outputs` a la main).

Il DETECTE, il ne CORRIGE PAS. La correction = re-executer la cellule dans le
vrai environnement (QC Cloud research pour QuantBook, kernel local pour
matplotlib) et committer la vraie sortie -- Stop&Repair, JAMAIS scrubber ni
supprimer pour cacher (regle secrets-hygiene 6 + sota-not-workaround Prong-A).

Ce qui est flagge (DETERMINISTE)
--------------------------------
Une sortie `text/plain` (ou `text/html` simplifie) d'une cellule code est
FABRIQUEE si elle contient :

  - le pattern "Row N" ou "Row {N}" (placeholder classique de resultat
    tabulaire qui n'a pas ete rempli -- litteral "Row " suivi d'un nombre)
  - un mini-dataframe "resultat backtest" presentant au moins 3 des 4 colonnes
    {Sharpe, CAGR, MaxDD, NetProfit} ET des valeurs entierement a 0.0
    (signature d'un backtest qui n'a pas tourne : moteur appele, donnees
    absentes, stats nulles)

Les seuils sont explicites (pas de ML, pas d'heuristique floue). La calibration
sur les 8 quantbooks de #6891 donne un signal deterministic :
    - 7/8 notebooks avec "Row N"  : AllWeather/DualMomentum/FuturesTrend/
                                    MomentumStrategy/RiskParity/SectorMomentum/
                                    TurnOfMonth
    - 3/8 avec dataframe all-zero  : AllWeather/RiskParity/TurnOfMonth

Known blind spots (hors scope par design)
-----------------------------------------
- SORTIE PARTIELLEMENT FABRIQUEE : une cellule peut avoir 1 ligne "Row N" dans
  50 lignes legitimes. On flagge la cellule au niveau 1 (presence du pattern),
  pas au niveau granularite (ratio). Ca pourrait produire des faux positifs
  sur un notebook pedagogique qui explique litteralement le pattern "Row N"
  dans un exemple. Mitigation : false-positive checking a la main sur le
  notebook flagge (l'outil est read-only, comme detect_blank_figures).
- VALEURS LEGITIMES NULLES : un backtest qui affiche reellement des stats a 0
  (algo = buy-and-hold cash, pas de trades, etc.). Le pattern exige les 3
  colonnes statistiques canoniques + 0.0 + structure dataframe -- combinaison
  rare mais possible. Mitigation : verification a la main, meme approche que
  pour detect_blank_figures (le verdict est un SIGNAL, pas une VERITE).
- TEXTE AUTRE LANGUE : on matche uniquement les noms de colonnes anglais
  (Sharpe/CAGR/MaxDD/NetProfit). Un notebook Francais avec "Ratio de Sharpe"
  ne sera pas detecte -- hors scope pour cette premiere passe (la majorite
  des quantbooks committes sont en anglais/keyword anglais meme dans un
  notebook Francais).

Usage
-----
    python detect_fabricated_outputs.py NB.ipynb                  # un notebook
    python detect_fabricated_outputs.py --family QuantConnect     # une famille
    python detect_fabricated_outputs.py                           # tous les notebooks
    python detect_fabricated_outputs.py NB.ipynb --json           # sortie machine
    python detect_fabricated_outputs.py NB.ipynb --check          # exit 1 si fabrication (CI-ready)
    python detect_fabricated_outputs.py --family QuantConnect --check  # CI pre-commit

Exit codes
----------
    0 -- aucune sortie fabriquee (ou mode non --check)
    1 -- une ou plusieurs sorties fabriquees (--check seulement)
    2 -- erreur (notebook illisible, famille introuvable)

Voir aussi
----------
- `detect_blank_figures.py` (#6918 MERGED) -- axe 1 : images degeneres
- `detect_ascii_workaround.py` (#3801) -- moitie ASCII du sweep Prong-A
- `.claude/rules/sota-not-workaround.md` -- Prong-A : vrai outil, pas workaround
- `.claude/rules/secrets-hygiene.md` regle 6 -- Stop&Repair : re-executer
- #6891 -- incident fondateur (8 quantbook.ipynb QC blank-PNG + Row N)

Part of #3801 (EPIC SOTA axe-2).
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path


# Pattern "Row N" : placeholder Pandas dataframe par defaut.
# Pandas nomme les lignes d'un dataframe sans index explicite comme "Row 0",
# "Row 1", etc. Quand un notebook committe une sortie dataframe SANS avoir
# defini d'index nomme, on obtient litteralement ces lignes en premiere colonne.
# C'est un signal FORTE de fabrication : un vrai backtest nomme ses indices
# (date, ticker, symbol...) -- "Row N" = index par defaut = dataframe bidon.
#
# On matche `Row N` en DEBUT de ligne (apres whitespace), suivi d'un nombre,
# suivi d'espace ou fin de ligne (pour eviter "Row 123" en milieu de phrase).
ROW_N_RE = re.compile(r"(?m)^\s*Row\s+\d+(?=\s|$)")

# Noms de colonnes canoniques d'un dataframe "resultat backtest".
# Si au moins 3 de ces 4 apparaissent dans la sortie ET que les valeurs sont
# toutes a 0.0 / 0 (dataframe present mais stats nulles = backtest pas tourne).
BACKTEST_STATS = ("Sharpe", "CAGR", "MaxDD", "NetProfit")
MIN_STATS_HIT = 3  # au moins 3 colonnes parmi 4 = signal dataframe resultat

# Pattern valeur numerique nulle : 0.0, 0, -0.0, +0.0, 0.00, etc.
ZERO_VALUE_RE = re.compile(r"^\s*[+\-]?0+(?:\.0+)?\s*$")


def _cell_text_outputs(cell: dict) -> list[str]:
    """Return concatenated text/plain content of all cell outputs as a list of lines."""
    lines = []
    for out in cell.get("outputs", []) or []:
        if not isinstance(out, dict):
            continue
        data = out.get("data", {}) if "data" in out else {}
        # text/plain est l'output standard d'un print() ou d'un display(...)
        for mime in ("text/plain", "text/html"):
            payload = data.get(mime)
            if payload is None:
                continue
            if isinstance(payload, list):
                payload = "".join(str(x) for x in payload)
            if not isinstance(payload, str):
                payload = str(payload)
            lines.extend(payload.splitlines())
        # stdout stream
        text = out.get("text")
        if isinstance(text, list):
            text = "".join(str(x) for x in text)
        if isinstance(text, str):
            lines.extend(text.splitlines())
    return lines


def _has_row_n(lines: list[str]) -> bool:
    """True if any line is a 'Row N' placeholder (litteral row not filled)."""
    blob = "\n".join(lines)
    return bool(ROW_N_RE.search(blob))


def _has_zero_stats_dataframe(lines: list[str]) -> bool:
    """True if the output looks like a backtest-stats dataframe with all-zero values.

    Heuristique stricte : au moins MIN_STATS_HIT noms de colonnes canoniques
    (Sharpe/CAGR/MaxDD/NetProfit) apparait dans les lignes, ET une proportion
    significative de valeurs numeriques dans le blob est a zero.

    Concu pour minimiser les FP sur les notebooks pedagogiques qui MENTIONNENT
    ces colonnes sans les FABRIQUER (ex: "the Sharpe ratio measures..."
    ne match pas car ce n'est pas un pattern tabulaire).
    """
    blob = "\n".join(lines)
    # Localiser la ou les lignes header qui contiennent les noms de colonnes.
    # Une header matche AU MOINS MIN_STATS_HIT colonnes canoniques.
    # Pour chaque header, examiner la section de donnees qui suit immediatement
    # jusqu'au prochain header (ou fin du blob). Si une section est entierement
    # a zero, c'est une fabrication.
    header_idxs = [
        i for i, ln in enumerate(lines)
        if sum(1 for s in BACKTEST_STATS if s in ln) >= MIN_STATS_HIT
    ]
    if not header_idxs:
        return False
    # Examiner les sections data associees a chaque header.
    sections_to_check = []
    for k, h_idx in enumerate(header_idxs):
        next_h = header_idxs[k + 1] if k + 1 < len(header_idxs) else len(lines)
        sections_to_check.append(lines[h_idx + 1:next_h])
    data_lines = [ln for section in sections_to_check for ln in section if ln.strip()]
    if not data_lines:
        return False
    # Compter combien de ces lignes ont TOUTES leurs valeurs numeriques a zero.
    # Approximation : on regarde le ratio de tokens numeriques a zero dans le blob
    # filtre. Si le ratio est eleve (>=0.5) ET qu'on a assez de colonnes matchees,
    # on flagge.
    zero_tokens = 0
    total_tokens = 0
    for ln in data_lines:
        for tok in re.findall(r"[+\-]?\d+(?:\.\d+)?", ln):
            total_tokens += 1
            if ZERO_VALUE_RE.match(tok):
                zero_tokens += 1
    if total_tokens < 3:
        # Pas assez de valeurs numeriques pour etablir un signal -- on laisse
        return False
    # Seuil eleve : un dataframe "resultat backtest" avec une seule vraie valeur
    # parmi des zeros = PAS une fabrication (backtest partiellement execute).
    # Le pattern #6891 = TOUTES les valeurs a 0.0 (backtest pas du tout execute).
    return (zero_tokens / total_tokens) >= 0.9


def detect_cell(cell: dict) -> list[dict]:
    """Return findings (one per fabrication signal) for a code cell."""
    if cell.get("cell_type") != "code":
        return []
    findings = []
    lines = _cell_text_outputs(cell)
    if not lines:
        return findings
    if _has_row_n(lines):
        # Compter les Row N pour contexte (un seul vs plusieurs).
        n_rows = sum(1 for ln in lines if ROW_N_RE.match(ln))
        findings.append({"signal": "row_n_placeholder", "count": n_rows})
    if _has_zero_stats_dataframe(lines):
        findings.append({"signal": "zero_stats_dataframe"})
    return findings


def scan_notebook(path: Path) -> dict:
    """Return a result dict for one notebook: path, hits[], error."""
    try:
        with open(path, encoding="utf-8") as f:
            nb = json.load(f)
    except (OSError, json.JSONDecodeError) as exc:
        return {"path": str(path), "error": str(exc), "hits": []}

    hits = []
    for ci, cell in enumerate(nb.get("cells", [])):
        for finding in detect_cell(cell):
            hits.append({"cell_index": ci, **finding})
    return {"path": str(path), "kernel": _kernel(nb), "hits": hits, "error": None}


def _kernel(nb: dict) -> str:
    return nb.get("metadata", {}).get("kernelspec", {}).get("name", "?")


# Dossiers a ignorer (alignes sur detect_blank_figures.py).
SKIP_DIRS = {
    ".lake", ".git", "__pycache__", "_archives", "archive", "_archive",
    ".ipynb_checkpoints", ".pytest_cache", "worktrees",
    "foundry-lib",  # lib vendored tierce, pas a nous a fixer
}

# Artefacts papermill (*_output.ipynb) : la source canonique est le livrable.
_OUTPUT_SUFFIX = "_output.ipynb"


def _should_skip(rel: Path) -> bool:
    if any(part in SKIP_DIRS for part in rel.parts):
        return True
    return rel.name.endswith(_OUTPUT_SUFFIX)


def _iter_notebooks(root: Path, family: str | None):
    base = root / "MyIA.AI.Notebooks"
    if family:
        base = base / family
    if not base.exists():
        return
    for nb in sorted(base.rglob("*.ipynb")):
        if _should_skip(nb.relative_to(base)):
            continue
        yield nb


def _human_report(results: list[dict]) -> str:
    total_hits = sum(len(r["hits"]) for r in results)
    affected = [r for r in results if r["hits"]]
    errored = [r for r in results if r.get("error")]
    lines = [
        f"Notebooks scanned     : {len(results)}",
        f"Fabricated outputs   : {total_hits}",
        f"Affected notebooks   : {len(affected)}",
        "",
    ]
    if not affected:
        lines.append("No fabricated text outputs detected (Row N / zero-stats dataframe check).")
        if errored:
            lines.append("")
            lines.append(f"NOTE: {len(errored)} notebook(s) unreadable (see --json for details).")
        return "\n".join(lines)
    for r in affected:
        short = r["path"].split("MyIA.AI.Notebooks")[-1].lstrip("\\/")
        lines.append(f"## {short}  [{r['kernel']}]")
        for h in r["hits"]:
            extra = ""
            if "count" in h:
                extra = f" x{h['count']}"
            lines.append(f"  - cell [{h['cell_index']}] signal: {h['signal']}{extra}")
        lines.append("")
    lines.append(
        "FIX: re-execute the cell in the real environment (QC Cloud research for "
        "QuantBook, local kernel for matplotlib) and commit the real output -- "
        "Stop&Repair, never scrub/delete to hide (secrets-hygiene rule 6)."
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
    parser.add_argument("--check", action="store_true", help="Exit 1 if any fabrication (CI-ready)")
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
