#!/usr/bin/env python3
"""Scan D2 window-openness for QC notebooks (EPIC #9768 Phase 1 outillage).

Pourquoi cet outil existe
-------------------------
L'EPIC #9768 a documente un mecanisme de degenerescence tres particulier,
qu'on appelle **D2 (fenetre non figee)** : un notebook de recherche declare
un `SetStartDate(...)` (en Python ou en C#) mais n'appelle jamais
`SetEndDate(...)`. La fenetre de backtest reste donc ouverte sur la date
courante, et **s'allonge a chaque execution**. Le meme code rend un nombre
different chaque mois -- sans que personne n'ait rien change.

Le cas-graine (#9754, `CSharp-BTC-MACD-ADX`) a montre qu'un notebook D2 peut
produire un Sharpe 0.225 le 2026-04-27 et un Sharpe 0.123 le 2026-08-06,
soit une degradation de ~46 % en 3,4 mois sur les memes parametres
committes. La barre de mesure etait `SetEndDate(2024, 12, 31)` absente.

L'audit Phase 0 (issue #9772, c.1331+13) a mesure le phenomene sur le depot
reel : 0 % des `main.py` QuantConnect sont D2+, mais **82 % des notebooks
QC (227/276)** le sont. ML-Training-Pipeline concentre 8/8 D2+ -- c'est un
cluster-specifique qui meriterait un audit dedie.

Cet outil transforme l'audit manuel (forensic au cas par cas) en un
**detecteur deterministe** utilisable en CI :

  - Scan recursive de `MyIA.AI.Notebooks/**/*.ipynb`.
  - Pour chaque notebook, evalue 3 criteres :
      1. **presence de l'ancre** (`SetEndDate(...)` Python, `SetEndDate(...)` C#,
         ou variante insensible a la casse avec parentheses non vides) ;
      2. **presence d'un appel `SetStartDate`** (sinon la notion de fenetre
         n'a pas de sens et on ne peut pas accuser D2) ;
      3. **role du notebook** : recherche (`.ipynb`) vs deployable (`main.py`,
         hors scope ici -- l'audit Phase 0 a montre 0 % sur `main.py`).
  - Verdict par notebook : `D2+` (les deux appels StartDate ET absence de
    EndDate) ou `CONFORME` (EndDate present) ou `NEUTRE` (pas de StartDate,
    notion de fenetre non-pertinente).
  - Sortie JSON + texte structure, plus un mode `--check` (CI-ready) qui
    echoue si un D2+ est detecte.

Ce qu'il DETECTE (deterministe)
-------------------------------
Trois regex compilées une seule fois au chargement :

  - ``RE_SET_END_DATE`` : matche `SetEndDate(...)` (Python ou C#) en tolerant
    les variantes typiques (`SetEndDate(2024,12,31)`, `SetEndDate(2024, 12, 31)`,
    `algorithm.SetEndDate(...)`, `self.SetEndDate(...)`).
  - ``RE_SET_START_DATE`` : matche `SetStartDate(...)` avec la meme tolerance.
  - ``RE_QC_CONTEXT`` : matche un token QuantConnect (`QuantConnect.Algorithm`,
    `QCAlgorithm`, `QuantBook`, `self.History`) pour eviter les faux positifs
    sur des notebooks Python non-QC qui parlent de "set_end_date" dans un
    autre contexte (matplotlib, pandas).

Un notebook est **D2+** si et seulement si les 3 conditions sont reunies :

    1. RE_QC_CONTEXT matche au moins une fois dans le code ;
    2. RE_SET_START_DATE matche au moins une fois ;
    3. RE_SET_END_DATE ne matche **JAMAIS** dans le code **ni dans les
       sorties de cellules** (un notebook qui ecrit "pas de SetEndDate"
       dans un print n'est pas D2+ ; un notebook qui appelle
       `SetEndDate(...)` est conforme).

Ce qu'il NE fait PAS (par design)
---------------------------------
- Pas de modification : comme les autres detecteurs de la partition
  (`detect_quantbook_window_divergence.py`, `detect_blank_figures.py`, etc.),
  il signale, il ne corrige pas. La correction est un changement de code
  qui doit passer par une PR dediee (Phase 2+ de #9768).
- Pas de re-execution : on parse le JSON du notebook tel qu'il est sur le
  disque (cf C.2 : les outputs font partie du livrable).
- Pas de classification "valide/invalide" sur le fond : un D2+ peut etre
  legitime (recherche exploratoire sur donnees "latest", comparaisons
  long-terme). On **rapporte**, le jugement reste humain.
- Pas de substitution yfinance / fallback : la machine qui heberge le
  notebook (GPU1, RTX 3070, etc.) n'a aucune influence sur le verdict ;
  on lit le fichier, c'est tout.

Usage
-----
  # Rapport JSON par defaut, stdout
  python scripts/notebook_tools/scan_d2_window_openness.py

  # Rapport texte structure (lecture humaine)
  python scripts/notebook_tools/scan_d2_window_openness.py --format text

  # Scan d'un sous-dossier (utile pour Phase 2 ciblee ML-Training-Pipeline)
  python scripts/notebook_tools/scan_d2_window_openness.py MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline

  # Mode CI : exit 0 si 0 D2+, exit 1 sinon (permet de cable un gate)
  python scripts/notebook_tools/scan_d2_window_openness.py --check

Sortie type (--format text)
---------------------------
  QC-Notebooks D2+ (fenetre non figee) : 227/276 (82 %)
  QC-Notebooks conformes (EndDate OK)   : 49/276 (18 %)
  QC-Notebooks sans SetStartDate (N/A)  : 0/276 (0 %)
  ---
  Echantillon D2+ (10 premiers) :
    MyIA.AI.Notebooks/QuantConnect/kelly_lean/Kelly_companion.ipynb
    MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/c875_hmm_alpha_dm_research.ipynb
    ...

Voir aussi
----------
- Issue #9772 (Phase 0 audit, c.1331+13) -- mesure empirique 227/276 D2+
- EPIC #9768 -- cadre methodologique (D1-D6)
- .claude/rules/audit-cross-source-distillation.md -- regle HARD 1 :
  aucun rapport committe (sorties de l'audit = dashboard + issues filles)
- `scripts/notebook_tools/detect_quantbook_window_divergence.py` --
  detecteur sibling sur le mecanisme A/B (lookback non disclosure),
  distinct de D2 (fenetre ouverte)
- `MEMORY.md` section "Lecons durables" -- c.1331+13-L1 ★★ (grep -L MSYS
  non fiable : on utilise ici pathlib natif, pas grep, donc immune).
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any

# -----------------------------------------------------------------------------
# Constantes
# -----------------------------------------------------------------------------

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
DEFAULT_ROOT = REPO_ROOT / "MyIA.AI.Notebooks"


# -----------------------------------------------------------------------------
# Regex (compilees une fois)
# -----------------------------------------------------------------------------
# On tolere :
#   - qualificateur optionnel (`self.`, `algorithm.`, `qb.`, `algo.`)
#   - casse libre (SetEndDate, set_end_date, SETENDDATE)
#   - espaces optionnels autour des parentheses et des virgules
# L'argument entre parentheses doit etre non vide (au moins un caractere),
# sinon `SetEndDate()` vide est un faux negatif -- pas une absence.

RE_SET_END_DATE = re.compile(
    r"\b(?:[a-zA-Z_][a-zA-Z0-9_]*\s*\.\s*)?"  # qualificateur optionnel (ex: qb./algorithm./self.)
    r"[Ss][Ee][Tt]_?[Ee][Nn][Dd]_?[Dd][Aa][Tt][Ee]"  # SetEndDate ou set_end_date
    r"\s*\(\s*\S[^)]*\)?",  # parenthese ouvrante + arg non vide
)

RE_SET_START_DATE = re.compile(
    r"\b(?:[a-zA-Z_][a-zA-Z0-9_]*\s*\.\s*)?"
    r"[Ss][Ee][Tt]_?[Ss][Tt][Aa][Rr][Tt]_?[Dd][Aa][Tt][Ee]"
    r"\s*\(\s*\S[^)]*\)?",
)

# Marqueurs QuantConnect : on accepte les namespaces C# ET Python, plus
# l'API History (Python) et les classes framework (QCAlgorithm). Un notebook
# qui mentionne `pandas.set_option` n'est PAS un contexte QC.

RE_QC_CONTEXT = re.compile(
    r"(?:\bQuantConnect\.\w+"           # namespace C#
    r"|\bQCAlgorithm\b"                 # classe de base C#
    r"|\bQuantBook\s*\("               # instanciation Python
    r"|\bself\.History\s*\("            # API History Python
    r"|\balgorithm\.Set\w+\s*\("       # appel algorithm.SetXxx
    r")",
)


# -----------------------------------------------------------------------------
# Parsing du notebook
# -----------------------------------------------------------------------------

def _extract_code_and_outputs(nb: dict) -> tuple[str, str]:
    """Concatene le source de toutes les cellules code + toutes les sorties.

    On scanne a la fois le code ET les outputs : un notebook qui imprime
    "pas de SetEndDate" dans une cellule n'est pas D2+ (la mention est
    divulgation, pas absence). Inversement, un notebook qui APPELLE
    SetEndDate(...) dans une cellule est conforme -- on regarde le code.

    Returns:
        (code_source, outputs_text)
    """
    code_parts: list[str] = []
    outputs_parts: list[str] = []
    for cell in nb.get("cells", []):
        if cell.get("cell_type") != "code":
            continue
        src = cell.get("source", "")
        if isinstance(src, list):
            src = "".join(src)
        code_parts.append(src)
        for out in cell.get("outputs", []):
            if isinstance(out, dict):
                # text/plain (print) ou stream (stdout/stderr)
                if "text" in out:
                    text = out["text"]
                    if isinstance(text, list):
                        text = "".join(text)
                    outputs_parts.append(str(text))
                elif "data" in out:
                    data = out["data"]
                    if isinstance(data, dict) and "text/plain" in data:
                        plain = data["text/plain"]
                        if isinstance(plain, list):
                            plain = "".join(plain)
                        outputs_parts.append(str(plain))
    return "\n".join(code_parts), "\n".join(outputs_parts)


def classify_notebook(path: Path) -> dict[str, Any]:
    """Classifie un notebook selon le verdict D2+/CONFORME/NEUTRE.

    Returns:
        dict avec les cles : path, verdict, has_set_start, has_set_end,
        has_qc_context, error (le cas echeant).
    """
    # ``path.relative_to(REPO_ROOT)`` plante pour les notebooks hors-repo
    # (tests pytest dans tmp_path, scan d'un chemin absolu exterieur). On
    # retombe sur le chemin absolu pour ne pas faire echouer la classification.
    try:
        path_str = str(path.relative_to(REPO_ROOT))
    except ValueError:
        path_str = str(path)
    rec: dict[str, Any] = {
        "path": path_str,
        "verdict": "UNKNOWN",
        "has_set_start": False,
        "has_set_end": False,
        "has_qc_context": False,
        "error": None,
    }
    try:
        with path.open("r", encoding="utf-8") as f:
            nb = json.load(f)
    except (json.JSONDecodeError, UnicodeDecodeError, OSError) as e:
        rec["error"] = f"{type(e).__name__}: {e}"
        return rec

    code, outputs = _extract_code_and_outputs(nb)
    rec["has_qc_context"] = bool(RE_QC_CONTEXT.search(code))
    rec["has_set_start"] = bool(RE_SET_START_DATE.search(code))
    # SetEndDate : on scanne le code ET les outputs (divulgation)
    rec["has_set_end"] = bool(
        RE_SET_END_DATE.search(code) or RE_SET_END_DATE.search(outputs)
    )

    if not rec["has_qc_context"] and not rec["has_set_start"]:
        rec["verdict"] = "NEUTRE"
    elif rec["has_set_end"]:
        rec["verdict"] = "CONFORME"
    elif rec["has_set_start"] and rec["has_qc_context"]:
        rec["verdict"] = "D2+"
    elif rec["has_set_start"]:
        # SetStartDate sans contexte QC detecte -- peut etre un faux positif
        # (matplotlib, pandas). On classe NEUTRE avec note.
        rec["verdict"] = "NEUTRE"
    else:
        rec["verdict"] = "NEUTRE"
    return rec


# -----------------------------------------------------------------------------
# Scan
# -----------------------------------------------------------------------------

def iter_notebooks(root: Path) -> list[Path]:
    """Liste tous les ``.ipynb`` sous ``root`` (recursif), tries par chemin."""
    if not root.exists():
        return []
    return sorted(root.rglob("*.ipynb"))


def scan(root: Path) -> dict[str, Any]:
    """Scan complet, retourne un rapport structure."""
    notebooks = iter_notebooks(root)
    verdicts: dict[str, int] = {"D2+": 0, "CONFORME": 0, "NEUTRE": 0, "UNKNOWN": 0}
    d2_samples: list[str] = []
    conforme_samples: list[str] = []
    errors: list[dict[str, str]] = []

    for nb_path in notebooks:
        rec = classify_notebook(nb_path)
        verdicts[rec["verdict"]] = verdicts.get(rec["verdict"], 0) + 1
        if rec["error"]:
            errors.append({"path": rec["path"], "error": rec["error"]})
        elif rec["verdict"] == "D2+":
            if len(d2_samples) < 10:
                d2_samples.append(rec["path"])
        elif rec["verdict"] == "CONFORME":
            if len(conforme_samples) < 10:
                conforme_samples.append(rec["path"])

    total = sum(verdicts.values())
    return {
        "root": str(root.relative_to(REPO_ROOT)),
        "total": total,
        "verdicts": verdicts,
        "d2_rate_pct": round(verdicts["D2+"] / total * 100, 1) if total else 0.0,
        "d2_samples": d2_samples,
        "conforme_samples": conforme_samples,
        "errors": errors,
    }


# -----------------------------------------------------------------------------
# CLI
# -----------------------------------------------------------------------------

def _format_text(report: dict[str, Any]) -> str:
    v = report["verdicts"]
    total = report["total"]
    lines = [
        f"QC-Notebooks D2+ (fenetre non figee) : {v.get('D2+', 0)}/{total} "
        f"({report['d2_rate_pct']} %)",
        f"QC-Notebooks conformes (EndDate OK)   : {v.get('CONFORME', 0)}/{total}",
        f"QC-Notebooks sans SetStartDate (N/A)  : {v.get('NEUTRE', 0)}/{total}",
        f"QC-Notebooks illisibles              : {v.get('UNKNOWN', 0)}/{total}",
        "---",
    ]
    if report["d2_samples"]:
        lines.append("Echantillon D2+ (10 premiers) :")
        lines.extend(f"  {p}" for p in report["d2_samples"])
    if report["conforme_samples"]:
        lines.append("Echantillon CONFORME (10 premiers) :")
        lines.extend(f"  {p}" for p in report["conforme_samples"])
    if report["errors"]:
        lines.append("Erreurs de lecture :")
        lines.extend(f"  {e['path']}: {e['error']}" for e in report["errors"])
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Scan D2 window-openness for QC notebooks (EPIC #9768 Phase 1). "
            "Detecte les notebooks qui declarent SetStartDate mais n'appellent "
            "jamais SetEndDate (fenetre de backtest ouverte sur la date courante)."
        )
    )
    parser.add_argument(
        "root",
        nargs="?",
        default=str(DEFAULT_ROOT),
        help=(
            "Racine du scan (defaut : MyIA.AI.Notebooks/). "
            "Cibler un sous-dossier (ex. ML-Training-Pipeline) pour un audit cible."
        ),
    )
    parser.add_argument(
        "--format",
        choices=["json", "text"],
        default="json",
        help="Format de sortie (defaut : json).",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help=(
            "Mode CI : exit 0 si 0 D2+ detectes, exit 1 sinon. "
            "Permet de cabler un gate progressif (Phase 2+) qui se durcit "
            "au fil de l'assainissement."
        ),
    )
    args = parser.parse_args(argv)

    root = Path(args.root)
    if not root.is_absolute():
        root = REPO_ROOT / root

    report = scan(root)

    if args.format == "json":
        print(json.dumps(report, indent=2, ensure_ascii=False))
    else:
        print(_format_text(report))

    if args.check and report["verdicts"].get("D2+", 0) > 0:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())