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

Historique de la mesure (IMPORTANT -- ne pas propager la mesure #9772) :

  - L'audit Phase 0 (issue #9772, c.1331+13) avait rapporte **82 % de D2+
    (227/276)** via un grep manuel `set_end_date`. Cette mesure SUR-COMPTAIT :
    elle incluait ~87 notebooks **sans aucune API QC** (ni QuantBook, ni
    QCAlgorithm, ni add_equity/set_start_date) sur lesquels `set_end_date` est
    un no-op ou un NameError. Les 8 notebooks `ML-Training-Pipeline/` cibles
    du correctif propose etaient tous dans ces 87 -- les ajouter aurait ete
    "satisfaire le grep sans corriger le defaut" (motif #1214).
  - Refute firsthand (issue #10230, re-mesure G.1) : ce probe deterministe
    rapporte **3/207 (1.4 %)** car il ne capte que la **forme S** (SetStartDate
    sans SetEndDate). Les 3 autres formes de drift -- N (`datetime.now()`),
    L (`qb.History(sym, N)` lookback-count), T (`timedelta`) -- qui constituent
    la majorite des drift reels, ECHAPPENT a ce probe.
  - Le detecteur canonique des 4 formes est ``scan_window_drift.py`` (#10235),
    qui rapporte ~31/207 DRIFT (verdicts DRIFT/PINNED/INDETERMINE/N-A).
    **Pour mesurer le D2 reel, utiliser scan_window_drift.py, pas ce probe.**

Ce probe reste utile comme **filtre forme-S** rapide (SetStartDate explicite
sans SetEndDate, le sous-ensemble le plus facile a corriger) et pour le scope
Phase 2 des sources deployables (``main.py`` / ``Main.cs``) non couvert par
scan_window_drift.py.

Cet outil transforme l'audit manuel (forensic au cas par cas) en un
**detecteur deterministe** utilisable en CI :

  - Scan recursive de `MyIA.AI.Notebooks/**/*.ipynb` (Phase 1) **et**
    `MyIA.AI.Notebooks/QuantConnect/projects/**/main.py` + `Main.cs`
    (Phase 2 -- deployables QC, FP-2 fix : commentaires strippes avant
    regex pour eviter le faux negatif documente sur `CSharp-BTC-MACD-ADX`).
  - Pour chaque fichier, evalue 3 criteres :
      1. **presence de l'ancre** (`SetEndDate(...)` Python, `SetEndDate(...)` C#,
         ou variante insensible a la casse avec parentheses non vides) ;
      2. **presence d'un appel `SetStartDate`** (sinon la notion de fenetre
         n'a pas de sens et on ne peut pas accuser D2) ;
      3. **role du fichier** : recherche (`.ipynb`) vs deployable (`main.py` /
         `Main.cs`, scope Phase 2).
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
  Total D2+ (fenetre non figee)       : 3/207 (1.4 %)   <- forme S seule
  Total CONFORME (EndDate OK)         : 43/207
  Total NEUTRE (sans SetStartDate)    : 161/207

  NOTE : ce probe ne capte que la forme S (SetStartDate sans SetEndDate).
  Les formes N/L/T (datetime.now / lookback-count / timedelta) echappent ;
  elles sont mesurees par scan_window_drift.py (~31/207 DRIFT, 4 formes).
  Voir issue #10230 (refutation firsthand de la mesure 82 % de #9772).
  ---
  Echantillon D2+ (10 premiers) :
    MyIA.AI.Notebooks/QuantConnect/kelly_lean/Kelly_companion.ipynb
    MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/c875_hmm_alpha_dm_research.ipynb
    ...

Voir aussi
----------
- Issue #9772 (Phase 0 audit, c.1331+13) -- mesure empirique 227/276 D2+
  **SUR-COMPTEE** (grep manuel incluant ~87 notebooks sans API QC = no-op).
  Refutee firsthand par issue #10230 (re-mesure G.1) : vrai D2 multi-forme
  ~9.5 %, ce probe forme-S = 1.4 %. NE PAS reprendre la mesure 82 %/#9772.
- Issue #10230 -- refutation de la mesure #9772 + diagnostic des 4 formes.
- ``scan_window_drift.py`` (#10235) -- detecteur CANONIQUE D2 (4 formes
  N/L/T/S, verdicts DRIFT/PINNED/INDETERMINE/N-A). A utiliser pour la mesure
  reelle ; ce probe est le filtre forme-S + scope sources deployables.
- EPIC #9768 -- cadre methodologique (D1-D6)
- .claude/rules/audit-cross-source-distillation.md -- regle HARD 1 :
  aucun rapport committe (sorties de l'audit = dashboard + issues filles)
- `scripts/notebook_tools/detect_quantbook_window_divergence.py` --
  detecteur sibling sur le mecanisme A/B (lookback non disclosure),
  distinct de D2 (fenetre ouverte)
- `MEMORY.md` section "Lecons durables" -- c.1331+13-L1 ★★ (grep -L MSYS
  non fiable : on utilise ici pathlib natif, pas grep, donc immune).
- c.1331+16 -- Phase 2 : extension scope aux sources `.cs`/`.py` deployees
  sur QC Cloud, avec fix FP-2 (commentaires strippes avant regex). Le
  cas-graine `CSharp-BTC-MACD-ADX/Main.cs` passe de faux CONFORME a
  veridique D2+.
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
        dict avec les cles : path, file_type, verdict, has_set_start,
        has_set_end, has_qc_context, error (le cas echeant).
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
        "file_type": "ipynb",
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
# Sources QC (.cs / .py)
# -----------------------------------------------------------------------------

def _strip_comments(source: str, file_type: str) -> str:
    """Neutralise les commentaires avant regex, par type de fichier.

    Pourquoi ce stripping :
      - C# : ``// commentaire`` (fin de ligne) + ``/* commentaire */`` (bloc).
      - Python : ``# commentaire`` (fin de ligne, PAS de bloc natif).

    On NE supprime pas -- on REMPLACE par des espaces de meme longueur, pour
    que les numeros de ligne ne soient pas decales (utile si on voulait un
    jour reporter une position). Pour l'instant le verdict binaire n'en a
    pas besoin, mais l'invariant est preserve.

    Note : on ne parse PAS les chaines (``"...\\n// not a comment"``). Un
    commentaire a l'interieur d'une string litterale passerait au travers.
    Faux negatif assume sur corpus QC reel -- aucun cas mesure.
    """
    if file_type == "cs":
        # // ... \n
        out = re.sub(r"//[^\n]*", lambda m: " " * len(m.group(0)), source)
        # /* ... */ (non-greedy, multi-line)
        out = re.sub(
            r"/\*.*?\*/",
            lambda m: " " * len(m.group(0)),
            out,
            flags=re.DOTALL,
        )
        return out
    elif file_type == "py":
        # # ... \n  (le caractere # n'a pas d'autre role syntaxique en Python)
        return re.sub(r"#[^\n]*", lambda m: " " * len(m.group(0)), source)
    else:
        raise ValueError(f"file_type inconnu: {file_type}")


def classify_source(path: Path, file_type: str) -> dict[str, Any]:
    """Classifie une source QC (.cs ou .py) selon le verdict D2+/CONFORME/NEUTRE.

    Meme logique que ``classify_notebook``, mais :
      - on strippe les commentaires AVANT la recherche regex (FP-2 fix pour
        les ``// SetEndDate(...)`` commentes -- le cas-graine
        ``CSharp-BTC-MACD-ADX/Main.cs`` contient 14 ``//SetStartDate`` /
        ``//SetEndDate`` commentes + 1 ``SetStartDate(2019, 4, 1)`` reel).
      - on ne regarde PAS les outputs (un .py/.cs n'en a pas ; le verdict
        porte sur le code execute).
    """
    try:
        path_str = str(path.relative_to(REPO_ROOT))
    except ValueError:
        path_str = str(path)
    rec: dict[str, Any] = {
        "path": path_str,
        "file_type": file_type,
        "verdict": "UNKNOWN",
        "has_set_start": False,
        "has_set_end": False,
        "has_qc_context": False,
        "error": None,
    }
    try:
        raw_text = path.read_text(encoding="utf-8")
    except (UnicodeDecodeError, OSError) as e:
        rec["error"] = f"{type(e).__name__}: {e}"
        return rec

    code = _strip_comments(raw_text, file_type)
    rec["has_qc_context"] = bool(RE_QC_CONTEXT.search(code))
    rec["has_set_start"] = bool(RE_SET_START_DATE.search(code))
    rec["has_set_end"] = bool(RE_SET_END_DATE.search(code))

    if not rec["has_qc_context"] and not rec["has_set_start"]:
        rec["verdict"] = "NEUTRE"
    elif rec["has_set_end"]:
        rec["verdict"] = "CONFORME"
    elif rec["has_set_start"] and rec["has_qc_context"]:
        rec["verdict"] = "D2+"
    elif rec["has_set_start"]:
        # SetStartDate sans contexte QC detecte -- peut etre un faux positif
        # (autre framework). On classe NEUTRE avec note.
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


def iter_sources(root: Path) -> list[tuple[Path, str]]:
    """Liste les sources QC strategiques sous ``root``.

    Cible :
      - ``MyIA.AI.Notebooks/QuantConnect/projects/**/main.py`` (Python)
      - ``MyIA.AI.Notebooks/QuantConnect/projects/**/Main.cs`` (C#)

    Pourquoi restreint a ``projects/`` : c'est la OU vivent les deployables
    (strategies committees, code execute sur QC Cloud). Les notebooks
    ``.ipynb`` vivent ailleurs (ML-Training-Pipeline, kelly_lean, etc.) et
    sont deja couverts par ``iter_notebooks``. Les scripts ``scripts/*.py``
    internes au tooling ne sont pas strategiques -- le scan du tooling QC
    est realise par d'autres outils (``detect_quantbook_window_divergence``).

    Returns:
        liste de tuples ``(chemin, file_type)`` ou ``file_type in {"py", "cs"}``.
    """
    if not root.exists():
        return []
    # ``root`` designe generalement le repo lui-meme (DEFAULT_ROOT =
    # ``<repo>/MyIA.AI.Notebooks`` quand ``iter_notebooks`` est appele avec
    # DEFAULT_ROOT). Pour rester robuste aux deux cas on essaie d'abord
    # ``<root>/MyIA.AI.Notebooks/QuantConnect/projects`` puis fallback sur
    # ``<root>/QuantConnect/projects``.
    candidates = [
        root / "MyIA.AI.Notebooks" / "QuantConnect" / "projects",
        root / "QuantConnect" / "projects",
    ]
    qc_projects = next((c for c in candidates if c.exists()), None)
    if qc_projects is None:
        return []
    out: list[tuple[Path, str]] = []
    for p in sorted(qc_projects.rglob("main.py")):
        out.append((p, "py"))
    for p in sorted(qc_projects.rglob("Main.cs")):
        out.append((p, "cs"))
    return out


def scan(root: Path) -> dict[str, Any]:
    """Scan complet, retourne un rapport structure.

    Combine :
      - ``.ipynb`` (notebooks de recherche) -- ``iter_notebooks``
      - ``main.py`` / ``Main.cs`` (deployables QC) -- ``iter_sources``

    Les verdicts sont agregees dans le meme compteur. Les echantillons
    distinguent les deux populations par le prefixe du chemin (deploiement =
    ``MyIA.AI.Notebooks/QuantConnect/projects/``).
    """
    verdicts: dict[str, int] = {"D2+": 0, "CONFORME": 0, "NEUTRE": 0, "UNKNOWN": 0}
    by_type: dict[str, dict[str, int]] = {}
    d2_samples: list[str] = []
    conforme_samples: list[str] = []
    errors: list[dict[str, str]] = []

    for nb_path in iter_notebooks(root):
        rec = classify_notebook(nb_path)
        verdicts[rec["verdict"]] = verdicts.get(rec["verdict"], 0) + 1
        by_type.setdefault("ipynb", {}).setdefault(rec["verdict"], 0)
        by_type["ipynb"][rec["verdict"]] += 1
        if rec["error"]:
            errors.append({"path": rec["path"], "error": rec["error"]})
        elif rec["verdict"] == "D2+":
            if len(d2_samples) < 10:
                d2_samples.append(rec["path"])
        elif rec["verdict"] == "CONFORME":
            if len(conforme_samples) < 10:
                conforme_samples.append(rec["path"])

    for path, file_type in iter_sources(root):
        rec = classify_source(path, file_type)
        verdicts[rec["verdict"]] = verdicts.get(rec["verdict"], 0) + 1
        by_type.setdefault(file_type, {}).setdefault(rec["verdict"], 0)
        by_type[file_type][rec["verdict"]] += 1
        if rec["error"]:
            errors.append({"path": rec["path"], "error": rec["error"]})
        elif rec["verdict"] == "D2+":
            if len(d2_samples) < 10:
                d2_samples.append(rec["path"])
        elif rec["verdict"] == "CONFORME":
            if len(conforme_samples) < 10:
                conforme_samples.append(rec["path"])

    total = sum(verdicts.values())
    # ``root.relative_to(REPO_ROOT)`` plante pour les chemins hors-repo
    # (tests pytest dans tmp_path). On retombe sur le chemin absolu pour ne
    # pas faire echouer le scan sur une sortie JSON de pure documentation.
    try:
        root_str = str(root.relative_to(REPO_ROOT))
    except ValueError:
        root_str = str(root)
    return {
        "root": root_str,
        "total": total,
        "verdicts": verdicts,
        "by_type": by_type,
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
    by_type = report.get("by_type", {})
    lines = [
        f"Total D2+ (fenetre non figee)       : {v.get('D2+', 0)}/{total} "
        f"({report['d2_rate_pct']} %)",
        f"Total CONFORME (EndDate OK)         : {v.get('CONFORME', 0)}/{total}",
        f"Total NEUTRE (sans SetStartDate)    : {v.get('NEUTRE', 0)}/{total}",
        f"Total UNKNOWN (illisibles)          : {v.get('UNKNOWN', 0)}/{total}",
        "---",
        "Repartition par type de fichier :",
    ]
    for ftype, counts in sorted(by_type.items()):
        sub_total = sum(counts.values())
        sub_d2 = counts.get("D2+", 0)
        sub_rate = round(sub_d2 / sub_total * 100, 1) if sub_total else 0.0
        lines.append(
            f"  {ftype:6s} : {sub_total} fichiers, "
            f"D2+ {sub_d2}/{sub_total} ({sub_rate} %), "
            f"CONFORME {counts.get('CONFORME', 0)}, "
            f"NEUTRE {counts.get('NEUTRE', 0)}, "
            f"UNKNOWN {counts.get('UNKNOWN', 0)}"
        )
    lines.append("---")
    if report["d2_samples"]:
        lines.append("Echantillon D2+ (10 premiers) :")
        lines.extend(f"  {p}" for p in report["d2_samples"])
    if report["conforme_samples"]:
        lines.append("Echantillon CONFORME (10 premiers) :")
        lines.extend(f"  {p}" for p in report["conforme_samples"])
    if report["errors"]:
        lines.append("Erreurs de lecture :")
        lines.extend(f"  {e['path']}: {e['error']}" for e in report["errors"])
    # Advisory : ce probe ne capte que la forme S (SetStartDate sans SetEndDate).
    # Les formes N/L/T (datetime.now / lookback-count / timedelta) echappent et
    # sont mesurees par scan_window_drift.py. Voir #10230 (refutation 82 %/#9772).
    lines.append("---")
    lines.append(
        "NOTE : ce probe capte la forme S (SetStartDate sans SetEndDate) "
        "uniquement."
    )
    lines.append(
        "      Formes N/L/T (datetime.now / qb.History(N) / timedelta) -> "
        "scan_window_drift.py (#10235, 4 formes, ~31 DRIFT)."
    )
    lines.append("      La mesure 82 % de #9772 etait SUR-COMPTEE (refutee #10230).")
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

    # Une racine inexistante doit echouer distinctement d'un succes (exit 0)
    # ou d'un D2+ detecte (exit 1). Convention argparse : exit 2 = erreur
    # d'usage (chemin invalide). Sans cette garde, un job Actions avec un
    # chemin mal tape passerait exit 1 (D2+) sur 0 fichier scanne -- ce qui
    # a deja faussé un audit Phase 0 (cf review ai-01 sur #9783).
    if not root.exists():
        print(
            f"error: chemin introuvable: {root}",
            file=sys.stderr,
        )
        return 2
    if not root.is_dir():
        print(
            f"error: chemin pas un repertoire: {root}",
            file=sys.stderr,
        )
        return 2

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