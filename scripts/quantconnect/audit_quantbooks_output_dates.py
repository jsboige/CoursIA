#!/usr/bin/env python3
"""QuantConnect quantbook output-date freshness auditor (ai-01 c.40, #8734).

Pourquoi cet outil existe
-------------------------
``audit_quantbooks_unexec.py`` (issue #6891) detecte l'absence d'EXECUTION
(``execution_count is None``, ``outputs == []``, ``output_type == "error"``).
``check_data_freshness.py`` (#8734, #8737) detecte la STAGNATION des ZIPS qui
nourrissent les notebooks. Aucun des deux n'attrape le cas ou un notebook
porte des sorties **anciennes** malgre un ``execution_count`` bien rempli :
un quantbook dont la sortie la plus fraiche date d'il y a trois mois affiche
une integrite formelle parfaite (H.5 EXEC_PROVED) tout en decrivant un marche
qui n'existe plus. C'est le defaut qu'aucun compte de cellules ne voit.

ai-01 c.40 (msg-20260729T000258) l'a nomme explicitement : « le champ qui
m'interesse le plus est la date la plus recente dans les sorties. C'est lui
qui distingue un notebook re-execute d'un notebook qui porte des sorties
anciennes avec un execution_count bien rempli ».

Ce qu'il fait (DETECTION, pas correction)
-----------------------------------------
Pour chaque ``quantbook.ipynb`` d'un dossier projets, extrait des OUTPUTS
commits :

  - ``exec_cells`` / ``total_code_cells`` -- couverture d'execution.
  - ``error_cells`` -- cellules dont une sortie est ``output_type == "error"``.
  - ``latest_exec_date`` -- la date la plus **recente** mentionnee dans les
    sorties (dates ISO ``YYYY-MM-DD`` ou ``YYYYMMDD`` parsee dans le texte
    des outputs). **C'est le pivot de fraicheur.**
  - ``latest_backtest_period_date`` -- la date la plus recente **typant une
    periode de backtest** (heuristique explicite, voir ci-dessous).
  - ``guard_present`` -- presence d'un fail-fast guard C942-L/C951-L
    (``fillDataForward`` / ``flat tail`` / ``C941`` / ``C942``).
  - ``verdict`` -- EXEC_PROVED_FRESH / STALE_OUTPUTS / PERIOD_DOMINATED_AGED /
    PERIOD_DOMINATED_RECENT / EXEC_PROVED_NO_DATE / INCOMPLETE / HAS_ERRORS /
    READ_ERROR. See ``_classify_freshness`` for the period-dominance nuance.

Distinction execution-date vs backtest-period-date (HARD, ai-01 c.40)
--------------------------------------------------------------------
ai-01 previent le faux positif inverse : les dates de **periode de
backtest** (``2025-12-31`` dans un ``SetEndDate`` ou un print ``Periode:
... a 2025-12-31``) NE sont PAS des dates d'execution. Les confondre ferait
crier au loup sur chaque notebook. Plutot qu'inventer une heuristique qui
se trompe, l'outil **rapporte les deux colonnes separement** :

  - ``latest_exec_date`` = TOUTE date ISO trouvee dans les outputs (fourchette
    haute : peut inclure une periode de backtest future).
  - ``latest_backtest_period_date`` = date isolee typant une periode
    (heuristique : mentionnee dans une ligne contenant ``Periode`` / ``Period``
    / ``SetEndDate`` / ``Start`` / ``End`` / ``a`` / ``to``).

Un notebook dont ``latest_exec_date`` est plus recent que
``latest_backtest_period_date`` est probablement re-execute sur data fraiche.
Un notebook dont les deux coincident a une vieille date est suspect de
sorties agees. Le verdict final est **conservateur** : il ne crie STALE que
si la date la plus recente dans les outputs est **anterieure au seuil** --
parce que si meme la mention la plus fraiche dans tout le notebook est
vieille, les sorties sont vieilles quelle que soit la nature (periode ou
execution) de cette mention.

Usage
-----
    python audit_quantbooks_output_dates.py
    python audit_quantbooks_output_dates.py --root <projets-dir>
    python audit_quantbooks_output_dates.py --min-year 2025
    python audit_quantbooks_output_dates.py --json   # machine-readable
    python audit_quantbooks_output_dates.py --no-fail  # always exit 0

Operationalise la lecon C942-L generalisee : presence != fraicheur, et
``execution_count`` rempli != sorties recentes. See #8734, #8737, #7575.
"""
from __future__ import annotations

import argparse
import datetime as _dt
import json
import re
import sys
from pathlib import Path

# Date patterns: ISO YYYY-MM-DD and compact YYYYMMDD (both appear in QC outputs).
_ISO_DATE = re.compile(r"(20\d{2})-(\d{2})-(\d{2})")
_COMPACT_DATE = re.compile(r"\b(20\d{2})(\d{2})(\d{2})\b")
# Lines that signal a backtest *period* (config), not an execution instant.
_PERIOD_HINT = re.compile(
    r"(?i)(periode|p[eé]riode|period|setenddate|setstartdate|start|end|de|a|to|from|window|fen[eê]tre|range|train|test|backtest)"
)


def _all_dates_in_text(text: str) -> list[str]:
    """Return ISO-normalized YYYY-MM-DD dates found in text (dedup, sorted)."""
    found: set[str] = set()
    for m in _ISO_DATE.finditer(text or ""):
        y, mo, d = int(m.group(1)), int(m.group(2)), int(m.group(3))
        if 1 <= mo <= 12 and 1 <= d <= 31:
            found.add(f"{y:04d}-{mo:02d}-{d:02d}")
    for m in _COMPACT_DATE.finditer(text or ""):
        y, mo, d = int(m.group(1)), int(m.group(2)), int(m.group(3))
        if 1 <= mo <= 12 and 1 <= d <= 31:
            found.add(f"{y:04d}-{mo:02d}-{d:02d}")
    return sorted(found)


def _cell_output_text(cell: dict) -> str:
    """Flatten a code cell's outputs to a single text blob (stream + data text)."""
    parts: list[str] = []
    for o in cell.get("outputs") or []:
        if not isinstance(o, dict):
            continue
        t = o.get("text")
        if isinstance(t, str):
            parts.append(t)
        elif isinstance(t, list):
            parts.extend(x for x in t if isinstance(x, str))
        data = o.get("data") or {}
        if isinstance(data, dict):
            for key, val in data.items():
                if key.startswith("text/"):
                    if isinstance(val, str):
                        parts.append(val)
                    elif isinstance(val, list):
                        parts.extend(x for x in val if isinstance(x, str))
    return "\n".join(parts)


def _guard_present(nb: dict) -> bool:
    """Detect a fail-fast freshness guard (C941-L/C942-L/C951-L) in any code cell."""
    needles = ("filldataforward", "fill_data_forward", "flat tail", "flat-tail",
               "c941", "c942", "c951", "fail-fast guard", "fail_fast guard",
               "tail(60).std", "regenerate via provision_lean_data")
    blob = json.dumps(nb, ensure_ascii=False).lower()
    return any(n in blob for n in needles)


def scan_notebook(path: Path) -> dict:
    """Scan one quantbook. Returns a structured verdict dict (never raises)."""
    result: dict = {"notebook": str(path), "error": None}
    try:
        nb = json.loads(path.read_text(encoding="utf-8"))
    except Exception as exc:  # noqa: BLE001 -- report, don't crash the scan
        result.update({"verdict": "READ_ERROR", "error": str(exc)})
        return result

    code_cells = [c for c in nb.get("cells", []) if c.get("cell_type") == "code"]
    total = len(code_cells)
    exec_cells = sum(1 for c in code_cells if c.get("execution_count") is not None)
    error_cells = sum(
        1
        for c in code_cells
        for o in (c.get("outputs") or [])
        if isinstance(o, dict) and o.get("output_type") == "error"
    )

    all_dates: set[str] = set()
    period_dates: set[str] = set()
    for c in code_cells:
        # dates from outputs
        out_text = _cell_output_text(c)
        for d in _all_dates_in_text(out_text):
            all_dates.add(d)
        # dates from source that look like period config
        src = "".join(c.get("source") or []) if isinstance(c.get("source"), list) else (c.get("source") or "")
        for line in src.split("\n"):
            if _PERIOD_HINT.search(line):
                for d in _all_dates_in_text(line):
                    period_dates.add(d)
        # also: a "Periode: X a Y" print output line counts as period config
        for line in out_text.split("\n"):
            if _PERIOD_HINT.search(line):
                for d in _all_dates_in_text(line):
                    period_dates.add(d)

    latest_exec = max(all_dates) if all_dates else None
    latest_period = max(period_dates) if period_dates else None
    guard = _guard_present(nb)

    result.update({
        "total_code_cells": total,
        "exec_cells": exec_cells,
        "error_cells": error_cells,
        "guard_present": guard,
        "latest_exec_date": latest_exec,
        "latest_backtest_period_date": latest_period,
    })

    # Verdict (conservative -- never cry wolf on a backtest-period date alone).
    if exec_cells < total or total == 0:
        result["verdict"] = "INCOMPLETE"
    elif error_cells > 0:
        result["verdict"] = "HAS_ERRORS"
    elif latest_exec is None:
        # Executed but no parseable date in outputs -- can't judge freshness.
        result["verdict"] = "EXEC_PROVED_NO_DATE"
    else:
        result["verdict"] = "EXEC_PROVED"  # freshness judged by the caller vs threshold
    return result


def _classify_freshness(result: dict, min_year: int) -> str:
    """Refine EXEC_PROVED into FRESH / STALE / PERIOD_DOMINATED vs threshold.

    HARD nuance (ai-01 c.40, PROVEN empirically on the ML family): when the
    freshest output date COINCIDES with the configured backtest period
    (``latest_exec_date == latest_backtest_period_date``), that date is the
    ``SetEndDate`` -- it describes the NOTEBOOK'S window, not WHEN the notebook
    was last executed. It therefore CANNOT prove execution recency.

    Proof: ML-DeepLearning (#8756) and ML-XGBoost (#8760) were freshly
    re-executed this week on 2026-07-28 data, yet both show 2024-12-31 in
    their outputs -- their ``SetEndDate(2024,12,31)``. They are
    indistinguishable by this field from ML-RandomForest / ML-SVM, which were
    NOT re-executed. Crying STALE on a period date = false positive.

    So the verdict distinguishes:
      - PERIOD_DOMINATED (the freshest output date IS the period): freshness
        UNDETERMINABLE from the date field. Split into _RECENT / _AGED by the
        threshold so an old window still draws a human glance without the
        false confidence of "STALE".
      - non-period date present: a date that is NOT the backtest period
        (e.g. a freshness-guard print, a "data fresh to 2026-07-28" line, a
        version/timestamp) -- THIS can judge recency -> FRESH / STALE_OUTPUTS.
    """
    latest = result.get("latest_exec_date")
    if latest is None:
        return result.get("verdict", "UNKNOWN")
    yr = int(latest[:4])
    period = result.get("latest_backtest_period_date")
    period_dominated = period is not None and latest == period
    if period_dominated:
        return "PERIOD_DOMINATED_AGED" if yr < min_year else "PERIOD_DOMINATED_RECENT"
    return "EXEC_PROVED_FRESH" if yr >= min_year else "STALE_OUTPUTS"


def scan_root(root: Path) -> list[dict]:
    """Scan every projects/*/quantbook.ipynb under root."""
    results: list[dict] = []
    for nb in sorted(root.glob("*/quantbook.ipynb")):
        results.append(scan_notebook(nb))
    return results


def human_report(results: list[dict], min_year: int) -> str:
    lines: list[str] = []
    lines.append(f"# Quantbook output-date freshness audit (threshold: latest date >= {min_year}-01-01)")
    lines.append("")
    header = f"{'Notebook':<38} {'exec':>8} {'errs':>5} {'guard':>6} {'latest_out':>12} {'latest_period':>14} {'verdict'}"
    lines.append(header)
    lines.append("-" * len(header))
    for r in results:
        name = Path(r["notebook"]).parent.name
        exec_str = f"{r.get('exec_cells', '?')}/{r.get('total_code_cells', '?')}"
        guard = "Y" if r.get("guard_present") else "n"
        latest_out = r.get("latest_exec_date") or "-"
        latest_per = r.get("latest_backtest_period_date") or "-"
        base = r.get("verdict", "?")
        verdict = _classify_freshness(r, min_year) if base == "EXEC_PROVED" else base
        r["final_verdict"] = verdict
        lines.append(f"{name:<38} {exec_str:>8} {r.get('error_cells', 0):>5} {guard:>6} {latest_out:>12} {latest_per:>14} {verdict}")
    lines.append("")
    stale = [r for r in results if r.get("final_verdict") == "STALE_OUTPUTS"]
    incomplete = [r for r in results if r.get("final_verdict") in ("INCOMPLETE", "HAS_ERRORS", "READ_ERROR")]
    fresh = [r for r in results if r.get("final_verdict") == "EXEC_PROVED_FRESH"]
    no_date = [r for r in results if r.get("final_verdict") == "EXEC_PROVED_NO_DATE"]
    pd_aged = [r for r in results if r.get("final_verdict") == "PERIOD_DOMINATED_AGED"]
    pd_recent = [r for r in results if r.get("final_verdict") == "PERIOD_DOMINATED_RECENT"]
    lines.append(f"Summary: {len(fresh)} FRESH, {len(stale)} STALE(non-period), "
                 f"{len(pd_aged)} PERIOD_AGED, {len(pd_recent)} PERIOD_RECENT, "
                 f"{len(no_date)} EXEC_NO_DATE, {len(incomplete)} INCOMPLETE/ERROR, {len(results)} total.")
    lines.append("")
    lines.append("NOTE: latest_date_in_outputs is PERIOD-DOMINATED for SetEndDate-anchored notebooks")
    lines.append("(cannot prove execution recency -- ML-DeepLearning/#8756 & ML-XGBoost/#8760 were")
    lines.append("freshly re-executed 2026-07-28 yet show 2024-12-31 = their SetEndDate(2024)).")
    lines.append("Actionable signal = INCOMPLETE executions below, not period dates.")
    if stale:
        lines.append("")
        lines.append("## STALE_OUTPUTS (non-period old date in outputs -- re-exec on fresh data)")
        for r in stale:
            lines.append(f"  - {Path(r['notebook']).parent.name}: latest output date {r.get('latest_exec_date')}, period={r.get('latest_backtest_period_date')}, guard={r.get('guard_present')}")
    if pd_aged:
        lines.append("")
        lines.append("## PERIOD_DOMINATED_AGED (freshest output = an old SetEndDate; freshness undeterminable, human glance warranted)")
        for r in pd_aged:
            lines.append(f"  - {Path(r['notebook']).parent.name}: date {r.get('latest_exec_date')} (=SetEndDate window), guard={r.get('guard_present')}")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    # Default root: discover relative to this script (repo/projects).
    default_root = Path(__file__).resolve().parents[2] / "MyIA.AI.Notebooks" / "QuantConnect" / "projects"
    p.add_argument("--root", default=str(default_root),
                   help=f"projects dir containing <Name>/quantbook.ipynb (default: {default_root})")
    p.add_argument("--min-year", type=int, default=2024,
                   help="freshness threshold: latest output date year >= this (default 2024, C942-L)")
    p.add_argument("--json", action="store_true", help="emit machine-readable JSON instead of a human table")
    p.add_argument("--no-fail", action="store_true", help="always exit 0 even if STALE outputs found")
    args = p.parse_args(argv)

    root = Path(args.root)
    if not root.is_dir():
        print(f"ERROR: root not found: {root}", file=sys.stderr)
        return 2

    results = scan_root(root)
    if args.json:
        # enrich with final verdict for machine consumers
        for r in results:
            if r.get("verdict") == "EXEC_PROVED":
                r["final_verdict"] = _classify_freshness(r, args.min_year)
            else:
                r["final_verdict"] = r.get("verdict", "UNKNOWN")
        print(json.dumps({"min_year": args.min_year, "results": results}, indent=2))
    else:
        print(human_report(results, args.min_year))

    stale = sum(1 for r in results if r.get("verdict") == "EXEC_PROVED"
                and _classify_freshness(r, args.min_year) == "STALE_OUTPUTS")
    if stale > 0 and not args.no_fail:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
