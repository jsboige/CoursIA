#!/usr/bin/env python3
"""Perimeter gate — enforces translations/PERIMETER.md against translations/**/*.csv.

Companion to :file:`scripts/translation/check_translation_sync.py` (T2 drift
detector, hash-based) and :file:`scripts/translation/render_notebook.py` (T4
renderer). This is the **structural perimeter gate** : for every CSV under
``translations/``, no column ``text_<lang>`` can carry a non-empty cell unless
that lang is **declared in-scope** in ``translations/PERIMETER.md``.

Why this matters (Epic #10038 §4 D3 — perimeter EN seul d'abord, corpus déclaré)
===============================================================================

Without a declared perimeter, anyone can fill any ``text_<lang>`` cell in any
CSV and T4 would render notebooks in that language. That would silently
**double the translation surface area** beyond what the team has approved for
review. The catalog gets re-rendered on a daily cron, but a translated
notebook is *content*, not metadata — it lands on ``main`` and grows the
backlog of strings to maintain in 7 languages.

This script enforces the perimeter mechanically :

1. If a CSV has cells in ``text_<lang>`` for a lang not declared in PERIMETER.md
   → **PERIMETER_VIOLATION**, the gate exits 1.
2. If PERIMETER.md declares a lang as in-scope for a CSV but the CSV has 0
   cells in that lang → **IN_SCOPE_UNUSED** (advisory only, exit 0 — there is
   no requirement to fill yet).
3. If PERIMETER.md is missing → **PERIMETER_MISSING**, the gate exits 2.
4. If PERIMETER.md is malformed (no matrix table) → **PERIMETER_MALFORMED**,
   the gate exits 2.

CI integration (grain E §4 Epic #10038) : the script returns 0 when the
perimeter is satisfied, 1 when violated, 2 when the perimeter file is
unreadable. Designed to be wired into ``.github/workflows/translation-guard.yml``
later (grain C, Epic #10038 §6) — for now this PR ships the standalone gate
+ tests.

Usage
-----

::

    # Default: verify against translations/PERIMETER.md, scan translations/**/*.csv
    python scripts/translation/check_perimeter.py

    # Custom paths (for tests)
    python scripts/translation/check_perimeter.py \\
        --perimeter path/to/PERIMETER.md \\
        --translations-root path/to/translations

    # Machine-readable output (one JSON line on stdout)
    python scripts/translation/check_perimeter.py --json-only

Exit codes
----------

- ``0``  perimeter satisfied (with or without IN_SCOPE_UNUSED advisories)
- ``1``  perimeter violated (PERIMETER_VIOLATION found)
- ``2``  perimeter file missing or malformed (cannot evaluate)

Verdicts
--------

- ``OK``                    — no violations, no advisories
- ``PERIMETER_VIOLATION``   — ``text_<lang>`` filled in a CSV for a lang not
  declared in PERIMETER.md. Detail = ``{csv, lang, n_cells, sample_cells}``.
- ``IN_SCOPE_UNUSED``       — PERIMETER.md declares ``<lang>`` in-scope for a
  CSV but no cells are filled yet. Advisory (exit 0), not a failure — the
  perimeter is *forward-looking*.
- ``PERIMETER_MISSING``     — the perimeter file does not exist (exit 2).
- ``PERIMETER_MALFORMED``   — the perimeter file is unreadable or has no
  matrix table (exit 2).

See :file:`tests/test_check_perimeter.py` for the full coverage (≥10 cases).
"""

from __future__ import annotations

import argparse
import csv
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple

# Langs tracked by the CSV schema (ratified #4957 §1). Order matches the
# schema header : text_<lang> columns in CSV order, with hash_<lang> after.
# The pivot lang ('fr') is always in-scope by construction (T1 extracts it).
#
# SINGLE SOURCE OF TRUTH (#10109). ``TARGET_LANGS`` is the ONLY place the
# ordered universe of 7 target languages may live as a literal. Every other
# site (translate_csv.TARGETS, check_resync_only.ALL_LANGS, the T4 step in
# translation-sync.yml) MUST consume it from here -- a duplicated list with a
# different order is a latent silent bug (any positional ``zip``/``enumerate``
# across two copies swaps translations without raising). The regression guard
# ``scripts/translation/tests/test_lang_single_source.py`` fails if a
# language-list literal reappears outside this module.
PIVOT_LANG = "fr"
TARGET_LANGS = ["en", "es", "ar", "fa", "zh", "ru", "pt"]
ALL_LANGS = [PIVOT_LANG] + TARGET_LANGS

# Defaults used when a CSV appears in translations/ but is NOT explicitly listed
# in PERIMETER.md. Conservative : a CSV not in the perimeter matrix is
# treated as ALL langs out-of-scope (forces explicit declaration before any
# translation work). The matrix in PERIMETER.md can override per-CSV.
DEFAULT_OUT_OF_SCOPE: Set[str] = set(TARGET_LANGS)


# ---------------------------------------------------------------------------
# PERIMETER.md parsing
# ---------------------------------------------------------------------------


def parse_perimeter(path: Path) -> Dict[str, Set[str]]:
    """Parse a PERIMETER.md file and return ``{csv_path: {in_scope_langs}}``.

    The file is expected to contain a markdown table of the form ::

        | CSV | en | es | ar | ... | Source |
        |---|---|---|---|---|---|
        | translations/genai/casestudies.csv | **en** | - | - | - | - | **ru** | - | #10017 |
        | translations/genai/image.csv | **en** | ... | ... | **ru** | ... | T3 image |

    Parsing rules :

    - Rows starting with ``| translations/`` are CSV entries.
    - First column is the CSV path (repo-relative POSIX).
    - Each lang column (``en``, ``es``, ``ar``, ``fa``, ``zh``, ``ru``, ``pt``)
      contains either ``**en**`` / ``**ru**`` (in-scope, bold) or ``-``
      (out-of-scope). The bold markup is required to mark in-scope : a plain
      ``en`` in a cell is treated as out-of-scope (forces explicit bold).
    - The pivot lang ``fr`` is implicit (always in-scope, never in the table).

    Returns
    -------
    ``{csv_path: {in_scope_langs}}`` where ``in_scope_langs ⊆ TARGET_LANGS``.

    Raises
    ------
    ValueError
        if the file does not contain a recognizable matrix table (caller maps
        to ``PERIMETER_MALFORMED``).
    """
    if not path.exists():
        raise FileNotFoundError(f"PERIMETER.md introuvable : {path}")

    text = path.read_text(encoding="utf-8")
    csv_to_langs: Dict[str, Set[str]] = {}

    # Match rows of the form ``| <csv> | ... |`` where <csv> starts with
    # ``translations/`` and ends with ``.csv``. Capture the whole row to
    # extract lang cells.
    row_pattern = re.compile(
        r"^\|\s*(`?translations/[^\s|`]+\.csv`?)\s*\|(.*?)\|\s*$",
        re.MULTILINE,
    )
    # Match the header row to know which lang columns are present + in order.
    # Accept both ``| CSV |`` and ``| CSV | Source |`` (any trailing columns).
    header_pattern = re.compile(
        r"^\|\s*CSV\s*\|((?:[^|]*\|)+)\s*$",
        re.MULTILINE,
    )
    header_match = header_pattern.search(text)
    if not header_match:
        raise ValueError(
            "PERIMETER.md ne contient pas de ligne d'en-tête '| CSV | ... |'."
        )
    header_cells = [c.strip() for c in header_match.group(1).split("|") if c.strip()]
    # Map lang → index in the row (header_cells excludes the first 'CSV' col).
    lang_idx: Dict[str, int] = {}
    for i, cell in enumerate(header_cells):
        cell_clean = cell.strip().strip("`").strip()
        if cell_clean in TARGET_LANGS:
            lang_idx[cell_clean] = i

    found_rows = False
    for m in row_pattern.finditer(text):
        found_rows = True
        csv_cell = m.group(1).strip().strip("`").strip()
        rest = m.group(2)
        row_cells = [c.strip() for c in rest.split("|")]
        in_scope: Set[str] = set()
        for lang, idx in lang_idx.items():
            if idx >= len(row_cells):
                continue
            cell_val = row_cells[idx].strip()
            # In-scope marker : the lang code is wrapped in **bold** (e.g. ``**en**``).
            # This is conservative : only explicit bold declares in-scope.
            if cell_val == f"**{lang}**":
                in_scope.add(lang)
        csv_to_langs[csv_cell] = in_scope

    if not found_rows:
        raise ValueError(
            "PERIMETER.md ne contient aucune ligne '| translations/...csv | ... |'."
        )

    return csv_to_langs


# ---------------------------------------------------------------------------
# CSV scanning
# ---------------------------------------------------------------------------


def scan_csv_langs(csv_path: Path) -> Dict[str, int]:
    """Return ``{lang: n_filled_cells}`` for markdown cells in ``csv_path``.

    A cell is counted as filled if the corresponding ``text_<lang>`` column
    has a non-empty (after ``.strip()``) value AND the ``cell_type`` is
    ``markdown``. Code cells are skipped (T4 copies them byte-for-byte; their
    translations live in code-comment form, not in the CSV).
    """
    counts: Dict[str, int] = {lang: 0 for lang in TARGET_LANGS}
    with csv_path.open(encoding="utf-8", newline="") as fh:
        reader = csv.DictReader(fh)
        if reader.fieldnames is None:
            return counts
        for row in reader:
            if row.get("cell_type") != "markdown":
                continue
            for lang in TARGET_LANGS:
                col = f"text_{lang}"
                if col in reader.fieldnames and row.get(col, "").strip():
                    counts[lang] += 1
    return counts


# ---------------------------------------------------------------------------
# Verdict computation
# ---------------------------------------------------------------------------


@dataclass
class Anomaly:
    verdict: str
    csv: str
    detail: Dict[str, object] = field(default_factory=dict)


def compute_anomalies(
    csv_paths: List[Path],
    perimeter: Dict[str, Set[str]],
    *,
    translations_root: Optional[Path] = None,
) -> Tuple[List[Anomaly], Dict[str, Dict[str, int]]]:
    """Walk CSVs and emit anomalies + a per-CSV fill report.

    Parameters
    ----------
    csv_paths
        All CSV files found under the translations root.
    perimeter
        ``{csv_relpath_posix: {in_scope_langs}}`` (parsed from PERIMETER.md).
    translations_root
        Used to compute the relative POSIX path of each CSV for comparison
        against the perimeter keys. If ``None``, uses ``Path.cwd()``.

    Returns
    -------
    (anomalies, fills_by_csv)
    """
    if translations_root is None:
        translations_root = Path.cwd()
    anomalies: List[Anomaly] = []
    fills_by_csv: Dict[str, Dict[str, int]] = {}

    for csv_path in csv_paths:
        # Compute the repo-relative POSIX path (matches PERIMETER.md keys).
        try:
            rel = csv_path.resolve().relative_to(translations_root.resolve()).as_posix()
        except ValueError:
            rel = csv_path.name
        # PERIMETER.md keys may include the ``translations/`` prefix (operating
        # out of repo root) or may be bare relative to translations_root. Try
        # both forms when looking up the declaration.
        keys_to_try = [rel, f"translations/{rel}"]
        counts = scan_csv_langs(csv_path)
        fills_by_csv[rel] = counts
        # Look up the perimeter declaration under both possible key forms.
        declared_in_scope: Set[str] = set()
        for key in keys_to_try:
            if key in perimeter:
                declared_in_scope = perimeter[key]
                break
        for lang in TARGET_LANGS:
            if counts[lang] > 0 and lang not in declared_in_scope:
                anomalies.append(
                    Anomaly(
                        verdict="PERIMETER_VIOLATION",
                        csv=rel,
                        detail={
                            "lang": lang,
                            "n_cells": counts[lang],
                            "declared_in_scope": sorted(declared_in_scope),
                        },
                    )
                )
            elif counts[lang] == 0 and lang in declared_in_scope:
                # Advisory only : the perimeter declares intent to fill, but no
                # cells yet. Not a violation (this is the natural state of a
                # fresh declaration). Surfaced via the JSON report so a human
                # reviewer can track declared-but-unfilled work.
                anomalies.append(
                    Anomaly(
                        verdict="IN_SCOPE_UNUSED",
                        csv=rel,
                        detail={
                            "lang": lang,
                            "declared_in_scope": sorted(declared_in_scope),
                        },
                    )
                )
    return anomalies, fills_by_csv


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def main(argv: Optional[List[str]] = None) -> int:
    p = argparse.ArgumentParser(
        description="Perimeter gate — enforces translations/PERIMETER.md "
        "against translations/**/*.csv (Epic #10038 grain E).",
    )
    p.add_argument(
        "--perimeter",
        type=Path,
        default=None,
        help="Path to PERIMETER.md (default: <translations-root>/PERIMETER.md).",
    )
    p.add_argument(
        "--translations-root",
        type=Path,
        default=None,
        help="Root of the translations directory (default: ./translations).",
    )
    p.add_argument(
        "--json-only",
        action="store_true",
        help="Emit JSON only (no human-readable summary).",
    )
    args = p.parse_args(argv)

    translations_root = args.translations_root or Path("translations")
    perimeter_path = args.perimeter or translations_root / "PERIMETER.md"

    if not translations_root.is_dir():
        print(f"ERROR: --translations-root introuvable : {translations_root}", file=sys.stderr)
        return 2

    if not perimeter_path.exists():
        report = {
            "verdict": "PERIMETER_MISSING",
            "perimeter_path": str(perimeter_path),
            "translations_root": str(translations_root),
            "anomalies": [],
        }
        print(json.dumps(report, ensure_ascii=False))
        if not args.json_only:
            print(
                f"ERROR: {perimeter_path} introuvable. Crée-le pour activer le périmètre.",
                file=sys.stderr,
            )
        return 2

    try:
        perimeter = parse_perimeter(perimeter_path)
    except ValueError as exc:
        report = {
            "verdict": "PERIMETER_MALFORMED",
            "perimeter_path": str(perimeter_path),
            "error": str(exc),
            "anomalies": [],
        }
        print(json.dumps(report, ensure_ascii=False))
        if not args.json_only:
            print(f"ERROR: PERIMETER.md malformé : {exc}", file=sys.stderr)
        return 2

    csv_paths = sorted(translations_root.rglob("*.csv"))
    anomalies, fills_by_csv = compute_anomalies(
        csv_paths, perimeter, translations_root=translations_root
    )

    violations = [a for a in anomalies if a.verdict == "PERIMETER_VIOLATION"]
    advisories = [a for a in anomalies if a.verdict == "IN_SCOPE_UNUSED"]
    overall = "OK" if not violations else "PERIMETER_VIOLATION"

    report = {
        "verdict": overall,
        "perimeter_path": str(perimeter_path),
        "translations_root": str(translations_root),
        "csv_count": len(csv_paths),
        "violation_count": len(violations),
        "advisory_count": len(advisories),
        "anomalies": [
            {
                "verdict": a.verdict,
                "csv": a.csv,
                "detail": a.detail,
            }
            for a in anomalies
        ],
        "fill_by_csv": fills_by_csv,
        "perimeter_declared": {k: sorted(v) for k, v in perimeter.items()},
    }
    print(json.dumps(report, ensure_ascii=False))

    if not args.json_only:
        if violations:
            print(
                f"\nPERIMETER_VIOLATION : {len(violations)} cellule(s) hors périmètre "
                f"sur {len(csv_paths)} CSV scannés.",
                file=sys.stderr,
            )
            for a in violations[:20]:
                d = a.detail
                print(
                    f"  [{a.verdict}] {a.csv} lang={d.get('lang')} "
                    f"n_cells={d.get('n_cells')}",
                    file=sys.stderr,
                )
            if len(violations) > 20:
                print(f"  ... et {len(violations) - 20} autres.", file=sys.stderr)
        elif advisories:
            print(
                f"\nOK (perimeter satisfied) — {len(advisories)} advisory "
                f"IN_SCOPE_UNUSED (déclaré mais pas encore rempli).",
                file=sys.stderr,
            )
        else:
            print(
                f"\nOK : {len(csv_paths)} CSV scannés, périmètre satisfait, 0 advisory.",
                file=sys.stderr,
            )

    return 1 if violations else 0


if __name__ == "__main__":
    sys.exit(main())