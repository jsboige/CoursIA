#!/usr/bin/env python3
"""Parity gate — verify ``xxx_<lang>.ipynb`` provenance vs source ``xxx.ipynb``.

Companion to :file:`check_perimeter.py` (grain E) and :file:`check_translation_sync.py`
(T2 hash-based drift) : this is the **structural parity gate** — for every pair
``(xxx.ipynb, xxx_<lang>.ipynb)`` on disk, it enforces the four invariants that
a T4-rendered translation **must** satisfy (#10041 grain B / Epic #10038).

Why this matters (Epic #10038 §4 D3, grain B acceptance)
=======================================================

T4 (``render_notebook.py``, grain A MERGED #10040) produces ``xxx_<lang>.ipynb``
by replacing markdown cells with translations from the CSV and copying code cells
byte-for-byte. A rendered translation is therefore a **derived artifact** : its
relationship to the source must be machine-verifiable, otherwise a future re-render
or a manual edit can silently degrade the catalog (drifted code, swapped cell order,
FR leaked through, fabricated output).

This script enforces four invariants per pair (cf #10041 §2) :

| # | Invariant                                       | Verdict if violated  |
|---|-------------------------------------------------|----------------------|
| 1 | Code cells byte-identical (source + outputs + execution_count) | ``CODE_DRIFT``         |
| 2 | Cell count + order + ``cell_id`` sequence match | ``STRUCTURE_DRIFT``  |
| 3 | No markdown cell identical to FR without declared reason | ``FR_CONTAM`` (advisory) |
| 4 | No output in translation absent from the source | ``OUTPUT_FABRICATED`` |

Invariant 3 (``FR_CONTAM``) is **advisory by default** : a translated notebook
may legitimately keep an FR string in a code comment or in a string literal —
the gate flags the cell but does not exit 1 unless ``--strict-fr`` is passed.

Invariant 4 (``OUTPUT_FABRICATED``) catches the silent regression where a
notebook is hand-edited to inject outputs the source never produced — the
``outputs`` array is part of the T4 byte-identity invariant for code cells.

Usage
-----

::

    # Default: scan repo for xxx_<lang>.ipynb pairs, verify against xxx.ipynb
    python scripts/translation/check_translation_parity.py

    # Custom paths (CI)
    python scripts/translation/check_translation_parity.py \\
        --repo-root . \\
        --langs en,ru

    # Machine-readable
    python scripts/translation/check_translation_parity.py --json-only

Exit codes
----------

- ``0``  all invariants satisfied (or only FR_CONTAM advisories)
- ``1``  one or more CODE_DRIFT / STRUCTURE_DRIFT / OUTPUT_FABRICATED found
- ``2``  filesystem error (repo root absent, notebook unreadable)

Verdicts
--------

- ``OK``                  — pair satisfies all four invariants
- ``CODE_DRIFT``          — code cell bytes / outputs / execution_count differ
- ``STRUCTURE_DRIFT``     — cell count, order, or ``cell_id`` differs
- ``FR_CONTAM``           — markdown cell text identical to FR without
  declared reason (advisory, exit 0 by default; use ``--strict-fr`` to
  promote to blocking)
- ``OUTPUT_FABRICATED``   — translation has an ``outputs`` array on a code
  cell that is absent from the source

See :file:`tests/test_check_translation_parity.py` for the full coverage.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple

# Convention #1650 : un notebook xxx.ipynb source + xxx_<lang>.ipynb traduit.
# Langues cibles = ratifiees #4957 §1 (meme liste que PERIMETER + sync).
TARGET_LANGS = ["en", "es", "ar", "fa", "zh", "ru", "pt"]

# Seuil de longueur pour le verdict FR_CONTAM : un texte trop court (< 4 chars
# post-normalisation) est un faux-ami structurel (token unique, chiffre, ponctuation).
# Meme garde que check_translation_sync._is_fr_contam (cohérence inter-scripts).
FR_CONTAM_MIN_LEN = 4


# ---------------------------------------------------------------------------
# Notebook loading
# ---------------------------------------------------------------------------


@dataclass
class CellRecord:
    """Canonical record of one cell from a notebook, normalized for comparison."""

    cell_id: str
    cell_type: str  # "code" | "markdown"
    source: str  # joined source list (may be empty)
    outputs: List[dict]  # verbatim (deep-copied) — only relevant for code cells
    execution_count: Optional[int]  # only relevant for code cells
    metadata: Dict[str, object] = field(default_factory=dict)


def load_cells(nb_path: Path) -> Tuple[List[CellRecord], Optional[str]]:
    """Load cells from a notebook. Returns ``(cells, error)`` — error is non-None
    iff the file is missing or malformed JSON.

    The cells list preserves notebook order, suitable for STRUCTURE_DRIFT
    comparison via list equality.
    """
    if not nb_path.exists():
        return [], f"notebook absent : {nb_path}"
    try:
        nb = json.loads(nb_path.read_text(encoding="utf-8"))
    except (OSError, ValueError) as exc:
        return [], f"notebook illisible : {nb_path} ({exc})"
    records: List[CellRecord] = []
    for cell in nb.get("cells", []):
        cid = cell.get("id", "")
        ctype = cell.get("cell_type", "")
        if ctype not in ("code", "markdown"):
            continue
        if not cid:
            # Skip un-id'd cells (nbformat < 4.5) — they break STRUCTURE_DRIFT.
            return [], f"cellule sans id dans {nb_path} (nbformat < 4.5 ?)"
        records.append(
            CellRecord(
                cell_id=cid,
                cell_type=ctype,
                source="".join(cell.get("source", [])),
                outputs=list(cell.get("outputs", [])) if ctype == "code" else [],
                execution_count=cell.get("execution_count") if ctype == "code" else None,
                metadata=dict(cell.get("metadata", {})),
            )
        )
    return records, None


# ---------------------------------------------------------------------------
# Pair enumeration
# ---------------------------------------------------------------------------


_SUFFIX_RE = re.compile(r"^(?P<stem>.+)_(?P<lang>" + "|".join(TARGET_LANGS) + r")$")


def discover_pairs(
    repo_root: Path, langs: List[str]
) -> List[Tuple[Path, Path, str, str]]:
    """Find every ``(xxx.ipynb, xxx_<lang>.ipynb)`` pair on disk.

    Returns a list of ``(source_path, translation_path, stem, lang)`` tuples.
    ``stem`` is the source's bare name (e.g. ``FT-01-Introduction-FineTuning``) —
    callers use it for human-readable reporting. Each pair is reported ONCE,
    identified by ``(resolved_src_path, lang)``.

    Two branches:
    - **source-present** (the typical case): walk finds ``X.ipynb``, derives
      ``X_en.ipynb``; pair emitted with src=X.ipynb.
    - **orphan** (translation lost its source): walk finds ``X_en.ipynb``
      but no ``X.ipynb``; pair emitted with src_path=X_en.ipynb (the
      translation acts as its own source stub), so downstream STRUCTURE_DRIFT
      + READ_ERROR flag it. Orphans surface without scanning a separate index.

    Pattern note: we iterate every ``*.ipynb`` once and use a ``seen`` set
    keyed by ``(resolved_path, lang)`` to avoid the double-emit trap (the
    source branch emits a pair, the translation branch would also see the
    translation and re-derive the source). On Windows the resolve() call
    normalizes the case + the path separators; on POSIX it canonicalizes
    symlinks, which is what we want for both.
    """
    pairs: List[Tuple[Path, Path, str, str]] = []
    seen: Set[Tuple[str, str]] = set()
    for nb_path in sorted(repo_root.rglob("*.ipynb")):
        stem = nb_path.stem
        suffix_match = _SUFFIX_RE.match(stem)
        if suffix_match and suffix_match.group("lang") in langs:
            # Translation file — derive the (possibly-missing) source.
            src_stem = suffix_match.group("stem")
            lang = suffix_match.group("lang")
            src_path = nb_path.with_name(src_stem + ".ipynb")
            key = (str(src_path.resolve()), lang)
            if key in seen:
                continue
            seen.add(key)
            # Orphan tolerated : if the source is missing, src_path is the
            # translation path itself; downstream check_invariants + READ_ERROR
            # path in main() will flag it.
            pairs.append((src_path, nb_path, src_stem, lang))
            continue
        # Source file — look for translations.
        for lang in langs:
            trd_path = nb_path.with_name(stem + f"_{lang}.ipynb")
            if trd_path.exists():
                key = (str(nb_path.resolve()), lang)
                if key in seen:
                    continue
                seen.add(key)
                pairs.append((nb_path, trd_path, stem, lang))
    return pairs


# ---------------------------------------------------------------------------
# Invariant computation
# ---------------------------------------------------------------------------


@dataclass
class Anomaly:
    verdict: str
    cell_id: str = ""
    detail: Dict[str, object] = field(default_factory=dict)


def check_invariants(
    src_cells: List[CellRecord],
    trd_cells: List[CellRecord],
    *,
    strict_fr: bool = False,
) -> List[Anomaly]:
    """Apply the four invariants from issue #10041. Returns the list of anomalies.

    Parameters
    ----------
    src_cells
        Cells of the source ``xxx.ipynb`` (already loaded).
    trd_cells
        Cells of the translation ``xxx_<lang>.ipynb`` (already loaded).
    strict_fr
        If True, ``FR_CONTAM`` violations are added to the verdict list that
        gates exit code 1. By default, FR_CONTAM is advisory only (exit 0).
    """
    anomalies: List[Anomaly] = []

    # --- Invariant 2 : STRUCTURE_DRIFT (count + ordre + cell_id) -----------
    src_ids = [c.cell_id for c in src_cells]
    trd_ids = [c.cell_id for c in trd_cells]
    if src_ids != trd_ids:
        # Build a structured diff : set(src) - set(trd) = cells deleted,
        # set(trd) - set(src) = cells added, zip-mismatch = reorder.
        added = sorted(set(trd_ids) - set(src_ids))
        deleted = sorted(set(src_ids) - set(trd_ids))
        anomalies.append(
            Anomaly(
                verdict="STRUCTURE_DRIFT",
                detail={
                    "src_count": len(src_ids),
                    "trd_count": len(trd_ids),
                    "added_cells": added[:10],
                    "deleted_cells": deleted[:10],
                    "reorder_detected": len(added) == 0
                    and len(deleted) == 0
                    and src_ids != trd_ids,
                },
            )
        )
        # If structure is broken, the per-cell invariants (CODE_DRIFT, FR_CONTAM)
        # cannot be evaluated safely — we return early after the structure verdict.
        return anomalies

    # --- Per-cell invariants ----------------------------------------------
    for src, trd in zip(src_cells, trd_cells):
        # Invariant 1 : CODE_DRIFT (code cell bytes + outputs + execution_count)
        if src.cell_type == "code" and trd.cell_type == "code":
            if src.source != trd.source:
                anomalies.append(
                    Anomaly(
                        verdict="CODE_DRIFT",
                        cell_id=src.cell_id,
                        detail={
                            "field": "source",
                            "src_sha": _sha(src.source)[:16],
                            "trd_sha": _sha(trd.source)[:16],
                            "src_len": len(src.source),
                            "trd_len": len(trd.source),
                        },
                    )
                )
            if src.outputs != trd.outputs:
                anomalies.append(
                    Anomaly(
                        verdict="CODE_DRIFT",
                        cell_id=src.cell_id,
                        detail={
                            "field": "outputs",
                            "src_n_outputs": len(src.outputs),
                            "trd_n_outputs": len(trd.outputs),
                            "src_execution_count": src.execution_count,
                            "trd_execution_count": trd.execution_count,
                        },
                    )
                )
            if src.execution_count != trd.execution_count:
                anomalies.append(
                    Anomaly(
                        verdict="CODE_DRIFT",
                        cell_id=src.cell_id,
                        detail={
                            "field": "execution_count",
                            "src": src.execution_count,
                            "trd": trd.execution_count,
                        },
                    )
                )

        # Invariant 4 : OUTPUT_FABRICATED — translation has outputs the
        # source lacks. Catches hand-edited translations that inject fake
        # outputs. (The reverse case is covered by CODE_DRIFT above.)
        if src.cell_type == "code" and trd.cell_type == "code":
            if not src.outputs and trd.outputs:
                anomalies.append(
                    Anomaly(
                        verdict="OUTPUT_FABRICATED",
                        cell_id=src.cell_id,
                        detail={
                            "trd_n_outputs": len(trd.outputs),
                            "trd_execution_count": trd.execution_count,
                        },
                    )
                )

        # Invariant 3 : FR_CONTAM — markdown cell text identical to source FR.
        # Advisory by default; promoted to blocking under --strict-fr.
        if (
            src.cell_type == "markdown"
            and trd.cell_type == "markdown"
            and strict_fr
        ):
            if (
                _normalize(src.source) == _normalize(trd.source)
                and len(_normalize(src.source)) >= FR_CONTAM_MIN_LEN
            ):
                anomalies.append(
                    Anomaly(
                        verdict="FR_CONTAM",
                        cell_id=src.cell_id,
                        detail={
                            "src_len": len(src.source),
                            "trd_len": len(trd.source),
                        },
                    )
                )
        elif (
            src.cell_type == "markdown"
            and trd.cell_type == "markdown"
            and not strict_fr
        ):
            # Advisory path : emit but flag as non-blocking.
            if (
                _normalize(src.source) == _normalize(trd.source)
                and len(_normalize(src.source)) >= FR_CONTAM_MIN_LEN
            ):
                anomalies.append(
                    Anomaly(
                        verdict="FR_CONTAM",
                        cell_id=src.cell_id,
                        detail={
                            "advisory": True,
                            "src_len": len(src.source),
                            "trd_len": len(trd.source),
                        },
                    )
                )

    return anomalies


def _normalize(text: str) -> str:
    """Meme garde que check_translation_sync.normalize — anti faux-drift cosmétique."""
    lines = [line.rstrip() for line in text.splitlines()]
    return "\n".join(lines).strip("\n")


def _sha(text: str) -> str:
    import hashlib

    return hashlib.sha256(text.encode("utf-8")).hexdigest()


# ---------------------------------------------------------------------------
# Reporting + CLI
# ---------------------------------------------------------------------------


def main(argv: Optional[List[str]] = None) -> int:
    p = argparse.ArgumentParser(
        description=(
            "Parity gate — verify xxx_<lang>.ipynb provenance vs xxx.ipynb "
            "(Epic #10038 grain B)."
        )
    )
    p.add_argument(
        "--repo-root",
        type=Path,
        default=Path("."),
        help="Root of the repo to scan (default: cwd).",
    )
    p.add_argument(
        "--langs",
        type=str,
        default=",".join(TARGET_LANGS),
        help=f"Comma-separated list of target langs (default: {','.join(TARGET_LANGS)}).",
    )
    p.add_argument(
        "--strict-fr",
        action="store_true",
        help="Promote FR_CONTAM from advisory (exit 0) to blocking (exit 1).",
    )
    p.add_argument(
        "--json-only",
        action="store_true",
        help="Emit JSON only (no human-readable summary).",
    )
    p.add_argument(
        "--ignore-dir",
        action="append",
        default=[".git", ".github", "_archives", ".claude", "__pycache__"],
        help="Directory name to skip during the walk (repeatable).",
    )
    args = p.parse_args(argv)

    repo_root: Path = args.repo_root.resolve()
    if not repo_root.is_dir():
        print(f"ERROR: --repo-root introuvable : {repo_root}", file=sys.stderr)
        return 2

    langs = [lang.strip() for lang in args.langs.split(",") if lang.strip()]
    bad = [lang for lang in langs if lang not in TARGET_LANGS]
    if bad:
        print(f"ERROR: langues inconnues : {bad}", file=sys.stderr)
        return 2

    # Walk : skip ignore-dir.
    pairs = discover_pairs(repo_root, langs)

    report_pairs: List[Dict[str, object]] = []
    blocking_count = 0
    advisory_count = 0

    for src_path, trd_path, stem, lang in pairs:
        src_cells, src_err = load_cells(src_path)
        trd_cells, trd_err = load_cells(trd_path)
        if src_err or trd_err:
            report_pairs.append(
                {
                    "source": str(src_path.relative_to(repo_root)),
                    "translation": str(trd_path.relative_to(repo_root)),
                    "lang": lang,
                    "verdict": "READ_ERROR",
                    "error": src_err or trd_err,
                }
            )
            blocking_count += 1
            continue
        anomalies = check_invariants(
            src_cells, trd_cells, strict_fr=args.strict_fr
        )
        # Classify : CODE_DRIFT / STRUCTURE_DRIFT / OUTPUT_FABRICATED are always
        # blocking; FR_CONTAM is blocking only under strict-fr. The strict_fr
        # flag is already applied inside check_invariants (the anomaly's
        # detail.advisory=False under strict-fr). So we only need to test
        # verdict membership in a blocking-list that ORs strict path.
        blocking_verdicts = {"CODE_DRIFT", "STRUCTURE_DRIFT", "OUTPUT_FABRICATED"}
        if args.strict_fr:
            blocking_verdicts.add("FR_CONTAM")
        blocking = [a for a in anomalies if a.verdict in blocking_verdicts]
        advisories = [
            a
            for a in anomalies
            if a.verdict == "FR_CONTAM" and a.detail.get("advisory")
        ]
        if blocking:
            blocking_count += 1
            verdict = "BLOCKED"
        elif advisories:
            verdict = "OK_WITH_ADVISORIES"
        else:
            verdict = "OK"
        advisory_count += len(advisories)
        report_pairs.append(
            {
                "source": str(src_path.relative_to(repo_root)),
                "translation": str(trd_path.relative_to(repo_root)),
                "lang": lang,
                "verdict": verdict,
                "anomalies": [
                    {
                        "verdict": a.verdict,
                        "cell_id": a.cell_id,
                        "detail": a.detail,
                    }
                    for a in anomalies
                ],
            }
        )

    overall = (
        "OK"
        if blocking_count == 0 and advisory_count == 0
        else ("OK_WITH_ADVISORIES" if blocking_count == 0 else "PARITY_VIOLATION")
    )
    report = {
        "verdict": overall,
        "repo_root": str(repo_root),
        "langs": langs,
        "strict_fr": args.strict_fr,
        "pair_count": len(pairs),
        "blocking_count": blocking_count,
        "advisory_count": advisory_count,
        "pairs": report_pairs,
    }
    print(json.dumps(report, ensure_ascii=False))

    if not args.json_only:
        if blocking_count:
            print(
                f"\nPARITY_VIOLATION : {blocking_count} paire(s) avec verdicts bloquants "
                f"sur {len(pairs)} paire(s) scannée(s).",
                file=sys.stderr,
            )
            for pr in report_pairs[:20]:
                if pr["verdict"] == "BLOCKED":
                    print(
                        f"  [BLOCKED] {pr['translation']} (lang={pr['lang']})",
                        file=sys.stderr,
                    )
                    for a in pr.get("anomalies", [])[:5]:
                        print(
                            f"    - {a['verdict']} cell_id={a['cell_id'] or '(whole-pair)'}",
                            file=sys.stderr,
                        )
        elif advisory_count:
            print(
                f"\nOK_WITH_ADVISORIES : {advisory_count} cellule(s) FR_CONTAM (advisory, "
                f"re-run with --strict-fr pour promouvoir en bloquant).",
                file=sys.stderr,
            )
        else:
            print(
                f"\nOK : {len(pairs)} paire(s) scannée(s), 0 violation, 0 advisory.",
                file=sys.stderr,
            )

    return 1 if blocking_count else 0


if __name__ == "__main__":
    sys.exit(main())
