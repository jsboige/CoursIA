#!/usr/bin/env python3
"""Code-span inline drift guard — measure loss of `` `...` `` markers between a
source ``xxx.ipynb`` and its translation ``xxx_<lang>.ipynb`` (Epic #10038,
issue #13536).

Background
==========

Issue #13536 measured firsthand on PR #12850 (first T4 batch) that the
FR->EN translation pipeline silently drops `` ` `` markdown code-spans in
the rendered notebook. On ``medical_chatbot`` (40 markdown cells) the
loss was **27 code-spans** across 7 cells (cell[2]/[8]/[16]/[19]/[26]/[36])
while ``FT-05-ModelMerging-Routing`` (26 markdown cells) had 0 losses.
The drops are invisible to ``check_translation_parity.py`` because the
invariant 1/2/3/4 set encodes *byte-identity of code cells* and *FR/EN
identity of full-cell text*, but not *the structural role of inline code
markers within prose*.

Why a 5th invariant — and why advisory
=======================================

A code-span `` `Kernel` `` in FR prose is **structural**, not stylistic :
it tells the student « this token is code, do not translate it ». When
the EN rendering flattens it to ``Kernel``, several concrete breaks
appear:

- `` ` ` ` `` inside a list item becomes a real H1 (``# Etape 1``)
  rendered as a header at first display — visually a section break in
  the middle of a bullet list (cf #13536 body, exemplar).
- The AST invariant that the FR/EN pairs are *translations* of the same
  inline structure is broken — the EN prose has fewer inline-code
  nodes than the FR source.

This module adds a 5th invariant : ``INLINE_CODE_DRIFT``. It is
**advisory by default** (``--strict-inline-code`` promotes to blocking)
because some legitimate renders translate `` ``code`` `` -> ``"code"``
or ``*code*`` (the backtick disappears by design). The flag is opt-in
for callers that want the strict gate.

The output is JSON for CI consumption (``--json-only``).

Usage
-----

::

    # Default: scan repo for xxx_<lang>.ipynb pairs, measure code-span loss
    python scripts/translation/check_inline_code_spans.py

    # Per-pair detail + block-on-loss
    python scripts/translation/check_inline_code_spans.py \\
        --repo-root . --langs en --strict-inline-code

    # Single pair
    python scripts/translation/check_inline_code_spans.py \\
        --src X.ipynb --translation X_en.ipynb

Exit codes
----------

- ``0``  no loss (or only advisory losses)
- ``1``  one or more blocking ``INLINE_CODE_DRIFT`` violations
- ``2``  filesystem error

See :file:`tests/test_check_inline_code_spans.py` for the coverage.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional, Tuple

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from check_perimeter import TARGET_LANGS  # noqa: E402  -- single source of truth

# ---------------------------------------------------------------------------
# Single-backtick inline code-span regex
# ---------------------------------------------------------------------------
# A code-span is `` ` `` + 1+ non-`` chars + `` ` `` on the SAME line. We
# exclude triple-backtick fences (``` ... ```) by requiring the char before
# and after the span to NOT be ``. ``. ``.  The regex is anchored to the
# start of a line OR preceded by a non-`` character, and the closing
# backtick is followed by EOL or non-`` (so we never match inside a triple
# fence). This matches the GitHub-flavored markdown definition of inline
# code-spans (https://github.github.com/gfm/#code-spans).
_BACKTICK = chr(96)
_INLINE_CODE_SPAN_RE = re.compile(
    rf"(?<![{_BACKTICK}])({_BACKTICK}[^{_BACKTICK}\n]+{_BACKTICK})(?![{_BACKTICK}])"
)


@dataclass
class SpanRecord:
    cell_id: str
    spans: List[str] = field(default_factory=list)


def extract_inline_code_spans(markdown_text: str) -> List[str]:
    """Extract all inline `` `...` `` code-spans from a markdown string.

    Triple-backtick fences are NOT matched (a span's neighbors must not be
    `` ` ``). Empty spans (`` `` ``) are excluded.

    Returns the list of spans in source order. The list is **deduped** at
    call-site responsibility if needed; here we return raw order so callers
    can compute symmetric diffs.
    """
    return [m.group(1) for m in _INLINE_CODE_SPAN_RE.finditer(markdown_text)]


def _load_markdown_cells(nb_path: Path) -> Tuple[List[SpanRecord], Optional[str]]:
    """Load markdown cells from a notebook as SpanRecord list.

    Returns ``(records, error)``. Records preserve notebook order; ``cell_id``
    is taken from ``cell['id']`` (nbformat 4.5+).
    """
    if not nb_path.exists():
        return [], f"notebook absent : {nb_path}"
    try:
        nb = json.loads(nb_path.read_text(encoding="utf-8"))
    except (OSError, ValueError) as exc:
        return [], f"notebook illisible : {nb_path} ({exc})"
    records: List[SpanRecord] = []
    for cell in nb.get("cells", []):
        if cell.get("cell_type") != "markdown":
            continue
        cid = cell.get("id", "")
        if not cid:
            return [], f"cellule markdown sans id dans {nb_path} (nbformat < 4.5 ?)"
        src = "".join(cell.get("source", []))
        records.append(SpanRecord(cell_id=cid, spans=extract_inline_code_spans(src)))
    return records, None


def measure_code_span_drift(
    src_records: List[SpanRecord],
    trd_records: List[SpanRecord],
) -> List[Dict[str, object]]:
    """Compare FR (src) to EN (trd) code-span inventory, per paired cell.

    Returns one entry per pair of cells, with:
    - ``cell_id`` (from src)
    - ``src_spans`` / ``trd_spans`` (raw counts including duplicates)
    - ``lost`` (set diff: count of distinct spans present in src but absent in trd)
    - ``gained`` (set diff: count of distinct spans present in trd but absent in src)
    - ``lost_examples`` (up to 3 spans present in src but not in trd)

    ``lost`` and ``gained`` are independent set-difference cardinalities —
    a span that's in both languages is NOT counted in either, even if
    duplicates differ. Use ``src_spans`` / ``trd_spans`` for raw counts.

    Pairing : record[i] aligns with record[i]; if lengths differ, the
    shorter list's last index is used. Excess cells are flagged with
    ``cell_id="<unpaired-in-src>"`` or ``"<unpaired-in-trd>"``.
    """
    out: List[Dict[str, object]] = []
    n = max(len(src_records), len(trd_records))
    for i in range(n):
        s = src_records[i] if i < len(src_records) else None
        t = trd_records[i] if i < len(trd_records) else None
        if s is None and t is not None:
            out.append({
                "cell_id": "<unpaired-in-src>",
                "src_spans": 0,
                "trd_spans": len(t.spans),
                "lost": 0,
                "gained": len(set(t.spans)),
                "lost_examples": [],
            })
            continue
        if t is None and s is not None:
            out.append({
                "cell_id": s.cell_id,
                "src_spans": len(s.spans),
                "trd_spans": 0,
                "lost": len(set(s.spans)),
                "gained": 0,
                "lost_examples": s.spans[:3],
            })
            continue
        # Both cells present.
        s_set = set(s.spans)
        t_set = set(t.spans)
        lost_spans = s_set - t_set
        gained_spans = t_set - s_set
        lost_examples = [sp for sp in s.spans if sp in lost_spans][:3]
        out.append({
            "cell_id": s.cell_id,
            "src_spans": len(s.spans),
            "trd_spans": len(t.spans),
            "lost": len(lost_spans),
            "gained": len(gained_spans),
            "lost_examples": lost_examples,
        })
    return out


def _scan_pair(src_path: Path, trd_path: Path) -> Dict[str, object]:
    """Compute the per-pair verdict block (JSON-serialisable)."""
    src_records, src_err = _load_markdown_cells(src_path)
    trd_records, trd_err = _load_markdown_cells(trd_path)
    if src_err or trd_err:
        return {
            "source": str(src_path),
            "translation": str(trd_path),
            "verdict": "READ_ERROR",
            "error": src_err or trd_err,
        }
    per_cell = measure_code_span_drift(src_records, trd_records)
    total_lost = sum(e["lost"] for e in per_cell if e["lost"] > 0)
    total_gained = sum(e["gained"] for e in per_cell if e["gained"] > 0)
    return {
        "source": str(src_path),
        "translation": str(trd_path),
        "verdict": "INLINE_CODE_DRIFT" if total_lost > 0 else "OK",
        "src_total_spans": sum(e["src_spans"] for e in per_cell),
        "trd_total_spans": sum(e["trd_spans"] for e in per_cell),
        "total_lost": total_lost,
        "total_gained": total_gained,
        "per_cell": per_cell,
    }


def main(argv: Optional[List[str]] = None) -> int:
    p = argparse.ArgumentParser(
        description=(
            "Inline code-span drift guard — measure `...` losses FR -> "
            "xxx_<lang>.ipynb (issue #13536, Epic #10038)."
        )
    )
    p.add_argument("--repo-root", type=Path, default=Path("."),
                   help="Root of the repo to scan (default: cwd).")
    p.add_argument("--langs", type=str, default=",".join(TARGET_LANGS),
                   help=f"Comma-separated target langs (default: {','.join(TARGET_LANGS)}).")
    p.add_argument("--src", type=Path, default=None,
                   help="Single-pair mode: path to source notebook.")
    p.add_argument("--translation", type=Path, default=None,
                   help="Single-pair mode: path to translated notebook.")
    p.add_argument("--strict-inline-code", action="store_true",
                   help="Promote INLINE_CODE_DRIFT from advisory to blocking.")
    p.add_argument("--ignore-dir", action="append",
                   default=[".git", ".github", "_archives", ".claude", "__pycache__"],
                   help="Directory name to skip during the walk (repeatable).")
    args = p.parse_args(argv)

    if args.src and args.translation:
        pairs = [(args.src, args.translation)]
    elif (args.src is None) != (args.translation is None):
        print("ERROR: --src et --translation doivent etre utilises ensemble",
              file=sys.stderr)
        return 2
    else:
        repo_root: Path = args.repo_root.resolve()
        if not repo_root.is_dir():
            print(f"ERROR: --repo-root introuvable : {repo_root}", file=sys.stderr)
            return 2
        langs = [lang.strip() for lang in args.langs.split(",") if lang.strip()]
        bad = [lang for lang in langs if lang not in TARGET_LANGS]
        if bad:
            print(f"ERROR: langues inconnues : {bad}", file=sys.stderr)
            return 2
        # Walk : find every (X.ipynb, X_<lang>.ipynb) pair.
        pairs = []
        seen = set()
        for nb_path in sorted(repo_root.rglob("*.ipynb")):
            stem = nb_path.stem
            for lang in langs:
                if stem.endswith(f"_{lang}"):
                    src_stem = stem[: -(len(lang) + 1)]
                    src_path = nb_path.with_name(src_stem + ".ipynb")
                    key = (str(src_path.resolve()), lang)
                    if key in seen:
                        continue
                    seen.add(key)
                    pairs.append((src_path, nb_path))
                    break
                candidate = nb_path.with_name(stem + f"_{lang}.ipynb")
                if candidate.exists():
                    key = (str(nb_path.resolve()), lang)
                    if key in seen:
                        continue
                    seen.add(key)
                    pairs.append((nb_path, candidate))

    blocking_count = 0
    advisory_count = 0
    pair_reports: List[Dict[str, object]] = []
    for src_path, trd_path in pairs:
        report = _scan_pair(src_path, trd_path)
        if report["verdict"] == "INLINE_CODE_DRIFT":
            if args.strict_inline_code:
                blocking_count += 1
                report["verdict"] = "BLOCKED_INLINE_CODE_DRIFT"
            else:
                advisory_count += 1
        pair_reports.append(report)

    overall = (
        "OK" if blocking_count == 0 and advisory_count == 0
        else ("BLOCKED" if blocking_count > 0 else "OK_WITH_ADVISORIES")
    )
    print(json.dumps({
        "verdict": overall,
        "strict_inline_code": args.strict_inline_code,
        "pair_count": len(pair_reports),
        "blocking_count": blocking_count,
        "advisory_count": advisory_count,
        "pairs": pair_reports,
    }, ensure_ascii=False))
    return 0 if blocking_count == 0 else 1


if __name__ == "__main__":
    sys.exit(main())