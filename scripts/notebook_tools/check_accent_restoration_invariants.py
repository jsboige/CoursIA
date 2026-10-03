#!/usr/bin/env python3
"""Invariant check for accent-restoration tranches (ruling #16638, 2026-10-03).

A restoration tranche must change NOTHING but accents. Reviewing #18814, the
coordinator found an artefact neither the review nor the dossier had caught:
33 mid-sentence capitalisations across 17 cells ("la Même convention",
"l'Inférence bayesienne", "le second Paramètre"). No ACCENT_PAIRS entry maps a
lowercase form to a capitalised one, so the tooling was not the cause -- the
tranche *procedure* was. The ruling therefore asks for a per-cell organ:

    strip_accents(base) == strip_accents(head)   for every markdown cell.

strip_accents drops combining marks but NOT case, so the equality is exact on
everything except accents: capitalisation, rewording, added/removed words,
renumbering -- all of it breaks the invariant and is reported. Code cells must
be byte-identical (a prose tranche never touches them), and the cell count and
each cell type must not move. The comparison base is the tranche's own parent
commit (--base-sha), never a distant main: renumberings landed between the
tranche and a later main are NOT tranche changes and must not poison the
check.

Validated by its false negatives, never by its hits: the #18814 defect
("la meme convention" -> "la Même convention") MUST be flagged, a clean
restoration ("theoreme" -> "théorème") MUST pass, and a code-cell edit MUST
be reported even though it produces no markdown diff.

Usage: python check_accent_restoration_invariants.py <notebook.ipynb>
                                   --base-sha <sha-or-ref> [--json]
                                   [--fail-on-findings]

Output: one line per finding `KIND cell #N (excerpt)`, then a total.
--fail-on-findings exits 2 when any finding exists. Exit 1 is reserved for
tool failure (git show failed, notebook unreadable) -- a vacuous crash is
never a clean check.
"""

import argparse
import json
import subprocess
import sys
import unicodedata
from pathlib import Path

# Sibling import (organ-first): the accent-stripping function is the detector's,
# never a copy. If the two organs ever diverge on what an accent is, they
# diverge together.
sys.path.insert(0, str(Path(__file__).resolve().parent))
from detect_markdown_deaccent import _strip_accents  # noqa: E402


def _cell_source(cell: dict) -> str:
    """Join a cell source given as list-of-lines or plain string."""
    src = cell.get("source", "")
    if isinstance(src, list):
        return "".join(src)
    return str(src)


def _first_diff_context(a: str, b: str, span: int = 30) -> tuple[str, str]:
    """Excerpt of both strings around their first divergent position."""
    limit = min(len(a), len(b))
    i = 0
    while i < limit and a[i] == b[i]:
        i += 1
    lo = max(0, i - span)
    return a[lo : i + span], b[lo : i + span]


def _load_base_notebook(notebook: Path, base_sha: str) -> dict:
    """Read the notebook as it stands at base_sha via `git show`."""
    top = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        check=True,
    ).stdout.strip()
    rel = notebook.resolve().relative_to(Path(top)).as_posix()
    raw = subprocess.run(
        ["git", "-C", top, "show", f"{base_sha}:{rel}"],
        capture_output=True,
        text=True,
        encoding="utf-8",
        check=True,
    ).stdout
    return json.loads(raw)


def _cell_invariant_violations(base_nb: dict, head_nb: dict) -> list[dict]:
    """Findings for every cell-level change an accent tranche must not make.

    Markdown cells are compared through strip_accents (case-preserving), code
    cells byte-for-byte; cell count and cell types must not move. Findings are
    ordered by cell index, kind by kind.
    """
    findings: list[dict] = []
    base_cells = base_nb.get("cells", [])
    head_cells = head_nb.get("cells", [])
    if len(base_cells) != len(head_cells):
        findings.append(
            {
                "kind": "CELL_COUNT_CHANGED",
                "cell": None,
                "detail": f"base {len(base_cells)} cells vs head {len(head_cells)} cells",
            }
        )
    for i, (b, h) in enumerate(zip(base_cells, head_cells)):
        b_type = b.get("cell_type", "")
        h_type = h.get("cell_type", "")
        if b_type != h_type:
            findings.append(
                {
                    "kind": "TYPE_CHANGED",
                    "cell": i,
                    "detail": f"base {b_type} vs head {h_type}",
                }
            )
            continue
        b_src = _cell_source(b)
        h_src = _cell_source(h)
        if b_type == "markdown":
            if _strip_accents(b_src) != _strip_accents(h_src):
                base_ctx, head_ctx = _first_diff_context(
                    _strip_accents(b_src), _strip_accents(h_src)
                )
                findings.append(
                    {
                        "kind": "MARKDOWN_INVARIANT",
                        "cell": i,
                        "detail": f"base ...{base_ctx!r} vs head ...{head_ctx!r}",
                    }
                )
        else:
            if b_src != h_src:
                base_ctx, head_ctx = _first_diff_context(b_src, h_src)
                findings.append(
                    {
                        "kind": "CODE_MODIFIED",
                        "cell": i,
                        "detail": f"base ...{base_ctx!r} vs head ...{head_ctx!r}",
                    }
                )
    return findings


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Check that an accent-restoration tranche changed nothing but accents."
    )
    parser.add_argument("notebook", type=Path, help="notebook on the tranche head")
    parser.add_argument(
        "--base-sha",
        required=True,
        help="commit (sha or ref) holding the pre-tranche notebook -- typically the tranche parent",
    )
    parser.add_argument("--json", action="store_true", help="emit a JSON report")
    parser.add_argument(
        "--fail-on-findings", action="store_true", help="exit 2 when any finding exists"
    )
    args = parser.parse_args(argv)

    try:
        head_nb = json.loads(args.notebook.read_text(encoding="utf-8"))
        base_nb = _load_base_notebook(args.notebook, args.base_sha)
    except (OSError, json.JSONDecodeError, subprocess.CalledProcessError) as exc:
        print(f"ERROR: cannot load notebook or base ({exc})", file=sys.stderr)
        return 1

    findings = _cell_invariant_violations(base_nb, head_nb)
    report = {
        "notebook": str(args.notebook),
        "base_sha": args.base_sha,
        "total": len(findings),
        "findings": findings,
    }
    if args.json:
        print(json.dumps(report, ensure_ascii=False, indent=2))
    else:
        for f in findings:
            cell = "cell #" + str(f["cell"]) if f["cell"] is not None else "cells"
            print(f"{f['kind']} {cell} ({f['detail']})")
        print(f"TOTAL {report['total']} finding(s) -- {args.notebook}")
    if findings and args.fail_on_findings:
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
