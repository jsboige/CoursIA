"""Scan code-cell comments for quantitative literal counters (#18493).

Different from prose-counts : the prose ratchet scans markdown cells, this
script scans **comments inside code cells**. The two ratchets are
complementary :

- prose-counts : markdown text with embedded numbers ("127 notebooks")
- this script  : Python comments with embedded numbers ("# ~1500 fichiers")

The class of issues is the same (literals that drift) but the fix path is
different : markdown edits are byte-identical (no re-exec), code-cell
edits trigger C.2 re-exec (papermill or kernel) of the whole notebook.
See #18493 for the originating rationale.

Output is a structured list (notebook, cell_index, kind, line) so a
follow-up PR can decide KEEP / EDIT / REMOVE per item without re-running
the scan.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter
from pathlib import Path
from typing import Iterator

REPO_ROOT = Path(__file__).resolve().parent.parent.parent

# ---- patterns ---------------------------------------------------------------
# Each pattern captures a *kind* of literal counter seen in code comments.
# `kind` is the call-site action : KEEP (pedagogical/calibration comment)
# vs EDIT (replace with runtime computation) vs REMOVE (no value).

KIND_PATTERNS = {
    "NOTE_runtime": re.compile(
        r"#\s*NOTE\s*:.*~?\d+\s+\w+",  # "# NOTE: ~1500 fichiers"
    ),
    "tilde_count": re.compile(
        r"#\s*~(\d+)\s+\w+",  # "# ~10 mots"
    ),
    "gt_runtime_threshold": re.compile(
        r"#\s*>\s*\d+\s*(\w+)",  # "# >100k theoremes" (NOT a runtime `if x > N`)
    ),
    "config_dict_doc": re.compile(
        r"#\s*\".*\"\s*:\s*\w+,\s*>?\d+\s*\w+",  # "# 'large': mathlib4, >100k theoremes"
    ),
}

# Disambiguation patterns : things that LOOK like counters but are
# operational runtime code. They get a FALSE_POSITIVE classification.
RUNTIME_GUARDS = (
    re.compile(r"\bif\b.*[<>]\s*\d"),  # `if x > N` -- code, not a counter
    re.compile(r"\bdelta_?e?\s*=\s*.*[<>]\s*\d"),  # `delta_e = y - y_new  # > 0 si ...`
    re.compile(r"\bslippage\(\)\s*>\s*\d"),  # operational threshold
)


def iter_notebooks(root: Path) -> Iterator[Path]:
    """Yield every deliverable notebook under MyIA.AI.Notebooks/."""
    for path in (root / "MyIA.AI.Notebooks").rglob("*.ipynb"):
        # Skip output / archive copies
        if "_output" in path.name or "_archive" in path.parts:
            continue
        yield path


def classify_line(line: str) -> tuple[str, str] | None:
    """Return (kind, line) if the line matches any pattern, else None.

    A line is excluded if it looks like runtime code (RUNTIME_GUARDS).
    """
    if any(g.search(line) for g in RUNTIME_GUARDS):
        return None
    for kind, pat in KIND_PATTERNS.items():
        if pat.search(line):
            return kind, line.strip()
    return None


def scan(root: Path = REPO_ROOT) -> list[dict]:
    """Return the list of hits as structured records."""
    records: list[dict] = []
    for nb in iter_notebooks(root):
        try:
            data = json.loads(nb.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        for cell_idx, cell in enumerate(data.get("cells", [])):
            if cell.get("cell_type") != "code":
                continue
            source = "".join(cell.get("source", []))
            for lineno, line in enumerate(source.splitlines(), start=1):
                hit = classify_line(line)
                if hit is None:
                    continue
                kind, snippet = hit
                records.append({
                    "notebook": str(nb.relative_to(root)),
                    "cell_index": cell_idx,
                    "line": lineno,
                    "kind": kind,
                    "snippet": snippet[:200],
                })
    return records


def summarize(records: list[dict]) -> str:
    by_kind = Counter(r["kind"] for r in records)
    by_nb = Counter(r["notebook"] for r in records)
    out = []
    out.append(f"== total hits: {len(records)} ==")
    out.append("")
    out.append("== by kind ==")
    for kind, n in by_kind.most_common():
        out.append(f"  {kind:24s} : {n}")
    out.append("")
    out.append(f"== notebooks touched: {len(by_nb)} ==")
    for nb, n in by_nb.most_common(10):
        out.append(f"  {nb:80s} : {n}")
    if len(by_nb) > 10:
        out.append(f"  ... and {len(by_nb) - 10} more")
    return "\n".join(out)


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Scan code-cell comments for quantitative literal counters (#18493)"
    )
    ap.add_argument("--json", action="store_true", help="Machine-readable output")
    ap.add_argument(
        "--root", type=Path, default=REPO_ROOT,
        help="Repo root (default: auto-detected)",
    )
    args = ap.parse_args()

    records = scan(args.root)
    if args.json:
        print(json.dumps({
            "total": len(records),
            "by_kind": dict(Counter(r["kind"] for r in records)),
            "by_notebook": dict(Counter(r["notebook"] for r in records)),
            "records": records,
        }, ensure_ascii=False, indent=1))
    else:
        print(summarize(records))
    return 0


if __name__ == "__main__":
    sys.exit(main())
