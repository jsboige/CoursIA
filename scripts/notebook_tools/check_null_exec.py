#!/usr/bin/env python3
"""Check H.3 null-exec compliance: refuse staging a notebook cell with no execution.

Rule H.3 (CLAUDE.md, regles-validation-detail.md §H.3): "Aucun commit de notebook
non-execute". A committed cell whose `execution_count is None` AND `outputs == []`
is either (a) a genuine execution gap (the agent forgot to re-execute per C.2),
or (b) a markdown cell / comment-only cell that should not have been authored as
code. Either way, the durable fix is the same: refuse the commit and force a
re-execution OR a cell-type fix.

This script is the pre-commit H.3 null-exec hook (see #9888). It runs on the
files named by pre-commit (pass_filenames = true), so it is intentionally
file-scoped — no catalog walk, no CI machinery, no network. The whole-tree scan
that mirrors `check_c2_compliance.py` lives in that script.

Allowed carve-outs (NOT a violation):
  - Empty code cell (source is all whitespace / `#` / `//` comments) — mirrors
    `check_c2_compliance.py` skip rule.
  - Notebook metadata `pii_no_output: true` (PII redaction flag) — commits
    EMPTY outputs BY DESIGN, identical key to the upstream gate.
  - Cell with `execution_count` populated OR a non-empty `outputs` list —
    obviously compliant.

Usage:
    python check_null_exec.py --check <path.ipynb> [<path2.ipynb> ...]
    python check_null_exec.py --check <path.ipynb>     # exit 0 if OK, 1 if any violation
    python check_null_exec.py --explain                  # human-readable rule summary

Exit codes:
    0 — All checked notebooks compliant
    1 — Violations found (commit refused)
    2 — Operational error (file-not-found, JSON parse, etc.)
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Iterable

# Same PII carve-out key as the upstream PR gate and check_c2_compliance.py —
# imported, never re-spelled, so the three cannot drift on the key name.
_REPO_ROOT = Path(__file__).resolve().parent.parent.parent
sys.path.insert(0, str(Path(__file__).resolve().parent))
from validate_pr_notebooks import PII_NO_OUTPUT_KEY  # noqa: E402


def _is_skippable_comment_only(source: str) -> bool:
    """Return True if the cell source is empty or only comments (Python/C-family)."""
    stripped = source.strip()
    if not stripped:
        return True
    # Python `#` and C-family `//` comment-marker lines (C#/.NET Interactive,
    # JS, Java). A cell whose body is exclusively comment lines is a
    # transition/explanation cell, not an executable one — skip on the same
    # grounds as check_c2_compliance.py.
    for line in stripped.splitlines():
        s = line.strip()
        if not s:
            continue
        if s.startswith("#") or s.startswith("//"):
            continue
        return False
    return True


def check_notebook(nb_path: Path) -> dict:
    """Check one notebook for H.3 null-exec violations.

    Returns dict with:
        path, total_code, violations (list of {cell_index, reason})
    """
    try:
        notebook = json.loads(nb_path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, UnicodeDecodeError) as e:
        return {
            "path": str(nb_path),
            "total_code": 0,
            "violations": [{"error": f"Cannot parse: {e}"}],
        }

    # PII carve-out: empty outputs are legitimate by design.
    pii_no_output = (
        notebook.get("metadata", {}).get(PII_NO_OUTPUT_KEY) is True
    )

    violations = []
    total_code = 0
    for i, cell in enumerate(notebook.get("cells", [])):
        if cell.get("cell_type") != "code":
            continue
        total_code += 1

        source = "".join(cell.get("source", []))
        if _is_skippable_comment_only(source):
            continue

        execution_count = cell.get("execution_count")
        outputs = cell.get("outputs", []) or []
        # H.3 strict: BOTH execution_count is None AND outputs is empty.
        # A cell with execution_count: 7 but outputs: [] is unusual (cleared
        # outputs on a real cell) — distinct from the H.3 null-exec case
        # and outside this hook's scope.
        if execution_count is None and not outputs:
            reason = "execution_count is None AND outputs is empty"
            if pii_no_output:
                reason += (
                    f" (BUT metadata.{PII_NO_OUTPUT_KEY}=true — PII carve-out "
                    "applies; counted as compliant below)"
                )
            violations.append({"cell_index": i, "reason": reason})

    if pii_no_output:
        # All listed violations are absorbed by the PII carve-out.
        return {
            "path": str(nb_path),
            "total_code": total_code,
            "violations": [],
            "pii_carve_out": True,
        }

    return {
        "path": str(nb_path),
        "total_code": total_code,
        "violations": violations,
    }


def check_paths(paths: Iterable[Path]) -> list[dict]:
    """Check a list of notebook paths. Returns list of result dicts."""
    return [check_notebook(Path(p)) for p in paths]


def _emit_result(res: dict, verbose: bool) -> None:
    """Emit one result to stderr (pre-commit expects stderr for diagnostics)."""
    nb_violations = res["violations"]
    if not nb_violations:
        if verbose:
            print(
                f"OK  {res['path']}  ({res['total_code']} code cells, "
                f"clean)"
                + (" [PII carve-out]" if res.get("pii_carve_out") else ""),
                file=sys.stderr,
            )
        return
    print(f"FAIL {res['path']}  ({res['total_code']} code cells)", file=sys.stderr)
    for v in nb_violations:
        if "error" in v:
            print(f"  - parse error: {v['error']}", file=sys.stderr)
        else:
            print(
                f"  - cell {v['cell_index']}: {v['reason']}",
                file=sys.stderr,
            )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="H.3 null-exec pre-commit hook (refuse staging un-executed "
        "code cells). See #9888.",
    )
    parser.add_argument(
        "--check",
        nargs="*",
        dest="paths",
        metavar="NOTEBOOK",
        default=None,
        help="Notebook paths to check (typically passed by pre-commit "
        "pass_filenames).",
    )
    parser.add_argument(
        "--explain",
        action="store_true",
        help="Print the rule summary and exit.",
    )
    parser.add_argument(
        "--verbose",
        "-v",
        action="store_true",
        help="Per-notebook status on stderr.",
    )
    args = parser.parse_args(argv)

    if args.explain:
        print(__doc__)
        return 0

    if args.paths is None:
        parser.error("--check needs at least one notebook path")

    results = check_paths(args.paths)
    if args.verbose:
        for r in results:
            _emit_result(r, verbose=True)

    parse_errors = []
    total_violations = 0
    for r in results:
        for v in r["violations"]:
            if "error" in v:
                parse_errors.append((r["path"], v["error"]))
            else:
                total_violations += 1

    if parse_errors:
        print(
            "H.3 null-exec: PARSE ERRORS in staged notebooks (refuse):",
            file=sys.stderr,
        )
        for path, err in parse_errors:
            print(f"  - {path}: {err}", file=sys.stderr)
        return 2

    if total_violations > 0:
        print(
            f"H.3 null-exec: {total_violations} un-executed code cell(s) "
            "in staged notebooks. Re-execute (Papermill / kernel) or replace "
            "with a markdown cell. See regles-validation-detail.md §H.3.",
            file=sys.stderr,
        )
        return 1

    if args.verbose:
        print(f"H.3 null-exec: {len(results)} notebook(s) OK.", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
