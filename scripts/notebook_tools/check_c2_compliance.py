#!/usr/bin/env python3
"""Check C.2 compliance: all code cells must have execution_count and outputs.

Rule C.2: Notebooks committed WITH outputs. Every executable code cell must have
execution_count: <int> and coherent outputs. Modification of a code cell = full
re-execution before commit.

Usage:
    python check_c2_compliance.py                       # Check all pedagogical notebooks
    python check_c2_compliance.py --maturity PRODUCTION  # PRODUCTION notebooks only
    python check_c2_compliance.py --serie Search         # Single serie
    python check_c2_compliance.py --path <file.ipynb>    # Single notebook
    python check_c2_compliance.py --fix                  # Show fix suggestions
    python check_c2_compliance.py --json                 # JSON output

Exit codes:
    0 — All checked notebooks compliant
    1 — Violations found
    2 — Error (catalog not found, etc.)
"""

import argparse
import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
CATALOG_PATH = REPO_ROOT / "COURSE_CATALOG.generated.json"
NOTEBOOKS_DIR = REPO_ROOT / "MyIA.AI.Notebooks"

EXCLUDE_ALWAYS = {".ipynb_checkpoints", "obj", "bin", "__pycache__", ".git"}
EXCLUDE_PEDAGOGICAL = {"research", "archive", "_output", "ESGF", "examples"}


def check_notebook(nb_path: Path) -> dict:
    """Check a single notebook for C.2 compliance.

    Returns dict with:
        path, total_code, violations (list of cell indices + reasons)
    """
    try:
        notebook = json.loads(nb_path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, UnicodeDecodeError) as e:
        return {
            "path": str(nb_path),
            "total_code": 0,
            "violations": [{"error": f"Cannot parse: {e}"}],
        }

    violations = []
    code_idx = 0

    for i, cell in enumerate(notebook.get("cells", [])):
        if cell.get("cell_type") != "code":
            continue
        code_idx += 1

        source = "".join(cell.get("source", []))
        # Skip empty code cells
        if not source.strip():
            continue

        # Skip cells that are only markdown-like comments
        lines = [l.strip() for l in source.split("\n") if l.strip()]
        if all(l.startswith("#") for l in lines):
            continue

        # Check execution_count
        exec_count = cell.get("execution_count")
        outputs = cell.get("outputs", [])

        if exec_count is None:
            violations.append({
                "cell_index": i,
                "code_cell": code_idx,
                "reason": "missing execution_count",
                "source_preview": source[:80].replace("\n", " "),
            })
        elif not outputs and source.strip():
            # Code cell with execution_count but no outputs
            # Only flag if the cell should produce output (print, return, expression)
            has_output_statement = any(
                kw in source for kw in
                ["print(", "display(", "plt.", "fig", "return ", "="]
            )
            # Skip cells that might legitimately have no output (imports, assignments)
            is_import = source.strip().startswith(("import ", "from "))
            is_assignment = (
                "=" in source
                and not any(kw in source for kw in ["print(", "display(", "plt."])
            )

            if has_output_statement and not is_import:
                violations.append({
                    "cell_index": i,
                    "code_cell": code_idx,
                    "reason": "execution_count set but no outputs",
                    "source_preview": source[:80].replace("\n", " "),
                })

    return {
        "path": str(nb_path),
        "total_code": code_idx,
        "violations": violations,
    }


def get_target_notebooks(args) -> list[Path]:
    """Get list of notebooks to check based on args."""
    if args.path:
        p = Path(args.path)
        if not p.is_absolute():
            p = REPO_ROOT / p
        return [p] if p.exists() else []

    if not CATALOG_PATH.exists() or args.no_catalog:
        # Fallback: scan all notebooks
        targets = []
        for nb_path in sorted(NOTEBOOKS_DIR.rglob("*.ipynb")):
            parts = nb_path.relative_to(NOTEBOOKS_DIR).parts
            if any(exc in part for part in parts for exc in EXCLUDE_ALWAYS):
                continue
            if any(exc in str(nb_path) for exc in EXCLUDE_PEDAGOGICAL):
                continue
            targets.append(nb_path)
        return targets

    catalog = json.loads(CATALOG_PATH.read_text(encoding="utf-8"))

    entries = catalog
    if args.serie:
        entries = [e for e in entries if e.get("serie") == args.serie]
    if args.maturity:
        entries = [e for e in entries if e.get("maturity") == args.maturity]
    if args.exclude_broken:
        entries = [e for e in entries if e.get("status") != "BROKEN"]

    return [
        NOTEBOOKS_DIR / e["path"]
        for e in entries
        if (NOTEBOOKS_DIR / e["path"]).exists()
    ]


def main():
    parser = argparse.ArgumentParser(
        description="Check C.2 compliance: all code cells have execution_count and outputs"
    )
    parser.add_argument("--serie", type=str, default=None, help="Check single serie")
    parser.add_argument("--maturity", type=str, default=None,
                        choices=["PRODUCTION", "BETA", "ALPHA", "DRAFT"],
                        help="Filter by maturity level")
    parser.add_argument("--path", type=str, default=None,
                        help="Check a single notebook file")
    parser.add_argument("--exclude-broken", action="store_true",
                        help="Skip BROKEN notebooks")
    parser.add_argument("--no-catalog", action="store_true",
                        help="Scan filesystem instead of catalog")
    parser.add_argument("--fix", action="store_true",
                        help="Show fix suggestions for violations")
    parser.add_argument("--json", action="store_true",
                        help="JSON output for scripts")
    args = parser.parse_args()

    targets = get_target_notebooks(args)
    if not targets:
        print("No notebooks to check.")
        return 0

    results = [check_notebook(p) for p in targets]
    violations = [r for r in results if r["violations"]]

    if args.json:
        print(json.dumps(results, indent=2, ensure_ascii=False))
        return 1 if violations else 0

    # Human-readable report
    total = len(results)
    compliant = total - len(violations)
    total_violations = sum(len(r["violations"]) for r in violations)

    print(f"C.2 Compliance Check: {compliant}/{total} notebooks compliant")
    if not violations:
        print("All clear!")
        return 0

    print(f"\nViolations: {total_violations} cells in {len(violations)} notebooks\n")

    for r in violations:
        rel = Path(r["path"]).relative_to(REPO_ROOT) if REPO_ROOT in Path(r["path"]).parents else r["path"]
        print(f"  {rel} ({len(r['violations'])} violations):")
        for v in r["violations"]:
            if "error" in v:
                print(f"    ERROR: {v['error']}")
            else:
                preview = v.get("source_preview", "")[:60]
                print(f"    cell #{v['code_cell']}: {v['reason']}")
                if args.fix:
                    print(f"      -> Re-execute cell or full notebook")

    print(f"\nSummary: {compliant}/{total} compliant, {len(violations)} with issues")
    return 1


if __name__ == "__main__":
    sys.exit(main())
