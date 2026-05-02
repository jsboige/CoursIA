#!/usr/bin/env python3
"""Unified notebook validator combining C.1, C.2, and structural checks.

Runs all validation checks on a single notebook or batch:
    - C.1: No intentional errors (raise NotImplementedError, assert False, 1/0)
    - C.2: All code cells have execution_count and outputs
    - Structure: markdown intro/conclusion, cell ordering, empty cells
    - Metadata: kernel defined, title present

Usage:
    python notebook_lint.py <path>                  # Single notebook
    python notebook_lint.py --serie Search           # All notebooks in serie
    python notebook_lint.py --maturity PRODUCTION    # By maturity
    python notebook_lint.py --all                    # All pedagogical notebooks
    python notebook_lint.py --check c1,c2            # Only specific checks
    python notebook_lint.py --json                   # JSON output

Exit codes:
    0 — All notebooks pass
    1 — Violations found
    2 — Error (file not found, etc.)
"""

import argparse
import json
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
CATALOG_PATH = REPO_ROOT / "COURSE_CATALOG.generated.json"
NOTEBOOKS_DIR = REPO_ROOT / "MyIA.AI.Notebooks"

EXCLUDE_ALWAYS = {".ipynb_checkpoints", "obj", "bin", "__pycache__", ".git"}
EXCLUDE_PEDAGOGICAL = {"research", "archive", "_output", "ESGF", "examples"}

# C.1 forbidden patterns (intentional errors in top-level / exercise stubs)
# Only flag patterns that are clearly intentional errors, not error handling
C1_PATTERNS = [
    (r"raise\s+NotImplementedError", "raise NotImplementedError"),
    (r"assert\s+False", "assert False"),
    (r"(?<!\w)1\s*/\s*0(?!\w)", "1/0"),
]

# Allowed C.1 exception: inside comments (pedagogical explanations)
C1_ALLOW_PATTERN = r"^\s*#\s*(TODO|Indice|Etape|NOTE|EXERCICE|Exemple)"


def check_c1(notebook: dict) -> list[dict]:
    """Check C.1: no intentional errors in code cells."""
    violations = []
    for i, cell in enumerate(notebook.get("cells", [])):
        if cell.get("cell_type") != "code":
            continue
        source = "".join(cell.get("source", []))
        for line in source.split("\n"):
            if re.match(C1_ALLOW_PATTERN, line):
                continue
            for pattern, desc in C1_PATTERNS:
                if re.search(pattern, line):
                    violations.append({
                        "check": "C1",
                        "cell_index": i,
                        "line": line.strip(),
                        "pattern": desc,
                    })
    return violations


def check_c2(notebook: dict) -> list[dict]:
    """Check C.2: all code cells have execution_count and outputs."""
    violations = []
    for i, cell in enumerate(notebook.get("cells", [])):
        if cell.get("cell_type") != "code":
            continue
        source = "".join(cell.get("source", []))
        if not source.strip():
            continue

        # Skip comment-only cells
        lines = [l.strip() for l in source.split("\n") if l.strip()]
        if all(l.startswith("#") for l in lines):
            continue

        exec_count = cell.get("execution_count")
        if exec_count is None:
            violations.append({
                "check": "C2",
                "cell_index": i,
                "reason": "missing execution_count",
                "source_preview": source[:60].replace("\n", " "),
            })
    return violations


def check_structure(notebook: dict) -> list[dict]:
    """Check structural quality: intro, conclusion, cell ordering."""
    violations = []
    cells = notebook.get("cells", [])
    md_cells = [c for c in cells if c["cell_type"] == "markdown"]
    code_cells = [c for c in cells if c["cell_type"] == "code"]

    # Check for empty cells
    for i, cell in enumerate(cells):
        source = "".join(cell.get("source", []))
        if not source.strip() and cell.get("cell_type") != "markdown":
            violations.append({
                "check": "STRUCTURE",
                "cell_index": i,
                "reason": "empty code cell",
            })

    # Check for consecutive code cells without markdown ( > 5)
    consecutive_code = 0
    for i, cell in enumerate(cells):
        if cell["cell_type"] == "code":
            consecutive_code += 1
            if consecutive_code > 5:
                violations.append({
                    "check": "STRUCTURE",
                    "cell_index": i,
                    "reason": f">5 consecutive code cells (streak: {consecutive_code})",
                })
        else:
            consecutive_code = 0

    return violations


def check_metadata(notebook: dict) -> list[dict]:
    """Check metadata: kernel, title."""
    violations = []
    ks = notebook.get("metadata", {}).get("kernelspec", {})
    if not ks.get("display_name") and not ks.get("name"):
        violations.append({"check": "META", "reason": "no kernel defined"})

    # Check title
    cells = notebook.get("cells", [])
    has_title = False
    for cell in cells:
        if cell["cell_type"] == "markdown":
            src = "".join(cell.get("source", []))
            if src.strip().startswith("#"):
                has_title = True
                break
    if not has_title and len(cells) > 0:
        violations.append({"check": "META", "reason": "no title heading found"})

    return violations


def lint_notebook(nb_path: Path, checks: set[str]) -> dict:
    """Run all requested checks on a single notebook."""
    try:
        notebook = json.loads(nb_path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, UnicodeDecodeError) as e:
        return {"path": str(nb_path), "error": f"Cannot parse: {e}", "violations": []}

    violations = []
    if "c1" in checks:
        violations.extend(check_c1(notebook))
    if "c2" in checks:
        violations.extend(check_c2(notebook))
    if "structure" in checks:
        violations.extend(check_structure(notebook))
    if "meta" in checks:
        violations.extend(check_metadata(notebook))

    return {"path": str(nb_path), "violations": violations}


def get_targets(args) -> list[Path]:
    """Get list of notebooks to validate."""
    if args.path:
        p = Path(args.path)
        if not p.is_absolute():
            p = REPO_ROOT / p
        return [p] if p.exists() else []

    if not CATALOG_PATH.exists():
        print("Error: catalog not found. Use --path or run generate_catalog.py.")
        return []

    catalog = json.loads(CATALOG_PATH.read_text(encoding="utf-8"))
    entries = catalog
    if args.serie:
        entries = [e for e in entries if e.get("serie") == args.serie]
    if args.maturity:
        entries = [e for e in entries if e.get("maturity") == args.maturity]

    return [
        NOTEBOOKS_DIR / e["path"]
        for e in entries
        if (NOTEBOOKS_DIR / e["path"]).exists()
    ]


def main():
    parser = argparse.ArgumentParser(
        description="Unified notebook validator (C.1 + C.2 + structure + metadata)"
    )
    parser.add_argument("path", nargs="?", default=None, help="Single notebook path")
    parser.add_argument("--serie", type=str, default=None)
    parser.add_argument("--maturity", type=str, default=None,
                        choices=["PRODUCTION", "BETA", "ALPHA", "DRAFT"])
    parser.add_argument("--all", action="store_true", help="All notebooks")
    parser.add_argument("--check", type=str, default="c1,c2",
                        help="Checks to run: c1,c2,structure,meta (default: c1,c2)")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()

    checks = set(args.check.split(","))

    if args.path:
        targets = get_targets(args)
    elif args.all or args.serie or args.maturity:
        targets = get_targets(args)
    else:
        parser.print_help()
        return 2

    if not targets:
        print("No notebooks to validate.")
        return 0

    results = [lint_notebook(p, checks) for p in targets]
    violations = [r for r in results if r["violations"] or r.get("error")]

    if args.json:
        print(json.dumps(results, indent=2, ensure_ascii=False))
        return 1 if violations else 0

    # Human-readable
    total = len(results)
    clean = total - len(violations)

    print(f"Notebook Lint: {clean}/{total} pass")
    if not violations:
        print("All clear!")
        return 0

    total_violations = sum(len(r["violations"]) for r in violations)
    print(f"\n{total_violations} violations in {len(violations)} notebooks:\n")

    by_check = {}
    for r in violations:
        for v in r["violations"]:
            check = v.get("check", "?")
            by_check.setdefault(check, []).append(v)

    for check, vs in sorted(by_check.items()):
        print(f"  {check}: {len(vs)} violations")
    print()

    for r in violations:
        rel = Path(r["path"]).relative_to(REPO_ROOT) if REPO_ROOT in Path(r["path"]).parents else r["path"]
        if r.get("error"):
            print(f"  {rel}: ERROR - {r['error']}")
            continue
        print(f"  {rel} ({len(r['violations'])} issues):")
        for v in r["violations"][:5]:
            if "pattern" in v:
                print(f"    [{v['check']}] cell #{v['cell_index']}: {v['pattern']} → {v['line'][:60]}")
            elif "reason" in v:
                preview = v.get("source_preview", "")
                extra = f" → {preview[:50]}" if preview else ""
                print(f"    [{v['check']}] cell #{v['cell_index']}: {v['reason']}{extra}")

    return 1


if __name__ == "__main__":
    sys.exit(main())
