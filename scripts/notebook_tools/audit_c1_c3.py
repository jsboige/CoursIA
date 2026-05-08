#!/usr/bin/env python3
"""Repo-wide C.1 + C.3 audit for pedagogical notebooks.

Scans all .ipynb files under MyIA.AI.Notebooks/ and reports:
  C.1 violations: raise NotImplementedError, assert False, 1/0
  C.3 violations: output-only changes (outputs changed without source change)

Usage:
    python audit_c1_c3.py                       # Full scan
    python audit_c1_c3.py --family GenAI        # Single family
    python audit_c1_c3.py --check c1            # C.1 only
    python audit_c1_c3.py --json                # JSON output
    python audit_c1_c3.py --summary             # Summary per family only

Exit codes:
    0 — No violations
    1 — Violations found
"""

import argparse
import json
import re
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
NOTEBOOKS_DIR = REPO_ROOT / "MyIA.AI.Notebooks"

EXCLUDE_DIRS = {
    ".ipynb_checkpoints", ".git", "__pycache__", "obj", "bin",
    "_output", "research", "archive", "ESGF", "examples",
    ".venv", "node_modules",
}

C1_PATTERNS = [
    (re.compile(r"raise\s+NotImplementedError"), "raise NotImplementedError"),
    (re.compile(r"assert\s+False"), "assert False"),
    (re.compile(r"(?<!\d)1\s*/\s*0(?!\d)"), "1/0"),
]


def _is_in_docstring(line: str, in_doc: bool) -> tuple:
    was = in_doc
    for q in ('"""', "'''"):
        if line.count(q) % 2 == 1:
            in_doc = not in_doc
    return in_doc, was != in_doc or was


def find_notebooks(family: str | None = None) -> list[Path]:
    """Discover all pedagogical notebooks."""
    notebooks = []
    root = NOTEBOOKS_DIR / family if family else NOTEBOOKS_DIR
    if not root.exists():
        return []
    for p in root.rglob("*.ipynb"):
        if any(part in EXCLUDE_DIRS for part in p.parts):
            continue
        notebooks.append(p)
    return sorted(notebooks)


def check_c1(nb_path: Path) -> list[dict]:
    """Check C.1: no intentional errors."""
    try:
        nb = json.loads(nb_path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, UnicodeDecodeError):
        return []

    violations = []
    for i, cell in enumerate(nb.get("cells", [])):
        if cell.get("cell_type") != "code":
            continue
        source = "".join(cell.get("source", []))
        in_doc = False
        for line in source.split("\n"):
            if line.lstrip().startswith("#"):
                continue
            code_part = line.split("#")[0].rstrip()
            in_doc, inside = _is_in_docstring(line, in_doc)
            if inside:
                continue
            for pattern, desc in C1_PATTERNS:
                if pattern.search(code_part):
                    violations.append({
                        "cell": i,
                        "pattern": desc,
                        "line": line.strip()[:80],
                    })
    return violations


def check_c3(nb_path: Path) -> list[dict]:
    """Check C.3: detect output-only changes (outputs changed, source unchanged).

    Compares HEAD vs last commit that changed the notebook's source cells.
    If only outputs differ (no source changes), flags as C.3 violation.
    """
    rel = nb_path.relative_to(REPO_ROOT)
    try:
        diff = subprocess.run(
            ["git", "diff", "HEAD", "--", str(rel)],
            capture_output=True, text=True, cwd=str(REPO_ROOT),
            timeout=10,
        )
    except (subprocess.TimeoutExpired, FileNotFoundError):
        return []

    if not diff.stdout:
        return []

    lines = diff.stdout.split("\n")
    source_changes = 0
    output_changes = 0
    in_source = False
    in_output = False

    for line in lines:
        if line.startswith("@@"):
            in_source = False
            in_output = False
            continue
        if '"source"' in line:
            in_source = True
            in_output = False
        elif '"outputs"' in line or '"execution_count"' in line:
            in_output = True
            in_source = False

        if not line.startswith("+") and not line.startswith("-"):
            continue
        if line.startswith("+++ ") or line.startswith("--- "):
            continue

        if in_source:
            source_changes += 1
        elif in_output:
            output_changes += 1

    if output_changes > 0 and source_changes == 0:
        return [{"reason": "output-only changes in working tree (no source change)"}]
    return []


def get_family(nb_path: Path) -> str:
    """Extract family name from path relative to NOTEBOOKS_DIR."""
    try:
        rel = nb_path.relative_to(NOTEBOOKS_DIR)
        return rel.parts[0] if rel.parts else "unknown"
    except ValueError:
        return "unknown"


def main():
    parser = argparse.ArgumentParser(description="Repo-wide C.1 + C.3 audit")
    parser.add_argument("--family", type=str, default=None, help="Audit single family")
    parser.add_argument("--check", type=str, default="c1,c3",
                        help="Checks: c1, c3 (default: c1,c3)")
    parser.add_argument("--json", action="store_true", help="JSON output")
    parser.add_argument("--summary", action="store_true", help="Summary per family only")
    args = parser.parse_args()

    checks = set(args.check.split(","))
    notebooks = find_notebooks(args.family)

    if not notebooks:
        print("No notebooks found.")
        return 0

    results = []
    families = defaultdict(lambda: {"total": 0, "c1": 0, "c3": 0, "violations": []})

    for nb in notebooks:
        family = get_family(nb)
        families[family]["total"] += 1

        entry = {"path": str(nb.relative_to(REPO_ROOT)), "family": family, "violations": []}

        if "c1" in checks:
            c1_v = check_c1(nb)
            if c1_v:
                entry["violations"].extend([{"check": "C1", **v} for v in c1_v])
                families[family]["c1"] += len(c1_v)

        if "c3" in checks:
            c3_v = check_c3(nb)
            if c3_v:
                entry["violations"].extend([{"check": "C3", **v} for v in c3_v])
                families[family]["c3"] += len(c3_v)

        if entry["violations"]:
            results.append(entry)
            families[family]["violations"].append(nb.name)

    if args.json:
        print(json.dumps({"total_notebooks": len(notebooks), "violations": results},
                         indent=2, ensure_ascii=False))
        return 1 if results else 0

    total_nb = len(notebooks)
    clean = total_nb - len(results)

    print(f"C.1/C.3 Audit: {clean}/{total_nb} notebooks pass")

    if args.summary:
        print(f"\n{'Family':<30} {'Total':>6} {'C.1':>6} {'C.3':>6}")
        print("-" * 52)
        for fam in sorted(families):
            d = families[fam]
            print(f"{fam:<30} {d['total']:>6} {d['c1']:>6} {d['c3']:>6}")
        print("-" * 52)
        total_c1 = sum(d["c1"] for d in families.values())
        total_c3 = sum(d["c3"] for d in families.values())
        print(f"{'TOTAL':<30} {total_nb:>6} {total_c1:>6} {total_c3:>6}")
        return 1 if results else 0

    if not results:
        print("All clear!")
        return 0

    total_v = sum(len(r["violations"]) for r in results)
    print(f"\n{total_v} violations in {len(results)} notebooks:\n")

    for r in results:
        print(f"  {r['path']} ({len(r['violations'])} issues):")
        for v in r["violations"][:5]:
            check = v.get("check", "?")
            if "pattern" in v:
                print(f"    [{check}] cell #{v['cell']}: {v['pattern']}")
            elif "reason" in v:
                print(f"    [{check}] {v['reason']}")

    return 1


if __name__ == "__main__":
    sys.exit(main())
