#!/usr/bin/env python3
"""Generate a coverage report for the notebook catalog.

Cross-references COURSE_CATALOG.generated.json with filesystem state,
README markers, and C.2 compliance to produce an actionable report.

Usage:
    python catalog_coverage.py                       # Full coverage report
    python catalog_coverage.py --serie GenAI         # Single serie
    python catalog_coverage.py --json                # JSON output
    python catalog_coverage.py --short               # Condensed one-line per serie

Checks performed:
    1. Catalog completeness — all notebooks have title, serie, kernel
    2. C.2 compliance — PRODUCTION/BETA have outputs
    3. README markers — each serie has CATALOG-STATUS marker
    4. Maturity distribution — reasonable spread
    5. Broken count — tracked and categorized
"""

import argparse
import json
import re
from collections import Counter
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
CATALOG_PATH = REPO_ROOT / "COURSE_CATALOG.generated.json"
NOTEBOOKS_DIR = REPO_ROOT / "MyIA.AI.Notebooks"

SERIES_ORDER = [
    "GenAI", "Search", "ML", "SymbolicAI", "QuantConnect",
    "GameTheory", "Sudoku", "Probas", "IIT", "RL", "EPF",
]


def check_catalog_completeness(entries: list[dict]) -> list[dict]:
    """Check for missing metadata in catalog entries."""
    issues = []
    for e in entries:
        if not e.get("title"):
            issues.append({"path": e["path"], "issue": "missing title"})
        if not e.get("serie"):
            issues.append({"path": e["path"], "issue": "missing serie"})
        if e.get("kernel", "unknown") == "unknown":
            issues.append({"path": e["path"], "issue": "missing kernel"})
        if e.get("cells_total", 0) == 0:
            issues.append({"path": e["path"], "issue": "zero cells"})
    return issues


def check_c2_by_maturity(entries: list[dict]) -> dict:
    """Check C.2 compliance by maturity level."""
    results = {}
    for maturity in ["PRODUCTION", "BETA", "ALPHA", "DRAFT"]:
        subset = [
            e for e in entries
            if e.get("maturity") == maturity and e.get("status") != "BROKEN"
        ]
        total = len(subset)
        no_missing = sum(
            1 for e in subset if e.get("cells_without_outputs", 0) == 0
        )
        results[maturity] = {
            "total": total,
            "compliant": no_missing,
            "rate": round(no_missing / total * 100, 1) if total else 0,
        }
    return results


def check_readme_markers(entries: list[dict]) -> list[dict]:
    """Check which series have CATALOG-STATUS markers in their README."""
    series = set(e["serie"] for e in entries)
    results = []
    marker_re = re.compile(r"CATALOG-STATUS", re.IGNORECASE)

    for serie in sorted(series):
        readme_path = NOTEBOOKS_DIR / serie / "README.md"
        if not readme_path.exists():
            results.append({
                "serie": serie,
                "has_readme": False,
                "has_marker": False,
            })
            continue

        content = readme_path.read_text(encoding="utf-8")
        has_marker = bool(marker_re.search(content))
        results.append({
            "serie": serie,
            "has_readme": True,
            "has_marker": has_marker,
        })
    return results


def generate_report(
    entries: list[dict],
    serie_filter: str | None = None,
    short: bool = False,
) -> str:
    """Generate human-readable coverage report."""
    if serie_filter:
        entries = [e for e in entries if e.get("serie") == serie_filter]

    lines = ["# Catalog Coverage Report", ""]

    # 1. Overview
    total = len(entries)
    by_status = Counter(e.get("status", "?") for e in entries)
    by_maturity = Counter(e.get("maturity", "?") for e in entries)

    lines.extend([
        "## Overview",
        "",
        f"| Metric | Value |",
        f"|--------|-------|",
        f"| Total notebooks | {total} |",
    ])
    for status in ["READY", "DEMO", "RESEARCH", "BROKEN"]:
        lines.append(f"| {status} | {by_status.get(status, 0)} |")
    lines.append("")
    for mat in ["PRODUCTION", "BETA", "ALPHA", "DRAFT"]:
        lines.append(f"| {mat} | {by_maturity.get(mat, 0)} |")
    lines.append("")

    if short:
        # One-line per serie
        lines.extend(["## Per-Serie Summary", ""])
        by_serie = {}
        for e in entries:
            by_serie.setdefault(e["serie"], []).append(e)
        for serie in SERIES_ORDER:
            if serie not in by_serie:
                continue
            items = by_serie[serie]
            n = len(items)
            prod = sum(1 for e in items if e.get("maturity") == "PRODUCTION")
            beta = sum(1 for e in items if e.get("maturity") == "BETA")
            broken = sum(1 for e in items if e.get("status") == "BROKEN")
            local = sum(1 for e in items if e.get("executable_locally"))
            lines.append(
                f"  {serie:15} {n:3d} notebooks | "
                f"P:{prod:2d} B:{beta:2d} BROKEN:{broken:2d} Local:{local:2d}"
            )
        return "\n".join(lines)

    # 2. Catalog completeness
    completeness_issues = check_catalog_completeness(entries)
    lines.extend([
        "## Catalog Completeness",
        "",
        f"| Check | Result |",
        f"|-------|--------|",
        f"| Missing titles | {sum(1 for i in completeness_issues if i['issue'] == 'missing title')} |",
        f"| Missing serie | {sum(1 for i in completeness_issues if i['issue'] == 'missing serie')} |",
        f"| Missing kernel | {sum(1 for i in completeness_issues if i['issue'] == 'missing kernel')} |",
        f"| Zero cells | {sum(1 for i in completeness_issues if i['issue'] == 'zero cells')} |",
        "",
    ])

    # 3. C.2 compliance by maturity
    c2 = check_c2_by_maturity(entries)
    lines.extend([
        "## C.2 Compliance by Maturity (non-BROKEN)",
        "",
        "| Maturity | Total | Compliant | Rate |",
        "|----------|-------|-----------|------|",
    ])
    for mat in ["PRODUCTION", "BETA", "ALPHA", "DRAFT"]:
        d = c2[mat]
        lines.append(f"| {mat} | {d['total']} | {d['compliant']} | {d['rate']}% |")
    lines.append("")

    # 4. README markers
    markers = check_readme_markers(entries)
    missing_markers = [m for m in markers if not m["has_marker"]]
    lines.extend([
        "## README Markers",
        "",
        f"| Serie | Has README | Has CATALOG-STATUS |",
        f"|-------|------------|---------------------|",
    ])
    for m in markers:
        readme = "Yes" if m["has_readme"] else "No"
        marker = "Yes" if m["has_marker"] else "No"
        lines.append(f"| {m['serie']} | {readme} | {marker} |")
    lines.append("")
    if missing_markers:
        lines.append(f"Missing markers: {', '.join(m['serie'] for m in missing_markers)}")
        lines.append("")

    # 5. Per-serie breakdown
    by_serie = {}
    for e in entries:
        by_serie.setdefault(e["serie"], []).append(e)

    lines.extend(["## Per-Serie Breakdown", ""])
    for serie in SERIES_ORDER:
        if serie not in by_serie:
            continue
        items = by_serie[serie]
        statuses = Counter(e.get("status") for e in items)
        maturities = Counter(e.get("maturity") for e in items)

        status_str = " ".join(
            f"{s}:{c}" for s, c in
            sorted(statuses.items(), key=lambda x: -x[1])
        )
        mat_str = " ".join(
            f"{m}:{c}" for m, c in
            sorted(maturities.items(), key=lambda x: -x[1])
        )

        local = sum(1 for e in items if e.get("executable_locally"))
        api = sum(1 for e in items if e.get("requires_api"))

        lines.extend([
            f"### {serie} ({len(items)} notebooks)",
            f"  Status: {status_str}",
            f"  Maturity: {mat_str}",
            f"  Local: {local} | API: {api} | Broken: {statuses.get('BROKEN', 0)}",
            "",
        ])

    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(
        description="Generate catalog coverage report"
    )
    parser.add_argument("--serie", type=str, default=None, help="Single serie")
    parser.add_argument("--json", action="store_true", help="JSON output")
    parser.add_argument("--short", action="store_true", help="Condensed report")
    parser.add_argument("--output", type=str, default=None, help="Output file")
    args = parser.parse_args()

    if not CATALOG_PATH.exists():
        print(f"Error: {CATALOG_PATH} not found. Run generate_catalog.py first.")
        return 2

    entries = json.loads(CATALOG_PATH.read_text(encoding="utf-8"))

    if args.json:
        report = {
            "total": len(entries),
            "completeness_issues": check_catalog_completeness(entries),
            "c2_compliance": check_c2_by_maturity(entries),
            "readme_markers": check_readme_markers(entries),
        }
        output = json.dumps(report, indent=2, ensure_ascii=False)
    else:
        output = generate_report(entries, serie_filter=args.serie, short=args.short)

    if args.output:
        Path(args.output).write_text(output, encoding="utf-8")
        print(f"Written to {args.output}")
    else:
        print(output)


if __name__ == "__main__":
    main()
