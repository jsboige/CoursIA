#!/usr/bin/env python3
"""Verify and inject CATALOG-STATUS markers in series READMEs.

Reads HTML comment blocks like:
    <!-- CATALOG-STATUS
    series: Search
    pedagogical_count: 40
    breakdown: Part1-Foundations=11, Part2-CSP=9, Applications=20
    updated: 2026-05-01
    -->

Then cross-checks declared counts against actual notebook scans.

Usage:
    python verify_catalog_readme.py                       # Verify all
    python verify_catalog_readme.py --series Search       # Verify single
    python verify_catalog_readme.py --inject              # Add/update markers
    python verify_catalog_readme.py --inject --series ML  # Inject single
"""

import argparse
import re
from datetime import date
from pathlib import Path

from count_notebooks_by_series import (
    NOTEBOOKS_DIR,
    SERIES_ORDER,
    count_notebooks_in_dir,
    extract_readme_count,
)

CATALOG_BLOCK_RE = re.compile(
    r"<!--\s*CATALOG-STATUS\s*\n(.*?)\n\s*-->",
    re.DOTALL,
)


def parse_catalog_block(text: str) -> dict | None:
    """Parse a CATALOG-STATUS block from README text."""
    m = CATALOG_BLOCK_RE.search(text)
    if not m:
        return None
    result = {}
    for line in m.group(1).strip().splitlines():
        if ":" not in line:
            continue
        key, _, val = line.partition(":")
        key = key.strip()
        val = val.strip()
        if key == "pedagogical_count":
            result[key] = int(val)
        elif key == "breakdown":
            result[key] = dict(
                p.split("=") for p in val.split(", ") if "=" in p
            )
            result[key] = {k: int(v) for k, v in result[key].items()}
        else:
            result[key] = val
    return result


def build_catalog_block(series: str, counts: dict) -> str:
    """Build a CATALOG-STATUS block string."""
    breakdown_parts = [
        f"{k}={v}" for k, v in sorted(counts["by_subfolder"].items())
    ]
    breakdown = ", ".join(breakdown_parts)
    return (
        f"<!-- CATALOG-STATUS\n"
        f"series: {series}\n"
        f"pedagogical_count: {counts['total']}\n"
        f"breakdown: {breakdown}\n"
        f"updated: {date.today().isoformat()}\n"
        f"-->"
    )


def verify_series(series_name: str, inject: bool = False) -> dict:
    """Verify a single series README against actual counts.

    Returns dict with keys: status, declared, actual, match, details.
    """
    readme_path = NOTEBOOKS_DIR / series_name / "README.md"
    counts = count_notebooks_in_dir(NOTEBOOKS_DIR / series_name, pedagogical=True)
    actual = counts["total"]

    if not readme_path.exists():
        return {"status": "NO_README", "actual": actual}

    text = readme_path.read_text(encoding="utf-8")
    catalog = parse_catalog_block(text)
    declared_catalog = catalog.get("pedagogical_count") if catalog else None
    declared_inline = extract_readme_count(readme_path)
    declared = declared_catalog or declared_inline

    match = declared == actual if declared is not None else None

    result = {
        "status": "OK" if match else "DRIFT" if match is False else "NO_MARKER",
        "declared": declared,
        "declared_source": "catalog" if declared_catalog else "inline",
        "actual": actual,
        "match": match,
        "breakdown": counts["by_subfolder"],
    }

    if inject:
        new_block = build_catalog_block(series_name, counts)
        if catalog is not None:
            text = CATALOG_BLOCK_RE.sub(new_block, text)
        else:
            title_match = re.search(r"^# .+\n", text, re.MULTILINE)
            if title_match:
                insert_pos = title_match.end()
                text = text[:insert_pos] + "\n" + new_block + "\n" + text[insert_pos:]
            else:
                text = new_block + "\n\n" + text

        readme_path.write_text(text, encoding="utf-8")
        result["injected"] = True

    return result


def main():
    parser = argparse.ArgumentParser(
        description="Verify CATALOG-STATUS markers in series READMEs"
    )
    parser.add_argument(
        "--series", type=str, default=None,
        help="Verify/inject a single series",
    )
    parser.add_argument(
        "--inject", action="store_true",
        help="Add or update CATALOG-STATUS markers",
    )
    args = parser.parse_args()

    series_list = [args.series] if args.series else SERIES_ORDER
    results = {}

    for series_name in series_list:
        series_dir = NOTEBOOKS_DIR / series_name
        if not series_dir.is_dir():
            continue
        results[series_name] = verify_series(series_name, inject=args.inject)

    action = "Injected" if args.inject else "Verified"
    print(f"\n{action} catalog markers")
    print(f"{'=' * 55}")
    print(f"{'Series':<15} {'Declared':>9} {'Actual':>7} {'Status':<12}")
    print(f"{'-' * 55}")

    drift_count = 0
    ok_count = 0
    no_marker_count = 0

    for name in SERIES_ORDER:
        if name not in results:
            continue
        r = results[name]
        declared = str(r.get("declared", "?"))
        actual = r.get("actual", 0)
        status = r["status"]

        if status == "OK":
            ok_count += 1
        elif status == "DRIFT":
            drift_count += 1
        else:
            no_marker_count += 1

        print(f"{name:<15} {declared:>9} {actual:>7} {status:<12}")

    print(f"{'=' * 55}")
    print(f"OK: {ok_count} | DRIFT: {drift_count} | NO_MARKER: {no_marker_count}")

    if drift_count > 0 and not args.inject:
        print(f"\nRun with --inject to update markers.")


if __name__ == "__main__":
    main()
