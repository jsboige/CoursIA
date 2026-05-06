#!/usr/bin/env python3
"""Validate QuantConnect project directory structure and README consistency.

Usage:
    python scripts/validate_qc_projects.py [--projects DIR] [--readme FILE] [--fix]

Checks:
    1. Every project dir has main.py or Main.cs
    2. Every project in README tables exists on disk
    3. Every project on disk appears in README
    4. Count matches between README header and actual
    5. Empty/orphan directories
    6. Duplicate detection across source dirs (projects-imported, ESGF-2026/examples)
"""

import argparse
import os
import re
import sys
from pathlib import Path


def find_projects(projects_dir: Path) -> dict[str, Path]:
    """Find all project directories with code files."""
    SKIP_DIRS = {"_docs", "_archives", "__pycache__", ".git"}
    projects = {}
    for child in sorted(projects_dir.iterdir()):
        if not child.is_dir():
            continue
        if child.name.startswith("_") or child.name in SKIP_DIRS:
            continue
        name = child.name
        has_code = any((child / f).exists() for f in ("main.py", "Main.cs"))
        projects[name] = child
    return projects


def parse_readme_projects(readme_path: Path) -> set[str]:
    """Extract project names from README markdown tables."""
    names = set()
    if not readme_path.exists():
        return names
    text = readme_path.read_text(encoding="utf-8")
    SKIP_NAMES = {
        "docs", "forum", "terminal", "OPTIMIZATION_BACKLOG.md",
        "..", "http", "https",
    }
    # Match [ProjectName](ProjectName/) or [ProjectName](path/ProjectName/)
    for match in re.finditer(r"\[([^\]]+)\]\(([^)]*?/)?([^)/]+)/?\)", text):
        name = match.group(3)
        if name in SKIP_NAMES or name.startswith(".") or name.startswith("http"):
            continue
        # Only count names that look like project dirs (not file extensions)
        if "." in name and not name.endswith("/"):
            continue
        names.add(name)
    return names


def parse_readme_counts(readme_path: Path) -> dict[str, int] | None:
    """Parse the summary line from README header."""
    if not readme_path.exists():
        return None
    text = readme_path.read_text(encoding="utf-8")
    counts = {}
    # Match patterns like **78 stratégies** or **8 clones**
    for match in re.finditer(r"\*\*(\d+)\s+([^*]+)\*\*", text):
        num = int(match.group(1))
        label = match.group(2).strip().lower()
        counts[label] = num
    return counts if counts else None


def check_duplicate_sources(qc_root: Path) -> list[str]:
    """Check for duplicate projects across source directories."""
    projects_dir = qc_root / "projects"
    canonical = set()
    for child in projects_dir.iterdir():
        if child.is_dir():
            canonical.add(child.name.lower().replace("-", "").replace("_", ""))

    issues = []
    source_dirs = [
        qc_root / "projects-imported",
        qc_root / "algorithms" / "python",
        qc_root / "ESGF-2026" / "examples",
    ]
    for src_dir in source_dirs:
        if not src_dir.exists():
            continue
        for child in src_dir.iterdir():
            if child.is_dir():
                norm = child.name.lower().replace("-", "").replace("_", "")
                if norm in canonical:
                    issues.append(
                        f"DUPLICATE: {child.relative_to(qc_root)} matches "
                        f"projects/ entry"
                    )
    return issues


def validate(projects_dir: Path, readme_path: Path) -> list[str]:
    """Run all validation checks, return list of issues."""
    issues = []

    # 1. Find all projects
    all_projects = find_projects(projects_dir)
    code_projects = {
        n: p for n, p in all_projects.items()
        if any((p / f).exists() for f in ("main.py", "Main.cs"))
    }
    empty_projects = {
        n: p for n, p in all_projects.items()
        if not any((p / f).exists() for f in ("main.py", "Main.cs"))
    }

    # 2. Parse README
    readme_names = parse_readme_projects(readme_path)

    # 3. Missing from disk (in README but not on disk)
    in_readme_not_disk = readme_names - set(all_projects.keys())
    for name in sorted(in_readme_not_disk):
        issues.append(f"MISSING_ON_DISK: {name} (in README but no directory)")

    # 4. Missing from README (on disk but not in README)
    on_disk_not_readme = set(all_projects.keys()) - readme_names
    for name in sorted(on_disk_not_readme):
        issues.append(f"MISSING_IN_README: {name} (directory exists but not in README)")

    # 5. Empty projects (no main.py/Main.cs)
    for name in sorted(empty_projects):
        issues.append(f"NO_CODE: {name} (directory exists but no main.py/Main.cs)")

    # 6. Count mismatch
    total_expected = len(code_projects)
    total_in_readme = len(readme_names & set(all_projects.keys()))
    if total_expected != total_in_readme:
        issues.append(
            f"COUNT_MISMATCH: {total_expected} projects with code on disk, "
            f"{total_in_readme} in README tables, "
            f"{len(on_disk_not_readme)} undocumented, "
            f"{len(in_readme_not_disk)} missing"
        )

    # 7. Duplicate sources
    qc_root = projects_dir.parent
    dup_issues = check_duplicate_sources(qc_root)
    issues.extend(dup_issues)

    # 8. Summary
    issues.append(f"SUMMARY: {len(all_projects)} dirs, {len(code_projects)} with code, "
                  f"{len(empty_projects)} empty, {len(readme_names)} in README")

    return issues


def main():
    parser = argparse.ArgumentParser(
        description="Validate QC projects structure and README consistency"
    )
    parser.add_argument(
        "--projects",
        default="MyIA.AI.Notebooks/QuantConnect/projects",
        help="Path to projects directory",
    )
    parser.add_argument(
        "--readme",
        default="MyIA.AI.Notebooks/QuantConnect/projects/README.md",
        help="Path to projects README.md",
    )
    parser.add_argument(
        "--fix", action="store_true",
        help="Print suggested fixes (not yet implemented)",
    )
    args = parser.parse_args()

    root = Path(__file__).parent.parent
    projects_dir = root / args.projects
    readme_path = root / args.readme

    if not projects_dir.exists():
        print(f"ERROR: projects directory not found: {projects_dir}")
        sys.exit(1)

    issues = validate(projects_dir, readme_path)

    errors = [i for i in issues if not i.startswith("SUMMARY")]
    for issue in issues:
        prefix = "" if issue.startswith("SUMMARY") else "  "
        print(f"{prefix}{issue}")

    if errors:
        print(f"\n{len(errors)} issue(s) found.")
        sys.exit(1)
    else:
        print("\nAll checks passed.")
        sys.exit(0)


if __name__ == "__main__":
    main()
