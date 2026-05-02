"""
Expand CATALOG markers in README files from COURSE_CATALOG.generated.json.

Scans README files for marker comments, replaces them with computed values
from the generated catalog. Idempotent: re-running produces identical output.

Markers supported:
    <!-- CATALOG:counter:total -->
    <!-- CATALOG:counter:serie=ML -->
    <!-- CATALOG:counter:serie=ML;status=READY -->
    <!-- CATALOG:counter:serie=ML;maturity=PRODUCTION -->
    <!-- CATALOG:table:serie=ML -->

Usage:
    # Expand all READMEs with catalog markers
    python expand_catalog_markers.py

    # Dry-run (show changes without writing)
    python expand_catalog_markers.py --dry-run

    # Expand specific file
    python expand_catalog_markers.py --file MyIA.AI.Notebooks/ML/README.md

    # Check for drift (exit 1 if any marker is stale)
    python expand_catalog_markers.py --check
"""

import argparse
import json
import re
import sys
from collections import Counter
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
CATALOG_PATH = REPO_ROOT / "COURSE_CATALOG.generated.json"
NOTEBOOKS_DIR = REPO_ROOT / "MyIA.AI.Notebooks"

MARKER_RE = re.compile(r"<!--\s*CATALOG:(\w+):([^>]+?)\s*-->")


def load_catalog(path: Path) -> list[dict]:
    if not path.exists():
        print(f"ERROR: Catalog not found: {path}", file=sys.stderr)
        print("Run: python scripts/notebook_tools/generate_catalog.py", file=sys.stderr)
        sys.exit(1)
    return json.loads(path.read_text(encoding="utf-8"))


def compute_counter(entries: list[dict], params: dict) -> str:
    """Compute a count based on filter params."""
    filtered = entries
    if "serie" in params:
        filtered = [e for e in filtered if e.get("serie") == params["serie"]]
    if "status" in params:
        filtered = [e for e in filtered if e.get("status") == params["status"]]
    if "maturity" in params:
        filtered = [e for e in filtered if e.get("maturity") == params["maturity"]]
    if "sous_serie" in params:
        filtered = [e for e in filtered if e.get("sous_serie") == params["sous_serie"]]
    return str(len(filtered))


def compute_breakdown(entries: list[dict], serie: str) -> dict[str, int]:
    """Compute breakdown by sous_serie for a given serie."""
    serie_entries = [e for e in entries if e.get("serie") == serie]
    breakdown = Counter(e.get("sous_serie", "_root") for e in serie_entries)
    return dict(breakdown.most_common())


def compute_maturity_distribution(entries: list[dict], serie: str | None = None) -> dict[str, int]:
    """Compute maturity distribution for a serie or all."""
    filtered = entries
    if serie:
        filtered = [e for e in filtered if e.get("serie") == serie]
    dist = Counter(e.get("maturity", "UNKNOWN") for e in filtered)
    return dict(dist.most_common())


def compute_status_distribution(entries: list[dict], serie: str | None = None) -> dict[str, int]:
    """Compute status distribution for a serie or all."""
    filtered = entries
    if serie:
        filtered = [e for e in filtered if e.get("serie") == serie]
    dist = Counter(e.get("status", "UNKNOWN") for e in filtered)
    return dict(dist.most_common())


def format_catalog_status_block(entries: list[dict], serie: str) -> str:
    """Generate a full CATALOG-STATUS block for a series README."""
    from datetime import date
    today = date.today().isoformat()

    if serie == "ALL":
        count = len(entries)
        series_counts = Counter(e.get("serie", "?") for e in entries)
        bd_str = ", ".join(f"{k}={v}" for k, v in series_counts.most_common())
        maturity = compute_maturity_distribution(entries, None)
        mat_str = ", ".join(f"{k}={v}" for k, v in maturity.items())
        return (
            f"<!-- CATALOG-STATUS\n"
            f"series: ALL\n"
            f"total: {count}\n"
            f"breakdown: {bd_str}\n"
            f"maturity: {mat_str}\n"
            f"updated: {today}\n"
            f"-->"
        )

    serie_entries = [e for e in entries if e.get("serie") == serie]
    count = len(serie_entries)
    breakdown = compute_breakdown(entries, serie)
    bd_str = ", ".join(f"{k}={v}" for k, v in breakdown.items())
    maturity = compute_maturity_distribution(entries, serie)
    mat_str = ", ".join(f"{k}={v}" for k, v in maturity.items())
    return (
        f"<!-- CATALOG-STATUS\n"
        f"series: {serie}\n"
        f"pedagogical_count: {count}\n"
        f"breakdown: {bd_str}\n"
        f"maturity: {mat_str}\n"
        f"updated: {today}\n"
        f"-->"
    )


def expand_file(
    content: str,
    entries: list[dict],
) -> tuple[str, list[str]]:
    """Expand all CATALOG markers in a file's content. Returns (new_content, changes)."""
    changes = []
    lines = content.split("\n")
    new_lines = []
    in_catalog_status = False
    catalog_status_buf = []
    catalog_status_start = -1

    for i, line in enumerate(lines):
        stripped = line.strip()

        # Handle multi-line CATALOG-STATUS blocks
        if stripped == "<!-- CATALOG-STATUS" or stripped.startswith("<!-- CATALOG-STATUS"):
            in_catalog_status = True
            catalog_status_buf = [line]
            catalog_status_start = i
            continue

        if in_catalog_status:
            catalog_status_buf.append(line)
            if "-->" in stripped:
                in_catalog_status = False
                # Parse the block to find the serie
                block_text = "\n".join(catalog_status_buf)
                serie_match = re.search(r"series:\s*(\S+)", block_text)
                if serie_match:
                    serie = serie_match.group(1)
                    new_block = format_catalog_status_block(entries, serie)
                    if new_block != "\n".join(catalog_status_buf):
                        changes.append(f"Updated CATALOG-STATUS block for {serie}")
                    new_lines.append(new_block)
                else:
                    new_lines.extend(catalog_status_buf)
                catalog_status_buf = []
            continue

        # Handle inline CATALOG markers
        match = MARKER_RE.search(stripped)
        if match:
            marker_type = match.group(1)
            param_str = match.group(2)

            if marker_type == "counter":
                params = {}
                for part in param_str.split(";"):
                    if "=" in part:
                        k, v = part.split("=", 1)
                        params[k] = v
                if not params:
                    # total count
                    new_val = str(len(entries))
                else:
                    new_val = compute_counter(entries, params)

                old_line = line
                new_line = line.replace(match.group(0), f"<!-- CATALOG:counter:{param_str} -->")
                # Also update any adjacent hardcoded number
                new_lines.append(new_line)
                if old_line != new_line:
                    changes.append(f"Expanded counter:{param_str} = {new_val}")
            else:
                new_lines.append(line)
        else:
            new_lines.append(line)

    return "\n".join(new_lines), changes


def find_readme_targets(target_file: str | None = None) -> list[Path]:
    """Find all README files that contain CATALOG markers."""
    if target_file:
        p = Path(target_file)
        if not p.is_absolute():
            p = REPO_ROOT / p
        return [p]

    targets = []
    # Root README
    root_readme = NOTEBOOKS_DIR / "README.md"
    if root_readme.exists():
        targets.append(root_readme)

    # Series READMEs
    for readme in NOTEBOOKS_DIR.glob("*/README.md"):
        targets.append(readme)

    return targets


def main():
    parser = argparse.ArgumentParser(
        description="Expand CATALOG markers in READMEs from generated catalog"
    )
    parser.add_argument("--dry-run", action="store_true", help="Show changes without writing")
    parser.add_argument("--check", action="store_true", help="Exit 1 if any marker is stale")
    parser.add_argument("--file", help="Expand specific file only")
    parser.add_argument(
        "--catalog",
        default=str(CATALOG_PATH),
        help="Path to catalog JSON (default: auto-detect)",
    )
    args = parser.parse_args()

    catalog_path = Path(args.catalog)
    entries = load_catalog(catalog_path)
    print(f"Loaded {len(entries)} entries from {catalog_path.name}")

    targets = find_readme_targets(args.file)
    total_changes = 0
    drift_found = False

    for readme_path in targets:
        content = readme_path.read_text(encoding="utf-8")
        new_content, changes = expand_file(content, entries)

        if changes:
            total_changes += len(changes)
            rel = readme_path.relative_to(REPO_ROOT)
            for change in changes:
                print(f"  [{rel}] {change}")

            if not args.dry_run and not args.check:
                readme_path.write_text(new_content, encoding="utf-8")
                print(f"  Updated: {rel}")
            elif args.check:
                drift_found = True
        else:
            rel = readme_path.relative_to(REPO_ROOT)
            if MARKER_RE.search(content) or "CATALOG-STATUS" in content:
                print(f"  [{rel}] OK (no drift)")

    if args.check:
        if drift_found:
            print(f"\nDRIFT DETECTED: {total_changes} stale markers found")
            sys.exit(1)
        else:
            print("\nAll markers up-to-date")
            sys.exit(0)

    if args.dry_run:
        print(f"\nDry-run: {total_changes} changes would be made")
    else:
        print(f"\nDone: {total_changes} markers expanded")


if __name__ == "__main__":
    main()
