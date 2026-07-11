#!/usr/bin/env python3
"""Check for broken relative markdown links and orphan docs across the repository.

Scans CLAUDE.md, docs/, .claude/rules/, .claude/agents/, .claude/skills/,
and all README.md files for relative links and verifies targets exist.

Also detects orphan .md files in docs/ (not referenced by any scanned file).

Usage:
    python scripts/check_docs_links.py               # Full scan
    python scripts/check_docs_links.py --baseline     # Write baseline report
    python scripts/check_docs_links.py --check        # Check against baseline
    python scripts/check_docs_links.py --quiet        # Minimal output (for CI)
    python scripts/check_docs_links.py --orphans      # Also report orphan docs

Exit codes:
    0 = all links valid (or only pre-existing broken links in baseline mode)
    1 = new broken links found (regression)
    2 = error during execution
"""

import argparse
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path
from urllib.parse import unquote

REPO_ROOT = Path(__file__).resolve().parent.parent

# Directories and files to scan for links
SCAN_SCOPES = [
    "CLAUDE.md",
    "docs/",
    ".claude/rules/",
    ".claude/agents/",
    ".claude/skills/",
]

# Directories to skip when scanning and resolving
SKIP_DIRS = {
    ".lake", "node_modules", ".git", "venv", "__pycache__",
    "_archives", "archive", "_output", ".ipynb_checkpoints", "worktrees",
    ".mypy_cache", ".pytest_cache", ".ruff_cache",
    "custom_nodes",  # Third-party ComfyUI plugins, not ours to fix
}

# Baseline file location
BASELINE_PATH = REPO_ROOT / "scripts" / "tests" / "baseline_docs_links.json"


def _load_submodule_paths() -> set[str]:
    """Read git submodule paths from .gitmodules (repo-relative, posix form).

    Submodule internals are third-party checkouts (Argumentum, MetaGeneticSharp):
    their broken links are not ours to fix, so we skip them like SKIP_DIRS.
    Returns an empty set if .gitmodules is absent or unparsable.
    """
    gitmodules = REPO_ROOT / ".gitmodules"
    if not gitmodules.is_file():
        return set()
    paths: set[str] = set()
    try:
        for line in gitmodules.read_text(encoding="utf-8").splitlines():
            line = line.strip()
            if line.startswith("path"):
                _, _, value = line.partition("=")
                value = value.strip().strip("/")
                if value:
                    paths.add(value)
    except OSError:
        return set()
    return paths


SUBMODULE_PATHS = _load_submodule_paths()

# Pattern: [link text](relative/path) — captures relative paths only (no http/https/#anchors)
LINK_PATTERN = re.compile(
    r"\[([^\]]*)\]\((?!https?://)(?!mailto:)(?!#)([^)\s#]+)\)"
)


@dataclass
class LinkRef:
    """A single link reference found in a file."""
    source: str       # relative path from repo root
    target: str       # the link target (raw)
    line: int         # line number
    text: str         # link text


@dataclass
class ScanResult:
    """Result of a full link scan."""
    broken: list[LinkRef] = field(default_factory=list)
    valid: list[LinkRef] = field(default_factory=list)
    orphans: list[str] = field(default_factory=list)
    scanned_files: int = 0
    total_links: int = 0


def _should_skip(path: Path) -> bool:
    """Check if a path should be skipped (in SKIP_DIRS, a submodule, or problematic)."""
    try:
        rel = path.relative_to(REPO_ROOT)
    except ValueError:
        return True
    if any(skip in rel.parts for skip in SKIP_DIRS):
        return True
    rel_posix = rel.as_posix()
    return any(rel_posix == sm or rel_posix.startswith(sm + "/") for sm in SUBMODULE_PATHS)


def _is_valid_target(target: str) -> bool:
    """Filter out non-file links (anchors, URLs, template variables)."""
    if not target:
        return False
    # Skip template variables, absolute paths, URLs
    if target.startswith(("{", "<", "http:", "https:", "mailto:", "#", "/")):
        return False
    # Skip image references in some edge cases
    if target.endswith((".png", ".jpg", ".jpeg", ".gif", ".svg", ".ico")):
        return True  # Still check these
    # Only check file-like targets
    if "." not in Path(target).name and not target.endswith("/"):
        return False
    return True


def find_scan_files() -> list[Path]:
    """Collect all files to scan for links."""
    files = []
    for scope in SCAN_SCOPES:
        p = REPO_ROOT / scope
        if p.is_file():
            files.append(p)
        elif p.is_dir():
            for f in sorted(p.rglob("*.md")):
                if not _should_skip(f):
                    files.append(f)

    # Add all README.md files (excluding skipped dirs)
    for readme in sorted(REPO_ROOT.rglob("README.md")):
        if not _should_skip(readme):
            if readme not in files:
                files.append(readme)

    return files


def scan_file(filepath: Path) -> list[LinkRef]:
    """Extract all relative links from a markdown file.

    Skips links inside fenced code blocks (```...```).
    """
    refs = []
    try:
        content = filepath.read_text(encoding="utf-8")
    except (UnicodeDecodeError, PermissionError, OSError):
        return refs

    in_code_block = False
    for line_num, line in enumerate(content.splitlines(), 1):
        stripped = line.strip()
        if stripped.startswith("```"):
            in_code_block = not in_code_block
            continue
        if in_code_block:
            continue

        # Strip inline code spans (`...`): their contents render as literal text,
        # so a [text](target) inside backticks is not a clickable link. This avoids
        # false positives on format templates in review ledgers, e.g. `[Foo](...)`.
        line = re.sub(r"`[^`]*`", "", line)

        for match in LINK_PATTERN.finditer(line):
            text = match.group(1)
            target = match.group(2)
            if _is_valid_target(target):
                try:
                    rel_source = str(filepath.relative_to(REPO_ROOT)).replace("\\", "/")
                except ValueError:
                    rel_source = str(filepath)
                refs.append(LinkRef(
                    source=rel_source,
                    target=target,
                    line=line_num,
                    text=text,
                ))
    return refs


def check_link(target: str, source_path: Path, root: Path = REPO_ROOT) -> bool:
    """Check if a relative link target exists.

    Args:
        target: The link target (relative path).
        source_path: Path of the file containing the link.
        root: Root directory for safety check (default: REPO_ROOT).
    """
    # Resolve relative to source file's directory (decode URL-encoded chars)
    try:
        decoded_target = unquote(target)
        resolved = (source_path.parent / decoded_target).resolve()
    except (OSError, ValueError):
        return False

    # Must be within root (safety: no escaping outside the repo)
    try:
        rel_posix = resolved.relative_to(root).as_posix()
    except ValueError:
        return False

    # Links into a git submodule are valid regardless of checkout state: CI uses
    # submodules: false, so the mount dir may be absent. Submodule content is
    # third-party — its presence is not this repo's concern to verify.
    if any(rel_posix == sm or rel_posix.startswith(sm + "/") for sm in SUBMODULE_PATHS):
        return True

    return resolved.exists()


def find_orphan_docs(scanned_files: list[Path], all_refs: list[LinkRef]) -> list[str]:
    """Find .md files in docs/ not referenced by any link in scanned files."""
    # Collect all link targets (resolved to repo-relative paths)
    referenced = set()
    for ref in all_refs:
        source_path = REPO_ROOT / ref.source
        resolved = (source_path.parent / ref.target).resolve()
        try:
            rel = str(resolved.relative_to(REPO_ROOT)).replace("\\", "/")
            referenced.add(rel)
        except ValueError:
            pass

    orphans = []
    docs_dir = REPO_ROOT / "docs"
    if docs_dir.exists():
        for md_file in sorted(docs_dir.rglob("*.md")):
            if _should_skip(md_file):
                continue
            try:
                rel = str(md_file.relative_to(REPO_ROOT)).replace("\\", "/")
            except ValueError:
                continue
            if rel not in referenced:
                orphans.append(rel)

    return orphans


def run_scan(report_orphans: bool = False) -> ScanResult:
    """Run a full link scan across the repository."""
    result = ScanResult()
    files = find_scan_files()
    result.scanned_files = len(files)

    all_refs = []
    for filepath in files:
        refs = scan_file(filepath)
        all_refs.extend(refs)

    result.total_links = len(all_refs)

    for ref in all_refs:
        source_path = REPO_ROOT / ref.source
        if check_link(ref.target, source_path):
            result.valid.append(ref)
        else:
            result.broken.append(ref)

    if report_orphans:
        result.orphans = find_orphan_docs(files, all_refs)

    return result


def write_baseline(result: ScanResult, path: Path = BASELINE_PATH) -> None:
    """Write scan results as a baseline JSON file."""
    path.parent.mkdir(parents=True, exist_ok=True)
    data = {
        "broken_links": [
            {"source": r.source, "target": r.target, "line": r.line, "text": r.text}
            for r in result.broken
        ],
        "orphans": result.orphans,
        "scanned_files": result.scanned_files,
        "total_links": result.total_links,
    }
    path.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n",
                    encoding="utf-8")


def load_baseline(path: Path = BASELINE_PATH) -> dict | None:
    """Load a baseline JSON file. Returns None if not found."""
    if not path.exists():
        return None
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, UnicodeDecodeError):
        return None


def check_regression(result: ScanResult, baseline: dict) -> list[LinkRef]:
    """Find broken links that are NOT in the baseline (new regressions)."""
    baseline_targets = {
        (b["source"], b["target"]) for b in baseline.get("broken_links", [])
    }
    new_broken = []
    for ref in result.broken:
        key = (ref.source, ref.target)
        if key not in baseline_targets:
            new_broken.append(ref)
    return new_broken


def format_report(result: ScanResult, show_orphans: bool = False) -> str:
    """Format scan results as a human-readable report."""
    lines = []
    lines.append(f"Scanned {result.scanned_files} files, {result.total_links} links")

    if result.broken:
        lines.append(f"\nBroken links ({len(result.broken)}):")
        for ref in sorted(result.broken, key=lambda r: (r.source, r.line)):
            lines.append(f"  {ref.source}:{ref.line} -> {ref.target}")
    else:
        lines.append("\nNo broken links found.")

    if show_orphans and result.orphans:
        lines.append(f"\nOrphan docs ({len(result.orphans)}) [WARN, non-blocking]:")
        for orphan in result.orphans:
            lines.append(f"  {orphan}")

    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(
        description="Check for broken relative links in markdown files",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("--baseline", action="store_true",
                        help="Write current state as baseline")
    parser.add_argument("--check", action="store_true",
                        help="Check for regressions against baseline")
    parser.add_argument("--orphans", action="store_true",
                        help="Also report orphan docs")
    parser.add_argument("--quiet", action="store_true",
                        help="Minimal output")
    args = parser.parse_args()

    try:
        result = run_scan(report_orphans=args.orphans)

        if args.baseline:
            write_baseline(result)
            if not args.quiet:
                print(f"Baseline written to {BASELINE_PATH}")
                print(format_report(result, show_orphans=True))
            return

        if args.check:
            baseline = load_baseline()
            if baseline is None:
                if not args.quiet:
                    print("No baseline found. Run with --baseline first.")
                # If no baseline, any broken link is a regression
                if result.broken:
                    if not args.quiet:
                        print(format_report(result))
                    sys.exit(1)
                sys.exit(0)

            new_broken = check_regression(result, baseline)
            if new_broken:
                if not args.quiet:
                    print(f"REGRESSION: {len(new_broken)} new broken link(s):")
                    for ref in new_broken:
                        print(f"  {ref.source}:{ref.line} -> {ref.target}")
                    print(f"\nBaseline had {len(baseline.get('broken_links', []))} known broken.")
                sys.exit(1)
            else:
                if not args.quiet:
                    print(f"OK: No new broken links. "
                          f"({len(result.broken)} pre-existing, {result.total_links} total)")
                sys.exit(0)

        # Default: full scan
        if not args.quiet:
            print(format_report(result, show_orphans=args.orphans))

        if result.broken:
            sys.exit(1)
        sys.exit(0)

    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(2)


if __name__ == "__main__":
    main()
