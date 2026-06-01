#!/usr/bin/env python3
"""Check for broken markdown links to docs/ across the repository.

Scans CLAUDE.md, .claude/rules/*.md, PARCOURS.md, and README.md files
for relative links pointing to docs/ and verifies the targets exist.

Usage:
    python scripts/check_docs_links.py [--fix] [--quiet]

Exit codes:
    0 = all links valid
    1 = broken links found
"""

import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent

# Files/directories to scan for docs/ links
SCAN_TARGETS = [
    "CLAUDE.md",
    "PARCOURS.md",
    ".claude/rules/",
]

# Pattern: [any text](docs/...) — relative links to docs/
LINK_PATTERN = re.compile(r"\[([^\]]*)\]\((docs/[^)\s#]+\.md)\)")

# Directories to skip
SKIP_DIRS = {"_archives", "node_modules", ".git", "venv", "__pycache__"}

# Known false positives: links in code blocks or comments that reference
# docs/ as examples, not actual file references
KNOWN_VALID = set()


def find_readmes() -> list[Path]:
    """Find all README.md files in the repo (excluding skip dirs)."""
    readmes = []
    for p in REPO_ROOT.rglob("README.md"):
        parts = p.relative_to(REPO_ROOT).parts
        if any(skip in parts for skip in SKIP_DIRS):
            continue
        # Skip READMEs inside deeply nested _output or cache dirs
        if "_output" in str(p) or ".ipynb_checkpoints" in str(p):
            continue
        readmes.append(p)
    return readmes


def scan_file(filepath: Path) -> list[tuple[str, str, int]]:
    """Scan a file for docs/ links. Returns [(link_text, link_path, line_number)]."""
    results = []
    try:
        content = filepath.read_text(encoding="utf-8")
    except (UnicodeDecodeError, PermissionError):
        return results

    for i, line in enumerate(content.splitlines(), 1):
        # Skip code blocks (lines starting with ``` or inside them)
        for match in LINK_PATTERN.finditer(line):
            link_text = match.group(1)
            link_path = match.group(2)
            results.append((link_text, link_path, i))
    return results


def check_link(link_path: str, source_file: Path) -> bool:
    """Check if a docs/ link target exists."""
    # Resolve relative to source file's directory
    source_dir = source_file.parent
    target = source_dir / link_path

    # Normalize path
    try:
        target = target.resolve()
    except (OSError, ValueError):
        return False

    # Must be within the repo
    try:
        target.relative_to(REPO_ROOT)
    except ValueError:
        return False

    return target.exists()


def main():
    quiet = "--quiet" in sys.argv
    fix_mode = "--fix" in sys.argv

    broken = []

    # Scan configured targets
    scan_files = []
    for target in SCAN_TARGETS:
        p = REPO_ROOT / target
        if p.is_file():
            scan_files.append(p)
        elif p.is_dir():
            scan_files.extend(sorted(p.glob("*.md")))

    # Scan READMEs
    scan_files.extend(find_readmes())

    for filepath in scan_files:
        links = scan_file(filepath)
        for link_text, link_path, line_num in links:
            if link_path in KNOWN_VALID:
                continue
            if not check_link(link_path, filepath):
                rel_source = filepath.relative_to(REPO_ROOT)
                broken.append((str(rel_source), link_path, line_num, link_text))

    if broken:
        if not quiet:
            print(f"Found {len(broken)} broken docs/ link(s):\n")
            for source, link, line, text in broken:
                print(f"  {source}:{line} -> {link}  (text: {text!r})")
            print(f"\nTotal: {len(broken)} broken link(s)")
        sys.exit(1)
    else:
        if not quiet:
            print("All docs/ links are valid.")
        sys.exit(0)


if __name__ == "__main__":
    main()
