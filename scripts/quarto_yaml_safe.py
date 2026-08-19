#!/usr/bin/env python3
"""Quarto YAML-safe pre-processor — escape standalone `---` separators in markdown cells.

Problem (issue #11611): notebook cells starting with `---` (visual section
separator before `## Heading`) are concatenated by Quarto's nbconvert pipeline
into a single markdown stream. Pandoc then tries to parse the result as a YAML
front matter, and a `---` cell followed by another `---` cell (or by a
markdown table) triggers:

  YAMLException: end of the stream or a document separator is expected (8:1)

The condition for breakage is:
  - cell A is markdown with `---` at L1 (standalone separator)
  - cell B (next) is markdown starting with content that pandoc interprets
    ambiguously (table `|` or another `---`)
  - the joined stream has multiple `---` markers that confuse YAML front-matter
    parsing.

Fix: convert standalone `---` at L1 of markdown cells into `***` (alternate
markdown horizontal rule syntax). The visual result is identical (a horizontal
rule), but `***` is not a YAML document separator. Round-trip is clean.

Apply scope: walk MyIA.AI.Notebooks/**.ipynb. Only modify cells where:
  - cell_type == 'markdown'
  - source is a non-empty list
  - first line == '---' (after strip)
  - second line is empty (separator pattern, not YAML front-matter)

Manifest (gitignored) records offsets so restore is verified. Byte-level
replacement, no JSON re-serialization.

Usage:
  python scripts/quarto_yaml_safe.py apply [--target <path>]
  python scripts/quarto_yaml_safe.py restore
  python scripts/quarto_yaml_safe.py check [--strict] [--target <path>]
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Iterable

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_ROOT = REPO_ROOT / "MyIA.AI.Notebooks"
DEFAULT_MANIFEST = REPO_ROOT / ".quarto_yaml_safe_manifest.json"

# In JSON source, the line `---` is encoded as the 7-byte literal `"---\n"`
# (backslash + n, NOT real newline 0x0a). The Python raw byte literal preserves
# backslash-n as two distinct bytes 0x5c 0x6e.
NEEDLE = rb'"---\n"'  # 7 bytes raw
REPLACEMENT = rb'"***\n"'  # 7 bytes raw


def iter_ipynb(root: Path) -> Iterable[Path]:
    yield from sorted(root.rglob("*.ipynb"))


def iter_ipynb_paths(paths: list[Path]) -> Iterable[Path]:
    """Yield .ipynb files for explicit paths (file or dir)."""
    for p in paths:
        if p.is_file() and p.suffix == ".ipynb":
            yield p
        elif p.is_dir():
            yield from sorted(p.rglob("*.ipynb"))


def _scan_cells(raw: bytes) -> list[tuple[int, int, int, dict]]:
    """Locate each cell object in raw JSON via brace-depth scan.

    Returns list of (cell_index, byte_start, byte_end, parsed_cell).
    """
    text = raw.decode("utf-8", errors="replace")
    try:
        nb = json.loads(text)
    except Exception:
        return []
    cells = nb.get("cells", [])
    # Find the cells array.
    cells_key = raw.find(b'"cells"')
    if cells_key < 0:
        return []
    array_open = raw.find(b'[', cells_key)
    if array_open < 0:
        return []
    results = []
    pos = array_open + 1
    idx = 0
    while pos < len(raw) and idx < len(cells):
        # Skip whitespace and commas
        while pos < len(raw) and raw[pos:pos+1] in b' \r\n\t,':
            pos += 1
        if pos >= len(raw) or raw[pos:pos+1] != b'{':
            break
        # Find matching closing brace
        depth = 0
        start = pos
        in_string = False
        escape = False
        while pos < len(raw):
            ch = raw[pos:pos+1]
            if in_string:
                if escape:
                    escape = False
                elif ch == b'\\':
                    escape = True
                elif ch == b'"':
                    in_string = False
            else:
                if ch == b'"':
                    in_string = True
                elif ch == b'{':
                    depth += 1
                elif ch == b'}':
                    depth -= 1
                    if depth == 0:
                        pos += 1
                        results.append((idx, start, pos, cells[idx]))
                        idx += 1
                        break
            pos += 1
    return results


def find_separator_cells(raw: bytes) -> list[tuple[int, int]]:
    """Return list of (cell_index, byte_offset_of_separator_token).

    A cell may contribute multiple offsets (one per standalone `---\n"`)
    within its own source range.
    """
    results = []
    scanned = _scan_cells(raw)
    for idx, start, end, c in scanned:
        if not isinstance(c, dict):
            continue
        if c.get("cell_type") != "markdown":
            continue
        src = c.get("source")
        if not isinstance(src, list) or not src:
            continue
        # Pattern: first element == "---\n", second element == "\n"
        if src[0] != "---\n":
            continue
        if len(src) < 2 or src[1] != "\n":
            continue
        # Find ALL `---\n"` occurrences within this cell's byte range.
        pos = start
        while pos < end:
            off = raw.find(NEEDLE, pos, end)
            if off < 0:
                break
            results.append((idx, off))
            pos = off + len(NEEDLE)
    return results


def apply(targets: list[Path], root: Path, manifest_path: Path) -> int:
    """Replace standalone `---` separators in markdown cells with `***`.
    Record file -> [offset, ...] in manifest.
    """
    manifest_data: dict[str, list[int]] = {}
    total_files = 0
    total_cells = 0
    if targets:
        iterator = iter_ipynb_paths(targets)
    else:
        iterator = iter_ipynb(root)
    for path in iterator:
        raw = path.read_bytes()
        cells = find_separator_cells(raw)
        if not cells:
            continue
        # Replace from last to first to preserve offsets.
        new_raw = raw
        for idx, offset in reversed(cells):
            new_raw = new_raw[:offset] + REPLACEMENT + new_raw[offset + len(NEEDLE):]
        # Sanity: re-parse the result.
        try:
            json.loads(new_raw)
        except Exception as e:
            print(f"  SKIP {path}: re-parse failed: {e}", file=sys.stderr)
            continue
        rel = path.relative_to(REPO_ROOT) if path.is_absolute() else path
        manifest_data[str(rel)] = [off for _, off in cells]
        path.write_bytes(new_raw)
        total_files += 1
        total_cells += len(cells)
    manifest_path.write_text(json.dumps(manifest_data, indent=2), encoding="utf-8")
    print(f"apply: {total_files} files, {total_cells} cells (manifest={manifest_path})")
    return 0


def restore(root: Path, manifest_path: Path) -> int:
    """Reverse: `***` -> `---` for every recorded offset."""
    if not manifest_path.exists():
        print(f"restore: no manifest at {manifest_path} — nothing to do")
        return 0
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    total_files = 0
    total_cells = 0
    for rel, offsets in manifest.items():
        path = root / rel
        if not path.exists():
            print(f"  MISSING {rel}", file=sys.stderr)
            continue
        raw = path.read_bytes()
        new_raw = raw
        for offset in sorted(offsets, reverse=True):
            new_raw = new_raw[:offset] + NEEDLE + new_raw[offset + len(REPLACEMENT):]
        try:
            json.loads(new_raw)
        except Exception as e:
            print(f"  FAIL {rel}: re-parse failed: {e}", file=sys.stderr)
            continue
        path.write_bytes(new_raw)
        total_files += 1
        total_cells += len(offsets)
    manifest_path.unlink(missing_ok=True)
    print(f"restore: {total_files} files, {total_cells} cells")
    return 0


def check(targets: list[Path], root: Path, strict: bool) -> int:
    """Verify no standalone `---` separator remains in markdown cells."""
    violations = 0
    if targets:
        iterator = iter_ipynb_paths(targets)
    else:
        iterator = iter_ipynb(root)
    for path in iterator:
        raw = path.read_bytes()
        cells = find_separator_cells(raw)
        if cells:
            rel = path.relative_to(REPO_ROOT) if path.is_absolute() else path
            print(f"  {rel}: {len(cells)} separator cells")
            violations += len(cells)
    if violations == 0:
        print("check: clean (no `---` separators)")
        return 0
    print(f"check: {violations} separator cells remaining")
    return 1 if strict else 0


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("action", choices=["apply", "restore", "check"])
    p.add_argument("--root", type=Path, default=DEFAULT_ROOT)
    p.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    p.add_argument("--strict", action="store_true",
                   help="(check only) exit 1 if any separator found")
    p.add_argument("--target", type=Path, action="append", default=[],
                   help="restrict to specific path(s) (file or dir); repeatable")
    args = p.parse_args()

    if args.action == "apply":
        return apply(args.target, args.root, args.manifest)
    if args.action == "restore":
        return restore(args.root, args.manifest)
    if args.action == "check":
        return check(args.target, args.root, args.strict)
    return 0


if __name__ == "__main__":
    raise(SystemExit(main()))