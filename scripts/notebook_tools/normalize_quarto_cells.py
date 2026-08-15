#!/usr/bin/env python3
"""Text-level `---` -> `***` for the first line of markdown cells.

Quarto 1.7.32's ipynb reader parses a leading ``---`` in a markdown cell as a
YAML front-matter delimiter (``readYamlFromMarkdown``), which crashes the whole
render or swallows the cell. This script replaces the first line ``---`` of
every markdown cell with ``***`` (a thematic break, NOT a YAML delimiter) so the
cell stays visually identical in Jupyter and becomes renderable by Quarto.

Unlike a JSON round-trip (nbformat / json.dumps), this applies a pure text-level
transformation: every byte of the file is preserved except the ``---`` on the
affected source lines. No reformat, no unicode re-escaping, no blank-line
changes — ``git diff`` shows only the intended lines.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path


def transform_text(raw: str) -> tuple[str, int]:
    """Return (new_text, cells_fixed) applying --- -> *** on the first line of
    every markdown cell's source array, byte-faithful elsewhere."""
    # Validate the file is parseable JSON before transforming.
    json.loads(raw)
    lines = raw.splitlines(keepends=True)
    cell_type = None
    in_markdown_source = False
    fixed = 0
    out = []
    i = 0
    while i < len(lines):
        line = lines[i]
        stripped = line.strip()
        # Track the current cell type (cell_type appears before source in a cell).
        if stripped.startswith('"cell_type"'):
            val = stripped.split(":", 1)[1].strip().strip('",')
            cell_type = val
        # A "source": [ opener — next line is the first source element.
        if stripped == '"source": [' and cell_type == "markdown":
            in_markdown_source = True
            out.append(line)
            i += 1
            if i < len(lines):
                elem = lines[i]
                elem_stripped = elem.strip()
                # First element line: a JSON string that may be "---\n", / "---\n"
                # / "---\n\n## ..." (single-element cells). Replace the leading ---.
                if elem_stripped.startswith('"---') and not elem_stripped.startswith('"----'):
                    # Replace the 3 dashes AFTER the opening quote; keep the
                    # quote and everything after the dashes verbatim.
                    quote_idx = elem.find('"---')
                    head = elem[: quote_idx + 1]
                    tail = elem[quote_idx + 4 :]
                    out.append(head + "***" + tail)
                    fixed += 1
                else:
                    out.append(elem)
                i += 1
            continue
        # Reset the source-array state when the array closes.
        if in_markdown_source and stripped in ("],", "]"):
            in_markdown_source = False
        out.append(line)
        i += 1
    return "".join(out), fixed


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("paths", nargs="+", metavar="PATH", type=Path)
    ap.add_argument("--dry-run", action="store_true",
                    help="report what would change without writing")
    args = ap.parse_args()

    total_changed = 0
    total_fixed = 0
    for path in args.paths:
        with open(path, "r", encoding="utf-8", newline="") as fh:
            raw = fh.read()
        new, fixed = transform_text(raw)
        if fixed:
            total_changed += 1
            total_fixed += fixed
            if args.dry_run:
                print(f"WOULD FIX {path}: {fixed} markdown cell(s)")
            else:
                path.write_text(new, encoding="utf-8", newline="")
                print(f"fixed   {path}: {fixed} markdown cell(s)")
        else:
            print(f"ok      {path}: unchanged")
    print(f"---\n{total_changed} notebook(s) affected, {total_fixed} cell(s)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
