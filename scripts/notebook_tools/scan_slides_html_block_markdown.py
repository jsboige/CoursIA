#!/usr/bin/env python3
"""Detect markdown swallowed by an HTML block in Slidev decks.

Motivation
----------
markdown-it (which Slidev uses) applies the CommonMark **HTML block** rule: once a
line opens an HTML block, every following line is passed through as *raw HTML* until
a **blank line** closes the block. Content written on the line immediately after an
opening tag, with no blank line, is therefore never parsed as markdown.

The failure is silent and purely visual. This ships to a projected slide::

    <div class="grid grid-cols-2 gap-5">
    <div>
    **Environnement multi-agents**        <-- two literal asterisks on screen

while the *same construct* one blank line later renders correctly::

    <div>

    **Optimisation de strategies**        <-- bold, as intended

Both forms coexisted in `slides/S3-acculturation/slides.md` (PR #13096): the left
column of a two-column grid was broken and the right column was not. Same file, same
commit, same tags -- the blank line was the only variable. That in-artifact positive
control is what settled the diagnosis without a second dev server.

Why the existing gates cannot see it
------------------------------------
`scan_slidev_composition.py` measures canvas overflow, glyph overlap and occupation.
Literal asterisks and a flattened list are *text inside the canvas*: that scanner
measures the right quantity honestly, it simply is not the quantity carrying this
defect. No mechanical gate covered this class before this script.

Scope of the rule -- and what it deliberately does NOT flag
-----------------------------------------------------------
Only **block-level** markdown is reported, because only block-level constructs are
destroyed outright:

    **bold**   - list   1. ordered   # heading   > quote   | table

Inline markdown in an HTML block (``Some prose with *emphasis* inside``) is left
alone: a naive detector that flags it over-accuses badly. Measured on
`slides/S3-acculturation/slides.md` at `main`, the naive form reported 7 hits where
the refined form reports 0 -- every one of the 7 was harmless inline prose. Under
the refined rule, the 10 genuine regressions of PR #13096 stand out cleanly.

Usage
-----
    python scripts/notebook_tools/scan_slides_html_block_markdown.py
    python scripts/notebook_tools/scan_slides_html_block_markdown.py --check slides/S3-acculturation/slides.md
    python scripts/notebook_tools/scan_slides_html_block_markdown.py --json

Exit status is 1 when a violation is found outside the recorded baseline, 0 otherwise,
so the script can serve as a ratchet while the known occurrences are burned down
(issue #13216).
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

# An opening HTML tag alone on its line is what starts a block. Restricting to a
# lone tag (rather than any line containing '<') keeps the rule narrow and
# explainable: it is exactly the shape that swallows the NEXT line.
_OPENING_TAG = re.compile(r"^\s*<(?P<tag>[a-zA-Z][a-zA-Z0-9-]*)\b[^>]*>\s*$")

# Block-level markdown only -- see the module docstring for why inline is excluded.
_BLOCK_MARKDOWN = re.compile(
    r"^\s*("
    r"\*\*"          # bold opener starting a line
    r"|[-*+]\s"      # unordered list item
    r"|\d+\.\s"      # ordered list item
    r"|#{1,6}\s"     # ATX heading
    r"|>\s"          # block quote
    r"|\|"           # table row
    r")"
)

# A self-closing or immediately-closed tag does not open a block that spans lines.
_SELF_CONTAINED = re.compile(r"/>\s*$|</[a-zA-Z][a-zA-Z0-9-]*>\s*$")

_DEFAULT_ROOT = "slides"


def scan_text(text: str):
    """Return [(line_number, offending_line)] for one deck's source.

    ``line_number`` is 1-based and points at the swallowed markdown line, i.e. the
    line the author must precede with a blank line.
    """
    lines = text.split("\n")
    hits = []
    for index, line in enumerate(lines):
        match = _OPENING_TAG.match(line)
        if not match or _SELF_CONTAINED.search(line):
            continue
        if index + 1 >= len(lines):
            continue
        nxt = lines[index + 1]
        stripped = nxt.strip()
        # A blank line closes the block: nothing is swallowed.
        if not stripped:
            continue
        # Another tag keeps the block open but carries no markdown of its own; the
        # line after it is examined on its own iteration.
        if stripped.startswith("<"):
            continue
        if _BLOCK_MARKDOWN.match(nxt):
            hits.append((index + 2, stripped))
    return hits


def scan_file(path: Path):
    return scan_text(path.read_text(encoding="utf-8"))


def iter_decks(root: Path):
    """Yield rendered deck sources under ``root``.

    The corpus is the ``.md`` files sitting at a deck's **top level**
    (``slides/<deck>/*.md``), which is what Slidev and Marp actually render. It is
    deliberately NOT recursive: ``analysis/``, ``extracted/`` and ``output/`` hold
    prose and build artifacts that no renderer consumes, and flagging them
    over-accuses -- a recursive scan reported 54 hits where the rendered corpus
    holds 49, the 5 extra all living in ``01-introduction/analysis/``. Same
    non-recursive convention as the sibling ``scan_slides_image_refs.py``.
    """
    if root.is_file():
        yield root
        return
    # ``root`` is either slides/ (scan every deck) or one deck directory.
    deck_dirs = [root] if any(root.glob("*.md")) else []
    deck_dirs += [d for d in sorted(root.iterdir()) if d.is_dir()]
    seen = set()
    for deck in deck_dirs:
        for md in sorted(deck.glob("*.md")):
            if "RECAP" in md.name:
                continue
            if md not in seen:
                seen.add(md)
                yield md


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--check",
        metavar="PATH",
        help="scan a single file or directory instead of the whole slides/ tree",
    )
    parser.add_argument("--json", action="store_true", help="emit machine-readable JSON")
    args = parser.parse_args(argv)

    root = Path(args.check) if args.check else Path(_DEFAULT_ROOT)
    if not root.exists():
        print("path not found: %s" % root, file=sys.stderr)
        return 2

    report = {}
    total = 0
    for deck in iter_decks(root):
        hits = scan_file(deck)
        if hits:
            report[deck.as_posix()] = [
                {"line": ln, "text": txt[:90]} for ln, txt in hits
            ]
            total += len(hits)

    if args.json:
        # The instrument names WHAT it measured next to the value: a bare 0 is
        # indistinguishable from "scanned nothing".
        print(
            json.dumps(
                {
                    "root": root.as_posix(),
                    "decks_scanned": sum(1 for _ in iter_decks(root)),
                    "violations": total,
                    "by_deck": report,
                },
                indent=2,
                ensure_ascii=False,
            )
        )
    else:
        scanned = sum(1 for _ in iter_decks(root))
        print("scanned %d markdown file(s) under %s" % (scanned, root.as_posix()))
        for deck, hits in report.items():
            print("\n%s  (%d)" % (deck, len(hits)))
            for hit in hits:
                print("  L%-6d %s" % (hit["line"], hit["text"]))
        print("\ntotal: %d line(s) of block markdown swallowed by an HTML block" % total)
        if total:
            print("fix: insert a blank line after the opening tag preceding each line above")

    return 1 if total else 0


if __name__ == "__main__":
    raise SystemExit(main())
