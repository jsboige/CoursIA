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

Two shapes are reported: a lone **opening** tag (`<div ...>`) and a lone
**closing** tag (`</div>`). CommonMark HTML block type 6 opens on both, and
the closing half was missing from the first version of this script -- caught
by review on #13218 and confirmed at the engine. One real occurrence survived
on main after the opening-tag burn-down of #13242 (`slides/01-introduction`,
`</div>` swallowing three bullets) -- burned down by #13345.

What stays out of scope, deliberately: a tag with trailing content on its
line (`<div>du texte`, `</div> et du texte`). markdown-it swallows those too,
but the rule enforced here is a tag ALONE on its line -- narrow enough to
explain in one sentence to an author. The tests name both forms so the gap
is on the record rather than implicit.

Usage
-----
    python scripts/notebook_tools/scan_slides_html_block_markdown.py
    python scripts/notebook_tools/scan_slides_html_block_markdown.py --check slides/S3-acculturation/slides.md
    python scripts/notebook_tools/scan_slides_html_block_markdown.py --json

Exit status is 1 when any violation is found, 0 otherwise. There is NO baseline
mechanism: the corpus sits at ZERO since #13345 burned down the last known
occurrence (the closing-tag form in `slides/01-introduction`), and the corpus
test in `tests/test_scan_slides_html_block_markdown.py` holds that line.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

# An HTML tag alone on its line is what starts a block. Restricting to a lone
# tag (rather than any line containing '<') keeps the rule narrow and
# explainable: it is exactly the shape that swallows the NEXT line.
#
# The `/?` is load-bearing and was added after the detector shipped: CommonMark
# HTML block type 6 opens on a CLOSING tag too, so a lone `</div>` swallows the
# markdown that follows it exactly as `<div>` does. Verified at the engine
# Slidev uses (markdown-it), against main:
#
#     md.render("</div>\n- Behaviourism\n")  ->  unchanged, the bullet
#     comes back as literal text (no <li> in the output).
#
# Missing this form left the ratchet blind to a class it exists to catch
# (found by review on #13218). One real occurrence on main: 01-introduction
# L597, where three bullets are swallowed on a course slide.
_OPENING_TAG = re.compile(r"^\s*</?(?P<tag>[a-zA-Z][a-zA-Z0-9-]*)\b[^>]*>\s*$")

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

# ...but a line that is NOTHING BUT a closing tag is not self-contained: it
# opens a block (see _OPENING_TAG above). Without this exception the `/?`
# widening would be inert, since _SELF_CONTAINED matches any line ending in
# `</tag>` -- `</div>` alone included. The two edits only work as a pair.
#
# Negative control that bounds the exception: `<span>x</span>` stays excluded,
# because _OPENING_TAG never matches it (trailing text after the first `>`
# breaks the end anchor). Asserted in the tests.
_BARE_CLOSING_TAG = re.compile(r"^\s*</[a-zA-Z][a-zA-Z0-9-]*>\s*$")

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
        if not match:
            continue
        if _SELF_CONTAINED.search(line) and not _BARE_CLOSING_TAG.match(line):
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
            print("fix: insert a blank line after the lone HTML tag preceding each line above")

    return 1 if total else 0


if __name__ == "__main__":
    raise SystemExit(main())
