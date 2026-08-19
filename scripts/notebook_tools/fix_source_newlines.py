#!/usr/bin/env python3
"""
Auto-fix markdown cells with collapsed ``source`` lists.

Detected by ``detect_markdown_rendering.py`` rule
``source_list_missing_newlines`` (HIGH), two patterns:

1. **Single-element list, no '\\n'** (heading + body collapsed into one string).
   Renders as a giant heading on Jupyter; the heading spans the whole cell.
   The fix splits the cell into ``[heading + '\\n', body]`` so the heading
   terminates and the body renders normally.

2. **Multi-element list, some elements lack trailing '\\n'**. Jupyter joins
   source lists with no separator, so an element without a trailing newline
   fuses into the next line. The fix ensures every non-last element ends
   with ``'\\n'``.

The split for case 1 is heuristic: it looks for the first body marker
(``' : '``, ``' **'``, ``' - '``, ``' 1. '``, ``' > '``) that follows the
heading marker (``#``/``##``/...). It is intentionally conservative: cells
where the heading has no clear boundary with the body are reported (in
``--scan`` mode) but **not** modified — the auto-fix on those is left to
manual follow-up.

**Round-trip invariant**: the fix only INSERTS ``'\\n'`` characters; no
character is removed. The whitespace-stripped cell content is byte-identical
before and after. This is asserted by ``tests/test_fix_source_newlines.py``,
test 2.

Usage:
    python fix_source_newlines.py --scan <path>      # dry-run, list defects
    python fix_source_newlines.py --scan-all          # dry-run repo-wide (.ipynb)
    python fix_source_newlines.py --scan-all --check  # exit 1 if defects
    python fix_source_newlines.py --apply <path>      # fix in place
    python fix_source_newlines.py --apply-all         # fix repo-wide
"""

import argparse
import json
import os
import re
import sys
from pathlib import Path

# --- detector parity: what triggers a defect ---
_COLLAPSED_HEADING_START_RE = re.compile(r"^\s{0,3}#{1,6}\s+\S")
_COLLAPSED_SINGLE_MIN_LEN = 80


# --- body markers used to split a single-element collapsed heading cell ---
# We split at the EARLIEST occurrence of any of these markers AFTER the
# heading marker '#'+spaces. The marker is INCLUDED in the body part.
_BODY_MARKERS = [
    re.compile(r"\s:\s+(?=[A-ZÀ-Ÿ*])"),
    re.compile(r"\s\*\*[A-ZÀ-Ÿ*]"),
    re.compile(r"\s-\s+(?=[A-ZÀ-Ÿ*])"),
    re.compile(r"\s\d+\.\s+(?=[A-ZÀ-Ÿ*])"),
    re.compile(r"\s> "),
]


def _find_single_split(s):
    """If ``s`` is a single-element collapsed cell, return the split point
    (heading, body). Otherwise None. The split is heuristic: the first body
    marker (': ', '**', '- ', '1. ', '> ') after the heading marker."""
    if "\n" in s or len(s.strip()) < _COLLAPSED_SINGLE_MIN_LEN:
        return None
    if not _COLLAPSED_HEADING_START_RE.match(s):
        return None
    m = re.match(r"^\s{0,3}#{1,6}\s+", s)
    if not m:
        return None
    prefix_len = m.end()
    best_pos = None
    for pat in _BODY_MARKERS:
        m2 = pat.search(s, prefix_len)
        if m2 and (best_pos is None or m2.start() < best_pos):
            best_pos = m2.start()
    if best_pos is None:
        return None
    heading = s[:best_pos]
    body = s[best_pos:]
    if not heading.rstrip() or not heading.rstrip()[-1].isalnum():
        return None
    if not body.strip():
        return None
    return heading + "\n", body


def find_source_newline_defects(nb):
    """Inspect a parsed notebook (dict) and return a list of defects.

    Each defect is a dict:
        ``cell_index`` (int): index in ``cells``
        ``kind`` (str): ``'single_collapsed'`` or ``'multi_missing_newlines'``
        ``before`` (list): the original ``source`` list
        ``after`` (list): the fixed ``source`` list (only populated for
            fixable defects; ``None`` for unrecoverable cases)
    """
    defects = []
    for i, cell in enumerate(nb.get("cells", [])):
        if cell.get("cell_type") != "markdown":
            continue
        src = cell.get("source")
        if not isinstance(src, list):
            continue
        if len(src) == 0:
            continue
        # Case 1: single-element list, no \n, heading + body collapsed
        if len(src) == 1:
            s = src[0]
            if "\n" in s or len(s.strip()) < _COLLAPSED_SINGLE_MIN_LEN:
                continue
            if not _COLLAPSED_HEADING_START_RE.match(s):
                continue
            split = _find_single_split(s)
            if split is None:
                # Unrecoverable: heading + body without clear separator
                defects.append({
                    "cell_index": i,
                    "kind": "single_collapsed",
                    "before": list(src),
                    "after": None,
                })
                continue
            heading, body = split
            defects.append({
                "cell_index": i,
                "kind": "single_collapsed",
                "before": list(src),
                "after": [heading, body],
            })
        else:
            # Case 2: multi-element list, some elements lack trailing '\n'
            nb_breaks = sum(1 for s in src if s.endswith("\n"))
            nonblank = [s for s in src if s.strip()]
            if nb_breaks < len(src) - 1 and len("".join(src).strip()) >= 40:
                # Build after: ensure all non-last elements end with '\n'
                after = []
                for s in src[:-1]:
                    if s.endswith("\n"):
                        after.append(s)
                    else:
                        after.append(s + "\n")
                after.append(src[-1])
                defects.append({
                    "cell_index": i,
                    "kind": "multi_missing_newlines",
                    "before": list(src),
                    "after": after,
                })
    return defects


def _apply_defects_to_nb(nb, defects):
    """Apply a list of defects (those with ``after``) to the notebook
    in-memory. Returns count of defects applied."""
    applied = 0
    for d in defects:
        if d.get("after") is None:
            continue
        nb["cells"][d["cell_index"]]["source"] = d["after"]
        applied += 1
    return applied


def _round_trip_invariant(before, after):
    """Whitespace-sensitive invariant: the count of non-whitespace characters
    must be identical before and after. The fix only INSERTS ``'\\n'`` and
    trailing newlines, so the set of non-whitespace characters is preserved
    (only their ordering may shift, which is intentional)."""
    def _nonws(s):
        return s.replace(" ", "").replace("\t", "").replace("\n", "").replace("\r", "")
    return _nonws("".join(before)) == _nonws("".join(after))


def _iter_notebooks(root):
    """Yield .ipynb paths under ``root`` (recursively)."""
    root = Path(root)
    if root.is_file() and root.suffix == ".ipynb":
        yield root
        return
    for p in root.rglob("*.ipynb"):
        if any(part.startswith(".") for part in p.parts):
            continue
        yield p


def _display_defect(d, nb_path):
    """Build a one-line human-readable description of a defect."""
    cell = d["cell_index"]
    kind = d["kind"]
    if kind == "single_collapsed":
        before_len = len(d["before"][0])
        if d["after"] is None:
            return f"{nb_path}:cell[{cell}] single-element list, no '\\n' (NO_AUTO_FIX: no body marker found)"
        return f"{nb_path}:cell[{cell}] single-element list, {before_len} chars -> split ({len(d['after'][0])} + {len(d['after'][1])})"
    if kind == "multi_missing_newlines":
        return f"{nb_path}:cell[{cell}] multi-element list, {len(d['before'])} elements, {sum(1 for s in d['before'] if s.endswith(chr(10)))} end with '\\n' (expected {len(d['before']) - 1})"
    return f"{nb_path}:cell[{cell}] {kind}"


def cmd_scan(args):
    """Scan mode: list defects, do not modify."""
    targets = args.paths if args.paths else (["."] if args.scan_all else [])
    code = 0
    fixed_count = 0
    skipped_count = 0
    for target in targets:
        for nb_path in _iter_notebooks(target):
            try:
                nb = json.loads(nb_path.read_text(encoding="utf-8"))
            except (json.JSONDecodeError, OSError) as e:
                print(f"SKIP {nb_path}: cannot read ({e})", file=sys.stderr)
                continue
            defects = find_source_newline_defects(nb)
            for d in defects:
                if d["after"] is None:
                    skipped_count += 1
                else:
                    fixed_count += 1
                print(_display_defect(d, nb_path))
    if args.check and (fixed_count > 0 or skipped_count > 0):
        code = 1
    return code, fixed_count, skipped_count


def cmd_apply(args):
    """Apply mode: write fixes to disk."""
    targets = args.paths if args.paths else (["."] if args.apply_all else [])
    fixed_total = 0
    skipped_total = 0
    cell_changes = 0
    for target in targets:
        for nb_path in _iter_notebooks(target):
            try:
                nb = json.loads(nb_path.read_text(encoding="utf-8"))
            except (json.JSONDecodeError, OSError) as e:
                print(f"SKIP {nb_path}: cannot read ({e})", file=sys.stderr)
                continue
            defects = find_source_newline_defects(nb)
            if not defects:
                continue
            fixable = [d for d in defects if d["after"] is not None]
            skipped = [d for d in defects if d["after"] is None]
            if not fixable:
                for d in skipped:
                    print(f"SKIP no-fix {nb_path}:cell[{d['cell_index']}]")
                skipped_total += len(skipped)
                continue
            # Round-trip invariant check before write
            for d in fixable:
                assert _round_trip_invariant(d["before"], d["after"]), (
                    f"Round-trip invariant violated on {nb_path}:cell[{d['cell_index']}]"
                )
            applied = _apply_defects_to_nb(nb, fixable)
            cell_changes += applied
            # Re-serialize: text-level would be ideal for byte preservation,
            # but detect_markdown_rendering.py itself uses json.dump, so we
            # follow the same convention. We preserve the original file's
            # newline mode (LF vs CRLF) by reading bytes if needed.
            original_bytes = nb_path.read_bytes()
            newline_mode = "\r\n" if b"\r\n" in original_bytes[:4096] else "\n"
            new_text = json.dumps(nb, ensure_ascii=False, indent=1)
            if newline_mode == "\r\n":
                new_text = new_text.replace("\n", "\r\n")
            # Match the trailing-newline convention of the original file.
            original_ended_with_newline = original_bytes.endswith(b"\n")
            if original_ended_with_newline and not new_text.endswith("\n"):
                new_text += "\n"
            nb_path.write_text(new_text, encoding="utf-8", newline=newline_mode)
            fixed_total += len(fixable)
            skipped_total += len(skipped)
            print(f"FIXED {nb_path}: {len(fixable)} cell(s) {'(skipped ' + str(len(skipped)) + ' no-fix)' if skipped else ''}")
    print(f"\nTotal: {fixed_total} cell(s) fixed, {skipped_total} cell(s) skipped (no body marker), {cell_changes} cell(s) modified")
    return 0, fixed_total, skipped_total


def main():
    p = argparse.ArgumentParser(
        description="Auto-fix markdown cells with collapsed source lists (detect_markdown_rendering.py rule source_list_missing_newlines)."
    )
    g = p.add_mutually_exclusive_group(required=True)
    g.add_argument("--scan", metavar="PATH", help="scan a file or directory for defects (dry-run)")
    g.add_argument("--scan-all", action="store_true", help="scan the whole repo (recursively) for defects")
    g.add_argument("--apply", metavar="PATH", help="fix a file or directory in place")
    g.add_argument("--apply-all", action="store_true", help="fix all .ipynb in the repo in place")
    p.add_argument("--check", action="store_true", help="(scan mode) exit 1 if any defect is found")
    p.add_argument("paths", nargs="*", help="positional paths (alternative to --scan/--apply)")
    args = p.parse_args()

    # Normalize: if --scan/--apply is given, prepend it to args.paths (don't
    # clobber the positional list — argparse splits the first arg into
    # --scan/--apply and the rest into args.paths).
    if args.scan is not None:
        args.paths = [args.scan] + list(args.paths or [])
    elif args.apply is not None:
        args.paths = [args.apply] + list(args.paths or [])

    if args.scan or args.scan_all:
        code, _, _ = cmd_scan(args)
        return code
    if args.apply or args.apply_all:
        return cmd_apply(args)[0]
    return 1


if __name__ == "__main__":
    sys.exit(main())
