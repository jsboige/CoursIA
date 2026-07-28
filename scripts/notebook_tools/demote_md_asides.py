#!/usr/bin/env python3
"""Demote HINT-AS-HEADING findings to blockquote callouts (multi-family).

Consolidates the byte-surgical pattern from c.922 Tweety (PR #8647), c.925
Sudoku (PR #8654), and c.914 GenAI/Texte (PR #8630) into a single
multi-family tool. Replaces the per-family one-shots
``scripts/fix_<family>_hierarchy.py``.

The pattern: demote headings that read like an aside or hint (e.g.
``### Indices``, ``### Étapes``, ``### Pistes d'amélioration``) to
``> **<text> :**`` blockquote callouts. The rendered notebook therefore
shows the demoted line as small body text rather than an oversized
heading, and the markdown TOC of the notebook stops being polluted by
per-exercise hint/intro/summary headings.

Constraints (L965 ★): LF-only CR=0, write via
``json.dumps().encode('utf-8')`` binary write (NOT ``nbformat.write``
which introduces CRLF). L948 ★★: NO cell output scrubbing. C.1/C.2/C.3:
no NotImplementedError, no empty cell edits, scoped to notebooks we
modified.

Idempotent: skips cells whose source already starts with ``> **`` (avoid
double-prefixing if re-run).

Targets demoted (consolidated from Sudoku + Tweety precedents):

  1. ``Indices`` (exact, bare aside)
  2. ``Étapes`` (exact, bare aside)
  3. ``Étapes a suivre`` (legacy no-accent variant)
  4. ``Étapes de la modélisation avec <engine>`` (long prefix)
  5. ``Pistes d'amélioration`` / ``Pistes d'amelioration`` (legacy)
  6. ``Notes techniques`` (with optional parenthetical, e.g.
     ``Notes techniques (Tweety 1.30)``)

The scanner in ``scripts/notebook_tools/scan_md_hierarchy.py`` detects
these headings via its HINT_RE; this tool acts only on the subset
already triaged by the two precedent PRs (#8647, #8654). New families
should ship their own rollout PR with new findings, then adopt this
tool via ``--dir <famille>``.

Usage::

    # Demote in a family directory
    python scripts/notebook_tools/demote_md_asides.py --dir MyIA.AI.Notebooks/Sudoku

    # Dry-run only
    python scripts/notebook_tools/demote_md_asides.py --dir MyIA.AI.Notebooks/Sudoku --dry-run

    # Single notebook
    python scripts/notebook_tools/demote_md_asides.py \\
        --dir MyIA.AI.Notebooks/Sudoku \\
        --target 1-Sudoku-Backtracking-Csharp.ipynb
"""

import argparse
import json
import pathlib
import re
import sys


# ---------------------------------------------------------------------------
# HINT-AS-HEADING detection (consolidated from Sudoku + Tweety precedents)
# ---------------------------------------------------------------------------


def _matches_target(text):
    """Return True if ``text`` is one of the bare asides we want to demote.

    Heading-stem normalization (L925-A/B/C):
      - Strip optional trailing parenthetical "(...)".
      - Normalize curly apostrophe U+2019 to straight U+0027 (L925-C ★).
      - Match exact or space-prefixed variants for "Étapes".
      - Match apostrophe-bound variants for "Pistes d'...".
    """
    stem = re.sub(r'\s*\(.*\)\s*$', '', text).strip()
    stem_norm = stem.replace('’', "'")

    # 1. Bare aside: exact "Indices"
    if stem == 'Indices':
        return True

    # 2-4. "Étapes" family: exact, or space-prefixed (Étapes a suivre,
    # Étapes de la modélisation avec X).
    if stem == 'Étapes':
        return True
    if stem.startswith('Étapes '):
        return True

    # 5. "Pistes d'amélioration" / "Pistes d'amelioration" — apostrophe-bound,
    # not space-bound (no space between "d" and apostrophe).
    if stem_norm.startswith("Pistes d'"):
        return True

    # 6. "Notes techniques" with optional parenthetical already stripped.
    if stem == 'Notes techniques':
        return True

    return False


# ---------------------------------------------------------------------------
# nbformat source format preservation (L925-A ★★, L982/L983 ★★)
# ---------------------------------------------------------------------------


def _detect_source_format(src):
    """Detect nbformat ``source`` field format to preserve byte structure.

    Three observed formats across the corpus (L983 ★★ mixed-format source):
      - ``string``       : single joined string element (one cell with full prose)
      - ``line-list``    : list of lines, each ending in ``\\n`` (except possibly last)
      - ``char-split``   : list of single characters (no ``\\n`` in any element)
    """
    if isinstance(src, str):
        return 'string'
    if not src:
        return 'line-list'  # treat empty as line-list for safety
    has_newline = any('\n' in (e or '') for e in src)
    if has_newline:
        return 'line-list'
    return 'char-split'


def _re_emit_in_format(original_format, new_lines):
    """Re-emit a list-of-lines in the original nbformat source format.

    Used to preserve byte-level structure on re-serialization.
    """
    if original_format == 'string':
        return ''.join(new_lines)
    if original_format == 'line-list':
        return new_lines
    if original_format == 'char-split':
        # Re-split into one-character list elements, preserving the
        # blockquote text but expanding it back to chars.
        joined_new = ''.join(new_lines)
        return list(joined_new)
    return new_lines


# ---------------------------------------------------------------------------
# Heading demotion (multi-heading per cell honored)
# ---------------------------------------------------------------------------


def _demote_all_headings(source_lines):
    """Replace EVERY matching heading line with ``> **<text> :**`` blockquote.

    A cell may contain multiple target headings (Sudoku-6-AIMA-CSP-Python
    cells have BOTH ``### Étapes`` AND ``### Indices`` in the same cell).
    We demote all occurrences and preserve the body untouched.

    nbformat quirk (L983 ★★): source can be character-split (each char
    its own line). We detect headings in the JOINED source, then locate
    their line ranges in the original split source.

    Returns ``(new_source_list, changed_count)``.
    """
    if not source_lines:
        return source_lines, 0

    joined = ''.join(source_lines)

    # Find all heading occurrences in the joined source.
    headings = []  # list of (start_idx, end_idx, heading_text)
    for m in re.finditer(r'^(#{1,6})\s+([^\n]+?)\s*$', joined, re.MULTILINE):
        prefix = m.group(1)
        text = m.group(2).strip()
        if _matches_target(text):
            headings.append((m.start(), m.end(), text))

    if not headings:
        return source_lines, 0

    # Map joined positions back to source_lines indices.
    line_offsets = []
    off = 0
    for line in source_lines:
        line_offsets.append((off, off + len(line)))
        off += len(line)

    # For each heading, find which line(s) it spans and replace them with
    # the blockquote. If a heading spans multiple lines (character-split
    # source), collapse them into a single blockquote line.
    new_lines = list(source_lines)
    # Process from end to start to keep indices valid.
    for start, end, text in reversed(headings):
        first_line = None
        last_line = None
        for i, (lo, hi) in enumerate(line_offsets):
            if hi > start and first_line is None:
                first_line = i
            if lo < end:
                last_line = i
        if first_line is None or last_line is None:
            continue
        # Preserve newline on the demoted line. Blockquote format:
        # `> **<text> :**\n`.
        replacement = [f'> **{text} :**\n']
        new_lines[first_line:last_line + 1] = replacement

    changed_count = len(headings)
    return new_lines, changed_count


# ---------------------------------------------------------------------------
# Notebook-level fix
# ---------------------------------------------------------------------------


def fix_notebook(path, dry_run=False):
    """Apply demotion to a single notebook. Returns ``(changed_count, error)``.

    ``error`` is ``None`` on success.
    """
    try:
        raw = path.read_bytes()
        nb = json.loads(raw.decode('utf-8'))
    except Exception as e:
        return 0, f'parse: {e}'

    cells = nb.get('cells', [])
    total_changed = 0
    for cell in cells:
        if cell.get('cell_type') != 'markdown':
            continue
        src = cell.get('source', [])
        if not src:
            continue
        # Skip already-demoted cells (idempotency guard).
        joined = ''.join(src).lstrip()
        if joined.startswith('> **'):
            continue

        # Determine the cell's original source format to preserve
        # byte-level structure on re-serialization (L982/L983 ★★).
        original_format = _detect_source_format(src)
        # _demote_all_headings expects a list; split the joined string
        # form into lines (keeping newlines) instead of wrapping it as a
        # single line. Without this, a 'string' source cell collapses to
        # one element and ALL non-heading body is lost when the heading
        # is replaced (incident c.925 #8654: 941 -> 16 chars on
        # Sudoku-1 cell 9).
        src_for_work = src if isinstance(src, list) else src.splitlines(keepends=True)
        new_src, changed = _demote_all_headings(src_for_work)
        if not changed:
            continue
        cell['source'] = _re_emit_in_format(original_format, new_src)
        total_changed += changed

    if total_changed and not dry_run:
        # L965 ★: write binary to preserve LF-only line endings.
        # Preserve a trailing newline if the original file had one
        # (common convention; some nbformat writers strip it on
        # re-serialize). Use indent=1 to match the existing repo
        # convention.
        trailing_nl = raw.endswith(b'\n')
        out = json.dumps(nb, ensure_ascii=False, indent=1).encode('utf-8')
        if trailing_nl and not out.endswith(b'\n'):
            out += b'\n'
        path.write_bytes(out)
    return total_changed, None


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def _resolve_dir(dir_arg):
    """Resolve the family directory argument into an absolute path.

    Accepts either an absolute path or a path relative to the worktree
    root (the directory two levels up from this script).
    """
    p = pathlib.Path(dir_arg)
    if p.is_absolute():
        return p
    # Worktree root = two levels up from scripts/notebook_tools/.
    root = pathlib.Path(__file__).resolve().parent.parent.parent
    return (root / dir_arg).resolve()


def main():
    ap = argparse.ArgumentParser(
        description='Demote HINT-AS-HEADING findings to blockquote callouts. '
                    'Replaces per-family one-shots (fix_sudoku_hierarchy.py, '
                    'fix_tweety_hierarchy.py).')
    ap.add_argument(
        '--dir', required=True,
        help='Path to the family directory (relative to repo root or absolute). '
             'Example: MyIA.AI.Notebooks/Sudoku')
    ap.add_argument(
        '--target',
        help='Fix only this notebook (relative to family dir).')
    ap.add_argument(
        '--dry-run', action='store_true',
        help='Detect changes but do not write to disk.')
    args = ap.parse_args()

    family_dir = _resolve_dir(args.dir)
    if not family_dir.is_dir():
        print(f'ERROR: not a directory: {family_dir}', file=sys.stderr)
        return 2

    if args.target:
        targets = [family_dir / args.target]
    else:
        targets = sorted(p for p in family_dir.rglob('*.ipynb')
                         if '_output' not in p.name)

    total_changed = 0
    for p in targets:
        if not p.exists():
            print(f'MISSING: {p}', file=sys.stderr)
            continue
        n, err = fix_notebook(p, dry_run=args.dry_run)
        if err:
            print(f'ERROR {p.name}: {err}', file=sys.stderr)
        elif n:
            print(f'{p.name}: {n} heading(s) demoted'
                  f'{" (dry-run)" if args.dry_run else ""}')
            total_changed += n
    print(f'\nTotal demoted: {total_changed}')
    return 0


if __name__ == '__main__':
    sys.exit(main())
