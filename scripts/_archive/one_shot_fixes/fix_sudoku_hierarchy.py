#!/usr/bin/env python3
"""Fix c.925 — Sudoku HINT-AS-HEADING findings (tranche 3 EPIC #3966).

Same byte-surgical pattern as c.922 GenAI/Tweety (#8647) and c.914 GenAI/Texte
(#8630): demote `### Indices`, `### Étapes`, `### Étapes a suivre`,
`#### Étapes de la modélisation avec ...`, `### Pistes d'amélioration` headings
to `> **... :**` blockquote callouts (rendered as small body text, not as
oversized headings).

Sudoku has 5 heading patterns (more diverse than Tweety's 3):
- `### Indices` (most common, ~20+)
- `### Étapes` and `### Étapes a suivre` (legacy no-accent variant)
- `#### Étapes de la modélisation avec <engine>` (long variants)
- `### Pistes d'amélioration` (and no-accent `d'amelioration` legacy variant)

Constraints (L965 ★): LF-only CR=0, write via `json.dumps().encode('utf-8')`
binary write (NOT `nbformat.write` which introduces CRLF). L948 ★★: NO cell
output scrubbing. C.1/C.2/C.3: no NotImplementedError, no empty cell edits,
scoped to notebooks we modified.

Idempotent: skips cells whose source already starts with `> **` (avoid
double-prefixing if re-run).

Usage:
    python fix_sudoku_hierarchy.py [--dry-run] [--target <notebook>]
"""
import argparse, json, pathlib, re, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent  # worktree root
FAMILY_DIR = ROOT / 'MyIA.AI.Notebooks' / 'Sudoku'

# Stem targets (parenthetical/suffix-stripped via _matches_target).
# Each entry = "canonical stem" matched after stripping trailing parenthetical
# OR (for longer patterns) used as prefix match. See _matches_target below.
TARGET_STEMS_PREFIX = [
    'Indices',           # exact "Indices" (most common)
    'Étapes',            # "Étapes" / "Étapes a suivre" / "Étapes de la modélisation ..."
    'Pistes d',          # "Pistes d'amélioration" / "Pistes d'amelioration" (legacy)
]


def _matches_target(text):
    """Return True if `text` is one of the bare asides we want to demote.

    Sudoku headings detected by the scanner (see `scan_md_hierarchy.py`):
    1. `Indices` (exact, bare aside)
    2. `Étapes` (exact, bare aside)
    3. `Étapes a suivre` (no accent, legacy variant)
    4. `Étapes de la modélisation avec <engine>` (long prefix variant)
    5. `Pistes d'amélioration` (curly apostrophe U+2019, Sudoku-1-Backtracking-Csharp)
    6. `Pistes d'amelioration` (straight apostrophe, no accent — legacy)
    """
    stem = re.sub(r'\s*\(.*\)\s*$', '', text).strip()
    # Normalize curly apostrophe (U+2019) to straight (U+0027).
    stem_norm = stem.replace('’', "'")

    # Bare aside: exact "Indices"
    if stem == 'Indices':
        return True

    # "Étapes" family: exact or space-prefixed (Étapes a suivre,
    # Étapes de la modélisation avec X).
    if stem == 'Étapes':
        return True
    if stem.startswith('Étapes '):
        # "Étapes a suivre" (legacy no accent) is the only one without accent.
        # "Étapes de la modélisation..." is the modern variant.
        # Both should be demoted.
        return True

    # "Pistes d'amélioration" / "Pistes d'amelioration" — apostrophe-bound,
    # not space-bound (no space between "d" and apostrophe).
    if stem_norm.startswith("Pistes d'"):
        return True

    return False


def _detect_source_format(src):
    """Detect nbformat `source` field format to preserve byte structure.

    Three observed formats across the corpus (L983 ★★ mixed-format source):
      - 'string' : single joined string element (one cell with full prose)
      - 'line-list' : list of lines, each ending in `\\n` (except possibly last)
      - 'char-split' : list of single characters (no `\\n` in any element)
    """
    if isinstance(src, str):
        return 'string'
    if not src:
        return 'line-list'  # treat empty as line-list for safety
    # If any element contains a newline, it's a line-list (or string-encoded-as-list).
    has_newline = any('\n' in (e or '') for e in src)
    if has_newline:
        return 'line-list'
    # No newline anywhere → character-split list.
    return 'char-split'


def _demote_all_headings(source_lines):
    """Replace EVERY matching heading line with `> **<text> :**` blockquote.

    A cell may contain multiple target headings (Sudoku-6-AIMA-CSP-Python
    cells have BOTH `### Étapes` AND `### Indices` in the same cell). We
    demote all occurrences and preserve the body untouched.

    nbformat quirk (L983 ★★): source can be character-split (each char its
    own line). We detect headings in the JOINED source, then locate their
    line ranges in the original split source.

    Returns (new_source_list, changed_count).
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
    # Build cumulative offsets of joined source per line boundary.
    line_offsets = []
    off = 0
    for line in source_lines:
        line_offsets.append((off, off + len(line)))
        off += len(line)
    total_len = off

    # For each heading, find which line(s) it spans, and replace them with
    # the blockquote. If a heading spans multiple lines (character-split
    # source), collapse them into a single blockquote line.
    # We'll build a new list of lines with replacements.
    new_lines = list(source_lines)
    # Process from end to start to keep indices valid.
    for start, end, text in reversed(headings):
        # Find first and last line index covering [start, end).
        first_line = None
        last_line = None
        for i, (lo, hi) in enumerate(line_offsets):
            if hi > start and first_line is None:
                first_line = i
            if lo < end:
                last_line = i
        if first_line is None or last_line is None:
            continue
        # Preserve any trailing newline on the last line (most cells end the
        # heading line with \n). Blockquote format: `> **<text> :**\n`.
        replacement = [f'> **{text} :**\n']
        new_lines[first_line:last_line + 1] = replacement

    # Count demoted headings.
    changed_count = len(headings)
    return new_lines, changed_count


def fix_notebook(path, dry_run=False):
    """Apply demotion to a single notebook. Returns (changed_count, error)."""
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

        # Determine the cell's original source format to preserve byte-level
        # structure on re-serialization (L982/L983 ★★ nbformat convention).
        # Three possible formats observed across the corpus:
        #  (a) single string (joined): one element, a complete string with \\n
        #  (b) list of lines: each element ends with \\n (except possibly the
        #      last), elements correspond to logical lines
        #  (c) character-split list: many single-char elements, no \\n
        # We must output the same format to keep diff surgical.
        original_format = _detect_source_format(src)
        # _demote_all_headings expects a list; split the joined string form
        # into lines (keeping newlines) instead of wrapping it as a single
        # line. Without this, a 'string' source cell collapses to one element
        # and ALL non-heading body is lost when the heading is replaced
        # (incident c.925 #8654: 941 -> 16 chars on Sudoku-1 cell 9).
        src_for_work = src if isinstance(src, list) else src.splitlines(keepends=True)
        new_src, changed = _demote_all_headings(src_for_work)
        if not changed:
            continue
        # Re-emit in the original format.
        if original_format == 'string':
            cell['source'] = ''.join(new_src)
        elif original_format == 'line-list':
            cell['source'] = new_src
        elif original_format == 'char-split':
            # Re-split into one-character list elements, preserving the
            # blockquote text but expanding it back to chars.
            joined_new = ''.join(new_src)
            cell['source'] = list(joined_new)
        else:
            cell['source'] = new_src
        total_changed += changed

    if total_changed and not dry_run:
        # L965 ★: write binary to preserve LF-only line endings.
        # Preserve a trailing newline if the original file had one (common
        # convention; some nbformat writers strip it on re-serialize).
        # Use indent=1 to match the existing repo convention.
        trailing_nl = raw.endswith(b'\n')
        out = json.dumps(nb, ensure_ascii=False, indent=1).encode('utf-8')
        if trailing_nl and not out.endswith(b'\n'):
            out += b'\n'
        path.write_bytes(out)
    return total_changed, None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--dry-run', action='store_true')
    ap.add_argument('--target', help='fix only this notebook (relative to family dir)')
    args = ap.parse_args()

    targets = []
    if args.target:
        targets = [FAMILY_DIR / args.target]
    else:
        targets = sorted(p for p in FAMILY_DIR.rglob('*.ipynb') if '_output' not in p.name)

    total_changed = 0
    for p in targets:
        if not p.exists():
            print(f'MISSING: {p}', file=sys.stderr)
            continue
        n, err = fix_notebook(p, dry_run=args.dry_run)
        if err:
            print(f'ERROR {p.name}: {err}', file=sys.stderr)
        elif n:
            print(f'{p.name}: {n} heading(s) demoted{" (dry-run)" if args.dry_run else ""}')
            total_changed += n
    print(f'\nTotal demoted: {total_changed}')


if __name__ == '__main__':
    main()