#!/usr/bin/env python3
"""Fix c.914 (re-applied) — GenAI/Texte H1-DEEP/MULTI-H1/HINT-AS-HEADING burn-down.

Re-runs the c.914 fix on top of origin/main after the first attempt (commit
`318faa104`) was reverted by ai-01 review: it accidentally collapsed two
header cells (11_Quantization cell[3] and 12_Test_Time_Scaling cell[2]) to
just their demoted title line, dropping Navigation / prerequisites /
learning objectives / Snell et al. (2024) citations.

This re-application uses the same byte-surgical pattern as
`fix_sudoku_hierarchy.py` (L925-A ★★ / L948 ★★ / L965 ★★) so source format
(`string` / `line-list` / `char-split`) is preserved per cell.

Two demotion classes:

1. **H1-DEEP -> H2** : a `# Some Title` heading in a markdown cell that
   starts with that heading AND that title is NOT the canonical notebook
   title in `cell[0]` (e.g. "1. Introduction a l'IA generative...").
   Demotes `# X` -> `## X` on the FIRST line only. Conservative: does NOT
   touch H1s inside code blocks (markdown fence) or in cells where the
   first line isn't a heading (e.g. bash output snippets with `# comment`).

2. **HINT-AS-HEADING -> blockquote** : `### Indices`, `### Pistes pour
   Aller Plus Loin` (and lowercase variants) -> `> **... :**` blockquote
   callout (rendered as small body text, not oversized heading).

Idempotent: skips cells whose source already starts with `> **` or
`## <title>` (already demoted).

Constraints (L965 ★): LF-only CR=0, write via `json.dumps().encode('utf-8')`
binary write. L948 ★★: NO cell output scrubbing. C.3: scoped to notebooks
we modified, 0 re-execution (markdown-only edits).

Usage:
    python fix_texte_hierarchy.py [--dry-run] [--target <notebook>]
"""
import argparse, json, pathlib, re, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent  # worktree root
FAMILY_DIR = ROOT / 'MyIA.AI.Notebooks' / 'GenAI' / 'Texte'

# Heading-as-aside patterns (case-insensitive on the stem).
HINT_AS_HEADINGS = {
    'Indices',                              # most common
    'Pistes pour Aller Plus Loin',          # c.914 original target on 1_OpenAI_Intro
    'Pistes pour aller plus loin',          # lowercase variant
    'Pistes d\'amélioration',               # apostrophe courbe
    'Pistes d\'amelioration',               # straight apostrophe + no accent (legacy)
}


def _matches_hint(text):
    """Return True if `text` is one of the bare asides we want to demote."""
    stem = re.sub(r'\s*\(.*\)\s*$', '', text).strip()
    stem_norm = stem.replace('’', "'")
    if stem in HINT_AS_HEADINGS:
        return True
    if stem_norm in HINT_AS_HEADINGS:
        return True
    return False


def _detect_source_format(src):
    """Detect nbformat `source` field format to preserve byte structure.

    Three observed formats across the corpus (L925-A ★★):
      - 'string' : single joined string element (one cell with full prose)
      - 'line-list' : list of lines, each ending in `\\n` (except possibly last)
      - 'char-split' : list of single characters (no `\\n` in any element)
    """
    if isinstance(src, str):
        return 'string'
    if not src:
        return 'line-list'  # treat empty as line-list for safety
    has_newline = any('\n' in (e or '') for e in src)
    if has_newline:
        return 'line-list'
    return 'char-split'


def _demote_first_line_h1(source_lines):
    """If the first line of `source_lines` is `# <title>`, demote to `## <title>`.

    Returns (new_source_list, changed_bool).

    Conservative: only the FIRST line of the cell is checked, so H1s buried
    in code fences / bash output snippets are left alone. Caller is
    responsible for skipping cell[0] (the canonical H1 is cell[0], not any
    H1 that happens to match its title string).
    """
    if not source_lines:
        return source_lines, False
    first = source_lines[0]
    m = re.match(r'^#\s+(.+?)\s*$', first)
    if not m:
        return source_lines, False
    title = m.group(1).strip()
    # Preserve trailing newline structure.
    if first.endswith('\n'):
        new_first = '## ' + title + '\n'
    else:
        new_first = '## ' + title
    new_source_lines = [new_first] + source_lines[1:]
    return new_source_lines, True


def _demote_all_hint_headings(source_lines):
    """Replace EVERY matching `### Indices` / `### Pistes ...` heading with
    `> **<text> :**` blockquote callout. Returns (new_source_list, count).

    nbformat quirk (L925-A ★★): source can be character-split (each char
    its own line). We detect headings in the JOINED source, then locate
    their line ranges in the original split source.
    """
    if not source_lines:
        return source_lines, 0
    joined = ''.join(source_lines)
    headings = []  # list of (start_idx, end_idx, heading_text)
    for m in re.finditer(r'^(#{1,6})\s+([^\n]+?)\s*$', joined, re.MULTILINE):
        text = m.group(2).strip()
        if _matches_hint(text):
            headings.append((m.start(), m.end(), text))
    if not headings:
        return source_lines, 0
    line_offsets = []
    off = 0
    for line in source_lines:
        line_offsets.append((off, off + len(line)))
        off += len(line)
    new_lines = list(source_lines)
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
        replacement = [f'> **{text} :**\n']
        new_lines[first_line:last_line + 1] = replacement
    return new_lines, len(headings)


def fix_notebook(path, dry_run=False):
    """Apply burn-down to a single notebook. Returns (changed_count, error)."""
    try:
        raw = path.read_bytes()
        nb = json.loads(raw.decode('utf-8'))
    except Exception as e:
        return 0, f'parse: {e}'

    cells = nb.get('cells', [])
    total_changed = 0
    for cell_idx, cell in enumerate(cells):
        if cell.get('cell_type') != 'markdown':
            continue
        # Skip cell[0]: that's the canonical notebook title (cell[0]'s H1 is
        # the legitimate one). Demoting it would erase the notebook's own
        # name from the rendered output.
        if cell_idx == 0:
            continue
        src = cell.get('source', [])
        if not src:
            continue
        joined = ''.join(src).lstrip()
        # Skip already-demoted (blockquote) or H2-already demoted first line.
        if joined.startswith('> **'):
            continue
        original_format = _detect_source_format(src)
        # L925-A ★★: split the joined string form into lines (keeping newlines)
        # instead of wrapping as a single line. Without this, a 'string' source
        # cell collapses to one element and ALL non-heading body is lost when
        # the heading is replaced (incident c.925 #8654: 941 -> 16 chars on
        # Sudoku-1 cell 9). Same root cause as the c.914 broken commit
        # `318faa104` which produced two -970 / -1594 char losses on
        # 11_Quantization cell[3] / 12_Test_Time_Scaling cell[2].
        src_for_work = src if isinstance(src, list) else src.splitlines(keepends=True)

        # 1) H1-DEEP -> H2 on first line (any cell except cell[0]).
        src_for_work, h1_changed = _demote_first_line_h1(src_for_work)
        # 2) HINT-AS-HEADING -> blockquote callouts.
        src_for_work, hint_changed = _demote_all_hint_headings(src_for_work)
        changed = h1_changed + hint_changed
        if not changed:
            continue

        # Re-emit in the original format.
        if original_format == 'string':
            cell['source'] = ''.join(src_for_work)
        elif original_format == 'line-list':
            cell['source'] = src_for_work
        elif original_format == 'char-split':
            joined_new = ''.join(src_for_work)
            cell['source'] = list(joined_new)
        else:
            cell['source'] = src_for_work
        total_changed += changed

    if total_changed and not dry_run:
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