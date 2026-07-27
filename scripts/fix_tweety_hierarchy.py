#!/usr/bin/env python3
"""Fix c.922 — SymbolicAI/Tweety HINT-AS-HEADING findings.

Same byte-surgical pattern as c.914 GenAI/Texte (#8630): demote `### Indices`,
`### Étapes`, `## Notes techniques (...)` headings to `> **Indices :**`,
`> **Étapes :**`, `> **Notes techniques :**` blockquote callouts (rendered as
small body text, not as oversized headings).

Constraints (L965 ★): LF-only CR=0, write via `json.dumps().encode('utf-8')`
binary write (NOT `nbformat.write` which introduces CRLF). L948 ★★: NO cell
output scrubbing. C.1/C.2/C.3: no NotImplementedError, no empty cell edits,
scoped to notebooks we modified.

Idempotent: skips cells whose source already starts with `> **` (avoid
double-prefixing if re-run).

Usage:
    python fix_tweety_hierarchy.py [--dry-run] [--target <notebook>]
"""
import argparse, json, pathlib, re, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent  # worktree root
FAMILY_DIR = ROOT / 'MyIA.AI.Notebooks' / 'SymbolicAI' / 'Tweety'

# Mirror scanner HINT_RE minus plurals-blind fix detail; we DEMOTE only the
# bare asides the scanner flagged (Indices / Étapes / Notes techniques).
TARGET_HEADINGS = {'Indices', 'Etapes', 'Étapes', 'Notes techniques'}

def _demote_heading(source_lines, heading_text):
    """Replace the first `### Indices` / `### Étapes` heading line with
    `> **Indices :**` blockquote. Returns (new_source_list, changed_bool).

    A heading cell is just `### Indices\\n` or `### Étapes\\n` — the prose body
    follows in subsequent lines. We replace ONLY the heading line and prepend
    the demoted blockquote in its place. The body stays untouched.

    nbformat convention: each line of `source` is a string ending in `\\n`
    EXCEPT the last (if non-empty). Headings in our findings are always a
    single line followed by a blank line then body content. We preserve the
    list-of-strings structure byte-for-byte except for the demoted line.
    """
    new_lines = []
    changed = False
    blockquote = f'> **{heading_text} :**\n'
    for i, line in enumerate(source_lines):
        m = re.match(r'^(#{1,6})\s+(.*\S)\s*$', line)
        if m and not changed and _matches_target(m.group(2).strip()):
            # Replace this heading with a blockquote callout.
            new_lines.append(blockquote)
            changed = True
        else:
            new_lines.append(line)
    return new_lines, changed


def _matches_target(text):
    """Return True if `text` is one of the bare asides we want to demote.
    `Notes techniques (Tweety 1.30)` is a valid target — drop any parenthetical
    to match the canonical form. `Notes pédagogiques sur Tweety` would NOT
    match (not in scope of this rollout).
    """
    # Strip optional parenthetical / trailing specifier.
    stem = re.sub(r'\s*\(.*\)\s*$', '', text).strip()
    return stem in TARGET_HEADINGS


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
        # Find a target heading in the source.
        target_text = None
        for line in src:
            m = re.match(r'^#{1,6}\s+(.*\S)\s*$', line)
            if m and _matches_target(m.group(1).strip()):
                target_text = m.group(1).strip()
                break
        if not target_text:
            continue
        new_src, changed = _demote_heading(src, target_text)
        if changed:
            cell['source'] = new_src
            total_changed += 1

    if total_changed and not dry_run:
        # L965 ★: write binary to preserve LF-only line endings.
        path.write_bytes(json.dumps(nb, ensure_ascii=False, indent=1).encode('utf-8'))
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