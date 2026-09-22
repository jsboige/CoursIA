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

#17143: the demotion unit is the BLOCK, not the line. When an aside's
continuation is written as further ``# `` lines, only the head becomes a
bold callout; the continuations become plain ``> `` lines. Demoting each
line on its own appends a `` :`` mid-sentence and bolds a fragment -- the
"split callout" defect. ``--detect`` reports that shape read-only (see
``is_split_callout_run`` for the discriminator and its known limits).

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

    Issue #17143: also match ``Indice : <body>`` and ``Etape N : <body>``
    forms — singular heading-style asides common in pedagogical notebooks
    (often spanning multiple contiguous lines; the demoter now collapses
    those into a single blockquote, see ``_demote_all_headings``).
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

    # 7. "Indice : <body>" — issue #17143. Match the singular form when
    # followed by a colon (signals an aside with body content).
    if stem.startswith('Indice :') or stem.startswith('Indice:'):
        return True

    # 8. "Etape N : <body>" — issue #17143. Match singular "Etape" followed
    # by digits/colon (e.g. "Etape 1 : preparer").
    if re.match(r'^Etape\s+\d+\s*:', stem):
        return True
    if re.match(r'^Étape\s+\d+\s*:', stem):
        return True

    return False


def _is_singular_target(text):
    """Return True iff ``text`` is a singular target (issue #17146 narrow scope).

    Singulars (``Indice :``, ``Etape N :``, etc.) are absorbed as continuations
    of a preceding plural heading; they don't trigger their own callout in a
    contiguous run.
    """
    if text.startswith('Indice :') or text.startswith('Indice:'):
        return True
    if re.match(r'^Etape\s+\d+\s*:', text):
        return True
    if re.match(r'^Étape\s+\d+\s*:', text):
        return True
    return False


# ---------------------------------------------------------------------------
# Split-callout detection (#17143)
# ---------------------------------------------------------------------------

# Line of a callout run terminated by an APPENDED colon: `> **<texte> :**`.
# A colon written by hand is legal (`> **Bonnes pratiques :**`); what this
# signature isolates is the shape the line-by-line demotion leaves behind.
_APPENDED_COLON_RE = re.compile(r' :\*\*\s*$')
# A continuation that is a list item or a nested heading, not bare prose.
_LIST_ITEM_RE = re.compile(r'^>\s*(?:[-*+]|\d+\.|#{1,6}\s)')


def _iter_callout_runs(source):
    """Yield the contiguous ``> `` runs of one markdown cell.

    A run is a maximal group of consecutive lines that open a blockquote;
    a blank line, prose or any other line closes it.
    """
    text = ''.join(source) if isinstance(source, list) else source
    run = []
    for line in text.split('\n') + ['']:  # sentinel closes the last run
        if line == '>' or line.startswith('> '):
            run.append(line)
            continue
        if run:
            yield list(run)
            run = []


def is_split_callout_run(run):
    """True if ``run`` is a callout split line by line (the #17143 defect).

    Two signals, both required:
      (a) at least one line ends with an appended `` :**``;
      (b) at least one *other* line is bare prose -- not an appended colon,
          not a list item, not a fenced code block.

    (b) is what separates "split sentence" from the two legitimate callouts
    measured on the corpus: a head followed by a bullet list, and a head
    followed by a fenced code block. A run whose lines ALL end with `` :**``
    is a term list, not a split sentence, so it is not flagged either.

    Known false-negative: a split sentence that happens to contain a code
    fence is not reported.
    """
    if len(run) < 2:
        return False
    appended = [bool(_APPENDED_COLON_RE.search(line)) for line in run]
    if not any(appended):
        return False
    if any(line.lstrip('> ').startswith('```') or line.rstrip().endswith('```')
           for line in run):
        return False
    return any(not mark and not _LIST_ITEM_RE.match(line)
               for line, mark in zip(run, appended))


def find_split_callouts(source):
    """Return the split-callout runs of one markdown cell source."""
    return [run for run in _iter_callout_runs(source) if is_split_callout_run(run)]


def detect_notebook(path):
    """Scan a notebook for split-callout runs. Returns ``(findings, error)``.

    Read-only: never writes. Each finding is a dict with the cell index, the
    run length, the number of appended colons and the offending lines.
    """
    try:
        nb = json.loads(pathlib.Path(path).read_bytes().decode('utf-8'))
    except Exception as e:
        return [], f'parse: {e}'

    findings = []
    for index, cell in enumerate(nb.get('cells', [])):
        if cell.get('cell_type') != 'markdown':
            continue
        for run in find_split_callouts(cell.get('source', [])):
            findings.append({
                'cell': index,
                'run_length': len(run),
                'appended_colons': sum(1 for line in run
                                       if _APPENDED_COLON_RE.search(line)),
                'lines': run,
            })
    return findings, None


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
    """Replace EVERY matching heading BLOCK with a single ``> **<text> :**`` callout.

    A cell may contain multiple target headings (Sudoku-06-AIMA-CSP-Python
    cells have BOTH ``### Étapes`` AND ``### Indices`` in the same cell).
    We demote all occurrences and preserve the body untouched.

    #17143 -- the unit is the BLOCK, not the line. An author who writes a
    hint's continuation as further ``# `` lines (``# Indices`` followed by
    ``# Etape 1 : ...``, ``# Etape 2 : ...``) has written ONE aside, not
    three headings. Demoting each line on its own appends a `` :`` to every
    fragment and bolds a sentence mid-way -- the split-callout defect. We
    therefore absorb the contiguous run of SAME-prefix lines that follows
    the matched heading: only the head is bolded and keeps the `` :``, the
    continuations become plain ``> `` lines.

    The run stops at a blank line, at a line whose prefix differs (a real
    nested section is not swallowed), and at a line that is itself a target
    heading (it gets its own callout). Two consecutive same-level headings
    are unidiomatic in Markdown, so absorbing them is the conservative
    reading of the author's intent.

    nbformat quirk (L983 ★★): source can be character-split (each char
    its own line). We detect headings in the JOINED source, then locate
    their line ranges in the original split source.

    Returns ``(new_source_list, changed_count)`` where ``changed_count``
    counts demoted target headings (one per callout, continuations folded).
    """
    if not source_lines:
        return source_lines, 0

    joined = ''.join(source_lines)

    # Find all heading occurrences in the joined source.
    headings = []  # list of (start_idx, end_idx, prefix, heading_text)
    for m in re.finditer(r'^(#{1,6})\s+([^\n]+?)\s*$', joined, re.MULTILINE):
        prefix = m.group(1)
        text = m.group(2).strip()
        if _matches_target(text):
            headings.append((m.start(), m.end(), prefix, text))

    if not headings:
        return source_lines, 0

    # Map joined positions back to source_lines indices.
    line_offsets = []
    off = 0
    for line in source_lines:
        line_offsets.append((off, off + len(line)))
        off += len(line)

    # Helper: find the source_lines index of the line containing a joined
    # offset `pos`. Returns None if pos falls on a line boundary (no such
    # line in practice given our inputs).
    def _line_idx_for_pos(pos):
        for i, (lo, hi) in enumerate(line_offsets):
            if lo <= pos < hi:
                return i
        return None

    # Group consecutive headings into "heading-block" entities ONLY when the
    # following heading is a singular target (issue #17146 narrow scope)
    # that should absorb into the preceding target's callout. Plural targets
    # always get their own callout (issue #17147). `changed_count` reflects
    # the number of callouts produced (one per block).
    # Each block carries: (first_start, last_end, prefix, [texts]).
    blocks = []  # list of (first_start, last_end, prefix, [texts])
    for start, end, prefix, text in headings:
        if blocks and _is_singular_target(text):
            prev_first, prev_last, prev_prefix, prev_texts = blocks[-1]
            prev_last_line = _line_idx_for_pos(prev_last - 1)
            this_first_line = _line_idx_for_pos(start)
            if (prev_last_line is not None and this_first_line is not None
                    and this_first_line == prev_last_line + 1
                    and prefix == prev_prefix):
                # Singular continuation: absorb into preceding block.
                blocks[-1] = (prev_first, end, prev_prefix, prev_texts + [text])
                continue
        blocks.append((start, end, prefix, [text]))

    # For each block, find which line(s) it spans and replace them with
    # the multi-line blockquote (one `> **` line for the first, then
    # `> <text>` continuation lines for absorbed singulars).
    new_lines = list(source_lines)
    # Process from end to start to keep indices valid.
    for first_start, last_end, prefix, texts in reversed(blocks):
        first_line = None
        last_line = None
        for i, (lo, hi) in enumerate(line_offsets):
            if hi > first_start and first_line is None:
                first_line = i
            if lo < last_end:
                last_line = i
        if first_line is None or last_line is None:
            continue

        # Absorb the contiguous run of SAME-prefix lines that follows the
        # matched heading (#17143). Stop on a different prefix, a plural
        # target heading (it gets its own callout), or any non-heading
        # line. Singular headings (e.g. "Indice :", "Etape 1 :") introduced
        # in #17146 narrow-scope are absorbed as continuations of a matched
        # plural heading above them, NOT as standalone callouts.
        run_last = last_line
        follow_texts = list(texts[1:])  # accumulated continuation texts
        while run_last + 1 < len(source_lines):
            follow = re.match(r'^(#{1,6})\s+(\S.*?)\s*$', source_lines[run_last + 1])
            if not follow or follow.group(1) != prefix:
                break
            follow_text = follow.group(2).strip()
            # Plural targets get their own callout — break the run.
            # Singular targets (with `:` and/or `N :`) absorb as continuation.
            # Non-target headings (e.g. "Corps de la note") also absorb as
            # continuation — original #17143 behaviour preserved.
            if _matches_target(follow_text) and not _is_singular_target(follow_text):
                break
            follow_texts.append(follow_text)
            run_last += 1

        # Build replacement lines: first line bolded with colon, subsequent
        # continuations plain (no bold, no colon). Continuations come from
        # both the block's absorbed texts (singulars joined at grouping time)
        # AND any non-target same-prefix headings walked below.
        head_text = texts[0]
        replacement = [f'> **{head_text} :**\n']
        for body in follow_texts:
            replacement.append(f'> {body}\n')
        # Preserve trailing-newline status of the LAST consumed line.
        last_consumed_line = source_lines[run_last] if run_last < len(source_lines) else ''
        if last_consumed_line and not last_consumed_line.endswith('\n'):
            replacement[-1] = replacement[-1].rstrip('\n')
        new_lines[first_line:run_last + 1] = replacement

    changed_count = len(blocks)
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
        # Sudoku-01 cell 9).
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
    ap.add_argument(
        '--detect', action='store_true',
        help='Read-only: report split-callout runs (#17143) instead of '
             'demoting. Exit 1 when any is found.')
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

    if args.detect:
        total_findings = 0
        for p in targets:
            if not p.exists():
                print(f'MISSING: {p}', file=sys.stderr)
                continue
            findings, err = detect_notebook(p)
            if err:
                print(f'ERROR {p.name}: {err}', file=sys.stderr)
                continue
            for f in findings:
                total_findings += 1
                print(f'{p.name}: cell {f["cell"]} -- split callout, '
                      f'{f["run_length"]} line(s), {f["appended_colons"]} '
                      f'appended colon(s)')
        print(f'\nTotal split callouts: {total_findings}')
        return 1 if total_findings else 0

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
