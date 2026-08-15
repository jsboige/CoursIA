#!/usr/bin/env python3
"""Source-level lint for GFM markdown table syntax defects.

Detects four pathologies that break table rendering in the GitHub preview
(source-level, render-agnostic -- it flags the *convention violation* that
breaks rendering on at least one common renderer, not a post-render check):

  - **COL_MISMATCH**: within a recognized table (one that HAS a `|---|`-shaped
    separator row), a data row's raw ``|`` count differs from the header row's.
    Canonical cause (MGS-3-Eukaryote cell[13], #10097): a bare ``|`` inside a
    cell that the author did not escape as ``\\|`` -- e.g. ``| Scope |
    `Crossover | Mutation` | ... |`` reads as 5 columns where the header had 4.
    A source-level lint counts raw pipes (it does not try to honor inline-code
    spans, because not every renderer does either -- the portable convention is
    to escape the pipe as ``\\|``). See #10097 acceptance sample.

  - **NO_SEP**: a run of 3+ consecutive ``|``-shaped lines with NO
    ``:?-+:?`` separator row among them. GFM does not recognize the block as a
    table without the separator and renders it as a ``pre`` block instead
    (MGS-15-LandscapeAnalysis cell[5]/cell[22]). A 3-line floor avoids flagging
    a stray two-line ``| a | b |`` snippet that is not meant to be a table.

  - **NO_BLANK_BEFORE**: a non-blank, non-heading, non-table line immediately
    precedes a table block. GFM (CommonMark) requires a blank line separating a
    paragraph from a following table; without it the table is absorbed into the
    paragraph and does not render as a table (MGS-1-Introduction, #10097).

  - **NO_BLANK_AFTER**: the symmetric case -- a non-blank, non-heading,
    non-table line immediately follows a table block, merging the next
    paragraph into it.

Scope (HORS scope, volontaire):
  - Render aesthetics (column width, padding) -- eye-judgement, not automatable.
  - Prose-vs-table-content coherence -- axe #8052/#8364 (scan_quant_classify).
  - Box-drawing / monospace grids -- axe #3969 (Sudoku grids), already decided
    out.

Usage:
  python scan_md_table_syntax.py <notebook-or-dir-or-md> [...] [--json] [--check]
  --check  exit 1 if >=1 finding (CI-ready); without it, exit 0 always on success.
  A scan that finds NOTHING to scan (no .ipynb/.md/README* under the targets,
  or a missing path) exits 2 with a stderr message -- a vacuous ``0 findings``
  is never printed, so a mistyped ``--root`` cannot masquerade as a clean scan
  (same guard as scan_md_hierarchy.py, #3968).

See #10097, #3966.
"""
import argparse
import json
import re
import sys
import pathlib

# ---------------------------------------------------------------------------
# Regexes
# ---------------------------------------------------------------------------

# A fence delimiter (``` or ~~~), possibly indented. Lines inside a fence are
# code -- a `|` there is a shell/pipe operator, NOT a table column, and must
# not be analyzed. We track fence state linearly (a ``` opens, the next ```
# closes; ~~~ mirrors). Indented ``` (4+ spaces) is an indented code block, not
# a fence, but GitHub treats fenced blocks tolerantly -- we open on any leading
# fence run for simplicity (matches scan_md_hierarchy.py's FENCE_RE).
FENCE_OPEN_RE = re.compile(r'^\s{0,3}(`{3,}|~{3,})')

# A line that "looks like a table row": contains a pipe. We do not require
# leading/trailing `|` (GFM tables may omit the outer borders). A lone `|`
# in flowing prose (e.g. "a | b" as an English aside) CAN trip this, so the
# block-grouper additionally requires the run to look table-like (>= 2 rows,
# or a separator present) before reporting pathologies -- a single ``a | b``
# line never forms a block of >= 2 and is thus ignored.
PIPE_LINE_RE = re.compile(r'\|')

# A GFM table separator row: optional leading/trailing pipe, then one or more
# cells of the form `:?-+:?` (dashes, optionally colon-padded for alignment),
# joined by pipes. e.g. `|---|---|`, `|:---:|---:|`, `---|---`.
# An optional blockquote marker ``>`` is tolerated: a GFM table wrapped in a
# blockquote keeps its separator as ``> |---|---|``, and ``^\s*`` alone missed
# the ``>`` and flagged valid blockquote tables as NO_SEP (ICT-0-Annexe, #10097).
SEP_ROW_RE = re.compile(
    r'^\s*>?\s*\|?\s*:?-+:?\s*(\|\s*:?-+:?\s*)+\|?\s*$'
)

# A markdown heading line (`#`..`######`). A heading directly above a table is
# a valid, common pattern that does NOT need a blank line before the table --
# excluding headings from NO_BLANK_BEFORE/AFTER avoids flagging it.
HEADING_RE = re.compile(r'^\s{0,3}#{1,6}\s')

# Spans whose interior `|` must NOT count as a column delimiter (GFM-correct
# column counting). Three classes, all NON-ACTIONABLE (flagging them would tell
# the author to "fix" something that is already correct, or impossible to fix):
#   1. Inline code spans `` `...` `` -- GFM table parsing protects them (the
#      spec parses code spans BEFORE splitting cells). A `|` inside `` `a|b` ``
#      is a literal, not a delimiter. Counting it (as the #10097 preliminary
#      ``gh api`` sample did for `` `Crossover | Mutation` ``) is a FALSE
#      POSITIVE: GitHub renders the cell correctly.
#   2. Escaped pipes ``\|`` -- the GFM-correct way to put a literal `|` in a
#      cell. The author did it RIGHT; flagging it is a false positive
#      (e.g. ``P(S=T\|C=T)`` in Infer-4 cell[7]).
#   3. Inline math ``$...$`` -- a `|` there is an absolute-value / norm bar in
#      LaTeX. It CANNOT be escaped (``$\|x\|$`` breaks the math), so flagging it
#      is non-actionable noise; current GitHub renders ``$|x|$`` correctly in
#      tables. Excluded by deliberate conservative choice.
CODE_SPAN_RE = re.compile(r'(`+)[^`]*\1')
# KaTeX-faithful inline-math span. The bare ``\$[^$\n]*\$`` treated two
# currency amounts in a cost table (``$15.00 | ~$0.75``) as ONE math span,
# swallowing the cell-delimiter pipe and false-positive-ing COL_MISMATCH on
# every price column fleet-wide. The real delimiter rule (KaTeX / GFM math):
# the opening ``$`` is NOT preceded by an alnum, and the closing ``$`` is NOT
# followed by an alnum. ``$0.75`` has the ``$`` followed by ``0`` so it cannot
# close a span, while ``$|x|$`` and ``$P(z_t|z_{t-1})$`` keep clean boundaries
# and stay protected. See #10097 (currency-price COL_MISMATCH FP class).
MATH_SPAN_RE = re.compile(r'(?<![A-Za-z0-9])\$[^$\n]*\$(?![A-Za-z0-9])')
ESCAPED_PIPE_RE = re.compile(r'\\\|')

# Conditional-probability / function-call notation: ``P(x|y)``, ``O(|A|*|S|)``,
# ``Cov(a|b)`` -- a ``|`` inside such a ``Letter(...)`` span is a math conditional
# bar, NOT a table column delimiter. Excluding these lines from block grouping
# prevents two consecutive ``P(X|Y)`` prose lines (e.g. an exercise enumerating
# conditional probabilities) from being mistaken for a 2-row table block, which
# was the dominant false-positive source on the Probas family (~71% of the
# NO_BLANK findings were ``P(X|Y)`` math pipes). See #10097.
COND_NOTATION_RE = re.compile(r'[A-Za-z]\([^)]*\|[^)]*\)')

# List-item marker (CommonMark): a line beginning with a bullet (``-``/``*``/
# ``+``) or an ordered-list marker (``1.``/``1)``) after up to 3 leading spaces.
# GFM parses list items BEFORE tables, so a list-item line is never a table row:
# any ``|`` in it is literal content. Excluding list items from table-block
# grouping kills the bare absolute-value math-pipe false positive -- e.g.
# ``- |r| > 0.7`` (Pearson correlation in a sub-list, 7_Code_Interpreter cell
# 36, the root cause of the c.198 #10221 retraction) -- without touching real
# tables: a GFM table row never starts with a list marker. See #10097.
LIST_MARKER_RE = re.compile(r'^ {0,3}(?:[-*+]|[0-9]{1,9}[.)])(?:[ \t]+|$)')


def _has_delimiter_pipe(line):
    """True if ``line`` has a pipe that could be a GFM table column delimiter.

    A pipe that survives removal of inline code, inline math, escaped pipes, and
    ``Letter(...|...)`` conditional notation is a candidate delimiter; a line
    whose only pipes live inside those spans is math/prose, not a table row.
    Mirrors the protection already applied by ``_column_count`` (which handles
    code/math/escaped) and extends it to bare ``P(X|Y)`` plain-text conditional
    notation that ``$...$`` stripping does not reach. A list-item line (CommonMark
    marker) is never a table row, so its pipes are content regardless.
    """
    if LIST_MARKER_RE.match(line):
        return False
    t = CODE_SPAN_RE.sub('', line)
    t = MATH_SPAN_RE.sub('', t)
    t = ESCAPED_PIPE_RE.sub('', t)
    t = COND_NOTATION_RE.sub('', t)
    return '|' in t


# ---------------------------------------------------------------------------
# Core: find table blocks in a list of (1-indexed) source lines
# ---------------------------------------------------------------------------

def _find_table_blocks(lines):
    """Return a list of table blocks.

    A block = dict(start, end, rows, has_sep, sep_index) spanning consecutive
    pipe-lines (1-indexed line numbers), tracked OUTSIDE code fences.
    """
    blocks = []
    in_fence = False
    fence_marker = None
    i = 0
    n = len(lines)
    while i < n:
        line = lines[i]
        stripped = line.strip()
        # Fence state transitions
        if in_fence:
            m = FENCE_OPEN_RE.match(line)
            if m and m.group(1)[0] == fence_marker:
                in_fence = False
                fence_marker = None
            i += 1
            continue
        m = FENCE_OPEN_RE.match(line)
        if m:
            in_fence = True
            fence_marker = m.group(1)[0]
            i += 1
            continue
        # Not in a fence: is this a pipe-line? (math/conditional pipes excluded)
        if not stripped or not _has_delimiter_pipe(line):
            i += 1
            continue
        # Start of a potential pipe-line run
        start = i
        rows = []
        while i < n:
            l = lines[i]
            ls = l.strip()
            if not ls or not _has_delimiter_pipe(l):
                break
            # stop if a fence opens mid-run
            if FENCE_OPEN_RE.match(l):
                break
            rows.append((i + 1, l))  # 1-indexed line number
            i += 1
        if len(rows) >= 2:
            # Determine if the run contains a separator row (GFM table).
            sep_index = None
            for idx, (lnum, l) in enumerate(rows):
                if SEP_ROW_RE.match(l.strip()):
                    sep_index = idx
                    break
            blocks.append({
                "start": start + 1,   # 1-indexed
                "end": rows[-1][0],
                "rows": rows,
                "has_sep": sep_index is not None,
                "sep_index": sep_index,
            })
        # else: a lone pipe-line (or run of 1) -- not a table, skip
    return blocks


def _column_count(line):
    """Count GFM table columns in a line.

    Strips protected spans (inline code, escaped pipes, inline math -- see the
    CODE_SPAN_RE / MATH_SPAN_RE / ESCAPED_PIPE_RE block above) so their interior
    pipes are not mistaken for delimiters, then drops the optional outer-border
    empty cells (a borderless ``a | b | c`` row has the same 3 columns as the
    bordered ``| a | b | c |``). Returns the logical column count.
    """
    tmp = CODE_SPAN_RE.sub('X', line)
    tmp = MATH_SPAN_RE.sub('X', tmp)
    tmp = ESCAPED_PIPE_RE.sub('X', tmp)
    parts = tmp.split('|')
    if parts and parts[0].strip() == '':
        parts = parts[1:]
    if parts and parts[-1].strip() == '':
        parts = parts[:-1]
    return len(parts)


def _is_blank(line):
    # A bare blockquote marker ``>`` (optionally followed by whitespace) renders
    # as a blank separator within a blockquote -- it provides the same visual
    # separation between a table and surrounding prose as a true blank line, so
    # for the table-glue checks (NO_BLANK_BEFORE/AFTER) it counts as blank
    # (a ``>`` line does NOT glue a blockquote table to its neighbors).
    s = line.strip()
    return s == "" or s == ">"


# ---------------------------------------------------------------------------
# Pathology detection on a cell/file's lines
# ---------------------------------------------------------------------------

def detect_md_table_syntax(lines, source_label="line"):
    """Detect the 4 pathologies in a list of source lines.

    Returns a list of findings: dict(pathology, line, detail, snippet).
    `line` is 1-indexed within `lines`. `source_label` is used only for the
    human report (e.g. "cell[12]" vs "line").
    """
    findings = []
    n = len(lines)
    blocks = _find_table_blocks(lines)

    for blk in blocks:
        rows = blk["rows"]
        # --- NO_SEP: a run of >= 3 pipe-lines with no separator row ---
        if not blk["has_sep"] and len(rows) >= 3:
            lnum, l = rows[0]
            findings.append({
                "pathology": "NO_SEP",
                "line": lnum,
                "detail": (
                    f"bloc table de {len(rows)} lignes sans ligne separateur "
                    f"('|---|') -> rendu en bloc <pre> au lieu d'une table"
                ),
                "snippet": l.strip()[:80],
            })
            # NO_SEP blocks are not GFM tables, so COL_MISMATCH does not apply
            # (the table is not recognized at all). Continue to blank-line
            # checks below, which still matter (a pre block glued to prose is
            # still ugly) -- but the primary defect here is NO_SEP.
            continue

        # --- COL_MISMATCH: recognized table (has sep), data-row pipe drift ---
        if blk["has_sep"]:
            sep_idx = blk["sep_index"]
            # Header is the row immediately above the separator (GFM layout).
            if sep_idx == 0:
                # Separator with no header above -- malformed; NO_SEP-like.
                lnum, l = rows[0]
                findings.append({
                    "pathology": "NO_SEP",
                    "line": lnum,
                    "detail": "ligne separateur sans en-tete au-dessus",
                    "snippet": l.strip()[:80],
                })
            else:
                header_lnum, header_line = rows[sep_idx - 1]
                header_cols = _column_count(header_line)
                # Check data rows (those below the separator).
                for idx in range(sep_idx + 1, len(rows)):
                    d_lnum, d_line = rows[idx]
                    d_cols = _column_count(d_line)
                    if d_cols != header_cols:
                        findings.append({
                            "pathology": "COL_MISMATCH",
                            "line": d_lnum,
                            "detail": (
                                f"{d_cols} colonnes vs {header_cols} dans l'en-tete "
                                f"-> colonne fantome (un '|' nu non-echappe dans la "
                                f"cellule ? echapper en '\\|')"
                            ),
                            "snippet": d_line.strip()[:80],
                        })

        # --- NO_BLANK_BEFORE: line immediately before the block is prose ---
        # block occupies lines [blk['start'] .. blk['end']] (1-indexed) in the
        # ORIGINAL line numbering. rows[0][0] == blk['start'].
        prev_idx = blk["start"] - 2  # 0-indexed of the line before the block
        if prev_idx >= 0:
            prev = lines[prev_idx]
            if (not _is_blank(prev)
                    and not HEADING_RE.match(prev)
                    and not PIPE_LINE_RE.search(prev)):
                findings.append({
                    "pathology": "NO_BLANK_BEFORE",
                    "line": blk["start"],
                    "detail": (
                        "ligne non-vide precede immediatement le bloc table "
                        "-> fusion avec le paragraphe (ajouter une ligne vide)"
                    ),
                    "snippet": prev.strip()[:80],
                })

        # --- NO_BLANK_AFTER: line immediately after the block is prose ---
        next_idx = blk["end"]  # 0-indexed of the line after the block
        if next_idx < n:
            nxt = lines[next_idx]
            if (not _is_blank(nxt)
                    and not HEADING_RE.match(nxt)
                    and not PIPE_LINE_RE.search(nxt)):
                findings.append({
                    "pathology": "NO_BLANK_AFTER",
                    "line": blk["end"],
                    "detail": (
                        "ligne non-vide suit immediatement le bloc table "
                        "-> fusion avec le paragraphe suivant (ajouter une "
                        "ligne vide)"
                    ),
                    "snippet": nxt.strip()[:80],
                })

    findings.sort(key=lambda f: (f["line"], f["pathology"]))
    return findings


# ---------------------------------------------------------------------------
# Notebook / markdown file walkers
# ---------------------------------------------------------------------------

def scan_notebook(path):
    """Scan a .ipynb: returns {path, findings: [{cell_index, ...pathology...}]}."""
    try:
        nb = json.loads(pathlib.Path(path).read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as e:
        return {"path": str(path), "error": str(e), "findings": []}
    findings = []
    for ci, cell in enumerate(nb.get("cells", [])):
        if cell.get("cell_type") != "markdown":
            continue
        src = cell.get("source", [])
        lines = "".join(src).split("\n") if isinstance(src, list) else src.split("\n")
        for f in detect_md_table_syntax(lines):
            findings.append({"cell_index": ci, **f})
    return {"path": str(path), "error": None, "findings": findings}


def scan_markdown(path):
    """Scan a .md/README file: returns {path, findings: [{line, ...pathology...}]}."""
    try:
        text = pathlib.Path(path).read_text(encoding="utf-8")
    except OSError as e:
        return {"path": str(path), "error": str(e), "findings": []}
    lines = text.split("\n")
    findings = detect_md_table_syntax(lines)
    return {"path": str(path), "error": None, "findings": findings}


def scan_path(path):
    """Dispatch on file type. Returns the per-file result dict."""
    p = pathlib.Path(path)
    s = str(path)
    if s.endswith(".ipynb"):
        return scan_notebook(s)
    if s.endswith(".md") or p.name.upper().startswith("README"):
        return scan_markdown(s)
    return {"path": s, "error": "unsupported file type", "findings": []}


# ---------------------------------------------------------------------------
# Recursive walker (skips .lake/, node_modules/, .git/, _archives/)
# ---------------------------------------------------------------------------

_SKIP_DIRS = {".lake", "node_modules", ".git", "_archives", ".pytest_cache",
              "__pycache__"}

# Out-of-scope zones excluded by DEFAULT (override with --include-all). Per the
# #10097 post-merge re-measure, ~73% of the raw defect count lives in committed
# *agent conversation transcripts* and *generated reports* where "GFM table
# rendering" is meaningless -- fixing them by hand rewrites a journal or a
# machine-generated doc, which is the opposite of the file's purpose. The
# scanner must exclude these zones itself (a rule each worker recalls is not
# applied; a default `--exclude` is). See #10097 comment (re-measure on main).
#
#   (a) Roo-Code/Corrections/**        -- Roo agent task transcripts committed
#                                         as "corriges d'atelier" (a journal,
#                                         not rendered prose). ~238/324 defects.
#   (b) Argumentum/**/*_Report.md      -- machine-generated Git-archaeology /
#                                         validation reports (not authored prose).
#   (c) *_output.ipynb                 -- papermill/execution artefacts (already
#                                         excluded by other gates; kept here for
#                                         a single source of truth).
# Matched by path PARTS (robust to repo layout changes) so the rule is a
# directory-shape / filename pattern, not a fragile absolute path.


def _is_out_of_scope(path_str):
    """True if `path_str` is a committed-transcript / generated-report /
    execution-artefact zone the scanner should exclude by default (#10097).
    Returns (excluded: bool, reason: str|None) so callers can tally the drop."""
    p = pathlib.Path(path_str)
    parts = [str(x) for x in p.parts]
    name = p.name
    # (a) Roo-Code/Corrections/** -- a Corrections dir anywhere under a Roo-Code dir.
    if "Corrections" in parts and "Roo-Code" in parts:
        return True, "Roo-Code/Corrections transcript"
    # (b) Argumentum/**/*_Report.md -- generated report under the Argumentum tree.
    if "Argumentum" in parts and name.endswith("_Report.md"):
        return True, "Argumentum generated report"
    # (c) *_output.ipynb -- execution artefact.
    if name.endswith("_output.ipynb"):
        return True, "execution artefact"
    return False, None


def iter_targets(paths, include_all=False):
    """Yield .ipynb + .md + README* files under the given paths.

    By default out-of-scope zones (transcripts, generated reports, execution
    artefacts -- see `_is_out_of_scope`) are skipped; pass `include_all=True`
    to audit the raw corpus (the count then includes the ~73% journal noise)."""
    seen = set()
    for p in paths:
        pp = pathlib.Path(p)
        if pp.is_file():
            if str(pp) not in seen:
                seen.add(str(pp))
                yield str(pp)
        elif pp.is_dir():
            for f in pp.rglob("*"):
                if any(part in _SKIP_DIRS for part in f.parts):
                    continue
                if not f.is_file():
                    continue
                name = f.name
                if (name.endswith(".ipynb") or name.endswith(".md")
                        or name.upper().startswith("README")):
                    if not include_all and _is_out_of_scope(str(f))[0]:
                        continue
                    if str(f) not in seen:
                        seen.add(str(f))
                        yield str(f)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main(argv=None):
    ap = argparse.ArgumentParser(
        description="Source-level lint for GFM markdown table syntax defects. "
                    "See #10097, #3966.")
    ap.add_argument("paths", nargs="+",
                    help="notebook(s) / markdown file(s) / dir(s) to scan")
    ap.add_argument("--json", action="store_true", dest="as_json",
                    help="emit machine-readable JSON instead of a human report")
    ap.add_argument("--check", action="store_true",
                    help="exit 1 if >=1 finding (CI-ready). Without it, "
                         "exit 0 on success regardless of findings.")
    ap.add_argument("--include-all", action="store_true",
                    help="do NOT exclude out-of-scope zones (Roo-Code/Corrections "
                         "transcripts, Argumentum generated reports, *_output.ipynb "
                         "artefacts). By default these are excluded (#10097); use "
                         "this to audit the raw corpus including journal noise.")
    args = ap.parse_args(argv)

    # Count out-of-scope files for the exclusion summary (makes the reduced count
    # explicit -- a silently lower total could hide a regression).
    if args.include_all:
        targets = list(iter_targets(args.paths, include_all=True))
        excluded = []
    else:
        all_targets = list(iter_targets(args.paths, include_all=True))
        excluded = [t for t in all_targets if _is_out_of_scope(t)[0]]
        in_scope = [t for t in all_targets if not _is_out_of_scope(t)[0]]
        targets = in_scope
    if not targets:
        sys.stderr.write(
            "scan_md_table_syntax: rien a scanner sous "
            f"{args.paths} (aucun .ipynb/.md/README*). Exit 2.\n")
        return 2

    results = [scan_path(t) for t in targets]
    total = sum(len(r["findings"]) for r in results)

    if args.as_json:
        print(json.dumps({"total_findings": total, "files": results},
                         ensure_ascii=False, indent=1))
    else:
        flagged = [r for r in results if r["findings"]]
        for r in flagged:
            print(f"\n=== {r['path']} ({len(r['findings'])} defaut(s)) ===")
            for f in r["findings"]:
                loc = f.get("cell_index")
                locstr = f"cell[{loc}]" if loc is not None else f"L{f['line']}"
                if loc is not None:
                    locstr = f"cell[{loc}] L{f['line']}"
                print(f"  [{f['pathology']}] {locstr}: {f['detail']}")
                print(f"      {f['snippet']!r}")
        print(f"\nTotal: {total} defaut(s) sur {len(flagged)}/{len(results)} "
              f"fichier(s) scanne(s).")
        if excluded:
            from collections import Counter
            reasons = Counter(_is_out_of_scope(t)[1] for t in excluded)
            rstr = ", ".join(f"{n} {r}" for r, n in reasons.items())
            print(f"        ({len(excluded)} fichier(s) hors-scope exclus: {rstr}; "
                  f"--include-all pour le corpus brut, #10097)")

    if args.check and total > 0:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
