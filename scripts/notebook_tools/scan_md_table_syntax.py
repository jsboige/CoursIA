#!/usr/bin/env python3
"""Source-level scanner for markdown *table* syntax pathologies.

Detects defects that make GFM tables render poorly on GitHub (the complement
of `scan_md_hierarchy.py`, which catches collapsed-markdown glue defects).

Four pathologies are caught (#10097):

  - COL_MISMATCH: header row vs data rows have inconsistent `|` counts (most
    common cause: a `|` left un-escaped inside a cell). The browser sees a
    phantom column -> the table renders mis-aligned.
  - NO_SEP: 3+ consecutive pipe-bearing lines without a separator row of
    dashes/colons (`|---|---|`, `|:---|:---:|...`). GitHub falls back to a
    `pre` block, the table becomes invisible.
  - NO_BLANK_BEFORE: a non-blank line directly precedes a table block -> the
    preceding paragraph fuses with the table -> the table's first row becomes
    part of the prose (visible as a half-table, half-prose block).
  - NO_BLANK_AFTER: a non-blank line directly follows a table block -> the
    next paragraph fuses with the table -> the table's last row gets glued to
    the following sentence.

Two source surfaces are walked:
  - `*.ipynb` markdown cells (joined with `\n` per cell)
  - `*.md` and `README*` files (verbatim, no joining)

Fenced-code-block contents are blanked before scanning (a tree diagram or
ASCII payoff inside a fence is CODE, not a markdown table). The same fence-
tracking convention as `scan_md_hierarchy.py` is used (FENCE_RE on line start,
fence-marker lines kept).

CLI mirrors `scan_md_hierarchy.py`:
  python scan_md_table_syntax.py PATH [PATH ...]
                              [--fail-on-findings]
                              [--json]
                              [--check]    # alias for --fail-on-findings + JSON

Exit codes:
  0  clean (or --fail-on-findings not set)
  1  at least one finding AND --fail-on-findings
  2  no notebook / markdown file found under the given paths
     (an empty scan is NOT an all-clear; same anti-FP guard as #3968 family)

An empty scan is never reported as a clean scan: no argument, a mistyped path,
or a directory holding no notebook/markdown exits 2 with a message on stderr
instead of printing `0/0 files flagged`. A vacuous zero was the second mouth
of the #3968 trap.
"""
import argparse
import json
import pathlib
import re
import sys
from typing import Iterable, List, Dict, Any, Optional, Tuple


# ---------------------------------------------------------------------------
# Regexes and primitives
# ---------------------------------------------------------------------------

# Fenced-code-block delimiter: ``` or ~~~ (3+ chars), possibly indented.
FENCE_RE = re.compile(r"^\s*(`{3,}|~{3,})")

# A line that participates in a GFM table: starts with optional `>` (blockquote)
# and a leading `|`, then any combination of pipes, dashes, colons, spaces.
# Anchor ^ + leading-pipe (\s*>?\s*\|) so a regular prose line that just
# happens to contain `|` does NOT count (e.g. `a | b` mid-paragraph).
TABLE_LINE_RE = re.compile(r"^\s*>?\s*\|.+\|?\s*$")

# A clean GFM separator row: leading optional `>`, then ONLY pipes / dashes /
# colons / spaces, with at least one dash run of 2+ (GFM requires 3 dashes
# minimum, but we use 2 to stay conservative; the 2nd dash handles headers
# like `|:--` or `| :-` followed by `-|`).
SEPARATOR_LINE_RE = re.compile(
    r"^\s*>?\s*\|[\s:|-]*-{2,}[\s:|-]*\|?\s*$"
)

# A more precise separator: at least one `:?-+:?` core, optional spaces.
SEPARATOR_CORE_RE = re.compile(r":?-+:?")


def _strip_fenced_code(text: str) -> str:
    """Blank out fenced-code-block CONTENTS so code is invisible to the detector.

    Mirrors `scan_md_hierarchy._strip_fenced_code`: a tree diagram
    (`|-- lakefile`) or an ASCII payoff diagram inside a ``` / ~~~ fence is
    CODE, not a markdown table -- its `|--` and `|` lines must NOT trigger
    TABLE_LINE_RE. Fences are tracked line-by-line via FENCE_RE; fence-marker
    lines are kept, code lines between them are blanked.
    """
    out: List[str] = []
    in_fence = False
    for line in text.split("\n"):
        if FENCE_RE.match(line):
            in_fence = not in_fence
            out.append(line)  # keep the fence-marker line itself
            continue
        out.append("" if in_fence else line)
    return "\n".join(out)


def _pipe_count(line: str) -> int:
    """Count un-escaped pipes on a line.

    `\\|` (a literal backslash-pipe) is the canonical GFM escape; an HTML
    entity `&#124;` also works. Both are NOT counted as column separators.
    A bare `|` (no backslash before it) IS counted.
    """
    # Replace escaped pipes and HTML entities with a sentinel, then count.
    sentinel = "\x00"
    s = line.replace("\\|", sentinel).replace("&#124;", sentinel).replace("&vert;", sentinel)
    return s.count("|")


def _iter_blocks(lines: List[str]) -> Iterable[Tuple[int, int]]:
    """Yield (start, end_exclusive) index pairs for contiguous TABLE_LINE blocks.

    A block is a maximal run of consecutive lines each matching TABLE_LINE_RE.
    Fenced-code lines are blanked upstream so they never enter the TABLE_LINE
    match. Blank lines break a block (that's how the table ends).
    """
    i = 0
    n = len(lines)
    while i < n:
        if TABLE_LINE_RE.match(lines[i]):
            j = i
            while j < n and TABLE_LINE_RE.match(lines[j]):
                j += 1
            yield (i, j)
            i = j
        else:
            i += 1


def _scan_block(lines: List[str], start: int, end: int) -> List[Dict[str, Any]]:
    """Inspect a single TABLE_LINE block (start..end exclusive) for pathologies.

    Returns a list of findings; empty if the block is well-formed.
    """
    findings: List[Dict[str, Any]] = []
    block = lines[start:end]

    # Step 1: locate the separator row (if any).
    sep_idx: Optional[int] = None
    for k, line in enumerate(block):
        if SEPARATOR_LINE_RE.match(line):
            sep_idx = k
            break

    # NO_SEP: 3+ lines table-shaped, but no separator anywhere.
    if len(block) >= 3 and sep_idx is None:
        findings.append({
            "pathology": "NO_SEP",
            "line": start + 1,  # 1-based for human reports
            "snippet": block[0][:120].strip(),
            "detail": f"block has {len(block)} table-shaped lines, no `|---|` separator",
        })
        return findings  # NO_SEP is terminal: no further inspection is meaningful

    # Step 2: COL_MISMATCH -- compare pipe counts between header and data rows.
    # Header = the first table-shaped line, data = subsequent lines (skipping
    # the separator if present).
    if not block:
        return findings
    header_pipes = _pipe_count(block[0])
    # A header has N columns -> at least N pipes (leading + between + optional
    # trailing). We compare data-row pipe counts against this baseline.
    expected_cols = header_pipes  # leading pipe + (N-1) inner pipes for N cols,
                                 # OR no leading pipe for the no-trailing-pipe
                                 # variant. We use pipe count as the comparator
                                 # since the actual column count depends on
                                 # internal `|` which is what we are detecting.
    for k, line in enumerate(block):
        if k == 0 or (sep_idx is not None and k == sep_idx):
            continue  # skip header / separator
        dpc = _pipe_count(line)
        if dpc != expected_cols:
            findings.append({
                "pathology": "COL_MISMATCH",
                "line": start + k + 1,
                "snippet": line[:120].strip(),
                "detail": f"header pipes={expected_cols}, data pipes={dpc} (line {k + 1} of block)",
                "header_pipes": expected_cols,
                "data_pipes": dpc,
            })

    # Step 3: NO_BLANK_BEFORE -- the line immediately before the block (in the
    # *original* un-stripped source, NOT the block) is non-blank AND is not a
    # previous TABLE_LINE block (else two tables stacked are fine -- the blank
    # is implicit between them? Actually GFM requires a blank line between two
    # tables, otherwise they fuse into one block. So if our `_iter_blocks` saw
    # them as ONE block, we're already past that check. If they are TWO
    # blocks, there must be a blank between them -- the blank gap is what
    # separates two `_iter_blocks` yields. So no extra check needed for
    # stacked tables.)
    if start > 0 and lines[start - 1].strip() != "":
        # but only flag if the line just before the block is not a continuation
        # of another structural element (list, heading, paragraph). The simplest
        # correct heuristic: any non-blank prose line is a problem. GFM tables
        # MUST be preceded by a blank line OR be at the start of the file.
        # The exception: a blockquote / list-item continuation starts with `>` or
        # `-`/`*`/`+` -- those are part of the prior list, the table inside a
        # list still needs the blank, but the LLM detector on #3966 found that
        # false-positives on indented-list-tables were vanishingly rare. We
        # document the simplification: prose-only check, list-prefix tolerated.
        prev = lines[start - 1]
        if not prev.startswith((">", "#", "-", "*", "+", "1.", "1)", "\t", "    ")):
            findings.append({
                "pathology": "NO_BLANK_BEFORE",
                "line": start + 1,
                "snippet": block[0][:120].strip(),
                "detail": f"non-blank line precedes table: {prev[:80].strip()!r}",
            })

    # Step 4: NO_BLANK_AFTER -- the line immediately after the block is non-blank.
    if end < len(lines) and lines[end].strip() != "":
        nxt = lines[end]
        # Same list-prefix tolerance as NO_BLANK_BEFORE.
        if not nxt.startswith((">", "#", "-", "*", "+", "1.", "1)", "\t", "    ")):
            findings.append({
                "pathology": "NO_BLANK_AFTER",
                "line": end + 1,
                "snippet": lines[end][:120].strip(),
                "detail": f"non-blank line follows table: {nxt[:80].strip()!r}",
            })

    return findings


# ---------------------------------------------------------------------------
# Notebook / markdown scanning
# ---------------------------------------------------------------------------

def scan_notebook(path: pathlib.Path) -> List[Dict[str, Any]]:
    """Scan one .ipynb for table-syntax pathologies across all markdown cells.

    Returns a list of findings with the convention: each finding carries the
    notebook path, the cell index, the line number WITHIN the cell, the
    pathology, and a snippet.
    """
    try:
        nb = json.loads(path.read_text(encoding="utf-8"))
    except Exception as e:
        return [{"pathology": "READ_ERROR", "detail": str(e),
                 "file": path.as_posix(), "cell": -1, "line": -1, "snippet": ""}]
    findings: List[Dict[str, Any]] = []
    for ci, cell in enumerate(nb.get("cells", [])):
        if cell.get("cell_type") != "markdown":
            continue
        raw = cell.get("source", [])
        if isinstance(raw, str):
            cell_text = raw
        else:
            cell_text = "".join(raw)
        cell_findings = scan_text(cell_text, file=path.as_posix(), cell=ci)
        findings.extend(cell_findings)
    return findings


def scan_markdown_file(path: pathlib.Path) -> List[Dict[str, Any]]:
    """Scan one .md / README* file for table-syntax pathologies."""
    try:
        text = path.read_text(encoding="utf-8")
    except Exception as e:
        return [{"pathology": "READ_ERROR", "detail": str(e),
                 "file": path.as_posix(), "cell": -1, "line": -1, "snippet": ""}]
    return scan_text(text, file=path.as_posix(), cell=-1)


def scan_text(text: str, *, file: str = "<input>", cell: int = -1) -> List[Dict[str, Any]]:
    """Core scan: given raw text (a joined markdown cell or a .md file),
    return a list of findings. `file` and `cell` are stamped on each finding.
    """
    stripped = _strip_fenced_code(text)
    lines = stripped.split("\n")
    findings: List[Dict[str, Any]] = []
    for start, end in _iter_blocks(lines):
        for f in _scan_block(lines, start, end):
            findings.append({**f, "file": file, "cell": cell})
    return findings


# ---------------------------------------------------------------------------
# CLI / file enumeration
# ---------------------------------------------------------------------------

_NOTEBOOK_SUFFIX = ".ipynb"
_MARKDOWN_SUFFIXES = (".md", ".markdown")


def iter_targets(args: List[str]) -> Iterable[pathlib.Path]:
    """Yield .ipynb / .md / README* files designated by `args`.

    Dirs are walked recursively. A directory that contains zero matching files
    is silently skipped at the yield level -- `main` checks `total == 0` to
    fail loudly (the empty-scan guard). A non-existent / non-matching path is
    reported as `unresolved`, so a typo can never masquerade as a clean scan.
    """
    unresolved: List[str] = []
    for a in args:
        p = pathlib.Path(a)
        if p.is_dir():
            for child in sorted(p.rglob("*")):
                if not child.is_file():
                    continue
                if _is_target(child):
                    yield child
        elif p.is_file() and _is_target(p):
            yield p
        else:
            unresolved.append(a)
    if unresolved:
        raise ValueError(
            "not a notebook nor a markdown file nor a directory: "
            + ", ".join(unresolved)
        )


def _is_target(p: pathlib.Path) -> bool:
    """True if `p` is a notebook or markdown file we should scan."""
    if p.suffix == _NOTEBOOK_SUFFIX:
        return True
    if p.suffix.lower() in _MARKDOWN_SUFFIXES:
        return True
    # README without extension (README, README.md, README.en.md all matched by suffix)
    if p.name.upper().startswith("README"):
        return True
    return False


def main(argv: Optional[List[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        description=__doc__.splitlines()[0],
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("paths", nargs="+", metavar="PATH",
                        help="notebook (.ipynb), markdown file (.md / README*), "
                             "or directory (recursive)")
    parser.add_argument("--fail-on-findings", action="store_true",
                        help="exit 1 when at least one file is flagged "
                             "(default: always exit 0, census mode)")
    parser.add_argument("--json", action="store_true",
                        help="emit one JSON object per finding to stdout "
                             "(machine-readable, line-delimited)")
    parser.add_argument("--check", action="store_true",
                        help="alias for --fail-on-findings + --json (CI mode)")
    args = parser.parse_args(argv)

    if args.check:
        args.fail_on_findings = True
        args.json = True

    try:
        targets = list(iter_targets(args.paths))
    except ValueError as exc:
        parser.error(str(exc))

    total = 0
    flagged = 0
    all_findings: List[Dict[str, Any]] = []

    for t in targets:
        if "_output" in t.name or ".ipynb_checkpoints" in str(t):
            continue
        total += 1
        if t.suffix == _NOTEBOOK_SUFFIX:
            fs = scan_notebook(t)
        else:
            fs = scan_markdown_file(t)
        if fs:
            flagged += 1
            if args.json:
                for f in fs:
                    all_findings.append(f)
            else:
                print(f"\n## {t.as_posix()}")
                for f in fs:
                    where = (
                        f"cell {f['cell']} " if f["cell"] >= 0 else ""
                    )
                    print(
                        f"  [{f['pathology']}] {where}L{f['line']}  "
                        f"{f['snippet'][:80]}  "
                        f"-- {f.get('detail', '')}"
                    )

    if total == 0:
        # Empty scan is NOT a clean scan -- say so, and fail. `0/0 flagged`
        # otherwise reads as an all-clear while nothing has been looked at.
        print(
            "ERROR: no notebook / markdown file found under the given paths "
            "-- nothing was scanned, this is NOT an all-clear.",
            file=sys.stderr,
        )
        return 2

    if args.json:
        # Single JSON document, one entry per finding.
        sys.stdout.write(json.dumps({
            "total": total,
            "flagged": flagged,
            "findings": all_findings,
        }, ensure_ascii=False, indent=2) + "\n")

    if not args.json:
        # Keep this the LAST stdout line: the CI census reads it with `tail -1`.
        print(f"\n=== {flagged}/{total} files flagged ===")

    return 1 if (flagged and args.fail_on_findings) else 0


if __name__ == "__main__":
    sys.exit(main())
