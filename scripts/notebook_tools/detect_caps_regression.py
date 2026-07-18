#!/usr/bin/env python3
"""Detect capitalization regression in markdown accent cures (#2876, #3801).

Companion GATE to ``detect_accent_stripping.py`` (the cure direction) and
``check_identifier_regression.py`` (#7157, the identifier-over-reach gate).
This tool catches a THIRD defect class those two do not cover: an accent-cure
script that **lowercases the initial capital** of a token when restoring its
accent.

Defect signature (caught firsthand on PRs #7191 / #7185, tiebreaker c.484):

    main  (heading) : "## 3. Modele Deux Joueurs"
    branch (cured)  : "## 3. modele Deux Joueurs"      <- WRONG (should be "Modèle")

    main  (nav)     : "| Precedent | Suivant |"
    branch (cured)  : "| precedent | Suivant |"        <- WRONG (should be "Précédent")

    main  (table)   : "| **Equipes** | Moyenne ..."
    branch (cured)  : "| **equipes** | Moyenne ..."    <- WRONG (should be "Équipes")

The cure script restored the accent but used the dictionary's lowercase form
instead of preserving the source token's initial capital. Positions that MUST
keep the capital (headings ``#``, nav links, table headers ``|``, list items
``N. `` / ``- ``, bold ``**``) become visibly broken.

Why ``check_identifier_regression.py`` (#7157) does not catch this : it scans
CODE-cell identifiers (Python/C#), not markdown prose. The caps defect is a
MARKDOWN-prose defect, so it sails past the identifier gate. This tool fills
that gap by comparing base (main) vs head (branch) MARKDOWN cell sources.

Contract
--------
Input : a BASE notebook (origin/main) and a HEAD notebook (the PR branch).
For each markdown cell, line-align the sources and compare word-by-word at
each position. A regression is a position where:

  (1) the base word and head word differ,
  (2) the head word carries an accent (``unicodedata`` category Mn after NFD),
  (3) stripping the accent from the head word yields the base word
      (case-insensitive) -- i.e. it IS an accent cure of that token, AND
  (4) the base word started with an uppercase letter that the head word
      lowercased.

Structural lines (word-count mismatch between base and head -- the cure
changed the number of tokens, not just substituted accents) are SKIPPED :
accent cures are 1:1 substitutions, so a count mismatch means the line is not
a pure cure and positional comparison would misalign. This keeps the detector
free of the false-positive mode that tripped up earlier non-positional scans.

Exit codes : 0 = clean, 1 = regression(s) found, 2 = error (unreadable base/head).

Usage
-----
Two invocation modes :

    # 1. Direct-file mode : two explicit notebook files
    python detect_caps_regression.py --base main_nb.ipynb --head branch_nb.ipynb

    # 2. Git-ref mode : point at one notebook, compare two git refs of it.
    #    Head defaults to the working-tree notebook on disk (no need to extract).
    python detect_caps_regression.py NB.ipynb --base origin/main --head origin/branch
    python detect_caps_regression.py NB.ipynb --base origin/main          # head = disk

    # JSON output for CI  / quiet (exit code only)
    python detect_caps_regression.py ... --json
    python detect_caps_regression.py ... --quiet       # or --check (#7197 alias)

See #2876, #3801. Companion to detect_accent_stripping.py, check_identifier_regression.py (#7157),
restore_accents_canonical.py (#7186).
"""
import argparse
import json
import re
import subprocess
import sys
import unicodedata
from pathlib import Path

# A word = run of letters incl. accented Latin. Used for positional alignment.
_WORD_RE = re.compile(r"[A-Za-zÀ-ÖØ-öø-ÿ]+", re.UNICODE)


def _strip_accents(token: str) -> str:
    """Return the accent-stripped form of a token (NFD + drop combining marks).

    ``"système"`` -> ``"systeme"``, ``"précédent"`` -> ``"precedent"``,
    ``"Équipes"`` -> ``"Equipes"``. Robust and decoupled from any dictionary :
    works on ANY accented token, not just the curated ``ACCENT_PAIRS`` set.
    """
    decomposed = unicodedata.normalize("NFD", token)
    return "".join(ch for ch in decomposed if unicodedata.category(ch) != "Mn")


def _has_accent(token: str) -> bool:
    """True if the token loses at least one char under accent-stripping."""
    return _strip_accents(token) != token


def _words(line: str) -> list[tuple[str, int]]:
    """Ordered (word, column) pairs in a line, used for positional alignment."""
    return [(m.group(0), m.start()) for m in _WORD_RE.finditer(line)]


def _classify_position(line: str, col: int, token: str) -> str:
    """Best-effort label for WHERE the token sits (helps the human report).

    Not used for the verdict -- the verdict is pure case-preservation. This
    only annotates the hit so a reviewer sees "heading"/"nav"/"table"/"list".
    """
    prefix = line[:col].rstrip()
    # Heading : line starts with markdown header markers.
    if re.match(r"\s*#{1,6}\s", line):
        return "heading"
    # Table header / cell : token follows a pipe (possibly with bold/markup).
    if prefix.endswith("|") or prefix.endswith("| **") or prefix.endswith("| *"):
        return "table"
    # Nav column (common pattern ``| Precedent | Suivant |``).
    if "| precedent |" in line.lower() or "| suivant |" in line.lower():
        return "nav"
    # List item : line starts with ``N. `` or ``- `` / ``* ``.
    if re.match(r"\s*(?:[0-9]+\.|[-*])\s", line):
        return "list"
    # Bold lead : token right after ``**``.
    if prefix.endswith("**"):
        return "bold"
    # First non-space token of the line (sentence start).
    if not prefix:
        return "sentence-start"
    return "prose"


def _check_line(base_line: str, head_line: str):
    """Yield (base_token, head_token, column, position) for each caps regression.

    Positional and exact : base/head words are aligned by index within the line.
    A line whose word count differs between base and head is SKIPPED (a pure
    accent cure preserves the token count ; a mismatch means structural change,
    not a cure, and positional comparison would misalign).
    """
    bw = _words(base_line)
    hw = _words(head_line)
    if len(bw) != len(hw):
        return  # structural change -- not a pure cure line, skip
    for (b_tok, b_col), (h_tok, _h_col) in zip(bw, hw):
        if b_tok == h_tok:
            continue
        if not _has_accent(h_tok):
            continue
        # Is h_tok an accent cure of b_tok (same letters modulo case + accents)?
        if _strip_accents(h_tok).lower() != b_tok.lower():
            continue
        # Case loss : base was initial-capital, head lowercased it.
        if b_tok[:1].isupper() and h_tok[:1].islower():
            pos = _classify_position(base_line, b_col, b_tok)
            yield (b_tok, h_tok, b_col, pos)


def _cell_source_lines(cell: dict) -> list[str]:
    """Markdown source as a list of lines (handles str OR nbformat list form)."""
    s = cell.get("source", [])
    if isinstance(s, str):
        return s.splitlines()
    out = []
    for chunk in s:
        out.extend(chunk.splitlines())
    return out


def _compare_notebooks(base_nb: dict, head_nb: dict) -> list[dict]:
    """Compare two in-memory notebooks, return the list of regression dicts.

    Shared core of :func:`scan_pair` (direct-file mode) and :func:`scan_ref_mode`
    (git-ref mode). Cell-by-cell : only markdown cells are in scope (code cells
    are the identifier gate's job, #7157). If the cell counts differ we still
    compare index-by-index up to the shorter list ; a count mismatch is itself a
    structural signal but not this detector's concern.
    """
    base_cells = base_nb.get("cells", [])
    head_cells = head_nb.get("cells", [])
    regressions = []
    for ci, (bc, hc) in enumerate(zip(base_cells, head_cells)):
        if bc.get("cell_type") != "markdown" or hc.get("cell_type") != "markdown":
            continue
        blines = _cell_source_lines(bc)
        hlines = _cell_source_lines(hc)
        for li, (bl, hl) in enumerate(zip(blines, hlines)):
            if bl == hl:
                continue
            for b_tok, h_tok, col, pos in _check_line(bl, hl):
                regressions.append({
                    "cell_index": ci,
                    "line_no": li,
                    "column": col,
                    "base_token": b_tok,
                    "head_token": h_tok,
                    "position": pos,
                    "base_line": bl,
                })
    return regressions


def scan_pair(base_path: Path, head_path: Path) -> dict:
    """Direct-file mode : compare two notebooks on disk, return a result dict.

    ``{"path": str, "regressions": [...], "error": str | None}`` where each
    regression is ``{cell_index, line_no, base_token, head_token, column,
    position, base_line}``.
    """
    try:
        base_nb = json.loads(base_path.read_text(encoding="utf-8"))
    except Exception as e:  # noqa: BLE001 -- report any read/parse failure as error
        return {"path": str(head_path), "regressions": [], "error": f"base unreadable: {e}"}
    try:
        head_nb = json.loads(head_path.read_text(encoding="utf-8"))
    except Exception as e:  # noqa: BLE001
        return {"path": str(head_path), "regressions": [], "error": f"head unreadable: {e}"}
    return {"path": str(head_path),
            "regressions": _compare_notebooks(base_nb, head_nb), "error": None}


def _git_show_notebook(ref: str, path: str, cwd=None):
    """Read a notebook at a git ref via ``git show <ref>:<path>``.

    Returns the parsed nbformat dict, or ``None`` if the ref/path is unreadable
    (missing blob, bad ref, JSON parse error). ``None`` (not a raised exception)
    lets the caller distinguish "base unreadable" from "head unreadable" and
    surface a precise error, mirroring :func:`scan_pair`. ``cwd`` is the
    directory to run git in (defaults to the process cwd -- for CLI use, the
    worker is at the repo root ; exposed for testing with a tmp git repo).
    """
    r = subprocess.run(["git", "show", f"{ref}:{path}"], capture_output=True, cwd=cwd)
    if r.returncode != 0:
        return None
    try:
        return json.loads(r.stdout.decode("utf-8"))
    except Exception:  # noqa: BLE001 -- any parse failure = "unreadable at ref"
        return None


def scan_ref_mode(notebook_path: Path, base_ref: str, head_ref, cwd=None) -> dict:
    """Git-ref mode : point at ONE notebook and compare two git refs of it.

    Worker-ergonomic alternative to :func:`scan_pair` -- no need to extract the
    base/head files first. Mirrors the invocation workers learned on
    ``check_caps_regression.py`` (#7197) so disposing that duplicate is lossless:

        detect_caps_regression.py NB.ipynb --base origin/main --head origin/branch
        detect_caps_regression.py NB.ipynb --base origin/main   # head = working tree

    ``notebook_path`` : the notebook on disk (used for head when ``head_ref`` is
    None AND to resolve the repo-relative path for ``git show``).
    ``base_ref``     : git ref for the base (default ``origin/main`` at the CLI).
    ``head_ref``     : git ref for the head, OR ``None`` to read the head
                       notebook from the working tree (the on-disk file).
    ``cwd``          : directory to run git in (defaults to process cwd).
    """
    # Resolve a repo-relative path for `git show` (git wants forward slashes and
    # a path relative to the repo root, not the cwd).
    git_path = str(notebook_path).replace("\\", "/")
    base_nb = _git_show_notebook(base_ref, git_path, cwd=cwd)
    if base_nb is None:
        return {"path": str(notebook_path), "regressions": [],
                "error": f"base unreadable at git ref {base_ref}:{git_path}"}

    if head_ref is None:
        # Head = working tree : read the on-disk notebook.
        if not notebook_path.exists():
            return {"path": str(notebook_path), "regressions": [],
                    "error": f"head unreadable: {notebook_path} not on disk and no --head given"}
        try:
            head_nb = json.loads(notebook_path.read_text(encoding="utf-8"))
        except Exception as e:  # noqa: BLE001
            return {"path": str(notebook_path), "regressions": [],
                    "error": f"head unreadable (disk): {e}"}
    else:
        head_nb = _git_show_notebook(head_ref, git_path, cwd=cwd)
        if head_nb is None:
            return {"path": str(notebook_path), "regressions": [],
                    "error": f"head unreadable at git ref {head_ref}:{git_path}"}

    return {"path": str(notebook_path),
            "regressions": _compare_notebooks(base_nb, head_nb), "error": None}


def _human_report(result: dict) -> str:
    """Plain-text report for terminal use."""
    path = result["path"]
    regs = result["regressions"]
    if result["error"]:
        return f"ERROR ({path}): {result['error']}"
    if not regs:
        return f"OK   ({path}): 0 caps-regression"
    out = [f"HIT  ({path}): {len(regs)} caps-regression(s)"]
    for r in regs[:20]:
        out.append(
            f"  cell {r['cell_index']} L{r['line_no']} [{r['position']}] "
            f"{r['base_token']!r} -> {r['head_token']!r}"
        )
        out.append(f"      base: {r['base_line'][:90]!r}")
    if len(regs) > 20:
        out.append(f"  ... +{len(regs) - 20} more")
    return "\n".join(out)


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Detect markdown caps-regression in accent cures. Two modes:\n"
            "  direct-file : --base FILE --head FILE\n"
            "  git-ref     : NOTEBOOK.ipynb --base origin/main --head origin/branch"
            " (head defaults to working tree)\n"
        ),
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("notebook", nargs="?", default=None,
                        help="git-ref mode : point at one notebook, compare two git refs of it")
    parser.add_argument("--base", default=None,
                        help="direct mode = base notebook FILE ; git-ref mode = base git ref "
                             "(default origin/main)")
    parser.add_argument("--head", default=None,
                        help="direct mode = head notebook FILE ; git-ref mode = head git ref "
                             "(default = working-tree notebook on disk)")
    parser.add_argument("--json", action="store_true", help="machine-readable JSON output")
    parser.add_argument("--quiet", action="store_true", help="no stdout (exit code only)")
    parser.add_argument("--check", action="store_true",
                        help="alias of --quiet (CI-ready exit code) -- #7197 muscle memory")
    args = parser.parse_args(argv)

    quiet = args.quiet or args.check

    if args.notebook is not None:
        # Git-ref mode : point at one notebook, compare two git refs of it.
        base_ref = args.base or "origin/main"
        result = scan_ref_mode(Path(args.notebook), base_ref, args.head)
    else:
        # Direct-file mode : two explicit notebook files.
        if not args.base or not args.head:
            parser.error(
                "direct-file mode requires --base FILE and --head FILE "
                "(or use git-ref mode: NOTEBOOK.ipynb --base origin/main --head origin/branch)")
        result = scan_pair(Path(args.base), Path(args.head))

    if args.json:
        print(json.dumps(result, ensure_ascii=False, indent=2))
    elif not quiet:
        print(_human_report(result))

    if result["error"]:
        return 2
    return 1 if result["regressions"] else 0


if __name__ == "__main__":
    sys.exit(main())
