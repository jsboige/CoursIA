"""Ratchet gate: no NEW ``subprocess`` call with ``text=True`` and no ``encoding=``.

Issue #13140 (generalisation of #12813/#12811): on Windows hosts and runners
whose locale is cp1252, ``subprocess.run(..., text=True)`` without ``encoding=``
decodes child output with the locale codec and raises ``UnicodeDecodeError``
the moment the payload contains UTF-8 bytes undefined in cp1252 (0x81/0x8D/
0x8F/0x90/0x9D -- frequent in the ICT symbols, French prose and notebook JSON
this repository processes). That exact class killed the lane-claim guard in
production (#12811).

This gate enforces the ratchet half only: a defect is reported iff it appears
in a file the change touches. The retroactive sweep (98 sites measured on
main, 2026-08-26) lands tranche by tranche in its own PRs; untouched files
with the defect never enter the diff, so the gate is green on main from day
one (same design as check_papermill_ratchet.py, #11155).

Detection follows the issue's measurement methodology: each
``subprocess.<fn>(`` call is parsed with balanced parentheses, and the call is
a violation iff it sets ``text=True`` (or the legacy alias
``universal_newlines=True``) without any ``encoding=`` kwarg in the same call
-- including when ``encoding=`` sits on a separate line of a multiline call.

Usage (two modes):
    python check_subprocess_encoding.py <file.{py,ipynb}> [file2 ...]
        Scan the given files (pre-commit mode: pre-commit passes the staged
        filenames). For .ipynb inputs, every Python code cell whose source
        contains a violating call is reported as ``path:cell_NN:line``.

    python check_subprocess_encoding.py --base origin/main
        Scan every .py/.ipynb file changed between merge-base(REF, HEAD)
        and HEAD, reading the working tree (in CI the checkout IS the head).

Exit code 1 iff at least one violation is reported. Vendored / external
subtrees (see EXCLUDE_MARKERS) are out of scope in both modes.

# ``.ipynb`` rationale (#19475): the ratchet hook filters on
# ``files: '\\.py$'``, but the defect class (cp1252 host decoding UTF-8
# payload from a subprocess returning ``text=True`` without ``encoding=``)
# lives almost exclusively in notebook code cells -- 19 sites were fixed
# under the #15629 sweep (Lean-03b, 12, 14, 15, 16a, 16b, 17c, 21c, 34, ...),
# every one in source of a cell. The extension reuses ``scan_source``
# unchanged: a code cell's text is extracted
# (``"".join(cell.get("source", []) or [])``), and any violation found
# inside is reported with the cell index for the reviewer's eye. The
# prose-suppression tokenize pass is reused as-is -- a markdown cell
# carries no executable source, but if it were ever scanned the
# suppression would still filter docstrings. The retroactive-clean
# invariant is preserved: only the notebooks a commit touches are
# scanned, so untouched notebooks with the historical defect stay
# invisible to the gate.

Known-good fix forms: ``encoding="utf-8", errors="replace"`` -- or the
single-quote variant ``encoding='utf-8', errors='replace'`` when the call
lives inside an f-string expression, where nested double quotes are a
SyntaxError before Python 3.12.
"""

from __future__ import annotations

import argparse
import io
import re
import subprocess
import sys
import tokenize
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent

# Vendored / external subtrees: outside the audit of production code
# (same perimeter as code-style.md and the #13140 sweep).
EXCLUDE_MARKERS = (
    "/.lake/", "/_peters/", "/reference_docs/", "/foundry-lib/lib/",
    "/.venv/", "/site-packages/", "/node_modules/",
)

_SUBPROC_CALL = re.compile(
    r"\bsubprocess\.(run|Popen|check_output|check_call|call)\s*\("
)


def excluded(path: str) -> bool:
    norm = path.replace("\\", "/")
    return any(marker in f"/{norm}" for marker in EXCLUDE_MARKERS)


def _prose_spans(src: str) -> list[tuple[int, int]]:
    """Absolute (start, end) offsets of comments and non-f string literals.

    Prose mentioning the pattern (docstrings, comments -- including this
    file's own module docstring) must not be flagged. F-strings are exempt
    from suppression on purpose: a real subprocess call can live inside an
    f-string expression (setup_hooks.py L225, #13140 tranche 2), and that
    site must stay detectable.
    """
    spans: list[tuple[int, int]] = []
    # Absolute offset of the start of each line (tokenize works row/col).
    line_starts = [0]
    for line in src.splitlines(keepends=True):
        line_starts.append(line_starts[-1] + len(line))
    try:
        tokens = tokenize.generate_tokens(io.StringIO(src).readline)
        for tok in tokens:
            if tok.type == tokenize.COMMENT:
                kind = "c"
            elif tok.type == tokenize.STRING:
                kind = "s"
            elif tok.type == getattr(tokenize, "FSTRING_MIDDLE", -1):
                kind = "f"  # 3.12+: literal prose inside f-strings
            else:
                continue
            if kind == "s":
                raw = tok.string.lstrip("rbRBuU")
                if raw[:1] in ("f", "F"):
                    continue  # f-string: scan inside, do not suppress
            start = line_starts[tok.start[0] - 1] + tok.start[1]
            end = line_starts[tok.end[0] - 1] + tok.end[1]
            spans.append((start, end))
    except (tokenize.TokenError, IndentationError, SyntaxError):
        pass  # unparseable source: scan raw, may flag prose (fail-open on prose)
    return spans


def _in_spans(offset: int, spans: list[tuple[int, int]]) -> bool:
    return any(s <= offset < e for s, e in spans)


def scan_source(src: str) -> list[tuple[int, str]]:
    """Return (1-based line, one-line snippet) for each violating call."""
    prose = _prose_spans(src)
    findings: list[tuple[int, str]] = []
    for m in _SUBPROC_CALL.finditer(src):
        if _in_spans(m.start(), prose):
            continue
        i = m.end() - 1
        depth, j = 1, i + 1
        while j < len(src) and depth:
            if src[j] == "(":
                depth += 1
            elif src[j] == ")":
                depth -= 1
            j += 1
        call = src[i:j]
        sets_text = re.search(r"\b(?:text|universal_newlines)\s*=\s*True\b", call)
        if sets_text and not re.search(r"\bencoding\s*=", call):
            line = src.count("\n", 0, m.start()) + 1
            snippet = " ".join(call.split())[:100]
            findings.append((line, snippet))
    return findings


def git_out(*args: str) -> str | None:
    try:
        proc = subprocess.run(
            ["git", *args], cwd=REPO_ROOT, capture_output=True,
            encoding="utf-8", errors="replace", check=False,
        )
    except OSError:
        return None
    return proc.stdout if proc.returncode == 0 else None


def scan_ipynb(path: str) -> list[tuple[int, int, str]]:
    """Return (cell_index, 1-based line, snippet) for each violating call found
    inside any code-cell of a Jupyter notebook.

    The notebook's ``cells`` list is walked; only cells with
    ``cell_type == "code"`` are scanned (markdown cells carry prose the
    prose-suppression pass would filter anyway, but we skip them to stay
    consistent with the notebook's kernel contract). Each cell's ``source``
    (a list of strings in nbformat) is joined and fed to ``scan_source``
    unchanged -- the predicate is identical to the .py path. Findings are
    reported with the cell index so the reviewer can navigate.

    The retroactive invariant is the same as the .py ratchet: only notebooks
    the commit touches are scanned, so untouched historical defects stay
    invisible to the gate (#19475).
    """
    import json
    findings: list[tuple[int, int, str]] = []
    try:
        nb = json.loads(Path(path).read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError):
        return findings  # unparseable notebook: skip silently (pre-commit path)
    for idx, cell in enumerate(nb.get("cells", []) or []):
        if cell.get("cell_type") != "code":
            continue
        src = "".join(cell.get("source", []) or [])
        if not src.strip():
            continue
        for line, snippet in scan_source(src):
            findings.append((idx, line, snippet))
    return findings


def changed_python_files(base: str) -> list[str]:
    """Files changed between merge-base(base, HEAD) and HEAD
    (paths for .py and .ipynb; other extensions are ignored)."""
    mb = git_out("merge-base", base, "HEAD")
    if mb is None:
        # No common ancestor (orphan branch): fall back to base tip.
        mb = base
    out = git_out("diff", "--name-only", "--diff-filter=AM", mb.strip(), "HEAD")
    if out is None:
        return []
    keep = (".py", ".ipynb")
    return [l.strip() for l in out.splitlines()
            if l.strip().endswith(keep) and not excluded(l.strip())]


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(
        description="Refuse NEW subprocess text=True calls without encoding=")
    p.add_argument("files", nargs="*", help="files to scan (pre-commit mode)")
    p.add_argument("--base", default=None, metavar="REF",
                   help="scan .py/.ipynb files changed since merge-base(REF, HEAD)")
    args = p.parse_args(argv)

    if args.base:
        targets = changed_python_files(args.base)
    else:
        targets = [
            f for f in args.files
            if (f.endswith(".py") or f.endswith(".ipynb")) and not excluded(f)
        ]

    violations = 0
    py_count = 0
    ipynb_count = 0
    for f in targets:
        path = Path(f)
        if not path.is_file():
            continue
        try:
            text = path.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError):
            continue
        if f.endswith(".ipynb"):
            ipynb_count += 1
            for cell_idx, line, snippet in scan_ipynb(f):
                violations += 1
                print(f"{f}:cell_{cell_idx:02d}:{line}: "
                      f"text=True without encoding= :: {snippet}")
        else:
            py_count += 1
            for line, snippet in scan_source(text):
                violations += 1
                print(f"{f}:{line}: text=True without encoding= :: {snippet}")

    if violations:
        print(f"\n{violations} subprocess call(s) set text=True without "
              'encoding= -- cp1252 hosts crash on UTF-8 payloads (#12811). '
              'Add encoding="utf-8", errors="replace" (single-quote variant '
              "inside f-string expressions).")
        return 1
    if args.base:
        print(f"subprocess-encoding ratchet: {py_count} .py + {ipynb_count} "
              f".ipynb = {len(targets)} changed file(s), 0 violation(s)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
