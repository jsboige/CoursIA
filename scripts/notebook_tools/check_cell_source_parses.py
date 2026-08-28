#!/usr/bin/env python3
"""Check that code cells in a notebook compile as valid Python.

Issue #13326 (myia-ai-01:CoursIA, 2026-08-28): no guard parses cell source.
A cell whose source is syntactically invalid (so it cannot have produced the
output it carries) crosses the 60+ checks without one red. Two instances:

  (a) PR #13287 cell -- `print(f"  donne un levier "prononce" (0.746)...")`
      -- double-quote OUTSIDE f-string substitution field: invalid in 3.11
      as in 3.14 (PEP 701 only covers the inside of `{}`).
  (b) `main` GameTheory-03d-Plan-de-deformation.ipynb cell[7] -- a markdown
      blob typed `code`, carrying an orphan output from another calculation.

This script:
  - parses each code cell whose kernel is Python with `compile(src, flags=ast.PyCF_ALLOW_TOP_LEVEL_AWAIT)`;
  - skips magics `!` / `%` (IPython, non-Python);
  - separates "syntax error" from "markdown-typed-code" (first non-empty line
    starts with `#{1,6} ` or looks like prose -- no leading `import`/`def`/`from`/`class`/`@`/`x =` etc.);
  - reports each occurrence, optionally scoped to a PR diff.

PEP 701 note
------------
Nested-quote f-strings (`print(f"{d["k"]}")`) parse on CPython 3.12+ but raise
`SyntaxError` on 3.10/3.11. The guard targets the project's CI Python
(default `--target-py 3.10`); pass `--target-py 3.12` when scanning a notebook
run on 3.12 (or later). The runtime in which the guard executes is independent
of the runtime the notebook is consumed on; on a 3.11 worker scanning a 3.12
notebook, the latter cells parse-clean only with `--target-py 3.12`.

Usage:
    python check_cell_source_parses.py                          # Whole repo, target 3.10
    python check_cell_source_parses.py --target-py 3.12          # Whole repo, target 3.12
    python check_cell_source_parses.py --path <file.ipynb>      # Single notebook
    python check_cell_source_parses.py --pr-diff origin/main    # Cells touched by a PR diff
    python check_cell_source_parses.py --json                    # JSON output

Exit codes:
    0 -- All cells parse (or only non-Python cells skipped)
    1 -- At least one compile failure (incl. markdown-typed-code)
    2 -- Error (catalog not found, unreadable notebook, etc.)
"""

import argparse
import ast
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Iterable, List, Optional, Tuple

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
NOTEBOOKS_DIR = REPO_ROOT / "MyIA.AI.Notebooks"


def _is_python_kernel(metadata: dict) -> bool:
    """A notebook with kernel Python (any minor) parses for compile(). .NET
    Interactive notebooks are skipped (their 'source' is C#/F#, not Python)."""
    ks = (metadata or {}).get("kernelspec", {}) or {}
    name = (ks.get("name") or "").lower()
    language = (ks.get("language") or "").lower()
    return name.startswith("python") or language == "python"


def _strip_ipython_magics(src: str) -> str:
    """Drop lines starting with `!` (shell) or `%` (magics incl. `%%`). The
    cell source may legitimately contain `!pip install` or `%%time` -- those
    are IPython, not Python. Naive `compile()` on the raw source would fail
    on the magic prefix and produce a false positive."""
    out_lines = []
    for line in src.splitlines():
        stripped = line.lstrip()
        if stripped.startswith("!") or stripped.startswith("%"):
            continue
        out_lines.append(line)
    return "\n".join(out_lines)


# Heuristic for "markdown typed code": the first non-empty line of the cell
# does NOT look like executable Python. Catches the instance (b) pattern
# (a `### Lecture du résultat` cell typed `code`) without false-positiving
# on legitimate code cells whose first line happens to start with `#` (e.g.
# a module docstring). The check is intentionally permissive on `code` and
# restrictive on `markdown-typed-code`: a false negative on a 1-line `#`
# docstring stays a code cell, never a markdown one.
_PROSE_RE = re.compile(r"^\s*(#{1,6}\s|\*\*[^*]|[A-ZÀ-Ž][a-zà-ž]+\s+[a-zà-ž]+.*[.!?:])")
_CODE_START_RE = re.compile(
    r"^\s*(import\s|from\s|def\s|class\s|@|async\s|"
    r"[A-Za-z_]\w*\s*=|"
    r"(?:return|raise|pass|if|for|while|with|try|except|finally)\b|"
    r"print\s*\()"
)


def _looks_like_markdown_typed_code(src: str) -> bool:
    """Return True if the first non-empty line is prose (heading or natural
    language), and the cell carries no Python-shape construct in its first
    ~5 lines. Used to disambiguate 'SyntaxError' from 'markdown typed code'
    on instance (b)."""
    lines = [ln for ln in src.splitlines() if ln.strip()]
    if not lines:
        return False
    head = "\n".join(lines[:5])
    if _PROSE_RE.match(lines[0]):
        # And nothing Python-shape in the first few lines
        if not any(_CODE_START_RE.match(ln) for ln in lines[:5]):
            return True
    return False


def _compile_cell(src: str, target_py: Tuple[int, int] = (3, 10)) -> Tuple[Optional[SyntaxError], str]:
    """Return (None, source) on success, (SyntaxError, source) on failure.
    Uses ast.PyCF_ALLOW_TOP_LEVEL_AWAIT so that `x = await foo()` (legal in
    Jupyter, instance #13326 control #1) does not false-positive. PEP 701
    nested-quote f-strings (`print(f"{d["k"]}")`) parse on 3.12+ only --
    target_py gates which constructs the guard considers valid via
    `ast.parse(feature_version=target_py)`.

    Caveat on PEP 701: feature_version gates *syntactic* acceptance but the
    parser itself is bound to the runtime's grammar tables. On a 3.11
    runtime with --target-py 3.12 the parse succeeds (feature_version
    accepts 3.12 grammar) but constructs introduced post-3.11 that require
    a 3.12+ grammar table still fail. The intended workflow: the CI runner
    is 3.12+ when a notebook uses PEP 701, and the guard runs natively
    with --target-py 3.12; no false positives. (c.672-L42 fix: previously
    target_py was plumbing-mort.)

    Note: `compile()` builtin has no `_feature_version` arg, so we use
    `ast.parse(...)` followed by `compile(ast_module, ...)` to honour the
    target version. Both `ast.PyCF_ALLOW_TOP_LEVEL_AWAIT` and
    `feature_version` apply; PEP 701 accepts the former on any runtime.
    """
    cleaned = _strip_ipython_magics(src)
    try:
        # Round-trip via ast.parse to honour feature_version, then compile
        # the AST (top-level expressions need exec mode on an Expression).
        mod = ast.parse(cleaned, "<cell>", "exec", feature_version=target_py)
        compile(mod, "<cell>", "exec", flags=ast.PyCF_ALLOW_TOP_LEVEL_AWAIT)
        return None, cleaned
    except SyntaxError as e:
        return e, cleaned


def _cells_touched_by_pr(diff_range: Iterable[str]) -> List[Path]:
    """Return the .ipynb paths modified between two refs (e.g. origin/main..HEAD)."""
    out: List[Path] = []
    for line in diff_range:
        # `git diff --name-only` line shape: 'MyIA.AI.Notebooks/.../foo.ipynb'
        p = REPO_ROOT / line.strip()
        if p.suffix == ".ipynb" and p.exists():
            out.append(p)
    return out


def _diff_range(base: str, head: str) -> Iterable[str]:
    """`git diff --name-only <base>..<head>`, or HEAD if no diff available."""
    try:
        cp = subprocess.run(
            ["git", "diff", "--name-only", f"{base}..{head}"],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            check=True,
        )
        return [ln for ln in cp.stdout.splitlines() if ln.strip()]
    except subprocess.CalledProcessError:
        return []


def _scan_notebook(path: Path, target_py: Tuple[int, int] = (3, 10)) -> List[dict]:
    """Return a list of findings (dicts with cell index, kind, error)."""
    findings: List[dict] = []
    try:
        with open(path, "r", encoding="utf-8") as f:
            nb = json.load(f)
    except (json.JSONDecodeError, OSError) as e:
        return [{
            "kind": "unreadable",
            "cell_index": -1,
            "message": f"cannot read notebook: {e}",
            "path": str(path),
        }]
    if not _is_python_kernel(nb.get("metadata", {})):
        return findings
    cells = nb.get("cells", []) or []
    for idx, cell in enumerate(cells):
        if (cell.get("cell_type") or "") != "code":
            continue
        src = "".join(cell.get("source", []) or [])
        if not src.strip():
            continue
        err, _ = _compile_cell(src, target_py=target_py)
        if err is None:
            continue
        if _looks_like_markdown_typed_code(src):
            findings.append({
                "kind": "markdown_typed_code",
                "cell_index": idx,
                "message": (
                    "cell_type is 'code' but source looks like markdown "
                    f"(prose or heading). compile() failed: {err.msg}"
                ),
                "path": str(path),
            })
        else:
            findings.append({
                "kind": "syntax_error",
                "cell_index": idx,
                "message": (
                    f"{err.msg} (line {err.lineno}, offset {err.offset})"
                ),
                "path": str(path),
            })
    return findings


def _iter_python_notebooks(roots: List[Path]) -> Iterable[Path]:
    for root in roots:
        if not root.exists():
            continue
        for p in root.rglob("*.ipynb"):
            if any(part.startswith(".") or part in {"__pycache__", "_output"} for part in p.parts):
                continue
            yield p


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("paths", nargs="*", type=Path, default=[],
                        help="Notebook(s) to scan. If omitted, scan the whole "
                             "repo (default). pre-commit's pass_filenames:true "
                             "injects the staged file(s) as positional args; "
                             "without this, every commit touching a .ipynb "
                             "would exit 2 on 'unrecognized arguments' "
                             "(c.672-L42 fix).")
    parser.add_argument("--path", type=Path, default=None,
                        help="Single notebook to scan (exclusive with positional `paths`)")
    parser.add_argument("--pr-diff", nargs=2, metavar=("BASE", "HEAD"), default=None,
                        help="Scan only notebooks modified between BASE and HEAD")
    parser.add_argument("--target-py", default="3.10",
                        help="Target Python version (X.Y) for parse. Default 3.10.")
    parser.add_argument("--json", action="store_true",
                        help="JSON output")
    args = parser.parse_args()

    try:
        target_py = tuple(int(x) for x in args.target_py.split("."))
        if len(target_py) != 2:
            raise ValueError
    except ValueError:
        print(f"invalid --target-py {args.target_py!r}; expected X.Y", file=sys.stderr)
        return 2

    if args.path and args.paths:
        print("error: --path is exclusive with positional `paths`", file=sys.stderr)
        return 2
    if args.path:
        paths = [args.path]
    elif args.paths:
        paths = [p for p in args.paths if p.exists()]
    elif args.pr_diff:
        names = _diff_range(args.pr_diff[0], args.pr_diff[1])
        paths = _cells_touched_by_pr(names)
    else:
        paths = list(_iter_python_notebooks([NOTEBOOKS_DIR]))

    findings: List[dict] = []
    for p in paths:
        findings.extend(_scan_notebook(p, target_py=target_py))

    if args.json:
        json.dump({"findings": findings, "scanned": len(paths)}, sys.stdout, indent=2)
        sys.stdout.write("\n")
    else:
        for f in findings:
            tag = f["kind"]
            idx = f.get("cell_index", -1)
            print(f"[{tag}] {f['path']} cell[{idx}]: {f['message']}")
        print(f"--- scanned: {len(paths)} notebook(s), findings: {len(findings)}")

    return 1 if findings else 0


if __name__ == "__main__":
    sys.exit(main())
