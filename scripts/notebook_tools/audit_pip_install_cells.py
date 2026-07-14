#!/usr/bin/env python3
"""Audit ``!pip install`` cells in Jupyter notebooks.

Standing-ASK class — ``!pip install`` in a committed notebook is an
**env-hygiene anti-pattern** AND a **machine-path leak vector**:

- The kernel shells out to ``pip`` which prints
  ``Requirement already satisfied: <pkg> in C:\\Users\\<user>\\AppData\\...\\site-packages``
  into the cell's ``stream`` output. The absolute path leaks the maintainer's
  machine layout in the committed notebook (regle secrets-hygiene §6,
  triage C = source-leak).
- The ``!pip install`` line itself is unnecessary in a committed notebook:
  the env should be pre-provisioned (regle F — env > contournement). It
  only matters at first-run, which is exactly when the maintainer has the
  freshest env (and the most informative leak).

Re-executing the cell on a machine where the package is already installed
will silently re-inject the leak — every subsequent exec re-leaks. Scrubbing
the *output* without scrubbing the *source* is **falsifying the proof of
execution** (Stop & Repair, mandate user 2026-06-22): the next re-exec
resurrects the leak. The only honest fix is **source-level** — remove the
``!pip install`` line (and prefer a conditional ``try/except ImportError →
subprocess.check_call(...)`` fallback when truly needed).

This script is the **detector** sibling of the manual fixes shipped in #6310
(Search-3-Informed) and #6313 (CSP-1-Fundamentals). It:

- scans a notebook (or repo-wide) for code cells whose source contains
  ``pip install`` (with or without ``!`` / ``%`` / sys.executable prefix),
- classifies each occurrence as one of:
    * ``UNCONDITIONAL_BASH`` — bare ``!pip install`` (leak vector, anti-pattern)
    * ``UNCONDITIONAL_SYS`` — ``!{sys.executable} -m pip install`` (leak vector)
    * ``CONDITIONAL_TRY`` — ``!pip install`` inside a ``try/except ImportError``
      block (defensible: only fires on real import failure)
    * ``NON_BASH`` — a ``pip install`` mention in a docstring / comment /
      printed string (no exec, no leak)
- reports counts by classification and lists the cell indices per file.

This is the **inventory** half of a fix; the **fix** itself is one PR per
notebook (surgical inject + re-execute, like #6310/#6313) and must be
authored by the notebook's owner (regle C.3 — strict scope of re-execution).

Usage:
    python audit_pip_install_cells.py --scan <path>      # one notebook
    python audit_pip_install_cells.py --scan-all         # repo-wide
    python audit_pip_install_cells.py --scan-all --check # exit 1 if defects
    python audit_pip_install_cells.py --scan-all --json  # JSON output
"""
from __future__ import annotations

import argparse
import json
import os
import re
import sys
from collections import Counter
from pathlib import Path
from typing import Iterable

# A line that runs pip in a cell. Captures:
#   !pip install pandas
#   !{sys.executable} -m pip install pandas
#   ! python -m pip install pandas
#   %pip install pandas   (IPython magic, same effect)
# Case-insensitive, tolerant of whitespace.
PIP_INSTALL_RE = re.compile(
    r"""
    (?:^|\n)\s*             # line start (multiline-aware)
    [!%]                     # bang or IPython magic
    \s*
    (?:                       # optional python/sys.executable prefix
        (?:\{\s*sys\.executable\s*\}|python(?:3)?)
        \s+
        -m\s+
        pip\s+install
        |
        pip\s+install
    )
    \b
    """,
    re.VERBOSE | re.IGNORECASE | re.MULTILINE,
)

# Cell classification signatures.
_TRY_BLOCK_RE = re.compile(r"\btry\s*:", re.MULTILINE)
_EXCEPT_IMPORT_RE = re.compile(r"\bexcept\s+ImportError\b", re.MULTILINE)


def _classify_cell(source: str) -> str:
    """Classify a pip-install occurrence by surrounding control flow.

    Returns one of: ``UNCONDITIONAL_BASH``, ``UNCONDITIONAL_SYS``,
    ``CONDITIONAL_TRY``, ``NON_BASH`` (mention only, no exec).

    The classifier is heuristic — it inspects the *cell* source for a
    ``try:/except ImportError`` guard around the pip-install line. Cells
    without such a guard are unconditional (the leak vector).
    """
    if not PIP_INSTALL_RE.search(source):
        return "NON_BASH"
    has_try = bool(_TRY_BLOCK_RE.search(source))
    has_except_import = bool(_EXCEPT_IMPORT_RE.search(source))
    if has_try and has_except_import:
        return "CONDITIONAL_TRY"
    # Distinguish bash vs sys.executable prefix (both leak, but the latter
    # is the more idiomatic IPython form and slightly less catastrophic
    # because pip prints the resolved path differently).
    if re.search(r"\{\s*sys\.executable\s*\}", source):
        return "UNCONDITIONAL_SYS"
    return "UNCONDITIONAL_BASH"


def _iter_notebooks(root: Path) -> Iterable[Path]:
    """Yield notebooks under ``root``, excluding papermill output artifacts.

    The ``iter_notebooks`` convention (cf #6312) excludes
    ``_output.ipynb`` and ``_executed.ipynb`` paths (papermill artifacts,
    never source). This keeps the audit focused on what's actually
    committed and reviewed.
    """
    for path in sorted(root.rglob("*.ipynb")):
        parts = path.parts
        if any(part.endswith("_output.ipynb") or part.endswith("_executed.ipynb")
               for part in parts):
            continue
        yield path


def _relpath(path: Path) -> str:
    """Compute a stable relative-to-cwd path; fall back to absolute if outside.

    Used to disambiguate same-named notebooks at different locations
    (e.g., ``CaseStudies/Diagnostic-Medical/solution/Diagnostic-Medical.ipynb``
    vs ``CaseStudies/Diagnostic-Medical/student/Diagnostic-Medical.ipynb``).
    """
    try:
        # Use os.path.relpath so cross-drive paths (Windows) don't ValueError.
        return os.path.relpath(path, Path.cwd())
    except ValueError:
        return str(path.resolve())


def scan_notebook(path: Path) -> dict:
    """Scan a single notebook for pip-install cells.

    Returns a dict with: ``file`` (relative path), ``total_cells``,
    ``code_cells``, ``occurrences`` (list of {cell_index, classification,
    source_preview}).
    """
    rel = _relpath(path)
    with open(path, encoding="utf-8") as f:
        nb = json.load(f)
    cells = nb.get("cells", [])
    code_cells = [c for c in cells if c.get("cell_type") == "code"]
    occurrences = []
    for i, c in enumerate(cells):
        if c.get("cell_type") != "code":
            continue
        src_list = c.get("source", [])
        src = "".join(src_list) if isinstance(src_list, list) else src_list
        if "pip install" not in src.lower():
            continue
        classification = _classify_cell(src)
        preview = src.strip().replace("\n", " | ")[:140]
        occurrences.append({
            "cell_index": i,
            "classification": classification,
            "source_preview": preview,
        })
    return {
        "file": str(rel),
        "total_cells": len(cells),
        "code_cells": len(code_cells),
        "occurrences": occurrences,
    }


def scan_repo(root: Path) -> list[dict]:
    """Scan all notebooks under ``root`` and return per-file reports."""
    reports = []
    for nb_path in _iter_notebooks(root):
        report = scan_notebook(nb_path)
        if report["occurrences"]:
            reports.append(report)
    return reports


def _format_text(reports: list[dict]) -> str:
    """Format the per-file reports as a human-readable table."""
    if not reports:
        return "No `!pip install` occurrences found. Repo is clean.\n"
    total = sum(len(r["occurrences"]) for r in reports)
    by_class: Counter = Counter()
    for r in reports:
        for occ in r["occurrences"]:
            by_class[occ["classification"]] += 1
    out = [
        f"# pip-install audit — {len(reports)} notebooks, {total} occurrences",
        "",
        "## Classification summary",
        "",
        "| Classification | Count | Severity |",
        "|----------------|-------|----------|",
        "| UNCONDITIONAL_BASH | {} | HIGH (leak vector) |".format(by_class.get("UNCONDITIONAL_BASH", 0)),
        "| UNCONDITIONAL_SYS  | {} | HIGH (leak vector) |".format(by_class.get("UNCONDITIONAL_SYS", 0)),
        "| CONDITIONAL_TRY    | {} | OK (defensible) |".format(by_class.get("CONDITIONAL_TRY", 0)),
        "| NON_BASH           | {} | INFO (mention only) |".format(by_class.get("NON_BASH", 0)),
        "",
        "## Per-file occurrences",
        "",
    ]
    for r in reports:
        out.append(f"### `{r['file']}` ({r['code_cells']} code cells)")
        out.append("")
        for occ in r["occurrences"]:
            out.append(
                f"- cell[{occ['cell_index']:>3}] **{occ['classification']}** — "
                f"{occ['source_preview']}"
            )
        out.append("")
    return "\n".join(out)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Audit `!pip install` cells in Jupyter notebooks."
    )
    parser.add_argument(
        "--scan", metavar="PATH",
        help="Scan a single notebook or directory of notebooks."
    )
    parser.add_argument(
        "--scan-all", action="store_true",
        help="Scan the entire MyIA.AI.Notebooks/ tree."
    )
    parser.add_argument(
        "--check", action="store_true",
        help="Exit 1 if any HIGH-severity (UNCONDITIONAL_*) occurrences found."
    )
    parser.add_argument(
        "--json", action="store_true",
        help="Emit machine-readable JSON instead of the text table."
    )
    args = parser.parse_args(argv)

    if not args.scan and not args.scan_all:
        parser.error("one of --scan or --scan-all is required")

    if args.scan_all:
        root = Path("MyIA.AI.Notebooks")
        if not root.exists():
            print(f"error: {root} not found (cwd={os.getcwd()})", file=sys.stderr)
            return 2
        reports = scan_repo(root)
    else:
        target = Path(args.scan)
        if target.is_file() and target.suffix == ".ipynb":
            reports = [scan_notebook(target)]
        elif target.is_dir():
            reports = scan_repo(target)
        else:
            print(f"error: {target} is not a notebook or directory", file=sys.stderr)
            return 2

    if args.json:
        print(json.dumps(reports, indent=2, ensure_ascii=False))
    else:
        print(_format_text(reports))

    if args.check:
        high = sum(
            1
            for r in reports
            for occ in r["occurrences"]
            if occ["classification"].startswith("UNCONDITIONAL_")
        )
        return 1 if high > 0 else 0
    return 0


if __name__ == "__main__":
    sys.exit(main())