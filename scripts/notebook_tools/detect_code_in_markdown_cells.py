#!/usr/bin/env python3
"""Detect code patterns embedded in markdown cells of Jupyter notebooks.

Motivation
----------
A markdown cell can carry executable code (``python`` or ``csharp``) that
**renders as prose** (not fenced code) and **never executes** because the
kernel only runs ``code`` cells. Two failure modes have shipped to ``main`` :

1. **Stubs that never run** : an ``Exercice N`` skeleton whose ``def`` /
   ``class`` signature lives in a markdown cell — the student edits prose,
   never code, and the auto-grader sees zero source.
2. **Dead Papermill parameter blocks** : a ``parameters``-tagged markdown cell
   carrying ``LOAD_MODEL_AND_TRAIN = False`` looks like an anchor but the
   kernel skips it, and the actual parameter value comes from a later code
   cell — opposite value, no warning.

Both share the same shape : **a markdown cell whose body has enough
*structural* code markers that it cannot be plausibly read as prose**. The
scanner is conservative on prose and aggressive on structure : it demands
either a Python ``def``/``class`` signature, two consecutive Python
assignments at column 0 (markdown render eats indent so we don't trust
prefixes), or any assignment inside a ``parameters``-tagged cell. A single
``x = 1`` in a sentence is NOT flagged — that's prose.

PR #12064 documents the trigger cases (``PT_11b_grpo_qwen_rlvr_on_verifiers.ipynb``
c5, parameter block, found 2026-08-21).

Rules
-----
- ``markdown_cell_with_python_signature``   (ERROR): markdown cell whose body
  contains a Python ``def`` or ``class`` signature at column 0.
- ``markdown_cell_with_python_assignment``  (ERROR): markdown cell whose body
  contains ≥ 2 un-fenced Python top-level assignments on consecutive
  non-blank lines (markdown render eats indent so we don't trust prefixes —
  the rule treats ``NAME = VALUE`` at line start after stripping whitespace
  as structural).
- ``markdown_cell_with_papermill_param``    (ERROR): markdown cell tagged
  ``parameters`` in its metadata whose body contains any Python assignment
  (the parameter block is dead by construction).

Usage
-----
::

    python scripts/notebook_tools/detect_code_in_markdown_cells.py \\
        MyIA.AI.Notebooks/ --report

    # CI gate (exit 1 on ERROR) :
    python scripts/notebook_tools/detect_code_in_markdown_cells.py \\
        MyIA.AI.Notebooks/ --check
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any

ERROR = "ERROR"
RULE_SEVERITY = {
    "markdown_cell_with_python_assignment": ERROR,
    "markdown_cell_with_python_signature": ERROR,
    "markdown_cell_with_papermill_param": ERROR,
}

# Top-level (column-0) Python assignment. We anchor at start-of-line after
# stripping a leading indent because markdown render eats the indent but
# keeps the assignment shape. The RHS must be a non-trivial value (not a
# bare name — that's a doc reference).
_PY_ASSIGN_RE = re.compile(
    r"^(?P<name>[A-Za-z_][A-Za-z0-9_]*)\s*=\s*(?P<value>\S.*)$"
)

_PY_SIGNATURE_RE = re.compile(
    r"^(?:def|class)\s+[A-Za-z_][A-Za-z0-9_]*\s*[\(:]"
)


def _is_markdown_cell(cell: dict[str, Any]) -> bool:
    return cell.get("cell_type") == "markdown"


def _cell_metadata_tags(cell: dict[str, Any]) -> list[str]:
    md = cell.get("metadata") or {}
    tags = md.get("tags") or []
    return list(tags) if isinstance(tags, list) else []


def _source_lines(cell: dict[str, Any]) -> list[str]:
    src = cell.get("source") or []
    if isinstance(src, list):
        return [str(s) for s in src]
    if isinstance(src, str):
        return src.splitlines(keepends=False)
    return []


def _line_evidence(line: str, max_len: int = 120) -> str:
    s = line.strip()
    if len(s) > max_len:
        s = s[: max_len - 1] + "…"
    return s


def _is_assignment(line: str) -> bool:
    m = _PY_ASSIGN_RE.match(line.strip())
    if not m:
        return False
    rhs = m.group("value").strip()
    # Skip walrus / equality / annotation-only (no value)
    if rhs.startswith("=") or not rhs:
        return False
    # Lexical pass kept as the upstream gate (scope unchanged); the AST pass
    # only adjudicates candidates the regex already retained — prose citing a
    # parameter twice (`n_est=200 obtient le meilleur...`) parses as a Compare,
    # not an Assign, and falls through (#12620).
    import ast as _ast
    try:
        tree = _ast.parse(line.strip(), mode="exec")
    except SyntaxError:
        return False
    if len(tree.body) != 1 or not isinstance(
        tree.body[0], (_ast.Assign, _ast.AnnAssign)
    ):
        return False
    return True


def _finding_hash(f: dict[str, Any]) -> str:
    import hashlib
    src = f.get("evidence", "")
    # Normalize path separators to POSIX for cross-platform stability:
    # baseline generated on Windows (backslash) doesn't match Linux scan (slash).
    file_path = f['file'].replace("\\", "/")
    payload = f"{file_path}:{f['cell']}:{f['rule']}:{f['line']}:{src}"
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()[:16]


# #12585 : le seul baseline du depot, celui que la CI passe explicitement.
# Un --check desarme (aucun baseline charge) rend un FAIL fantome sur un main
# vert -- toutes les violations acceptees ressortent « new ». Le default aligne
# l'invocation locale sur l'invocation CI.
DEFAULT_BASELINE = Path(__file__).resolve().parent / "code_in_markdown_cells_baseline.json"


def load_baseline(path: Path) -> set[str]:
    if not path or not path.exists():
        return set()
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError):
        return set()
    hashes = data.get("hashes") or []
    return set(hashes) if isinstance(hashes, list) else set()


def _scan_python_assignments(
    lines: list[str],
) -> tuple[int, list[tuple[str, int]]] | None:
    """Return (count, hits) where hits are (raw_line, line_index_1based).

    Requires ≥ 2 consecutive non-blank lines that are valid assignments.
    Consecutiveness is the structural marker — a list bullet ``- x = y``
    interrupted by blank lines or prose is NOT a code block."""
    hits: list[tuple[str, int]] = []
    streak = 0
    for idx, raw in enumerate(lines, start=1):
        if _is_assignment(raw):
            hits.append((raw, idx))
            streak += 1
        elif raw.strip() == "":
            streak = 0
            hits.clear()
        else:
            streak = 0
            hits.clear()
        if len(hits) >= 2:
            return (len(hits), hits)
    return None


def _scan_python_signatures(
    lines: list[str],
) -> tuple[str, int] | None:
    for idx, raw in enumerate(lines, start=1):
        if _PY_SIGNATURE_RE.match(raw.strip()):
            return (raw, idx)
    return None


def _scan_papermill_param(
    lines: list[str],
    tags: list[str],
) -> tuple[str, int] | None:
    if "parameters" not in tags:
        return None
    for idx, raw in enumerate(lines, start=1):
        if _is_assignment(raw):
            return (raw, idx)
    return None


_FENCE_RE = re.compile(r"^ {0,3}(?:`{3,}|~{3,})")


def _strip_fenced_blocks(lines: list[str]) -> list[str]:
    """Blank out CommonMark fenced code blocks, preserving line numbering.

    A fenced block in a markdown cell *renders as code* and never executes:
    it is the legitimate way to quote an anti-pattern, another language, or
    an excerpt of a source module. The scanners below target code that
    renders as PROSE, so fenced regions must not reach them -- see the module
    docstring, which already states the contract ("un-fenced"). Blank lines
    are substituted rather than dropped so reported line numbers keep pointing
    at the real cell offset, and so consecutive-assignment runs break at the
    fence. An unclosed fence runs to the end of the cell, per CommonMark.
    """
    out: list[str] = []
    inside = False
    for line in lines:
        if _FENCE_RE.match(line):
            inside = not inside
            out.append("\n")
            continue
        out.append("\n" if inside else line)
    return out


def scan_cell(cell: dict[str, Any], cell_index: int) -> list[dict[str, Any]]:
    if not _is_markdown_cell(cell):
        return []
    lines = _strip_fenced_blocks(_source_lines(cell))
    if not lines:
        return []
    tags = _cell_metadata_tags(cell)
    findings: list[dict[str, Any]] = []

    py_sig = _scan_python_signatures(lines)
    if py_sig is not None:
        findings.append({
            "rule": "markdown_cell_with_python_signature",
            "severity": ERROR,
            "line": py_sig[1],
            "evidence": _line_evidence(py_sig[0]),
        })

    py_assign = _scan_python_assignments(lines)
    if py_assign is not None:
        count, hits = py_assign
        first = hits[0]
        findings.append({
            "rule": "markdown_cell_with_python_assignment",
            "severity": ERROR,
            "line": first[1],
            "evidence": _line_evidence(first[0])
                      + f"  (+{count - 1} more assignments)",
        })

    pm = _scan_papermill_param(lines, tags)
    if pm is not None:
        findings.append({
            "rule": "markdown_cell_with_papermill_param",
            "severity": ERROR,
            "line": pm[1],
            "evidence": _line_evidence(pm[0]),
        })

    for f in findings:
        f["cell"] = cell_index
        f["tags"] = tags
    return findings


def scan_notebook(path: Path) -> list[dict[str, Any]]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError) as exc:
        print(f"warn: cannot read {path}: {exc}", file=sys.stderr)
        return []
    cells = data.get("cells") or []
    findings: list[dict[str, Any]] = []
    for i, cell in enumerate(cells):
        for f in scan_cell(cell, i):
            f["file"] = str(path)
            findings.append(f)
    return findings


def gather(root: Path) -> list[dict[str, Any]]:
    if root.is_file():
        return scan_notebook(root)
    findings: list[dict[str, Any]] = []
    for path in sorted(root.rglob("*.ipynb")):
        findings.extend(scan_notebook(path))
    return findings


def _selfcheck() -> int:
    """Run embedded positive/negative controls so a bad regex rewrite is caught."""
    cells = [
        # Negative : real markdown prose (no structural code)
        {"cell_type": "markdown", "source": ["## Title\n", "Some prose.\n"],
         "metadata": {}},
        # Negative : single assignment in a sentence (prose reference)
        {"cell_type": "markdown",
         "source": ["Voir `x = 1` ci-dessous pour le cas simple.\n"],
         "metadata": {}},
        # Negative : assignment interrupted by prose (not a code block)
        {"cell_type": "markdown",
         "source": ["x = 1\n", "Some prose in between.\n", "y = 2\n"],
         "metadata": {}},
        # Positive : PT_11 c5 shape — parameter block with assignments
        {"cell_type": "markdown",
         "source": [
             "# Papermill injects LOAD_MODEL_AND_TRAIN\n",
             "LOAD_MODEL_AND_TRAIN = False\n",
             "RUN_SEED = 42\n",
             'print(f"LOAD_MODEL_AND_TRAIN = {LOAD_MODEL_AND_TRAIN}")\n',
             "if not LOAD_MODEL_AND_TRAIN:\n",
             '    print("(Mode CPU-safe)")\n',
         ],
         "metadata": {"tags": ["parameters"]}},
        # Positive : Python signature in markdown
        {"cell_type": "markdown",
         "source": ["## Skeleton\n", "def fibonacci(n):\n",
                    "    return fibonacci(n - 1) + fibonacci(n - 2)\n"],
         "metadata": {}},
        # Negative : code cell — scanner does not visit
        {"cell_type": "code", "source": ["x = 1\n", "print(x)\n"],
         "metadata": {}},
        # Negative : FENCED python block — renders as code, never executes.
        # Control whose absence let 225 fenced findings ship as "baseline"
        # (2026-08-23) : the module contract above already says "un-fenced".
        {"cell_type": "markdown",
         "source": ["Anti-pattern a NE PAS reproduire :\n",
                    "```python\n",
                    "critere = Job.duree_seconeds > 100\n",
                    "liste = Job.select().where(critere)\n",
                    "```\n"],
         "metadata": {}},
        # Negative : FENCED non-Python block (Lean) quoting a source module
        {"cell_type": "markdown",
         "source": ["Les trois predicats :\n",
                    "```lean\n",
                    "def isStillLife (g : Grid) : Bool := step g == g\n",
                    "```\n"],
         "metadata": {}},
        # Positive : the SAME content UN-fenced is still flagged — proves the
        # fence strip narrowed the surface without disabling the scanners.
        {"cell_type": "markdown",
         "source": ["critere = Job.duree_seconeds > 100\n",
                    "liste = Job.select().where(critere)\n"],
         "metadata": {}},
    ]
    expected_rules = {
        0: set(),
        1: set(),
        2: set(),
        3: {"markdown_cell_with_python_assignment",
            "markdown_cell_with_papermill_param"},
        4: {"markdown_cell_with_python_signature"},
        5: set(),
        6: set(),
        7: set(),
        8: {"markdown_cell_with_python_assignment"},
    }
    failures: list[str] = []
    for i, cell in enumerate(cells):
        got = {f["rule"] for f in scan_cell(cell, i)}
        if got != expected_rules[i]:
            failures.append(
                f"selfcheck cell {i}: expected={sorted(expected_rules[i])}, "
                f"got={sorted(got)}"
            )
    if failures:
        for f in failures:
            print(f"SELFCHECK FAIL: {f}", file=sys.stderr)
        return 1
    print(f"selfcheck OK ({len(cells)}/{len(cells)} controls)")
    return 0


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    ap.add_argument(
        "root",
        nargs="?",
        default="MyIA.AI.Notebooks",
        help="notebook file or directory to scan (default: MyIA.AI.Notebooks)",
    )
    ap.add_argument(
        "--check",
        action="store_true",
        help="exit 1 if any ERROR-level finding is reported",
    )
    ap.add_argument(
        "--report",
        action="store_true",
        help="human-readable listing (default if neither --check nor --json)",
    )
    ap.add_argument(
        "--json",
        action="store_true",
        help="machine-readable JSON output",
    )
    ap.add_argument(
        "--selfcheck",
        action="store_true",
        help="run embedded positive/negative controls and exit (no root required)",
    )
    ap.add_argument(
        "--baseline",
        type=Path,
        default=None,
        help="baseline JSON of known violations; --check fails only on NEW ones",
    )
    ap.add_argument(
        "--update-baseline",
        action="store_true",
        help="write the current violation set to --baseline and exit",
    )
    args = ap.parse_args(argv)

    if args.selfcheck:
        return _selfcheck()

    root = Path(args.root)
    if not root.exists():
        print(f"error: path not found: {root}", file=sys.stderr)
        return 2

    findings = gather(root)

    # ---- update baseline --------------------------------------------------------
    if args.update_baseline:
        if not args.baseline:
            print("error: --update-baseline requires --baseline PATH",
                  file=sys.stderr)
            return 2
        hashes = sorted({_finding_hash(f) for f in findings})
        payload = {
            "_comment": "Baseline of code-in-markdown-cells violations. Burn down, do not grow. "
                        "Regenerate with: python scripts/notebook_tools/detect_code_in_markdown_cells.py "
                        "--update-baseline --baseline <this file>",
            "count": len(hashes),
            "hashes": hashes,
        }
        args.baseline.write_text(json.dumps(payload, indent=2, ensure_ascii=False)
                                 + "\n", encoding="utf-8")
        print(f"baseline written: {len(hashes)} violations -> {args.baseline}")
        return 0

    # #12585 : --check/--report/--json sans --baseline comparent au baseline
    # canonique, pas a un ensemble vide. --update-baseline exige toujours son
    # chemin explicitement (garde ci-dessus). L'identite de la reference est
    # affichee : un baseline vide et un baseline plein ne doivent plus rendre
    # la meme forme de verdict.
    baseline_path = args.baseline if args.baseline else DEFAULT_BASELINE
    baseline = load_baseline(baseline_path)
    if not args.update_baseline:
        # #12858 : --json doit rendre du JSON pur sur stdout. La ligne
        # d'identite reste visible a l'humain mais est emise sur stderr en
        # mode json, pour que stdout reste pipeable (| jq).
        identity = f"baseline: {baseline_path} ({len(baseline)} entries)"
        if args.json:
            print(identity, file=sys.stderr)
        else:
            print(identity)
    new_findings = [f for f in findings
                    if _finding_hash(f) not in baseline] if baseline else findings

    if args.json:
        print(json.dumps({
            "total": len(findings),
            "new": len(new_findings),
            "baseline_size": len(baseline),
            "findings": findings,
        }, indent=2, ensure_ascii=False))
    elif args.report or not args.check:
        by_rule: dict[str, int] = {}
        for f in findings:
            by_rule[f["rule"]] = by_rule.get(f["rule"], 0) + 1
        print(f"scanned: {root}")
        print(f"violations: {len(findings)} total"
              + (f" ({len(new_findings)} new vs baseline of {len(baseline)})"
                 if baseline else ""))
        for rule in sorted(by_rule):
            sev = RULE_SEVERITY.get(rule, "?")
            print(f"  {sev:>5} {rule}: {by_rule[rule]}")
        shown = new_findings if baseline else findings
        for f in shown:
            flag = "NEW " if (baseline and _finding_hash(f) not in baseline) else ""
            print(f"  {flag}{f['severity']:>5} {f['file']} cell#{f['cell']} [{f['rule']}]")
            print(f"        line {f['line']}: {f['evidence']}")

    if args.check:
        blocking = [f for f in new_findings if f["severity"] == ERROR]
        if blocking:
            print(
                f"\nFAIL: {len(blocking)} new code-in-markdown-cell violation(s).",
                file=sys.stderr,
            )
            for f in blocking[:50]:
                print(
                    f"  {f['file']} cell#{f['cell']} [{f['rule']}] {f['evidence']}",
                    file=sys.stderr,
                )
            return 1
        # #12858 : en mode --json, stdout est le document JSON pur ; le
        # verdict humain migre sur stderr, comme la ligne d'identite.
        print("OK: no new code-in-markdown-cell violations.",
              file=sys.stderr if args.json else sys.stdout)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
