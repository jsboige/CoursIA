#!/usr/bin/env python3
"""
Detect solution leaks in Jupyter notebooks.

A "solution leak" is an exercise cell (labeled "Exercice N") that contains
complete working code instead of a stub (pass, print("Exercice a completer"),
return None, # TODO, // TODO).

Usage:
    python detect_solution_leaks.py --scan <path>
    python detect_solution_leaks.py --scan-all
    python detect_solution_leaks.py --scan-all --check  (exit 1 if leaks found)

Severity levels:
    HIGH   = "Exercice N" label + complete solution code (not stub)
    MEDIUM = Duplicate exercise numbering
    LOW    = "Exemple guide" label with stub code (inconsistency)
"""

import argparse
import json
import os
import re
import sys
from pathlib import Path

STUB_PATTERNS = [
    r'print\(["\']Exercice a completer',
    r'print\(["\']Exercices a completer',
    r'^\s*pass\s*$',
    r'return None',
    r'#\s*TODO',
    r'//\s*TODO',
    r'Console\.WriteLine\(["\']Exercice a completer',
    r'Console\.WriteLine\(["\']Exercices a completer',
    # Lean stub idioms (Lean line comments start with `--`).
    r'--\s*TODO',
    # Lean `sorry` tactic admits the goal — an exercise cell using it is a stub
    # (the proof is unverified, intentionally left for the student).
    r'\bsorry\b',
    # .NET Interactive / F# `.Display("...a completer")` idiom (the existing
    # patterns only cover Console.WriteLine / print).
    r'\.Display\s*\([^)]*(?:a compl[ée]ter|compl[ée]ter)',
    # Python assignment-stub: `result = None  # TODO etudiant` /
    # `matrice = None  # Remplacez None`. `return None` only matches a return
    # statement, not an assignment that defers the work to the student.
    r'=\s*None\s*#.*(?:TODO|Remplacez|a compl[ée]ter|compl[ée]ter)',
]

EXERCISE_HEADER_RE = re.compile(
    r'^#+\s*(?:\d+[.:]\s*)?(?:Exercice|Exercise)\s*(\d*)\s*[:.]?\s*(.*)',
    re.MULTILINE | re.IGNORECASE,
)

SOUMIS_PAR_RE = re.compile(r'soumis par|submitted by', re.IGNORECASE)

SOLUTION_MARKER_RE = re.compile(
    r'[Ss]olution|[Rr][eé]ponse|[Rr]esultat|ref\s*:',
    re.IGNORECASE,
)

# A worked-example header line (Exemple guide / Exemple resolu / Example / Worked).
# Used for closest-preceding-header attribution: a code cell whose nearest header
# is a worked example is NOT an exercise solution leak, even if a broader
# "Exercices" section header sits further back (cf exercise-example-labeling.md,
# content-based rule). Distinguished from EXERCISE_HEADER_RE (Exercice/Exercise).
EXAMPLE_HEADER_RE = re.compile(
    r'^#+\s*(?:\d+[.:]\s*)?(?:Exempl?es?|Examples?|Worked)',
    re.IGNORECASE,
)

# Any markdown ATX/SETEXT-like header line, for closest-header attribution.
HEADER_LINE_RE = re.compile(r'^#{1,6}\s+.+$', re.MULTILINE)

# A worked-example label appearing as the FIRST code comment line of a code cell
# (e.g. "# Exemple guide : ...", "// Example 1 : ...", "-- Exemple resolu").
# Mirrors EXAMPLE_HEADER_RE for the case where the worked-example label lives in
# a leading code comment rather than a markdown header. Cf exercise-example-labeling.md
# (content-based rule): a code cell that self-labels as a worked example is never an
# exercise solution leak, even under a broader "## Exercices" section header.
EXAMPLE_CODE_COMMENT_RE = re.compile(
    r'^\s*(?:#|//|--)\s*(?:\d+[.:]\s*)?(?:Exempl?es?|Examples?|Worked)',
    re.IGNORECASE,
)


def closest_preceding_header_is_example(cells, code_idx):
    """Return True if the closest preceding markdown header line is a worked
    example.

    Scans backwards from ``code_idx``; within a markdown cell, the LAST header
    line wins (it is the closest to the code that follows). A code cell owned by
    a worked example is never an exercise solution leak — this suppresses false
    positives where a code cell sits under a ``## Exercices`` section header but
    its actual nearest sub-header is ``### Exemple guide`` (in the same cell or
    an intervening one). Cf exercise-example-labeling.md (content-based rule).
    """
    for k in range(code_idx - 1, -1, -1):
        cell = cells[k]
        if cell.get('cell_type') != 'markdown':
            continue
        src = ''.join(cell.get('source', []))
        header_lines = HEADER_LINE_RE.findall(src)
        if not header_lines:
            continue  # prose-only markdown cell; keep scanning further back
        return bool(EXAMPLE_HEADER_RE.search(header_lines[-1]))
    return False


def code_cell_first_comment_labels_example(source: str) -> bool:
    """Return True if the first non-empty line of the code is a worked-example
    comment label.

    Some notebooks label a worked example via a leading code comment
    (``# Exemple guide : ...``, ``// Example 1 : ...``) sitting under a
    ``## Exercices`` section header, with NO intervening markdown sub-header.
    Such a cell is a worked example, not an exercise solution leak — it would be
    a false positive under header-only attribution. Suppresses that FP.
    Cf exercise-example-labeling.md (content-based rule).
    """
    for line in source.split('\n'):
        if not line.strip():
            continue
        return bool(EXAMPLE_CODE_COMMENT_RE.search(line))
    return False


def _header_level(line: str) -> int:
    """Return the ATX heading level (count of leading ``#``), or 0 if not a
    header line."""
    m = re.match(r'^(#{1,6})\s', line)
    return len(m.group(1)) if m else 0


def intervening_section_breaks_attribution(cells, exercise_idx, code_idx) -> bool:
    """Return True if a markdown header at the same or higher level than the
    exercise header appears between ``exercise_idx`` and ``code_idx``.

    A same-or-higher-level header (e.g. ``## Conclusion``, ``## Section 6``,
    or a ``### 6.1 ...`` sibling of ``### Exercice 2``) starts a new section and
    breaks the attribution of the code cell to the exercise: the code then
    belongs to that later section, not the exercise. A DEEPER sub-header (e.g.
    ``### Indice`` under a ``## Exercice 1``) does NOT break the section (it is
    a child of the exercise, common in worked exercise scaffolding).

    This suppresses cross-cell false positives where a demo/visualisation code
    cell sits a few cells after an exercise header but is actually owned by a
    later ``## Conclusion`` / ``## Section N`` section. Cf exercise-example-labeling.md
    (content-based rule). Safe default: if the exercise header level cannot be
    determined, do not suppress.
    """
    ex_src = ''.join(cells[exercise_idx].get('source', []))
    ex_level = 0
    for line in ex_src.split('\n'):
        if EXERCISE_HEADER_RE.search(line):
            ex_level = _header_level(line)
            break
    if not ex_level:
        return False
    for k in range(exercise_idx + 1, code_idx):
        cell = cells[k]
        if cell.get('cell_type') != 'markdown':
            continue
        src = ''.join(cell.get('source', []))
        for header_line in HEADER_LINE_RE.findall(src):
            if _header_level(header_line) <= ex_level:
                return True
    return False


def is_stub_code(source: str) -> bool:
    """Check if code cell source is a stub (not a real solution)."""
    lines = source.strip().split('\n')
    non_empty = [l.strip() for l in lines if l.strip() and not l.strip().startswith('//') and not l.strip().startswith('#')]

    if not non_empty:
        return True

    for pattern in STUB_PATTERNS:
        # re.MULTILINE so anchored patterns like `^\s*pass\s*$` match an
        # INDENTED `pass` inside a function body (the real-world stub case),
        # not just a top-level `pass` at the start of the cell source.
        if re.search(pattern, source, re.IGNORECASE | re.MULTILINE):
            return True

    code_lines = [l for l in non_empty if not l.startswith('import ') and not l.startswith('from ')]
    if len(code_lines) <= 1:
        return True

    return False


def scan_notebook(path: str) -> list[dict]:
    """Scan a single notebook for solution leaks."""
    findings = []
    try:
        with open(path, 'r', encoding='utf-8-sig') as f:
            nb = json.load(f)
    except (json.JSONDecodeError, UnicodeDecodeError):
        return [{"path": path, "severity": "ERROR", "message": "Failed to parse notebook"}]

    cells = nb.get('cells', [])
    exercise_numbers = {}

    for i, cell in enumerate(cells):
        if cell.get('cell_type') != 'markdown':
            continue

        source = ''.join(cell.get('source', []))

        m = EXERCISE_HEADER_RE.search(source)
        if not m:
            continue

        num = m.group(1)
        title = m.group(2)
        has_soumis = bool(SOUMIS_PAR_RE.search(source))

        if num:
            if num in exercise_numbers:
                findings.append({
                    "path": path,
                    "cell_index": i,
                    "cell_type": "markdown",
                    "severity": "MEDIUM",
                    "exercise_num": num,
                    "message": f"Duplicate Exercice {num} (first at cell {exercise_numbers[num]})",
                    "preview": source[:100],
                })
            else:
                exercise_numbers[num] = i

        next_code_idx = None
        next_code_source = None
        for j in range(i + 1, min(i + 4, len(cells))):
            if cells[j].get('cell_type') == 'code':
                next_code_idx = j
                next_code_source = ''.join(cells[j].get('source', []))
                break

        if next_code_source is None:
            continue

        if has_soumis:
            if not is_stub_code(next_code_source):
                findings.append({
                    "path": path,
                    "cell_index": next_code_idx,
                    "cell_type": "code",
                    "severity": "HIGH",
                    "exercise_num": num or "?",
                    "message": f"Solution leak: Exercice {num or '?'} with 'soumis par' has complete code (not stub)",
                    "preview": next_code_source[:150],
                    "fix": f"Relabel cell {i} from 'Exercice' to 'Exemple guide'",
                })
            continue

        if not is_stub_code(next_code_source):
            # Closest-preceding-header attribution: a code cell whose nearest
            # header is a worked example (Exemple guide / Exemple resolu / ...)
            # is not an exercise leak, even if a broader "## Exercices" section
            # header sits further back. Suppress the false positive.
            # Also suppress when the code cell SELF-LABELS as a worked example
            # via its first comment line ('# Exemple guide : ...') under such a
            # section — no markdown sub-header to attribute to. Cf exercise-example-labeling.md.
            if (closest_preceding_header_is_example(cells, next_code_idx)
                    or code_cell_first_comment_labels_example(next_code_source)):
                continue
            # Cross-cell attribution guard: if a same-or-higher-level markdown
            # section header (e.g. "## Conclusion", "## Section 6", a "### 6.1"
            # sibling) appears between the exercise header and this code cell,
            # the code belongs to that later section, not the exercise. Suppress
            # the false positive. A deeper sub-header ("### Indice" under
            # "## Exercice 1") does not break the section.
            if intervening_section_breaks_attribution(cells, i, next_code_idx):
                continue
            solution_markers = bool(SOLUTION_MARKER_RE.search(next_code_source))
            if solution_markers or len(next_code_source.strip().split('\n')) > 8:
                findings.append({
                    "path": path,
                    "cell_index": next_code_idx,
                    "cell_type": "code",
                    "severity": "HIGH",
                    "exercise_num": num or "?",
                    "message": f"Solution leak: Exercice {num or '?'} has {len(next_code_source)} chars of code (not stub)",
                    "preview": next_code_source[:150],
                    "fix": "Relabel header to 'Exemple guide' or replace code with stub",
                })

    return findings


def discover_notebooks(root: str) -> list[str]:
    """Find all .ipynb files under root, excluding _output and .ipynb_checkpoints."""
    notebooks = []
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d not in ('.ipynb_checkpoints', '_output', '.git', '__pycache__', 'node_modules')]
        for f in filenames:
            if f.endswith('.ipynb') and not f.endswith('_output.ipynb'):
                notebooks.append(os.path.join(dirpath, f))
    return sorted(notebooks)


def main():
    parser = argparse.ArgumentParser(description="Detect solution leaks in notebooks")
    parser.add_argument("--scan", help="Scan a specific notebook or directory")
    parser.add_argument("--scan-all", action="store_true", help="Scan all notebooks in repo")
    parser.add_argument("--check", action="store_true", help="Exit 1 if any HIGH findings")
    parser.add_argument("--verbose", action="store_true", help="Show all findings including LOW")
    parser.add_argument(
        "--json",
        action="store_true",
        help="Emit findings as a JSON array (for CI delta guard, cf solution_leak_delta.py)",
    )
    args = parser.parse_args()

    repo_root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    nb_root = os.path.join(repo_root, "MyIA.AI.Notebooks")

    if args.scan_all:
        notebooks = discover_notebooks(nb_root)
    elif args.scan:
        target = args.scan
        if os.path.isdir(target):
            notebooks = discover_notebooks(target)
        elif os.path.isfile(target):
            notebooks = [target]
        else:
            candidates = discover_notebooks(nb_root)
            notebooks = [n for n in candidates if target.lower() in n.lower()]
            if not notebooks:
                print(f"No notebooks matching '{target}'")
                return 1
    else:
        parser.print_help()
        return 1

    if not args.json:
        print(f"Scanning {len(notebooks)} notebooks...")

    all_findings = []
    for nb_path in notebooks:
        findings = scan_notebook(nb_path)
        all_findings.extend(findings)

    # Machine-readable output for CI delta guards (cf solution_leak_delta.py,
    # mirror of pip_leak_delta.py). Emitted before any human-readable prose so
    # downstream parsers can consume stdout verbatim.
    if args.json:
        import json as _json

        print(_json.dumps(all_findings, ensure_ascii=False))
        return 0

    high = [f for f in all_findings if f.get('severity') == 'HIGH']
    medium = [f for f in all_findings if f.get('severity') == 'MEDIUM']
    errors = [f for f in all_findings if f.get('severity') == 'ERROR']

    print(f"\nResults: {len(high)} HIGH (leaks), {len(medium)} MEDIUM (duplicates), {len(errors)} errors")
    print(f"Scanned: {len(notebooks)} notebooks\n")

    if high:
        print("=== HIGH SEVERITY (Solution Leaks) ===")
        for f in high:
            rel = os.path.relpath(f['path'], repo_root)
            print(f"  [{f['severity']}] {rel}:cell {f['cell_index']} — {f['message']}")
            if args.verbose and 'preview' in f:
                print(f"    Preview: {f['preview'][:120]}...")
            if 'fix' in f:
                print(f"    Fix: {f['fix']}")
        print()

    if medium:
        print("=== MEDIUM SEVERITY (Duplicate Numbers) ===")
        for f in medium:
            rel = os.path.relpath(f['path'], repo_root)
            print(f"  [{f['severity']}] {rel}:cell {f['cell_index']} — {f['message']}")
        print()

    if errors:
        print("=== ERRORS ===")
        for f in errors:
            print(f"  {f['path']}: {f['message']}")
        print()

    if args.check and high:
        return 1

    return 0


if __name__ == '__main__':
    sys.exit(main())
