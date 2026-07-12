#!/usr/bin/env python3
"""
Detect solution leaks in Jupyter notebooks.

A "solution leak" is an exercise cell (labeled "Exercice N") that contains
complete working code instead of a stub (pass, print("Exercice a completer"),
return None, # TODO).

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
    r'Console\.WriteLine\(["\']Exercice a completer',
    r'Console\.WriteLine\(["\']Exercices a completer',
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


def is_stub_code(source: str) -> bool:
    """Check if code cell source is a stub (not a real solution)."""
    lines = source.strip().split('\n')
    non_empty = [l.strip() for l in lines if l.strip() and not l.strip().startswith('//') and not l.strip().startswith('#')]

    if not non_empty:
        return True

    for pattern in STUB_PATTERNS:
        if re.search(pattern, source, re.IGNORECASE):
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

    print(f"Scanning {len(notebooks)} notebooks...")

    all_findings = []
    for nb_path in notebooks:
        findings = scan_notebook(nb_path)
        all_findings.extend(findings)

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
