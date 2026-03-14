"""Repair corrupted GenAI notebooks - fix missing newline terminators.

The corruption was caused by scripts/fix_robust_dotenv.py which used
ROBUST_PATTERN.split('\n') producing strings WITHOUT trailing '\n'.
When these were stored in cell['source'] and then ''.join(source)
was called, lines collapsed into single mega-lines (500+ chars).

The fix is simple: ensure every source element except the last ends
with '\n'. This is the Jupyter notebook JSON format requirement.
"""
import json
import glob
import os
import sys
from pathlib import Path
from collections import defaultdict


def is_cell_corrupted(source):
    """Check if a cell's source has missing newline terminators.

    Two detection methods:
    1. Collapsed lines: ''.join(source) produces lines > 300 chars
       containing Python keywords (from the robust .env pattern)
    2. Missing terminators: 3+ non-empty mid-array elements lack '\n'
    """
    if not source or not isinstance(source, list):
        return False

    # Method 1: collapsed lines
    joined = ''.join(source)
    for line in joined.split('\n'):
        if len(line) > 300 and ('import' in line or 'def ' in line
                                 or 'dotenv' in line or 'load_dotenv' in line
                                 or 'env_loaded' in line or 'GENAI_ROOT' in line):
            return True

    # Method 2: missing \n terminators on mid-array elements
    if len(source) > 3:
        non_empty = [s for s in source[:-1] if s and s.strip()]
        missing = sum(1 for s in non_empty if not s.endswith('\n'))
        if missing >= 3:
            return True

    return False


def fix_source(source):
    """Fix a corrupted source array by adding missing '\\n' terminators.

    Returns (new_source, was_fixed).
    """
    if not source or not isinstance(source, list):
        return source, False

    if not is_cell_corrupted(source):
        return source, False

    # Simple fix: ensure every element except the last ends with \n
    new_source = []
    for i, element in enumerate(source):
        if i < len(source) - 1:
            # Mid-array elements MUST end with \n
            if element and not element.endswith('\n'):
                new_source.append(element + '\n')
            else:
                new_source.append(element)
        else:
            # Last element: keep as-is (may or may not have \n)
            new_source.append(element)

    return new_source, True


def repair_notebook(nb_path, dry_run=False):
    """Repair a single notebook. Returns (fixed_cells, total_code_cells)."""
    with open(nb_path, 'r', encoding='utf-8') as f:
        nb = json.load(f)

    fixed_cells = 0
    total_code_cells = 0

    for i, cell in enumerate(nb.get('cells', [])):
        if cell.get('cell_type') != 'code':
            continue
        total_code_cells += 1

        source = cell.get('source', [])
        new_source, was_fixed = fix_source(source)

        if was_fixed:
            fixed_cells += 1
            if not dry_run:
                cell['source'] = new_source

    if fixed_cells > 0 and not dry_run:
        with open(nb_path, 'w', encoding='utf-8', newline='\n') as f:
            json.dump(nb, f, indent=1, ensure_ascii=False)
            f.write('\n')

    return fixed_cells, total_code_cells


def main():
    dry_run = '--dry-run' in sys.argv
    verbose = '--verbose' in sys.argv or '-v' in sys.argv

    if dry_run:
        print("=== DRY RUN MODE - no files will be modified ===\n")

    base = Path('MyIA.AI.Notebooks/GenAI')
    notebooks = sorted(glob.glob(str(base / '**/*.ipynb'), recursive=True))
    notebooks = [n for n in notebooks if 'EPF' not in n.split(os.sep) and '/EPF/' not in n]

    results = defaultdict(lambda: {'fixed': 0, 'clean': 0, 'fixed_cells': 0})
    total_fixed = 0
    total_clean = 0

    for nb_path in notebooks:
        short = nb_path.replace(str(base) + os.sep, '').replace(str(base) + '/', '')
        parts = short.replace('\\', '/').split('/')
        series = parts[0]

        fixed_cells, total_cells = repair_notebook(nb_path, dry_run=dry_run)

        if fixed_cells > 0:
            results[series]['fixed'] += 1
            results[series]['fixed_cells'] += fixed_cells
            total_fixed += 1
            if verbose:
                print(f"  REPAIRED: {short} ({fixed_cells} cells)")
        else:
            results[series]['clean'] += 1
            total_clean += 1

    print("=== REPAIR RESULTS ===\n")
    for series in sorted(results.keys()):
        r = results[series]
        total = r['fixed'] + r['clean']
        if r['fixed'] > 0:
            print(f"{series}: {r['fixed']}/{total} repaired ({r['fixed_cells']} cells)")
        else:
            print(f"{series}: all {total} clean")

    print(f"\nTOTAL: {total_fixed} notebooks repaired, {total_clean} already clean")

    if dry_run:
        print("\n(dry run - no files modified)")
    else:
        print("\nRun 'python scripts/audit_genai_corruption.py' to verify repairs.")

    return total_fixed


if __name__ == '__main__':
    main()
