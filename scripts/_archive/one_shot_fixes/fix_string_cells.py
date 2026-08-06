#!/usr/bin/env python
"""
Fix notebook cell source format issues:
1. STRING cells: 'source' as a string instead of list of lines
2. MISSING NEWLINES: list elements (except last) not ending with '\\n'

Both issues cause Jupyter to display cells incorrectly (lines concatenated).

Usage:
    fix_string_cells.py <notebook_or_directory> [--dry-run] [--recursive]
"""

import json
import sys
import glob
import os
from pathlib import Path


def fix_notebook_sources(notebook_path, dry_run=False):
    """Fix both STRING cells and missing newlines in a notebook."""
    with open(notebook_path, 'r', encoding='utf-8') as f:
        nb = json.load(f)

    string_fixes = 0
    newline_fixes = 0

    for cell in nb.get('cells', []):
        source = cell.get('source')

        # Fix 1: source is a string instead of list
        if isinstance(source, str):
            lines = source.splitlines(keepends=True)
            if not lines:
                lines = ['']
            # Ensure each line EXCEPT the last ends with \n
            for i in range(len(lines) - 1):
                if not lines[i].endswith('\n'):
                    lines[i] = lines[i] + '\n'
            cell['source'] = lines
            string_fixes += 1

        # Fix 2: source is a list but lines missing trailing \n
        elif isinstance(source, list) and len(source) > 1:
            fixed = False
            for i in range(len(source) - 1):
                if source[i] and not source[i].endswith('\n'):
                    source[i] = source[i] + '\n'
                    fixed = True
            if fixed:
                newline_fixes += 1

    total = string_fixes + newline_fixes
    if total == 0:
        return False, "OK"

    msg_parts = []
    if string_fixes:
        msg_parts.append(f"{string_fixes} STRING->LIST")
    if newline_fixes:
        msg_parts.append(f"{newline_fixes} missing-newline")

    if dry_run:
        return True, f"Would fix: {', '.join(msg_parts)}"

    with open(notebook_path, 'w', encoding='utf-8') as f:
        json.dump(nb, f, indent=1, ensure_ascii=False)
        f.write('\n')

    return True, f"Fixed: {', '.join(msg_parts)}"


# Keep old name as alias for backwards compatibility
fix_string_cells = fix_notebook_sources


def main():
    if len(sys.argv) < 2:
        print("Usage: fix_string_cells.py <notebook_or_directory> [--dry-run] [--recursive]")
        sys.exit(1)

    target = Path(sys.argv[1])
    dry_run = '--dry-run' in sys.argv
    recursive = '--recursive' in sys.argv

    if target.is_dir():
        pattern = os.path.join(str(target), '**/*.ipynb') if recursive else os.path.join(str(target), '*.ipynb')
        paths = [Path(p) for p in glob.glob(pattern, recursive=recursive)
                 if '_output' not in p and '.ipynb_checkpoints' not in p]
    elif target.exists():
        paths = [target]
    else:
        print(f"Error: {target} does not exist")
        sys.exit(1)

    fixed_count = 0
    for path in sorted(paths):
        success, message = fix_notebook_sources(path, dry_run)
        if success:
            print(f"  FIX  {path}: {message}")
            fixed_count += 1

    print(f"\n{fixed_count}/{len(paths)} notebooks {'would be ' if dry_run else ''}fixed")
    return 0


if __name__ == '__main__':
    sys.exit(main())
