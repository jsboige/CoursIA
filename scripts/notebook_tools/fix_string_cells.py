#!/usr/bin/env python3
"""
Convert STRING source cells to LIST format in Jupyter notebooks.

Jupyter notebooks store cell source as either:
- STRING: "code line 1\ncode line 2"
- LIST: ["code line 1", "code line 2"]

This script converts all STRING cells to LIST format for consistency.
"""

import json
from pathlib import Path
from typing import List


def convert_string_to_list(source) -> List[str]:
    """Convert STRING source to LIST format.

    nbformat convention: each line except the last ends with '\\n'.
    Example: "a\\nb\\nc" -> ["a\\n", "b\\n", "c"]
    """
    if isinstance(source, list):
        return source
    lines = source.split('\n')
    # Add '\n' to each line except the last (nbformat convention)
    return [line + '\n' for line in lines[:-1]] + [lines[-1]] if lines else []


def fix_list_newlines(source: List[str]) -> List[str]:
    """Fix LIST cells missing trailing '\\n' on non-last lines.

    Detects lists where lines are missing '\\n' (from a buggy split)
    and adds them back per nbformat convention.
    """
    if not source or len(source) <= 1:
        return source
    # Check if lines are missing '\n' (buggy conversion)
    needs_fix = False
    for line in source[:-1]:
        if line and not line.endswith('\n'):
            needs_fix = True
            break
    if not needs_fix:
        return source
    # Fix: add '\n' to all lines except the last
    return [line + '\n' if not line.endswith('\n') else line for line in source[:-1]] + [source[-1]]


def fix_notebook(notebook_path: Path, dry_run: bool = False) -> bool:
    """Fix STRING cells and LIST cells with missing newlines. Returns True if changes were made."""
    with open(notebook_path, 'r', encoding='utf-8') as f:
        data = json.load(f)

    modified = False
    for cell in data.get('cells', []):
        source = cell.get('source')
        if source and isinstance(source, str):
            cell['source'] = convert_string_to_list(source)
            modified = True
        elif source and isinstance(source, list) and len(source) > 1:
            fixed = fix_list_newlines(source)
            if fixed != source:
                cell['source'] = fixed
                modified = True

    if modified and not dry_run:
        with open(notebook_path, 'w', encoding='utf-8') as f:
            json.dump(data, f, indent=1, ensure_ascii=False)
            # Add trailing newline
            f.write('\n')

    return modified


def main():
    import argparse

    parser = argparse.ArgumentParser(description='Fix STRING cells in Jupyter notebooks')
    parser.add_argument('path', help='Notebook file or directory')
    parser.add_argument('--dry-run', action='store_true', help='Show changes without modifying')
    parser.add_argument('--genai-only', action='store_true', help='Only process GenAI notebooks')
    args = parser.parse_args()

    path = Path(args.path)
    notebooks = []

    if path.is_file() and path.suffix == '.ipynb':
        notebooks = [path]
    elif path.is_dir():
        for nb in path.rglob('*.ipynb'):
            if '_output' in str(nb):
                continue
            if args.genai_only and 'GenAI' not in str(nb):
                continue
            notebooks.append(nb)

    fixed_count = 0
    for nb in notebooks:
        if fix_notebook(nb, dry_run=args.dry_run):
            print(f'  [FIXED] {nb}')
            fixed_count += 1
        elif args.dry_run:
            # Show all notebooks even if no changes
            print(f'  [OK] {nb}')

    print(f'\nTotal: {fixed_count}/{len(notebooks)} notebooks fixed')
    if args.dry_run:
        print('(Dry run - no files modified)')


if __name__ == '__main__':
    main()
