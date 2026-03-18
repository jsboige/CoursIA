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
    """Convert STRING source to LIST format."""
    if isinstance(source, list):
        return source
    # Split by newline and preserve empty lines
    return source.split('\n')


def fix_notebook(notebook_path: Path, dry_run: bool = False) -> bool:
    """Fix STRING cells in a notebook. Returns True if changes were made."""
    with open(notebook_path, 'r', encoding='utf-8') as f:
        data = json.load(f)

    modified = False
    for cell in data.get('cells', []):
        source = cell.get('source')
        if source and isinstance(source, str):
            cell['source'] = convert_string_to_list(source)
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
