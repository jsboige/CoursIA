#!/usr/bin/env python
"""
Fix STRING source cells in Jupyter notebooks.
Converts cells with 'source' as a string to 'source' as a list of lines.
"""

import json
import sys
from pathlib import Path


def fix_string_cells(notebook_path, dry_run=False):
    """Convert STRING source cells to LIST format."""
    with open(notebook_path, 'r', encoding='utf-8') as f:
        nb = json.load(f)
    
    changes = 0
    for cell in nb.get('cells', []):
        source = cell.get('source')
        if isinstance(source, str):
            # Convert string to list of lines
            lines = source.splitlines(keepends=True)
            if not lines:
                lines = ['']
            # Ensure each line ends with \n
            lines = [line if line.endswith('\n') else line + '\n' for line in lines]
            cell['source'] = lines
            changes += 1
    
    if changes == 0:
        return False, "No STRING cells found"
    
    if dry_run:
        return True, f"Would fix {changes} STRING cells"
    
    # Write back
    with open(notebook_path, 'w', encoding='utf-8') as f:
        json.dump(nb, f, indent=1, ensure_ascii=False)
        f.write('\n')
    
    return True, f"Fixed {changes} STRING cells"


def main():
    if len(sys.argv) < 2:
        print("Usage: fix_string_cells.py <notebook.ipynb> [--dry-run]")
        sys.exit(1)
    
    path = Path(sys.argv[1])
    dry_run = '--dry-run' in sys.argv
    
    if not path.exists():
        print(f"Error: {path} does not exist")
        sys.exit(1)
    
    success, message = fix_string_cells(path, dry_run)
    print(f"{path}: {message}")
    return 0 if success else 1


if __name__ == '__main__':
    sys.exit(main())
