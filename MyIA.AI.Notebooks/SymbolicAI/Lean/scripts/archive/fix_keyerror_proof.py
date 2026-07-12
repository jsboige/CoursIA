#!/usr/bin/env python3
"""
Fix KeyError: 'proof' -> 'final_proof' in all demo cells
"""

import json
import sys
import re
from pathlib import Path

def fix_keyerror_proof(notebook_path: str) -> None:
    """Fix KeyError by replacing result['proof'] with result['final_proof']"""

    print(f"Loading notebook: {notebook_path}")
    with open(notebook_path, 'r', encoding='utf-8') as f:
        nb = json.load(f)

    fixed_count = 0
    total_cells = len(nb['cells'])

    print(f"Scanning {total_cells} cells for result_N['proof'] pattern...")

    for idx, cell in enumerate(nb['cells']):
        if cell['cell_type'] != 'code':
            continue

        source = ''.join(cell['source']) if isinstance(cell['source'], list) else cell['source']

        # Check if this cell contains the problematic pattern
        if "['proof']" in source and 'result_' in source:
            original_source = source

            # Replace result_N['proof'] with result_N['final_proof']
            source = re.sub(r"(result_\d+\[)'proof'(\])", r"\1'final_proof'\2", source)

            if source != original_source:
                # Convert back to list format
                cell['source'] = source.split('\n')
                # Add newlines back (except last line)
                cell['source'] = [line + '\n' for line in cell['source'][:-1]] + [cell['source'][-1]]

                fixed_count += 1
                print(f"  ✓ Fixed cell index {idx} (cell #{idx+1})")

                # Show what was changed
                for line_num, (old_line, new_line) in enumerate(zip(original_source.split('\n'), source.split('\n'))):
                    if old_line != new_line:
                        print(f"    Line {line_num+1}: {old_line.strip()}")
                        print(f"         -> {new_line.strip()}")

    if fixed_count > 0:
        # Save backup
        backup_path = notebook_path + '.backup'
        print(f"\nCreating backup: {backup_path}")
        with open(backup_path, 'w', encoding='utf-8') as f:
            json.dump(nb, f, indent=1, ensure_ascii=False)

        # Save fixed notebook
        print(f"Saving fixed notebook: {notebook_path}")
        with open(notebook_path, 'w', encoding='utf-8') as f:
            json.dump(nb, f, indent=1, ensure_ascii=False)

        print(f"\n✅ Fixed {fixed_count} cells successfully!")
    else:
        print("\n⚠ No changes were made - pattern not found")

if __name__ == '__main__':
    notebook_path = Path(__file__).parent / 'Lean-8-Agentic-Proving.ipynb'

    if not notebook_path.exists():
        print(f"Error: Notebook not found at {notebook_path}")
        sys.exit(1)

    fix_keyerror_proof(str(notebook_path))
