#!/usr/bin/env python3
"""
Update Lean-10-LeanDojo.ipynb content and references in other notebooks
"""

import json
import sys
from pathlib import Path
from typing import Dict, Any

def read_notebook(path: str) -> Dict[str, Any]:
    """Read notebook JSON"""
    with open(path, 'r', encoding='utf-8') as f:
        return json.load(f)

def write_notebook(path: str, nb: Dict[str, Any]) -> None:
    """Write notebook JSON"""
    with open(path, 'w', encoding='utf-8') as f:
        json.dump(nb, f, indent=1, ensure_ascii=False)

def get_cell_source(cell: Dict[str, Any]) -> str:
    """Get cell source as string"""
    return ''.join(cell['source']) if isinstance(cell['source'], list) else cell['source']

def set_cell_source(cell: Dict[str, Any], source: str) -> None:
    """Set cell source from string"""
    lines = source.split('\n')
    cell['source'] = [line + '\n' for line in lines[:-1]] + ([lines[-1]] if lines[-1] else [])

def update_lean10_content(nb: Dict[str, Any]) -> int:
    """Update Lean-10 notebook title and navigation"""
    changes = 0

    # Cell 0: Update title and navigation
    if nb['cells'][0]['cell_type'] == 'markdown':
        source = get_cell_source(nb['cells'][0])

        # Replace "Lean 9" with "Lean 10"
        new_source = source.replace('# Lean 9 :', '# Lean 10 :')
        new_source = new_source.replace('# Lean 9:', '# Lean 10:')

        # Update navigation to point to Lean-9-SK-Multi-Agents
        new_source = new_source.replace(
            '[← Lean-8-Agentic-Proving](Lean-8-Agentic-Proving.ipynb)',
            '[← Lean-9-SK-Multi-Agents](Lean-9-SK-Multi-Agents.ipynb)'
        )
        new_source = new_source.replace(
            '[← Lean-8-Agentic-Proving]',
            '[← Lean-9-SK-Multi-Agents]'
        )

        if new_source != source:
            set_cell_source(nb['cells'][0], new_source)
            print(f"  ✓ Updated cell 0: title and navigation")
            changes += 1

    return changes

def update_lean9_navigation(nb: Dict[str, Any]) -> int:
    """Update Lean-9 navigation to point to Lean-10"""
    changes = 0

    # Cell 0: Update navigation
    if nb['cells'][0]['cell_type'] == 'markdown':
        source = get_cell_source(nb['cells'][0])

        # Update navigation to point to Lean-10-LeanDojo
        new_source = source.replace(
            '[Lean-10-Advanced →](Lean-10-Advanced.ipynb)',
            '[Lean-10-LeanDojo →](Lean-10-LeanDojo.ipynb)'
        )
        new_source = new_source.replace(
            'Lean-10-Advanced',
            'Lean-10-LeanDojo'
        )

        # Also fix the conclusion if it references Lean-10
        if new_source != source:
            set_cell_source(nb['cells'][0], new_source)
            print(f"  ✓ Updated Lean-9 navigation: Lean-10-Advanced → Lean-10-LeanDojo")
            changes += 1

    # Last cell: Update conclusion if needed
    last_cell = nb['cells'][-1]
    if last_cell['cell_type'] == 'markdown':
        source = get_cell_source(last_cell)

        if 'Lean-10' in source or 'Prochain notebook' in source:
            new_source = source.replace(
                'Lean-10',
                'Lean-10-LeanDojo'
            )

            if new_source != source:
                set_cell_source(last_cell, new_source)
                print(f"  ✓ Updated Lean-9 conclusion reference")
                changes += 1

    return changes

def main():
    """Main execution"""
    notebook_dir = Path(__file__).parent
    lean10_path = notebook_dir / 'Lean-10-LeanDojo.ipynb'
    lean9_path = notebook_dir / 'Lean-9-SK-Multi-Agents.ipynb'

    print("=" * 80)
    print("UPDATE LEAN-10 CONTENT")
    print("=" * 80)

    if not lean10_path.exists():
        print(f"Error: {lean10_path} not found")
        sys.exit(1)

    lean10 = read_notebook(str(lean10_path))
    changes = update_lean10_content(lean10)

    if changes > 0:
        write_notebook(str(lean10_path), lean10)
        print(f"\n✅ Lean-10: {changes} changes saved")
    else:
        print(f"\n⚠ Lean-10: No changes needed")

    print("\n" + "=" * 80)
    print("UPDATE LEAN-9 NAVIGATION")
    print("=" * 80)

    if not lean9_path.exists():
        print(f"Error: {lean9_path} not found")
        sys.exit(1)

    lean9 = read_notebook(str(lean9_path))
    changes = update_lean9_navigation(lean9)

    if changes > 0:
        write_notebook(str(lean9_path), lean9)
        print(f"\n✅ Lean-9: {changes} changes saved")
    else:
        print(f"\n⚠ Lean-9: No changes needed")

    print("\n" + "=" * 80)
    print("✅ ALL REFERENCES UPDATED")
    print("=" * 80)

if __name__ == '__main__':
    main()
