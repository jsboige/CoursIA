#!/usr/bin/env python3
"""
Fix execution errors in Lean-8 and Lean-9 notebooks.

LEAN-8 FIXES:
1. Cell 17: Replace lean_runner import with python-dotenv
2. Cell 14: Fix typo "Erdosos" -> "Erdos"

LEAN-9 FIXES:
1. Cell 38+: Replace result['proof'] with result['final_proof']
"""

import json
import re
from pathlib import Path
from typing import Dict, Any

def read_notebook(path: str) -> Dict[str, Any]:
    """Read notebook JSON with proper encoding"""
    with open(path, 'r', encoding='utf-8', newline='') as f:
        return json.load(f)

def write_notebook(path: str, nb: Dict[str, Any]) -> None:
    """Write notebook JSON with LF line endings"""
    with open(path, 'w', encoding='utf-8', newline='\n') as f:
        json.dump(nb, f, indent=1, ensure_ascii=False)
        f.write('\n')

def get_cell_source(cell: Dict[str, Any]) -> str:
    """Get cell source as string"""
    return ''.join(cell['source']) if isinstance(cell['source'], list) else cell['source']

def set_cell_source(cell: Dict[str, Any], source: str) -> None:
    """Set cell source from string"""
    lines = source.split('\n')
    cell['source'] = [line + '\n' for line in lines[:-1]] + ([lines[-1]] if lines[-1] else [])

def fix_lean8(nb: Dict[str, Any]) -> int:
    """Fix Lean-8 errors"""
    changes = 0

    for i, cell in enumerate(nb['cells']):
        source = get_cell_source(cell)
        modified = False

        # Fix 1: Replace lean_runner import with python-dotenv
        if 'from lean_runner import load_env_file' in source:
            print(f"  Cell {i}: Replacing lean_runner import with python-dotenv")

            old_lines = [
                "# Utiliser load_env_file de lean_runner (evite les problemes d'introspection)",
                "from lean_runner import load_env_file",
                "env_path = Path.cwd() / \".env\"",
                "load_env_file(env_path)"
            ]

            new_lines = [
                "# Charger les variables d'environnement",
                "from dotenv import load_dotenv",
                "env_path = Path.cwd() / \".env\"",
                "load_dotenv(env_path)"
            ]

            for old_line, new_line in zip(old_lines, new_lines):
                source = source.replace(old_line, new_line)

            modified = True
            changes += 1

        # Fix 2: Fix typo "Erdosos" -> "Erdos"
        if 'Erdosos' in source:
            print(f"  Cell {i}: Fixing typo 'Erdosos' -> 'Erdos'")
            source = source.replace('Erdosos', 'Erdos')
            modified = True
            changes += 1

        if modified:
            set_cell_source(cell, source)

    return changes

def fix_lean9(nb: Dict[str, Any]) -> int:
    """Fix Lean-9 errors"""
    changes = 0

    for i, cell in enumerate(nb['cells']):
        if cell['cell_type'] != 'code':
            continue

        source = get_cell_source(cell)
        original = source

        # Fix: Replace result_X['proof'] with result_X['final_proof']
        # This handles result_1, result_2, result_3, result_4, etc.
        if "['proof']" in source or '["proof"]' in source:
            print(f"  Cell {i}: Replacing 'proof' with 'final_proof'")

            # Replace both quote styles
            source = source.replace("['proof']", "['final_proof']")
            source = source.replace('["proof"]', '["final_proof"]')

            changes += 1

        if source != original:
            set_cell_source(cell, source)

    return changes

def main():
    """Main execution"""
    script_dir = Path(__file__).parent
    notebook_dir = script_dir.parent
    lean8_path = notebook_dir / 'Lean-8-Agentic-Proving.ipynb'
    lean9_path = notebook_dir / 'Lean-9-SK-Multi-Agents.ipynb'

    print("=" * 80)
    print("FIX EXECUTION ERRORS - LEAN-8 AND LEAN-9")
    print("=" * 80)

    # Fix Lean-8
    print("\nFixing Lean-8...")
    lean8 = read_notebook(str(lean8_path))
    changes8 = fix_lean8(lean8)
    if changes8 > 0:
        write_notebook(str(lean8_path), lean8)
        print(f"✅ Lean-8: {changes8} fixes applied")
    else:
        print("✅ Lean-8: No changes needed")

    # Fix Lean-9
    print("\nFixing Lean-9...")
    lean9 = read_notebook(str(lean9_path))
    changes9 = fix_lean9(lean9)
    if changes9 > 0:
        write_notebook(str(lean9_path), lean9)
        print(f"✅ Lean-9: {changes9} fixes applied")
    else:
        print("✅ Lean-9: No changes needed")

    print(f"\n{'='*80}")
    print("✅ EXECUTION ERRORS FIXED")
    print(f"{'='*80}\n")
    print("Summary:")
    print(f"  Lean-8: {changes8} fixes (lean_runner import + Erdosos typo)")
    print(f"  Lean-9: {changes9} fixes (proof -> final_proof)")
    print()
    print("Next steps:")
    print("  1. Test Lean-8 cells 17-19")
    print("  2. Test Lean-9 cells 38-44 (DEMO_1 through DEMO_4)")

if __name__ == '__main__':
    main()
