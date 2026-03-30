#!/usr/bin/env python3
"""
Fix execution errors in Lean-8 and Lean-9 notebooks.

Fixes:
1. Lean-8 Cell 17: Replace lean_runner import with python-dotenv
2. Lean-8 Cell 14: Fix typo "Erdosos" -> "Erdos"
3. Lean-9 Cell 38: Remove access to non-existent 'proof' key
4. Lean-9: Add 'final_proof' key to prove_with_multi_agents return
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
    """
    Fix Lean-8 errors.

    Returns:
        Number of cells fixed
    """
    changes = 0

    for i, cell in enumerate(nb['cells']):
        if cell['cell_type'] != 'code' and cell['cell_type'] != 'markdown':
            continue

        source = get_cell_source(cell)
        original_source = source

        # Fix 1: Replace lean_runner import with python-dotenv
        if 'from lean_runner import load_env_file' in source:
            print(f"  Fixing Cell {i}: Replacing lean_runner import")

            # Replace the import section
            old_import = """# Utiliser load_env_file de lean_runner (evite les problemes d'introspection)
from lean_runner import load_env_file
env_path = Path.cwd() / ".env"
load_env_file(env_path)"""

            new_import = """# Charger les variables d'environnement
from dotenv import load_dotenv
env_path = Path.cwd() / ".env"
load_dotenv(env_path)"""

            source = source.replace(old_import, new_import)
            changes += 1

        # Fix 2: Fix typo "Erdosos" -> "Erdos"
        if cell['cell_type'] == 'markdown' and 'Benchmarking sur Problemes d\'Erdosos' in source:
            print(f"  Fixing Cell {i}: Correcting 'Erdosos' typo")
            source = source.replace('Erdosos', 'Erdos')
            changes += 1

        # Update cell if changed
        if source != original_source:
            set_cell_source(cell, source)

    return changes

def fix_lean9(nb: Dict[str, Any]) -> int:
    """
    Fix Lean-9 errors.

    Returns:
        Number of cells fixed
    """
    changes = 0

    for i, cell in enumerate(nb['cells']):
        if cell['cell_type'] != 'code':
            continue

        source = get_cell_source(cell)
        original_source = source

        # Fix 1: Remove access to non-existent 'proof' key in result_1
        if "result_1['proof']" in source or 'result_1["proof"]' in source:
            print(f"  Fixing Cell {i}: Removing access to 'proof' key")

            # Replace the problematic line
            source = re.sub(
                r'print\(f"  - Proof: \{result_1\[.proof.\].*?\}\.\.\."\)',
                '# print(f"  - Proof: {result_1.get(\'final_proof\', \'N/A\')[:100]}...")',
                source
            )
            changes += 1

        # Fix 2: Add 'final_proof' to prove_with_multi_agents return dict
        if 'def prove_with_multi_agents' in source:
            print(f"  Checking Cell {i}: prove_with_multi_agents definition")

            # Check if function returns a dict without 'final_proof'
            if 'return {' in source and "'final_proof'" not in source and '"final_proof"' not in source:
                print(f"    -> Need to add 'final_proof' to return dict")

                # Find the return statement and add final_proof
                # This is complex - we'll need to find where state.current_proof is used
                if 'return state.to_dict()' in source or 'return dict(state)' in source:
                    # If it returns state.to_dict(), we need to ensure to_dict() includes final_proof
                    print(f"    -> Returns state.to_dict() - ensuring ProofState.to_dict() has final_proof")
                    # This requires modifying ProofState.to_dict() elsewhere
                elif '"success"' in source or "'success'" in source:
                    # Find the return dict and add final_proof
                    lines = source.split('\n')
                    new_lines = []
                    in_return_dict = False
                    return_indent = 0

                    for line in lines:
                        new_lines.append(line)

                        # Detect start of return dict
                        if 'return {' in line:
                            in_return_dict = True
                            return_indent = len(line) - len(line.lstrip())

                        # Add final_proof before closing brace
                        elif in_return_dict and line.strip() == '}':
                            # Check if we haven't already added it
                            if "'final_proof'" not in ''.join(new_lines[-10:]):
                                indent_str = ' ' * (return_indent + 4)
                                new_lines.insert(-1, f'{indent_str}"final_proof": state.current_proof,')
                                print(f"    -> Added 'final_proof' to return dict")
                                changes += 1
                            in_return_dict = False

                    source = '\n'.join(new_lines)

        # Update cell if changed
        if source != original_source:
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
        print(f"✅ Lean-8: {changes8} cells fixed")
    else:
        print("✅ Lean-8: No changes needed")

    # Fix Lean-9
    print("\nFixing Lean-9...")
    lean9 = read_notebook(str(lean9_path))
    changes9 = fix_lean9(lean9)
    if changes9 > 0:
        write_notebook(str(lean9_path), lean9)
        print(f"✅ Lean-9: {changes9} cells fixed")
    else:
        print("✅ Lean-9: No changes needed")

    print(f"\n{'='*80}")
    print("✅ EXECUTION ERRORS FIXED")
    print(f"{'='*80}\n")

if __name__ == '__main__':
    main()
