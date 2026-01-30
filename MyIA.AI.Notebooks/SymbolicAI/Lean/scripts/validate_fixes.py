#!/usr/bin/env python3
"""
Validate that fixes have been applied correctly.
"""

import json
import ast
from pathlib import Path
from typing import Dict, Any, List

def read_notebook(path: str) -> Dict[str, Any]:
    """Read notebook JSON"""
    with open(path, 'r', encoding='utf-8', newline='') as f:
        return json.load(f)

def get_cell_source(cell: Dict[str, Any]) -> str:
    """Get cell source as string"""
    return ''.join(cell['source']) if isinstance(cell['source'], list) else cell['source']

def validate_lean8(nb: Dict[str, Any]) -> List[str]:
    """Validate Lean-8 fixes"""
    issues = []

    # Check Cell 17 for lean_runner import
    for i, cell in enumerate(nb['cells']):
        if cell['cell_type'] == 'code':
            source = get_cell_source(cell)

            if 'from lean_runner import' in source:
                issues.append(f"❌ Cell {i}: Still has lean_runner import")
            elif 'from dotenv import' in source and 'ImprovedSearchAgent' in source:
                # This should be Cell 17 with the fix
                print(f"✅ Cell {i}: dotenv import found (lean_runner fix applied)")

                # Validate Python syntax
                try:
                    ast.parse(source)
                    print(f"✅ Cell {i}: Python syntax valid")
                except SyntaxError as e:
                    issues.append(f"❌ Cell {i}: Syntax error - {e}")

    # Check for Erdosos typo
    for i, cell in enumerate(nb['cells']):
        if cell['cell_type'] == 'markdown':
            source = get_cell_source(cell)
            if 'Erdosos' in source:
                issues.append(f"❌ Cell {i}: 'Erdosos' typo still present")

    return issues

def validate_lean9(nb: Dict[str, Any]) -> List[str]:
    """Validate Lean-9 fixes"""
    issues = []
    fixed_cells = []

    for i, cell in enumerate(nb['cells']):
        if cell['cell_type'] == 'code':
            source = get_cell_source(cell)

            # Check for old 'proof' key access
            if "['proof']" in source or '["proof"]' in source:
                # Check if it's not 'final_proof'
                if "['final_proof']" not in source and '["final_proof"]' not in source:
                    issues.append(f"❌ Cell {i}: Still uses result['proof']")
                else:
                    # Validated fix
                    if 'result_' in source and "['final_proof']" in source:
                        fixed_cells.append(i)

            # Validate Python syntax for cells with result_
            if 'result_' in source and ('DEMO' in source or 'demo' in source):
                try:
                    ast.parse(source)
                    print(f"✅ Cell {i}: Python syntax valid (DEMO cell)")
                except SyntaxError as e:
                    issues.append(f"❌ Cell {i}: Syntax error - {e}")

    if fixed_cells:
        print(f"✅ Cells {fixed_cells}: 'final_proof' access validated")

    return issues

def main():
    """Main validation"""
    script_dir = Path(__file__).parent
    notebook_dir = script_dir.parent
    lean8_path = notebook_dir / 'Lean-8-Agentic-Proving.ipynb'
    lean9_path = notebook_dir / 'Lean-9-SK-Multi-Agents.ipynb'

    print("=" * 80)
    print("VALIDATE EXECUTION FIXES")
    print("=" * 80)

    all_issues = []

    # Validate Lean-8
    print("\nValidating Lean-8...")
    print("-" * 60)
    try:
        lean8 = read_notebook(str(lean8_path))
        issues8 = validate_lean8(lean8)
        all_issues.extend(issues8)
    except Exception as e:
        all_issues.append(f"❌ Lean-8: Failed to read/validate - {e}")

    # Validate Lean-9
    print("\nValidating Lean-9...")
    print("-" * 60)
    try:
        lean9 = read_notebook(str(lean9_path))
        issues9 = validate_lean9(lean9)
        all_issues.extend(issues9)
    except Exception as e:
        all_issues.append(f"❌ Lean-9: Failed to read/validate - {e}")

    # Summary
    print(f"\n{'='*80}")
    print("VALIDATION SUMMARY")
    print(f"{'='*80}")

    if all_issues:
        print(f"\n⚠️  {len(all_issues)} ISSUES FOUND:\n")
        for issue in all_issues:
            print(f"  {issue}")
        return 1
    else:
        print("\n✅ ALL VALIDATIONS PASSED")
        print("\nNext steps for manual testing:")
        print("  1. Lean-8 Cell 17:")
        print("     - Requires: pip install python-dotenv")
        print("     - Requires: .env file with OPENAI_API_KEY")
        print("     - Test: Execute cell and verify no ModuleNotFoundError")
        print()
        print("  2. Lean-9 Cells 38, 40, 42, 44:")
        print("     - Requires: All previous cells executed")
        print("     - Requires: prove_with_multi_agents defined")
        print("     - Test: Execute DEMO cells and verify no KeyError")
        return 0

if __name__ == '__main__':
    exit(main())
