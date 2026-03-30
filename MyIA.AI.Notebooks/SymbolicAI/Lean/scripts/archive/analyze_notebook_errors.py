#!/usr/bin/env python3
"""
Analyze specific cells in Lean notebooks to identify errors.
"""

import json
import sys
from pathlib import Path

def get_cell_source(cell):
    """Get cell source as string"""
    return ''.join(cell['source']) if isinstance(cell['source'], list) else cell['source']

def analyze_lean8():
    """Analyze Lean-8 errors"""
    notebook_path = Path(__file__).parent.parent / 'Lean-8-Agentic-Proving.ipynb'

    with open(notebook_path, 'r', encoding='utf-8') as f:
        nb = json.load(f)

    print("="*80)
    print("LEAN-8 ANALYSIS")
    print("="*80)

    # Find cell with lean_runner import
    for i, cell in enumerate(nb['cells']):
        source = get_cell_source(cell)
        if 'from lean_runner import' in source:
            print(f"\nCell {i} (ERREUR - lean_runner import):")
            print("-" * 60)
            print(source[:500])
            print("..." if len(source) > 500 else "")
            break

    # Find cell with "Benchmarking sur Problemes d'Erdosos"
    for i, cell in enumerate(nb['cells']):
        if cell['cell_type'] == 'markdown':
            source = get_cell_source(cell)
            if "Benchmarking sur Problemes d'Erdos" in source:
                print(f"\nCell {i} (Section Benchmarking):")
                print("-" * 60)
                print(source)

                # Check next cell
                if i + 1 < len(nb['cells']):
                    next_cell = nb['cells'][i + 1]
                    next_source = get_cell_source(next_cell)
                    print(f"\nCell {i+1} (Code apres Benchmarking - premiers 500 chars):")
                    print("-" * 60)
                    print(next_source[:500])
                break

def analyze_lean9():
    """Analyze Lean-9 errors"""
    notebook_path = Path(__file__).parent.parent / 'Lean-9-SK-Multi-Agents.ipynb'

    with open(notebook_path, 'r', encoding='utf-8') as f:
        nb = json.load(f)

    print("\n" + "="*80)
    print("LEAN-9 ANALYSIS")
    print("="*80)

    # Find cell with KeyError: 'proof'
    for i, cell in enumerate(nb['cells']):
        if cell['cell_type'] == 'code':
            source = get_cell_source(cell)
            if "result_1['proof']" in source or "result_1[\"proof\"]" in source:
                print(f"\nCell {i} (ERREUR - KeyError 'proof'):")
                print("-" * 60)
                print(source)

                # Find where result_1 is defined
                for j in range(max(0, i-5), i):
                    prev_source = get_cell_source(nb['cells'][j])
                    if 'result_1' in prev_source and '=' in prev_source:
                        print(f"\nCell {j} (Definition de result_1):")
                        print("-" * 60)
                        print(prev_source[:800])
                        break
                break

if __name__ == '__main__':
    analyze_lean8()
    analyze_lean9()
