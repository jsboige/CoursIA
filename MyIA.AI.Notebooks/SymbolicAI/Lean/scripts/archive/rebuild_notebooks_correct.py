#!/usr/bin/env python3
"""
Rebuild Lean-8 and Lean-9 notebooks correctly from original version.

Fixes the conceptual migration error where SK concepts remained in Lean-8.
"""

import json
import sys
from pathlib import Path
from typing import Dict, Any, List

def read_notebook(path: str) -> Dict[str, Any]:
    """Read notebook JSON with proper encoding"""
    with open(path, 'r', encoding='utf-8', newline='') as f:
        return json.load(f)

def write_notebook(path: str, nb: Dict[str, Any]) -> None:
    """Write notebook JSON with LF line endings (Unix style)"""
    with open(path, 'w', encoding='utf-8', newline='\n') as f:
        json.dump(nb, f, indent=1, ensure_ascii=False)
        f.write('\n')  # Ensure trailing newline

def get_cell_source(cell: Dict[str, Any]) -> str:
    """Get cell source as string"""
    return ''.join(cell['source']) if isinstance(cell['source'], list) else cell['source']

def create_notebook_base() -> Dict[str, Any]:
    """Create base notebook structure"""
    return {
        "cells": [],
        "metadata": {
            "kernelspec": {
                "display_name": "Python 3 (WSL)",
                "language": "python",
                "name": "python3"
            },
            "language_info": {
                "name": "python",
                "version": "3.10.0"
            }
        },
        "nbformat": 4,
        "nbformat_minor": 2
    }

def create_navigation_cell(prev_notebook: str, next_notebook: str) -> Dict[str, Any]:
    """Create navigation header cell"""
    source = f"**Navigation** : [← {prev_notebook}]({prev_notebook}.ipynb) | [Index](Lean-1-Setup.ipynb) | [{next_notebook} →]({next_notebook}.ipynb)\n\n---\n\n"

    return {
        "cell_type": "markdown",
        "metadata": {},
        "source": [source]
    }

def rebuild_lean8_adhoc(original_nb: Dict[str, Any]) -> Dict[str, Any]:
    """
    Rebuild Lean-8 with ad-hoc agents only.

    Extracts:
    - Cells 0-10: Agents ad-hoc (Introduction + 4 agents)
    - Cells 54-63: Harmonic Aristotle + Exercises
    """
    lean8 = create_notebook_base()

    # Part 1: Ad-hoc agents (cells 0-10)
    print("  Extracting cells 0-10 (Ad-hoc agents)...")
    lean8['cells'].extend(original_nb['cells'][0:11])  # 0-10 inclusive

    # Part 2: Harmonic Aristotle + Exercises (cells 54-63)
    print("  Extracting cells 54-63 (Harmonic Aristotle + Exercises)...")
    lean8['cells'].extend(original_nb['cells'][54:64])  # 54-63 inclusive

    print(f"  Total cells in Lean-8: {len(lean8['cells'])}")
    return lean8

def rebuild_lean9_sk(original_nb: Dict[str, Any]) -> Dict[str, Any]:
    """
    Rebuild Lean-9 with complete SK implementation.

    Extracts:
    - Navigation header (new)
    - Cells 10-53: Complete SK (ProofState, Plugins, Agents, Strategies, Demos)
    """
    lean9 = create_notebook_base()

    # Add navigation
    print("  Adding navigation header...")
    nav_cell = create_navigation_cell("Lean-8-Agentic-Proving", "Lean-10-LeanDojo")
    lean9['cells'].append(nav_cell)

    # Extract SK content (cells 10-53 from original)
    print("  Extracting cells 10-53 (Complete SK implementation)...")
    sk_cells = original_nb['cells'][10:54]  # 10-53 inclusive

    # Update first cell title
    first_cell = sk_cells[0]
    if first_cell['cell_type'] == 'markdown':
        source = get_cell_source(first_cell)
        # Change "## 🎯 Architecture" to "# Lean 9 : Multi-Agents avec Semantic Kernel"
        new_source = "# Lean 9 : Multi-Agents avec Semantic Kernel\n\n" + source
        lines = new_source.split('\n')
        first_cell['source'] = [line + '\n' for line in lines[:-1]] + ([lines[-1]] if lines[-1] else [])

    lean9['cells'].extend(sk_cells)

    print(f"  Total cells in Lean-9: {len(lean9['cells'])}")
    return lean9

def renumber_sections_lean8(nb: Dict[str, Any]) -> None:
    """Renumber sections in Lean-8 to be consistent"""
    section_map = {
        "## 1. Agent de Recherche": "## 1. Agent de Recherche de Theoremes",
        "## 2. Agent de Generation": "## 2. Agent de Generation de Tactiques",
        "## 3. Agent de Verification": "## 3. Agent de Verification",
        "## 4. Agent Orchestrateur": "## 4. Agent Orchestrateur",
        "## 6. Techniques de Harmonic Aristotle": "## 5. Techniques de Harmonic Aristotle",
        "## 7. Benchmarking": "## 6. Benchmarking sur Problemes d'Erdos",
        "## 8. Exercices": "## 7. Exercices",
    }

    for cell in nb['cells']:
        if cell['cell_type'] != 'markdown':
            continue

        source = get_cell_source(cell)
        modified = False

        for old, new in section_map.items():
            if source.startswith(old):
                source = source.replace(old, new, 1)
                modified = True
                break

        if modified:
            lines = source.split('\n')
            cell['source'] = [line + '\n' for line in lines[:-1]] + ([lines[-1]] if lines[-1] else [])

def main():
    """Main execution"""
    script_dir = Path(__file__).parent
    notebook_dir = script_dir.parent
    original_path = notebook_dir / 'lean8_original_temp.ipynb'

    print("=" * 80)
    print("REBUILD LEAN-8 AND LEAN-9 NOTEBOOKS FROM ORIGINAL")
    print("=" * 80)

    # Check original exists
    if not original_path.exists():
        print(f"\nError: Original notebook not found at {original_path}")
        print("Expected it to be extracted by previous commands.")
        sys.exit(1)

    # Read original
    print(f"\nReading original notebook...")
    original = read_notebook(str(original_path))
    print(f"  Original has {len(original['cells'])} cells")

    # Rebuild Lean-8
    print(f"\n{'='*80}")
    print("REBUILDING LEAN-8 (AD-HOC ONLY)")
    print(f"{'='*80}")
    lean8 = rebuild_lean8_adhoc(original)
    renumber_sections_lean8(lean8)

    lean8_path = notebook_dir / 'Lean-8-Agentic-Proving.ipynb'
    write_notebook(str(lean8_path), lean8)
    print(f"\n✅ Lean-8 rebuilt: {lean8_path}")
    print(f"   {len(lean8['cells'])} cells (ad-hoc agents + Harmonic Aristotle)")

    # Rebuild Lean-9
    print(f"\n{'='*80}")
    print("REBUILDING LEAN-9 (SK COMPLETE)")
    print(f"{'='*80}")
    lean9 = rebuild_lean9_sk(original)

    lean9_path = notebook_dir / 'Lean-9-SK-Multi-Agents.ipynb'
    write_notebook(str(lean9_path), lean9)
    print(f"\n✅ Lean-9 rebuilt: {lean9_path}")
    print(f"   {len(lean9['cells'])} cells (SK with explanations + demos)")

    # Summary
    print(f"\n{'='*80}")
    print("✅ RECONSTRUCTION COMPLETE")
    print(f"{'='*80}")
    print(f"\nLean-8: {len(lean8['cells'])} cells")
    print("  - Cells 0-10: Ad-hoc agents (TheoremSearch, Tactic, Verifier, Orchestrator)")
    print("  - Cells 11-21: Harmonic Aristotle + Exercises + Resume")
    print(f"\nLean-9: {len(lean9['cells'])} cells")
    print("  - Cell 0: Navigation")
    print("  - Cells 1-44: Complete SK (ProofState, Plugins, Agents, Strategies, Demos)")
    print(f"\n{'='*80}")
    print("\nNext steps:")
    print("1. Review git diff to confirm changes")
    print("2. Apply markdown formatting if needed")
    print("3. Test notebooks functionally")
    print(f"{'='*80}\n")

if __name__ == '__main__':
    main()
