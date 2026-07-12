#!/usr/bin/env python3
"""
Fix section numbering in Lean-8 and Lean-9 notebooks.
"""

import json
import sys
from pathlib import Path
from typing import Dict, Any
import re

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

def fix_lean8_sections(nb: Dict[str, Any]) -> int:
    """Fix section numbering in Lean-8"""
    changes = 0

    for i, cell in enumerate(nb['cells']):
        if cell['cell_type'] != 'markdown':
            continue

        source = get_cell_source(cell)
        lines = source.split('\n')
        modified = False

        for j, line in enumerate(lines):
            # Fix doublons
            if "de Theoremes de Theoremes" in line:
                lines[j] = line.replace("de Theoremes de Theoremes", "de Theoremes")
                modified = True
            elif "de Tactiques de Tactiques" in line:
                lines[j] = line.replace("de Tactiques de Tactiques", "de Tactiques")
                modified = True
            elif "sur Problemes d'Erdos sur Problemes d'Erd" in line:
                lines[j] = line.replace("sur Problemes d'Erdos sur Problemes d'Erd", "sur Problemes d'Erdos")
                modified = True

        if modified:
            set_cell_source(cell, '\n'.join(lines))
            changes += 1
            print(f"  Fixed cell {i}")

    return changes

def fix_lean9_sections(nb: Dict[str, Any]) -> int:
    """Renumber Lean-9 sections to be consistent"""
    changes = 0

    # Mapping ancien -> nouveau
    section_map = {
        "## 5. Integration avec Semantic Kernel": "## 1. Introduction : Semantic Kernel pour Preuves",
        "### 8.2-8.5 Plugins Semantic Kernel": "### 1.1. Vue d'ensemble des Plugins",
        "### 8.3.2 LeanSearchPlugin": "### 1.2. LeanSearchPlugin",
        "### 8.4-8.5 Plugins de Tactiques et Verification": "### 1.3. Plugins de Tactiques et Verification",
        "### 8.4.2 LeanVerificationPlugin": "### 1.4. LeanVerificationPlugin",
        "### 8.6 Definition des 5 Agents Specialises": "## 2. Architecture : 5 Agents Specialises",
        "### 8.6.2 SimpleAgent": "### 2.1. SimpleAgent : Agent Fallback",
        "### Patterns de Delegation Multi-Agents": "### 2.2. Patterns de Delegation Multi-Agents",
        "### Quand CriticAgent et CoordinatorAgent Interviennent": "### 2.3. Quand CriticAgent et CoordinatorAgent Interviennent",
        "### Vue d'Ensemble des 5 Agents Specialises": "### 2.4. Vue d'Ensemble des 5 Agents Specialises",
        "### 8.7 Strategies d'Orchestration": "## 3. Orchestration Multi-Agents",
        "### 8.8 Demonstration Complete": "### 3.1. Workflow Complet de Preuve",
        "### 8.7.1 ProofSelectionStrategy": "### 3.2. ProofSelectionStrategy : Selection d'Agent",
        "### 8.7.2 ProofTerminationStrategy": "### 3.3. ProofTerminationStrategy : Detection de Completion",
        "### 8.7.3 ProofAgentGroupChat": "### 3.4. ProofAgentGroupChat : Chat Multi-Agents",
        "### 8.7.4 Test des Strategies et Orchestration": "### 3.5. Test des Strategies",
        "## 🧪 Démonstrations Progressives": "## 4. Demonstrations Progressives",
        "### Execution DEMO_1 : Preuve Triviale": "### 4.1. DEMO_1 : Preuve Triviale",
        "### Execution DEMO_2 : Preuve Simple": "### 4.2. DEMO_2 : Preuve Simple",
        "### Execution DEMO_3 : Preuve Intermediaire": "### 4.3. DEMO_3 : Preuve Intermediaire",
        "### Execution DEMO_4 : Preuve Avancee": "### 4.4. DEMO_4 : Preuve Avancee",
    }

    for i, cell in enumerate(nb['cells']):
        if cell['cell_type'] != 'markdown':
            continue

        source = get_cell_source(cell)
        lines = source.split('\n')
        modified = False

        for j, line in enumerate(lines):
            for old, new in section_map.items():
                if line.strip().startswith(old):
                    lines[j] = line.replace(old, new)
                    modified = True
                    print(f"  Cell {i}: {old} -> {new}")
                    break

        if modified:
            set_cell_source(cell, '\n'.join(lines))
            changes += 1

    return changes

def main():
    """Main execution"""
    script_dir = Path(__file__).parent
    notebook_dir = script_dir.parent
    lean8_path = notebook_dir / 'Lean-8-Agentic-Proving.ipynb'
    lean9_path = notebook_dir / 'Lean-9-SK-Multi-Agents.ipynb'

    print("=" * 80)
    print("FIX SECTION NUMBERING")
    print("=" * 80)

    # Fix Lean-8
    print("\nFixing Lean-8 section titles...")
    lean8 = read_notebook(str(lean8_path))
    changes8 = fix_lean8_sections(lean8)
    if changes8 > 0:
        write_notebook(str(lean8_path), lean8)
        print(f"✅ Lean-8: {changes8} cells fixed")
    else:
        print("✅ Lean-8: No changes needed")

    # Fix Lean-9
    print("\nRenumbering Lean-9 sections...")
    lean9 = read_notebook(str(lean9_path))
    changes9 = fix_lean9_sections(lean9)
    if changes9 > 0:
        write_notebook(str(lean9_path), lean9)
        print(f"✅ Lean-9: {changes9} cells renumbered")
    else:
        print("✅ Lean-9: No changes needed")

    print(f"\n{'='*80}")
    print("✅ SECTION NUMBERING FIXED")
    print(f"{'='*80}\n")

if __name__ == '__main__':
    main()
