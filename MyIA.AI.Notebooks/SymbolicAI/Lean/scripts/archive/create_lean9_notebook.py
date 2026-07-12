#!/usr/bin/env python3
"""
Create Lean-9-SK-Multi-Agents.ipynb by extracting Semantic Kernel content from Lean-8
"""

import json
import sys
from pathlib import Path
from typing import List, Dict, Any

def get_cell_summary(cell: Dict[str, Any], idx: int) -> str:
    """Get a summary of a cell for analysis"""
    if cell['cell_type'] == 'markdown':
        source = ''.join(cell['source']) if isinstance(cell['source'], list) else cell['source']
        first_line = source.split('\n')[0][:80]
        return f"Cell {idx}: [MD] {first_line}"
    else:
        source = ''.join(cell['source']) if isinstance(cell['source'], list) else cell['source']
        first_line = source.split('\n')[0][:80]
        return f"Cell {idx}: [CODE] {first_line}"

def analyze_notebook_structure(notebook_path: str) -> None:
    """Analyze notebook structure to identify SK cells"""

    print(f"Analyzing notebook: {notebook_path}")
    with open(notebook_path, 'r', encoding='utf-8') as f:
        nb = json.load(f)

    print(f"\nNotebook has {len(nb['cells'])} cells\n")
    print("=" * 100)
    print("STRUCTURE ANALYSIS")
    print("=" * 100)

    # Identify sections
    sk_start = None
    sk_end = None

    for idx, cell in enumerate(nb['cells']):
        summary = get_cell_summary(cell, idx)

        # Look for SK markers
        if cell['cell_type'] == 'markdown':
            source = ''.join(cell['source']) if isinstance(cell['source'], list) else cell['source']

            if 'Semantic Kernel' in source and sk_start is None:
                sk_start = idx
                print(f"\n>>> SK START: {summary}")

            if ('Démonstrations' in source or 'DEMO' in source or 'Demo' in source) and sk_start is not None and sk_end is None:
                sk_end = idx
                print(f"\n>>> SK END (before demos): {summary}")

        if cell['cell_type'] == 'code':
            source = ''.join(cell['source']) if isinstance(cell['source'], list) else cell['source']

            if '@kernel_function' in source or 'ChatHistory' in source or 'GroupChat' in source:
                if idx >= 10 and idx <= 45:  # Approximate range
                    print(f"  SK Cell: {summary}")

    if sk_start is not None:
        print(f"\n{'=' * 100}")
        print(f"SK Section identified: cells {sk_start} to {sk_end if sk_end else '?'}")
        print(f"{'=' * 100}")

def create_lean9_notebook(source_path: str, target_path: str) -> None:
    """Create Lean-9 notebook with SK content"""

    print(f"\nCreating Lean-9 notebook...")
    print(f"Source: {source_path}")
    print(f"Target: {target_path}")

    with open(source_path, 'r', encoding='utf-8') as f:
        source_nb = json.load(f)

    # Create new notebook structure
    new_nb = {
        "cells": [],
        "metadata": source_nb['metadata'].copy(),
        "nbformat": source_nb['nbformat'],
        "nbformat_minor": source_nb['nbformat_minor']
    }

    # Update notebook metadata
    if 'title' in new_nb['metadata']:
        new_nb['metadata']['title'] = "Lean 9 - Multi-Agents avec Semantic Kernel"

    # Add introduction cell
    intro_cell = {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "# Lean 9 - Multi-Agents avec Semantic Kernel\n",
            "\n",
            "## Introduction\n",
            "\n",
            "Ce notebook explore l'utilisation de **Microsoft Semantic Kernel (SK)** pour orchestrer des agents autonomes dans la preuve de théorèmes Lean 4.\n",
            "\n",
            "**Prérequis** : Notebook Lean-8 (fondations agents ad-hoc, orchestration basique)\n",
            "\n",
            "**Objectifs** :\n",
            "- Architecture multi-agents avec SK\n",
            "- Plugins avec décorateur `@kernel_function`\n",
            "- Coordination via `GroupChat` et stratégies de sélection/terminaison\n",
            "- Gestion d'état partagé (`ProofState`)\n",
            "- Intégration production\n",
            "\n",
            "**Durée estimée** : 50 min\n",
            "\n",
            "---\n"
        ]
    }
    new_nb['cells'].append(intro_cell)

    # Extract SK cells (roughly 11-43 based on analysis)
    # We'll look for cells containing SK markers
    sk_keywords = [
        '@kernel_function',
        'ProofState',
        'ChatHistory',
        'GroupChat',
        'KernelPlugin',
        'ChatCompletionAgent'
    ]

    print("\nExtracting SK cells...")
    extracted_count = 0

    for idx, cell in enumerate(source_nb['cells']):
        source = ''.join(cell['source']) if isinstance(cell['source'], list) else cell['source']

        # Skip early cells (before SK introduction)
        if idx < 10:
            continue

        # Stop at demos section
        if idx > 43:
            break

        # Include markdown cells in SK range
        if cell['cell_type'] == 'markdown':
            if any(keyword in source for keyword in ['Semantic Kernel', '8.2', '8.3', '8.4', '8.5']):
                new_nb['cells'].append(cell)
                extracted_count += 1
                print(f"  Added markdown cell {idx}")

        # Include code cells with SK markers
        elif cell['cell_type'] == 'code':
            if any(keyword in source for keyword in sk_keywords):
                new_nb['cells'].append(cell)
                extracted_count += 1
                print(f"  Added code cell {idx}")

    # Add conclusion cell
    conclusion_cell = {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "\n---\n",
            "\n",
            "## Conclusion\n",
            "\n",
            "Vous avez maintenant une architecture complète de multi-agents avec Semantic Kernel pour la preuve automatique de théorèmes Lean 4.\n",
            "\n",
            "**Prochain notebook** : Lean-10 (applications avancées)\n",
            "\n",
            "**Ressources** :\n",
            "- [Semantic Kernel Documentation](https://learn.microsoft.com/en-us/semantic-kernel/)\n",
            "- [Lean 4 Documentation](https://lean-lang.org/documentation/)\n",
            "- [Mathlib4](https://github.com/leanprover-community/mathlib4)\n"
        ]
    }
    new_nb['cells'].append(conclusion_cell)

    print(f"\nExtracted {extracted_count} cells")
    print(f"Total cells in new notebook: {len(new_nb['cells'])}")

    # Save new notebook
    with open(target_path, 'w', encoding='utf-8') as f:
        json.dump(new_nb, f, indent=1, ensure_ascii=False)

    print(f"\n✅ Created {target_path}")

if __name__ == '__main__':
    notebook_dir = Path(__file__).parent
    lean8_path = notebook_dir / 'Lean-8-Agentic-Proving.ipynb'
    lean9_path = notebook_dir / 'Lean-9-SK-Multi-Agents.ipynb'

    if not lean8_path.exists():
        print(f"Error: Source notebook not found at {lean8_path}")
        sys.exit(1)

    # First analyze
    analyze_notebook_structure(str(lean8_path))

    # Then create Lean-9
    print("\n" + "=" * 100)
    create_lean9_notebook(str(lean8_path), str(lean9_path))
