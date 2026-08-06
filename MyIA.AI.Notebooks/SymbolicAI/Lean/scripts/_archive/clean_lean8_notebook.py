#!/usr/bin/env python3
"""
Clean Lean-8 notebook by removing SK content (extracted to Lean-9)
Keep only: ad-hoc foundations, basic orchestration, advanced techniques
"""

import json
import sys
from pathlib import Path
from typing import List, Dict, Any

def clean_lean8_notebook(notebook_path: str) -> None:
    """Remove SK cells and restructure Lean-8"""

    print(f"Loading notebook: {notebook_path}")
    with open(notebook_path, 'r', encoding='utf-8') as f:
        nb = json.load(f)

    original_count = len(nb['cells'])
    print(f"Original cell count: {original_count}")

    # SK keywords to identify cells to remove
    sk_keywords = [
        '@kernel_function',
        'ProofState',
        'ChatHistory',
        'GroupChat',
        'KernelPlugin',
        'ChatCompletionAgent',
        'ProofSelectionStrategy',
        'ProofTerminationStrategy',
        'ProofAgentGroupChat'
    ]

    # Identify cells to keep
    cells_to_keep = []
    cells_removed = []

    for idx, cell in enumerate(nb['cells']):
        source = ''.join(cell['source']) if isinstance(cell['source'], list) else cell['source']

        # Keep cells before SK introduction (0-9)
        if idx < 10:
            cells_to_keep.append((idx, cell))
            continue

        # Remove SK introduction and implementation (10-43)
        if idx >= 10 and idx <= 43:
            # Check if it's a SK cell
            if cell['cell_type'] == 'code':
                if any(keyword in source for keyword in sk_keywords):
                    cells_removed.append(idx)
                    print(f"  Removing SK code cell {idx}")
                    continue

            if cell['cell_type'] == 'markdown':
                if any(marker in source for marker in ['8.2', '8.3', '8.4', '8.5', 'Semantic Kernel']):
                    cells_removed.append(idx)
                    print(f"  Removing SK markdown cell {idx}")
                    continue

        # Keep everything after SK section (demos, advanced techniques, exercises)
        if idx > 43:
            cells_to_keep.append((idx, cell))
            continue

        # If we reach here, keep the cell (transition cells, etc.)
        cells_to_keep.append((idx, cell))

    # Update notebook
    nb['cells'] = [cell for _, cell in cells_to_keep]

    print(f"\nCells removed: {len(cells_removed)}")
    print(f"Cells kept: {len(cells_to_keep)}")
    print(f"New cell count: {len(nb['cells'])}")

    # Save backup
    backup_path = notebook_path + '.clean.backup'
    print(f"\nCreating backup: {backup_path}")
    with open(backup_path, 'w', encoding='utf-8') as f:
        json.dump(nb, f, indent=1, ensure_ascii=False)

    # Save cleaned notebook
    print(f"Saving cleaned notebook: {notebook_path}")
    with open(notebook_path, 'w', encoding='utf-8') as f:
        json.dump(nb, f, indent=1, ensure_ascii=False)

    print(f"\n✅ Cleaned Lean-8 successfully!")
    print(f"   Removed {len(cells_removed)} SK cells")
    print(f"   Kept {len(cells_to_keep)} foundational cells")

if __name__ == '__main__':
    notebook_path = Path(__file__).parent / 'Lean-8-Agentic-Proving.ipynb'

    if not notebook_path.exists():
        print(f"Error: Notebook not found at {notebook_path}")
        sys.exit(1)

    clean_lean8_notebook(str(notebook_path))
