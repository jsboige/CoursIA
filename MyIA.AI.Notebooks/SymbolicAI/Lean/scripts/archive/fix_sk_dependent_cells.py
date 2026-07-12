#!/usr/bin/env python3
"""
Fix SK-dependent cells (28, 30) to be conditional on SK_AVAILABLE.
"""

import json
from pathlib import Path


def read_notebook(path: str):
    with open(path, 'r', encoding='utf-8', newline='') as f:
        return json.load(f)


def write_notebook(path: str, nb):
    with open(path, 'w', encoding='utf-8', newline='\n') as f:
        json.dump(nb, f, indent=1, ensure_ascii=False)
        f.write('\n')


def get_cell_source(cell):
    return ''.join(cell['source']) if isinstance(cell['source'], list) else cell['source']


def set_cell_source(cell, source):
    lines = source.split('\n')
    cell['source'] = [line + '\n' for line in lines[:-1]] + ([lines[-1]] if lines[-1] else [])


# Conditional wrapper for SK-dependent cells
CELL_28_REPLACEMENT = '''# =============================================================================
# ProofSelectionStrategy - Selection basee sur l'etat partage
# =============================================================================
# NOTE: Ces classes SK ne sont definies que si SK est disponible.
# Le mode simulation n'en a pas besoin.

if SK_AVAILABLE:
    from semantic_kernel.agents.strategies.selection.selection_strategy import SelectionStrategy

    class ProofSelectionStrategy(SelectionStrategy):
        """Strategie de selection SK (non utilisee en mode simulation)."""
        pass
else:
    print("ProofSelectionStrategy: Skipped (SK non disponible)")
'''

CELL_30_REPLACEMENT = '''# =============================================================================
# ProofTerminationStrategy - Terminaison basee sur l'etat partage
# =============================================================================
# NOTE: Ces classes SK ne sont definies que si SK est disponible.
# Le mode simulation n'en a pas besoin.

if SK_AVAILABLE:
    from semantic_kernel.agents.strategies.termination.termination_strategy import TerminationStrategy

    class ProofTerminationStrategy(TerminationStrategy):
        """Strategie de terminaison SK (non utilisee en mode simulation)."""
        pass
else:
    print("ProofTerminationStrategy: Skipped (SK non disponible)")
'''


def main():
    script_dir = Path(__file__).parent
    notebook_dir = script_dir.parent
    lean9_path = notebook_dir / 'Lean-9-SK-Multi-Agents.ipynb'

    print("=" * 80)
    print("FIX SK-DEPENDENT CELLS (28, 30)")
    print("=" * 80)

    nb = read_notebook(str(lean9_path))
    print(f"Read {len(nb['cells'])} cells")

    changes = 0

    # Find and replace cells 28 and 30
    for i, cell in enumerate(nb['cells']):
        if cell['cell_type'] != 'code':
            continue
        src = get_cell_source(cell)

        if 'class ProofSelectionStrategy' in src and 'SelectionStrategy' in src:
            print(f"Found ProofSelectionStrategy in cell {i}")
            set_cell_source(cell, CELL_28_REPLACEMENT)
            print("  Made conditional on SK_AVAILABLE")
            changes += 1

        elif 'class ProofTerminationStrategy' in src and 'TerminationStrategy' in src:
            print(f"Found ProofTerminationStrategy in cell {i}")
            set_cell_source(cell, CELL_30_REPLACEMENT)
            print("  Made conditional on SK_AVAILABLE")
            changes += 1

    if changes >= 2:
        write_notebook(str(lean9_path), nb)
        print(f"\nNotebook saved with {changes} update(s)")
    else:
        print(f"\nOnly {changes}/2 cells found")


if __name__ == '__main__':
    main()
