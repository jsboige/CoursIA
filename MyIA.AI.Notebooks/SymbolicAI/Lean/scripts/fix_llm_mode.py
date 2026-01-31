#!/usr/bin/env python3
"""
Set USE_LLM_MODE = False to use simulation mode (which works).
SK agents have a different invoke signature and don't work with _run_fallback.
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


def main():
    script_dir = Path(__file__).parent
    notebook_dir = script_dir.parent
    lean9_path = notebook_dir / 'Lean-9-SK-Multi-Agents.ipynb'

    print("=" * 80)
    print("FIX USE_LLM_MODE - SET TO FALSE FOR SIMULATION")
    print("=" * 80)

    nb = read_notebook(str(lean9_path))
    print(f"Read {len(nb['cells'])} cells")

    changes = 0

    # Find and replace USE_LLM_MODE
    for i, cell in enumerate(nb['cells']):
        if cell['cell_type'] != 'code':
            continue
        src = get_cell_source(cell)

        if 'USE_LLM_MODE = True' in src and 'DEMOS = [' in src:
            print(f"Found USE_LLM_MODE in cell {i}")
            new_src = src.replace(
                'USE_LLM_MODE = True  # True pour LLM réel, False pour simulation',
                'USE_LLM_MODE = False  # False pour simulation (defaut), True pour LLM reel'
            )
            if new_src != src:
                set_cell_source(cell, new_src)
                print("  Changed USE_LLM_MODE from True to False")
                changes += 1
            break

    if changes >= 1:
        write_notebook(str(lean9_path), nb)
        print(f"\nNotebook saved with {changes} update(s)")
    else:
        print("\nUSE_LLM_MODE = True not found!")


if __name__ == '__main__':
    main()
