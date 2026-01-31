#!/usr/bin/env python3
"""
Fix DEMOS definition to include expected_lemmas field.
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


# New DEMOS definition with expected_lemmas
NEW_DEMOS = '''DEMOS = [
    {
        "name": "DEMO_1_TRIVIAL",
        "theorem": "theorem demo_rfl (n : Nat) : n = n",
        "description": "Reflexivite - 1 lemme direct (Eq.refl)",
        "expected_iterations": "2-3",
        "expected_lemmas": 1,
        "complexity": "Triviale"
    },
    {
        "name": "DEMO_2_COMPOSITION",
        "theorem": "theorem add_zero_comm (n m : Nat) : n + m + 0 = m + n",
        "description": "Composition - 2 lemmes (add_zero + add_comm)",
        "expected_iterations": "5-7",
        "expected_lemmas": 2,
        "complexity": "Simple - necessite combiner 2 lemmes"
    },
    {
        "name": "DEMO_3_MULTI_REWRITE",
        "theorem": "theorem quad_comm (a b c d : Nat) : (a + b) + (c + d) = (d + c) + (b + a)",
        "description": "Reecritures multiples - 4 applications de add_comm + add_assoc",
        "expected_iterations": "10-15",
        "expected_lemmas": 2,
        "complexity": "Intermediaire - chaine de reecritures"
    },
    {
        "name": "DEMO_4_STRUCTURED",
        "theorem": "theorem distrib_both (a b c : Nat) : (a + b) * c + a * c = a * c + a * c + b * c",
        "description": "Preuve structuree - right_distrib + add_assoc + add_comm",
        "expected_iterations": "15-20",
        "expected_lemmas": 3,
        "complexity": "Avancee - decomposition + recombinaison"
    }
]'''


def main():
    script_dir = Path(__file__).parent
    notebook_dir = script_dir.parent
    lean9_path = notebook_dir / 'Lean-9-SK-Multi-Agents.ipynb'

    print("=" * 80)
    print("FIX DEMOS - ADD expected_lemmas FIELD")
    print("=" * 80)

    nb = read_notebook(str(lean9_path))
    print(f"Read {len(nb['cells'])} cells")

    changes = 0

    # Find and replace DEMOS definition
    for i, cell in enumerate(nb['cells']):
        if cell['cell_type'] != 'code':
            continue
        src = get_cell_source(cell)

        if 'DEMOS = [' in src and 'DEMO_1_TRIVIAL' in src:
            print(f"Found DEMOS in cell {i}")

            # Find DEMOS definition boundaries
            start = src.find('DEMOS = [')
            bracket_count = 0
            end = start
            for j, c in enumerate(src[start:]):
                if c == '[':
                    bracket_count += 1
                elif c == ']':
                    bracket_count -= 1
                    if bracket_count == 0:
                        end = start + j + 1
                        break

            new_src = src[:start] + NEW_DEMOS + src[end:]
            set_cell_source(cell, new_src)
            print("  Added expected_lemmas field to all 4 demos")
            changes += 1
            break

    if changes >= 1:
        write_notebook(str(lean9_path), nb)
        print(f"\nNotebook saved with {changes} update(s)")
    else:
        print("\nDEMOS definition not found!")


if __name__ == '__main__':
    main()
