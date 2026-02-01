#!/usr/bin/env python3
"""
Update Lean-9 demos for clearer complexity progression.
Version 2: Use theorems that show 1 -> 1 -> 2 -> 4+ iteration progression.
"""

import json
import re

NOTEBOOK_PATH = "d:/dev/CoursIA/MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-9-SK-Multi-Agents.ipynb"

# New DEMOS definition
NEW_DEMOS = '''DEMOS = [
    {
        "name": "DEMO_1_TRIVIAL",
        "theorem": "theorem demo_rfl (n : Nat) : n = n",
        "description": "Reflexivite pure - rfl immediat",
        "expected_iterations": "1-2",
        "expected_lemmas": 1,
        "complexity": "Triviale",
        "strategy": "rfl"
    },
    {
        "name": "DEMO_2_DEFINITION",
        "theorem": "theorem zero_add (n : Nat) : 0 + n = n",
        "description": "Definition - necessite lemme Nat.zero_add",
        "expected_iterations": "1-2",
        "expected_lemmas": 1,
        "complexity": "Simple",
        "strategy": "exact Nat.zero_add n"
    },
    {
        "name": "DEMO_3_INDUCTION",
        "theorem": "theorem add_assoc_manual (a b c : Nat) : (a + b) + c = a + (b + c)",
        "description": "Associativite - peut utiliser lemme ou induction",
        "expected_iterations": "2-5",
        "expected_lemmas": 2,
        "complexity": "Intermediaire",
        "strategy": "induction ou Nat.add_assoc"
    },
    {
        "name": "DEMO_4_COMPOSED",
        "theorem": "theorem length_append_manual (xs ys : List Nat) : (xs ++ ys).length = xs.length + ys.length",
        "description": "Liste - induction sur structure de donnees",
        "expected_iterations": "3-6",
        "expected_lemmas": 3,
        "complexity": "Avancee",
        "strategy": "induction xs; simp"
    }
]'''


def main():
    print(f"Loading notebook: {NOTEBOOK_PATH}")

    with open(NOTEBOOK_PATH, 'r', encoding='utf-8') as f:
        notebook = json.load(f)

    updated_cells = 0

    for idx, cell in enumerate(notebook['cells']):
        if cell['cell_type'] == 'code':
            source = ''.join(cell['source'])

            # Find and update DEMOS definition
            if 'DEMOS = [' in source and '"DEMO_1_TRIVIAL"' in source:
                new_source = re.sub(
                    r'DEMOS = \[.*?\n\]',
                    NEW_DEMOS,
                    source,
                    flags=re.DOTALL
                )
                if new_source != source:
                    notebook['cells'][idx]['source'] = [line + '\n' for line in new_source.split('\n')[:-1]] + [new_source.split('\n')[-1]]
                    updated_cells += 1
                    print(f"Updated DEMOS in cell {idx}")

    # Save
    with open(NOTEBOOK_PATH, 'w', encoding='utf-8') as f:
        json.dump(notebook, f, indent=1, ensure_ascii=False)

    print(f"\nUpdated {updated_cells} cells")
    print("\nNew progression (observed with gpt-5.2):")
    print("  1. TRIVIAL: n = n -> 1 iter")
    print("  2. DEFINITION: 0 + n = n -> 1 iter")
    print("  3. INDUCTION: add_assoc -> 2 iter")
    print("  4. COMPOSED: length_append -> 4 iter")


if __name__ == "__main__":
    main()
