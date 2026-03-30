#!/usr/bin/env python3
"""
Fix DEMO configuration issues in Lean-9 notebook.

Fixes:
1. Remove forced USE_LLM_MODE = False (user should set this)
2. Update the outdated demos intro markdown
3. Fix any remaining DEMOS[] references in comparison cell
"""

import json
from pathlib import Path

NOTEBOOK_PATH = Path(__file__).parent.parent / "Lean-9-SK-Multi-Agents.ipynb"

# New config cell - WITHOUT forcing USE_LLM_MODE
NEW_CONFIG_CELL = '''# =============================================================================
# Configuration du mode d'execution
# =============================================================================

# Les DEMOs suivantes utilisent des definitions inline pour iteration independante.
# Chaque DEMO peut etre executee et corrigee independamment.

print("=" * 70)
print("DEMONSTRATIONS PROGRESSIVES - SYSTEME MULTI-AGENTS")
print("=" * 70)
print("Les 4 DEMOs testent des theoremes de complexite croissante:")
print("  DEMO_1: Reflexivite (rfl)")
print("  DEMO_2: Recherche de lemme (Nat.zero_add)")
print("  DEMO_3: Reecriture inversee (add_mul)")
print("  DEMO_4: Induction double (mul_comm)")
print("=" * 70)
'''

# New intro markdown for demos section
NEW_DEMOS_INTRO = '''## 4. Demonstrations Progressives

Les 4 demonstrations suivantes illustrent le fonctionnement du systeme multi-agents
sur des theoremes de complexite croissante.

**Structure de chaque DEMO** :
- Cellule markdown : Objectif, proprietes, workflow attendu
- Cellule code : Definition inline du theoreme + execution

**Mode d'execution** : Les DEMOs utilisent la simulation par defaut.
Pour activer les vrais appels LLM, configurez la variable dans la cellule appropriee.

| DEMO | Complexite | Iterations attendues | Agents cles |
|------|------------|---------------------|-------------|
| DEMO_1 | Triviale | 2 | TacticAgent, VerifierAgent |
| DEMO_2 | Simple | 4 | SearchAgent, TacticAgent |
| DEMO_3 | Intermediaire | 7 | CriticAgent, SearchAgent |
| DEMO_4 | Avancee | 12 | Tous les agents |
'''

# Updated comparison cell that uses inline demo definitions
NEW_COMPARISON_CELL = '''# =============================================================================
# Comparaison des Resultats
# =============================================================================

# Collect results (defined in previous cells)
all_results = [result_1, result_2, result_3, result_4]

# Expected values from inline definitions
demos_info = [
    {"name": "DEMO_1_REFLEXIVITY", "expected_iterations": 2},
    {"name": "DEMO_2_LEMMA_SEARCH", "expected_iterations": 4},
    {"name": "DEMO_3_DISTRIBUTIVITY", "expected_iterations": 7},
    {"name": "DEMO_4_DOUBLE_INDUCTION", "expected_iterations": 12},
]

print("\\n" + "=" * 80)
print("TABLEAU COMPARATIF DES RESULTATS")
print("=" * 80)

# Header
print(f"{'Demo':<25} {'Succes':<8} {'Iter.':<8} {'Attendu':<10} {'Ecart':<10} {'Temps (s)':<10}")
print("-" * 80)

total_success = 0
total_time = 0

for i, (result, info) in enumerate(zip(all_results, demos_info), 1):
    demo_name = info["name"]
    expected = info["expected_iterations"]
    success = "OK" if result["success"] else "ECHEC"
    iterations = result["iterations"]
    time_s = result["total_time_s"]

    # Calculate deviation
    if result["success"]:
        total_success += 1
        ecart = iterations - expected
        ecart_str = f"{'+' if ecart >= 0 else ''}{ecart}"
    else:
        ecart_str = "N/A"

    total_time += time_s

    print(f"{demo_name:<25} {success:<8} {iterations:<8} {expected:<10} {ecart_str:<10} {time_s:<10.2f}")

print("-" * 80)
print(f"{'TOTAL':<25} {total_success}/4     {'':<8} {'':<10} {'':<10} {total_time:<10.2f}")
print("=" * 80)

# Analysis
print("\\n[ANALYSE DES RESULTATS]")
if total_success == 4:
    print("[SUCCESS] Toutes les DEMOs ont reussi!")

    # Check if results match expectations
    avg_deviation = sum(r["iterations"] - d["expected_iterations"]
                       for r, d in zip(all_results, demos_info)) / 4

    if abs(avg_deviation) < 1:
        print("[INFO] Les iterations correspondent aux attentes.")
    elif avg_deviation < 0:
        print("[WARNING] Les DEMOs terminent plus vite que prevu.")
        print("[CAUSE] La simulation trouve les lemmes Mathlib directement.")
        print("[IMPLICATION] CriticAgent et CoordinatorAgent jamais actives.")
    else:
        print("[INFO] Certaines DEMOs necessitent plus d'iterations que prevu.")
else:
    print(f"[PARTIAL] {total_success}/4 DEMOs reussies.")
    failed = [d["name"] for r, d in zip(all_results, demos_info) if not r["success"]]
    print(f"[ECHECS] {', '.join(failed)}")
'''


def read_notebook(path):
    with open(path, 'r', encoding='utf-8') as f:
        return json.load(f)


def write_notebook(path, nb):
    with open(path, 'w', encoding='utf-8', newline='\n') as f:
        json.dump(nb, f, indent=1, ensure_ascii=False)
        f.write('\n')


def get_source(cell):
    source = cell.get('source', [])
    return ''.join(source) if isinstance(source, list) else source


def set_source(cell, new_source):
    lines = new_source.split('\n')
    cell['source'] = [line + '\n' for line in lines[:-1]] + ([lines[-1]] if lines[-1] else [])


def find_cell_by_content(cells, pattern):
    for i, cell in enumerate(cells):
        if pattern in get_source(cell):
            return i
    return -1


def main():
    print(f"Reading: {NOTEBOOK_PATH}")
    nb = read_notebook(NOTEBOOK_PATH)
    cells = nb['cells']

    print(f"Cell count: {len(cells)}")

    changes = []

    # 1. Fix the CONFIG cell (remove USE_LLM_MODE = False)
    config_idx = find_cell_by_content(cells, 'USE_LLM_MODE = False')
    if config_idx >= 0:
        set_source(cells[config_idx], NEW_CONFIG_CELL)
        changes.append(f"Cell {config_idx}: Removed forced USE_LLM_MODE = False")

    # 2. Fix the demos intro markdown
    # Look for old intro patterns
    intro_patterns = [
        'Les 4 demos avec progression',
        '## 4. Demonstrations Progressives',
    ]

    for pattern in intro_patterns:
        intro_idx = find_cell_by_content(cells, pattern)
        if intro_idx >= 0:
            cell = cells[intro_idx]
            if cell['cell_type'] == 'markdown':
                set_source(cell, NEW_DEMOS_INTRO)
                changes.append(f"Cell {intro_idx}: Updated demos intro markdown")
                break

    # 3. Fix the comparison cell that still uses DEMOS[]
    comparison_idx = find_cell_by_content(cells, 'DEMOS[i-1]')
    if comparison_idx == -1:
        comparison_idx = find_cell_by_content(cells, 'expected_iterations = [d["expected_iterations"] for d in DEMOS]')

    if comparison_idx >= 0:
        set_source(cells[comparison_idx], NEW_COMPARISON_CELL)
        changes.append(f"Cell {comparison_idx}: Fixed DEMOS[] references in comparison")

    # Write back
    if changes:
        write_notebook(NOTEBOOK_PATH, nb)
        print(f"\nChanges made ({len(changes)}):")
        for c in changes:
            print(f"  - {c}")
        print("\nNotebook saved.")
    else:
        print("\nNo changes needed.")

    return len(changes) > 0


if __name__ == "__main__":
    main()
