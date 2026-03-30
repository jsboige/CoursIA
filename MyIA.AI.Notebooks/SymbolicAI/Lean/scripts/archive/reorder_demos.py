#!/usr/bin/env python3
"""
Reorder DEMOs in Lean-9 notebook:
- DEMO_1: Reflexivity (stays)
- DEMO_2: Distributivity (was DEMO_3)
- DEMO_3: Mul commutativity (was DEMO_4)
- DEMO_4: Power addition (new, harder)
"""

import json
import sys
from pathlib import Path

NOTEBOOK_PATH = Path(__file__).parent.parent / "Lean-9-SK-Multi-Agents.ipynb"

# New DEMO definitions
DEMOS = [
    {
        "num": 1,
        "name": "DEMO_1_REFLEXIVITY",
        "theorem": "theorem demo_rfl (n : Nat) : n = n",
        "expected_iterations": 2,
        "expected_lemmas": 0,
        "complexity": "Triviale - rfl suffit",
        "strategy": "rfl",
        "md_title": "### 4.1. DEMO_1 : Reflexivite Pure",
        "md_objective": "Valider le pipeline complet avec un theoreme trivial",
        "md_behavior": "1-2 iterations : `rfl` suffit immediatement"
    },
    {
        "num": 2,
        "name": "DEMO_2_DISTRIBUTIVITY",
        "theorem": "theorem add_mul_distrib (a b c : Nat) : a * c + b * c = (a + b) * c",
        "expected_iterations": 5,
        "expected_lemmas": 1,
        "complexity": "Simple - forme inversee du lemme standard",
        "strategy": "rw [<- Nat.add_mul]",
        "md_title": "### 4.2. DEMO_2 : Distributivite Inversee",
        "md_objective": "Montrer la recherche de lemme avec reecriture inversee",
        "md_behavior": "4-6 iterations : recherche `Nat.add_mul`, reecriture inversee"
    },
    {
        "num": 3,
        "name": "DEMO_3_MUL_COMM",
        "theorem": "theorem mul_comm_manual (m n : Nat) : m * n = n * m",
        "expected_iterations": 8,
        "expected_lemmas": 2,
        "complexity": "Intermediaire - necessite lemme de commutativite",
        "strategy": "exact Nat.mul_comm m n",
        "md_title": "### 4.3. DEMO_3 : Commutativite Multiplication",
        "md_objective": "Tester une propriete fondamentale avec recherche",
        "md_behavior": "6-10 iterations : decouverte de `Nat.mul_comm`"
    },
    {
        "num": 4,
        "name": "DEMO_4_POWER_ADD",
        "theorem": "theorem pow_add_manual (a m n : Nat) : a ^ (m + n) = a ^ m * a ^ n",
        "expected_iterations": 15,
        "expected_lemmas": 4,
        "complexity": "Avancee - induction et lemmes auxiliaires multiples",
        "strategy": "induction n avec Nat.pow_succ, Nat.mul_assoc",
        "md_title": "### 4.4. DEMO_4 : Addition des Puissances",
        "md_objective": "Stresser le systeme avec induction et lemmes multiples",
        "md_behavior": "12-18 iterations : induction sur n, decouverte de pow_succ, mul_assoc"
    }
]

def generate_markdown_cell(demo):
    """Generate markdown cell content for a demo."""
    return f"""{demo['md_title']}

**Objectif** : {demo['md_objective']}

**Theoreme** : `{demo['theorem']}`

**Comportement attendu** : {demo['md_behavior']}
"""

def generate_code_cell(demo):
    """Generate code cell content for a demo."""
    return f'''# =============================================================================
# DEMO_{demo['num']} : {demo['name'].replace(f"DEMO_{demo['num']}_", "")}
# =============================================================================

# Definition inline pour iteration independante
demo_{demo['num']} = {{
    "name": "{demo['name']}",
    "theorem": "{demo['theorem']}",
    "expected_iterations": {demo['expected_iterations']},
    "expected_lemmas": {demo['expected_lemmas']},
    "complexity": "{demo['complexity']}",
    "strategy": "{demo['strategy']}"
}}

print("\\n" + "=" * 70)
print(f"DEMO {demo['num']}/4: {{demo_{demo['num']}['name']}}")
print("=" * 70)
print(f"Theoreme: {{demo_{demo['num']}['theorem']}}")
print(f"Complexite: {{demo_{demo['num']}['complexity']}}")
print(f"Iterations attendues: {{demo_{demo['num']}['expected_iterations']}}")
print("=" * 70)

result_{demo['num']} = prove_with_multi_agents(
    theorem=demo_{demo['num']}["theorem"],
    max_iterations=20,
    verbose=True,
    use_simulation=not USE_LLM_MODE
)

print(f"\\nResultat DEMO_{demo['num']}:")
print(f"  - Success: {{result_{demo['num']}['success']}}")
print(f"  - Iterations: {{result_{demo['num']}['iterations']}} (attendu: {{demo_{demo['num']}['expected_iterations']}})")
print(f"  - Proof: {{result_{demo['num']}['final_proof']}}")'''

def generate_comparison_cell():
    """Generate the comparison cell."""
    return '''# =============================================================================
# Comparaison des Resultats
# =============================================================================

print("\\n" + "=" * 70)
print("COMPARAISON DES RESULTATS")
print("=" * 70)

# Definitions inline pour iteration independante
demos_info = [
    {"name": "DEMO_1_REFLEXIVITY", "theorem": "n = n", "expected_iter": 2, "expected_lemmas": 0},
    {"name": "DEMO_2_DISTRIBUTIVITY", "theorem": "a*c + b*c = (a+b)*c", "expected_iter": 5, "expected_lemmas": 1},
    {"name": "DEMO_3_MUL_COMM", "theorem": "m * n = n * m", "expected_iter": 8, "expected_lemmas": 2},
    {"name": "DEMO_4_POWER_ADD", "theorem": "a^(m+n) = a^m * a^n", "expected_iter": 15, "expected_lemmas": 4},
]

results = [result_1, result_2, result_3, result_4]

print(f"{'Demo':<25} {'Success':<10} {'Iter':<12} {'Lemmas':<10} {'Status':<15}")
print("-" * 72)

for i, (demo, result) in enumerate(zip(demos_info, results), 1):
    success_str = "OK" if result["success"] else "FAILED"
    iter_str = f"{result['iterations']}/{demo['expected_iter']}"
    lemmas_str = f"{result.get('lemmas_found', 0)}/{demo['expected_lemmas']}"

    if result["success"]:
        if result["iterations"] <= demo["expected_iter"]:
            status = "Optimal"
        else:
            status = "Slow"
    else:
        status = "Failed"

    print(f"{demo['name']:<25} {success_str:<10} {iter_str:<12} {lemmas_str:<10} {status:<15}")

print("-" * 72)
total_success = sum(1 for r in results if r["success"])
print(f"Total: {total_success}/4 reussies")

# Resume de la progression
print("\\n" + "=" * 70)
print("PROGRESSION DE COMPLEXITE")
print("=" * 70)
print("DEMO_1: Reflexivite     -> Pipeline validation (rfl)")
print("DEMO_2: Distributivite  -> Recherche + reecriture inversee")
print("DEMO_3: Commutativite   -> Propriete fondamentale (exact)")
print("DEMO_4: Puissances      -> Induction + lemmes multiples")'''

def main():
    print(f"Reading notebook: {NOTEBOOK_PATH}")

    with open(NOTEBOOK_PATH, 'r', encoding='utf-8') as f:
        notebook = json.load(f)

    cells = notebook['cells']
    changes = 0

    # Update DEMO markdown cells (38, 40, 42, 44)
    md_indices = [38, 40, 42, 44]
    for i, demo in zip(md_indices, DEMOS):
        new_source = generate_markdown_cell(demo)
        cells[i]['source'] = new_source.split('\n')
        cells[i]['source'] = [line + '\n' if j < len(cells[i]['source'])-1 else line
                              for j, line in enumerate(new_source.split('\n'))]
        print(f"  Updated markdown cell {i}: {demo['md_title'][:40]}...")
        changes += 1

    # Update DEMO code cells (39, 41, 43, 45)
    code_indices = [39, 41, 43, 45]
    for i, demo in zip(code_indices, DEMOS):
        new_source = generate_code_cell(demo)
        lines = new_source.split('\n')
        cells[i]['source'] = [line + '\n' if j < len(lines)-1 else line
                              for j, line in enumerate(lines)]
        print(f"  Updated code cell {i}: DEMO_{demo['num']}")
        changes += 1

    # Update comparison cell (47)
    comparison_source = generate_comparison_cell()
    lines = comparison_source.split('\n')
    cells[47]['source'] = [line + '\n' if j < len(lines)-1 else line
                           for j, line in enumerate(lines)]
    print(f"  Updated comparison cell 47")
    changes += 1

    # Update intro markdown (35)
    intro_md = '''## 4. Demonstrations Progressives

Les 4 demonstrations suivantes illustrent le fonctionnement du systeme multi-agents avec une progression de complexite croissante :

| Demo | Theoreme | Complexite | Iterations | Technique |
|------|----------|------------|------------|-----------|
| DEMO_1 | `n = n` | Triviale | 2 | `rfl` direct |
| DEMO_2 | `a*c + b*c = (a+b)*c` | Simple | 5 | Recherche + reecriture inversee |
| DEMO_3 | `m * n = n * m` | Intermediaire | 8 | Lemme `Nat.mul_comm` |
| DEMO_4 | `a^(m+n) = a^m * a^n` | Avancee | 15 | Induction + lemmes multiples |

**Progression pedagogique** :
- DEMO_1 : Validation du pipeline (cas trivial)
- DEMO_2 : Introduction de la recherche de lemmes
- DEMO_3 : Propriete fondamentale avec `exact`
- DEMO_4 : Stress-test avec induction complexe
'''
    lines = intro_md.split('\n')
    cells[35]['source'] = [line + '\n' if j < len(lines)-1 else line
                           for j, line in enumerate(lines)]
    print(f"  Updated intro cell 35")
    changes += 1

    # Write back
    with open(NOTEBOOK_PATH, 'w', encoding='utf-8') as f:
        json.dump(notebook, f, indent=1, ensure_ascii=False)

    print(f"\nTotal changes: {changes} cells updated")
    print("Done!")

if __name__ == "__main__":
    main()
