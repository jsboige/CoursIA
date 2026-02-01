#!/usr/bin/env python3
"""
Reorganize DEMO cells in Lean-9 notebook for better iteration support.

Changes:
1. Move DEMOS definition to its own cell (separate from prove_with_multi_agents)
2. Each DEMO markdown cell includes the full definition dict
3. Each DEMO code cell only contains the execution
"""

import json
from pathlib import Path

NOTEBOOK_PATH = Path(__file__).parent.parent / "Lean-9-SK-Multi-Agents.ipynb"

# New configuration cell (will be inserted after prove_with_multi_agents)
CONFIG_CELL = '''# =============================================================================
# Configuration du mode d'execution
# =============================================================================

# Mode LLM ou Simulation
USE_LLM_MODE = False  # True = appels OpenAI reels, False = simulation

print(f"Mode: {'LLM (OpenAI)' if USE_LLM_MODE else 'Simulation'}")
print("Les DEMOs suivantes utilisent des definitions inline pour iteration independante.")
'''

# New markdown cells for each DEMO
DEMO_MARKDOWNS = {
    1: '''### 4.1. DEMO_1 : Reflexivite Pure

**Objectif** : Valider le pipeline complet avec un theoreme trivial

| Propriete | Valeur |
|-----------|--------|
| **Theoreme** | `theorem demo_rfl (n : Nat) : n = n` |
| **Complexite** | Triviale |
| **Iterations attendues** | 2 |
| **Lemmes necessaires** | 0 |
| **Strategie** | `rfl` |

**Workflow attendu** :
1. **TacticAgent** : Reconnait pattern d'egalite reflexive
2. **VerifierAgent** : Confirme `rfl` resout le goal

> **Note pedagogique** : Ce cas de base valide que le systeme peut resoudre
> les preuves triviales sans surcharge de recherche.
''',

    2: '''### 4.2. DEMO_2 : Recherche de Lemme

**Objectif** : Montrer que `rfl` echoue et qu'il faut chercher un lemme

| Propriete | Valeur |
|-----------|--------|
| **Theoreme** | `theorem zero_add_eq (n : Nat) : 0 + n = n` |
| **Complexite** | Simple - mais piege tactique |
| **Iterations attendues** | 4 |
| **Lemmes necessaires** | 1 (`Nat.zero_add`) |
| **Strategie** | `exact Nat.zero_add n` |

**Piege** : `rfl` echoue car `0 + n` n'est pas *definitionellement* egal a `n` en Lean 4.

**Workflow attendu** :
1. **TacticAgent** : Essaie `rfl` (echec)
2. **CriticAgent** : "rfl echoue, cherche un lemme"
3. **SearchAgent** : Trouve `Nat.zero_add`
4. **TacticAgent** : `exact Nat.zero_add n`
5. **VerifierAgent** : SUCCES

> **Note pedagogique** : Illustre la difference entre egalite definitionnelle
> et egalite propositionnelle en theorie des types.
''',

    3: '''### 4.3. DEMO_3 : Distributivite Inversee

**Objectif** : Tester la reecriture dans le sens inverse

| Propriete | Valeur |
|-----------|--------|
| **Theoreme** | `theorem add_mul_distrib (a b c : Nat) : a * c + b * c = (a + b) * c` |
| **Complexite** | Intermediaire - forme inversee |
| **Iterations attendues** | 7 |
| **Lemmes necessaires** | 2 |
| **Strategie** | `rw [<- Nat.add_mul]` ou `ring` |

**Piege** : Le lemme `Nat.add_mul` existe mais dans le sens `(a + b) * c = a * c + b * c`.
Il faut utiliser `<-` pour l'appliquer dans l'autre sens.

**Workflow attendu** :
1. **SearchAgent** : Trouve `Nat.add_mul`, `Nat.right_distrib`
2. **TacticAgent** : Essaie `rfl`, `simp`, `ring` (echecs partiels)
3. **CriticAgent** : "Forme inversee, utilise <- pour rewrite"
4. **TacticAgent** : `rw [Nat.add_mul]` (mauvais sens)
5. **CriticAgent** : "Inverse le sens avec <-"
6. **TacticAgent** : `rw [<- Nat.add_mul]`
7. **VerifierAgent** : SUCCES

> **Note pedagogique** : Montre l'importance de la direction dans les reecritures
> et le role du CriticAgent pour guider les corrections.
''',

    4: '''### 4.4. DEMO_4 : Induction Double

**Objectif** : Stresser le systeme avec une preuve par induction structuree

| Propriete | Valeur |
|-----------|--------|
| **Theoreme** | `theorem mul_comm_manual (m n : Nat) : m * n = n * m` |
| **Complexite** | Avancee - induction multi-etapes |
| **Iterations attendues** | 12 |
| **Lemmes necessaires** | 4+ |
| **Strategie** | Induction sur `m` avec lemmes auxiliaires |

**Difficulte** : Cette preuve necessite une **induction sur m** avec :
- **Cas base** : `0 * n = n * 0` (utilise `Nat.zero_mul`, `Nat.mul_zero`)
- **Cas inductif** : `(m+1) * n = n * (m+1)` (utilise `Nat.succ_mul`, `Nat.mul_succ`, `Nat.add_comm`)

**Workflow attendu** :
1. **SearchAgent** : Trouve lemmes `mul_succ`, `succ_mul`, `mul_zero`, `zero_mul`
2. **TacticAgent** : Essaie `rfl`, `simp`, `ring`, `omega` (tous echecs)
3. **CriticAgent** : "Necessite induction sur m"
4. **TacticAgent** : `induction m`
5. **VerifierAgent** : Progres partiel, deux goals
6. **CriticAgent** : "Cas base: utilise zero_mul/mul_zero"
7. **TacticAgent** : Resout cas base
8. **CriticAgent** : "Cas inductif: utilise succ_mul, mul_succ, add_comm"
9-11. **TacticAgent** : Applique les lemmes progressivement
12. **VerifierAgent** : SUCCES

> **Note pedagogique** : DEMO_4 teste la capacite du systeme a decomposer
> un probleme complexe en sous-problemes et a coordonner plusieurs agents.
> Si elle se complete en <10 iterations, la simulation est trop optimiste.
'''
}

# New code cells for each DEMO execution - INLINE DEFINITION (no DEMOS[i] reference)
DEMO_CODES = {
    1: '''# =============================================================================
# DEMO_1 : Reflexivite Pure
# =============================================================================

# Definition inline pour iteration independante
demo_1 = {
    "name": "DEMO_1_REFLEXIVITY",
    "theorem": "theorem demo_rfl (n : Nat) : n = n",
    "expected_iterations": 2,
    "expected_lemmas": 0,
    "complexity": "Triviale - rfl suffit",
    "strategy": "rfl"
}

print("\\n" + "=" * 70)
print(f"DEMO 1/4: {demo_1['name']}")
print("=" * 70)
print(f"Theoreme: {demo_1['theorem']}")
print(f"Complexite: {demo_1['complexity']}")
print(f"Iterations attendues: {demo_1['expected_iterations']}")
print("=" * 70)

result_1 = prove_with_multi_agents(
    theorem=demo_1["theorem"],
    max_iterations=20,
    verbose=True,
    use_simulation=not USE_LLM_MODE
)

print(f"\\nResultat DEMO_1:")
print(f"  - Success: {result_1['success']}")
print(f"  - Iterations: {result_1['iterations']} (attendu: {demo_1['expected_iterations']})")
print(f"  - Proof: {result_1['final_proof']}")
''',

    2: '''# =============================================================================
# DEMO_2 : Recherche de Lemme
# =============================================================================

# Definition inline pour iteration independante
demo_2 = {
    "name": "DEMO_2_LEMMA_SEARCH",
    "theorem": "theorem zero_add_eq (n : Nat) : 0 + n = n",
    "expected_iterations": 4,
    "expected_lemmas": 1,
    "complexity": "Simple - necessite recherche de lemme",
    "strategy": "exact Nat.zero_add n"
}

print("\\n" + "=" * 70)
print(f"DEMO 2/4: {demo_2['name']}")
print("=" * 70)
print(f"Theoreme: {demo_2['theorem']}")
print(f"Complexite: {demo_2['complexity']}")
print(f"Iterations attendues: {demo_2['expected_iterations']}")
print("=" * 70)

result_2 = prove_with_multi_agents(
    theorem=demo_2["theorem"],
    max_iterations=20,
    verbose=True,
    use_simulation=not USE_LLM_MODE
)

print(f"\\nResultat DEMO_2:")
print(f"  - Success: {result_2['success']}")
print(f"  - Iterations: {result_2['iterations']} (attendu: {demo_2['expected_iterations']})")
print(f"  - Proof: {result_2['final_proof']}")
''',

    3: '''# =============================================================================
# DEMO_3 : Distributivite Inversee
# =============================================================================

# Definition inline pour iteration independante
demo_3 = {
    "name": "DEMO_3_DISTRIBUTIVITY",
    "theorem": "theorem add_mul_distrib (a b c : Nat) : a * c + b * c = (a + b) * c",
    "expected_iterations": 7,
    "expected_lemmas": 2,
    "complexity": "Intermediaire - forme inversee du lemme",
    "strategy": "rw [<- Nat.add_mul]"
}

print("\\n" + "=" * 70)
print(f"DEMO 3/4: {demo_3['name']}")
print("=" * 70)
print(f"Theoreme: {demo_3['theorem']}")
print(f"Complexite: {demo_3['complexity']}")
print(f"Iterations attendues: {demo_3['expected_iterations']}")
print("=" * 70)

result_3 = prove_with_multi_agents(
    theorem=demo_3["theorem"],
    max_iterations=20,
    verbose=True,
    use_simulation=not USE_LLM_MODE
)

print(f"\\nResultat DEMO_3:")
print(f"  - Success: {result_3['success']}")
print(f"  - Iterations: {result_3['iterations']} (attendu: {demo_3['expected_iterations']})")
print(f"  - Proof: {result_3['final_proof']}")
''',

    4: '''# =============================================================================
# DEMO_4 : Induction Double
# =============================================================================

# Definition inline pour iteration independante
demo_4 = {
    "name": "DEMO_4_DOUBLE_INDUCTION",
    "theorem": "theorem mul_comm_manual (m n : Nat) : m * n = n * m",
    "expected_iterations": 12,
    "expected_lemmas": 4,
    "complexity": "Avancee - induction multi-etapes",
    "strategy": "induction m avec lemmes auxiliaires"
}

print("\\n" + "=" * 70)
print(f"DEMO 4/4: {demo_4['name']}")
print("=" * 70)
print(f"Theoreme: {demo_4['theorem']}")
print(f"Complexite: {demo_4['complexity']}")
print(f"Iterations attendues: {demo_4['expected_iterations']}")
print("=" * 70)

result_4 = prove_with_multi_agents(
    theorem=demo_4["theorem"],
    max_iterations=20,
    verbose=True,
    use_simulation=not USE_LLM_MODE
)

print(f"\\nResultat DEMO_4:")
print(f"  - Success: {result_4['success']}")
print(f"  - Iterations: {result_4['iterations']} (attendu: {demo_4['expected_iterations']})")
print(f"  - Proof: {result_4['final_proof']}")
'''
}


def read_notebook(path):
    with open(path, 'r', encoding='utf-8') as f:
        return json.load(f)


def write_notebook(path, nb):
    with open(path, 'w', encoding='utf-8', newline='\n') as f:
        json.dump(nb, f, indent=1, ensure_ascii=False)
        f.write('\n')


def make_cell(cell_type, source, cell_id=None):
    """Create a new notebook cell."""
    import uuid
    lines = source.split('\n')
    source_list = [line + '\n' for line in lines[:-1]] + ([lines[-1]] if lines[-1] else [])

    cell = {
        "cell_type": cell_type,
        "id": cell_id or str(uuid.uuid4())[:8],
        "metadata": {},
        "source": source_list
    }

    if cell_type == 'code':
        cell["outputs"] = []
        cell["execution_count"] = None

    return cell


def get_source(cell):
    """Get cell source as string."""
    source = cell.get('source', [])
    return ''.join(source) if isinstance(source, list) else source


def find_cell_by_content(cells, pattern):
    """Find cell index containing pattern."""
    for i, cell in enumerate(cells):
        if pattern in get_source(cell):
            return i
    return -1


def main():
    print(f"Reading: {NOTEBOOK_PATH}")
    nb = read_notebook(NOTEBOOK_PATH)
    cells = nb['cells']

    print(f"Original cell count: {len(cells)}")

    # Find key cells
    prove_func_idx = find_cell_by_content(cells, 'def prove_with_multi_agents')
    demos_intro_idx = find_cell_by_content(cells, 'Les 4 demos avec progression')
    demo1_md_idx = find_cell_by_content(cells, '### 4.1. DEMO_1')
    demo1_code_idx = find_cell_by_content(cells, 'DEMOS[0]')
    demo2_md_idx = find_cell_by_content(cells, '### 4.2. DEMO_2')
    demo2_code_idx = find_cell_by_content(cells, 'DEMOS[1]')
    demo3_md_idx = find_cell_by_content(cells, '### 4.3. DEMO_3')
    demo3_code_idx = find_cell_by_content(cells, 'DEMOS[2]')
    demo4_md_idx = find_cell_by_content(cells, '### 4.4. DEMO_4')
    demo4_code_idx = find_cell_by_content(cells, 'DEMOS[3]')

    print(f"\nFound cells:")
    print(f"  prove_with_multi_agents: {prove_func_idx}")
    print(f"  demos intro: {demos_intro_idx}")
    print(f"  DEMO_1 md: {demo1_md_idx}, code: {demo1_code_idx}")
    print(f"  DEMO_2 md: {demo2_md_idx}, code: {demo2_code_idx}")
    print(f"  DEMO_3 md: {demo3_md_idx}, code: {demo3_code_idx}")
    print(f"  DEMO_4 md: {demo4_md_idx}, code: {demo4_code_idx}")

    # Strategy: Replace existing DEMO cells with new organized ones
    changes = []

    # 1. Find cell that has DEMOS definition and prove_with_multi_agents
    #    Remove DEMOS from it (keep only the function)
    if prove_func_idx >= 0:
        prove_source = get_source(cells[prove_func_idx])
        # Check if DEMOS is defined here
        if 'DEMOS = [' in prove_source:
            # Split: keep only prove_with_multi_agents
            demos_start = prove_source.find('# Mode LLM')
            if demos_start == -1:
                demos_start = prove_source.find('USE_LLM_MODE')
            if demos_start == -1:
                demos_start = prove_source.find('DEMOS = [')

            if demos_start > 0:
                new_source = prove_source[:demos_start].rstrip() + '\n'
                cells[prove_func_idx]['source'] = [line + '\n' for line in new_source.split('\n')[:-1]] + [new_source.split('\n')[-1]]
                changes.append(f"Cell {prove_func_idx}: Removed DEMOS from prove_with_multi_agents cell")

    # 2. Replace DEMO markdown and code cells
    demo_updates = [
        (demo1_md_idx, demo1_code_idx, 1),
        (demo2_md_idx, demo2_code_idx, 2),
        (demo3_md_idx, demo3_code_idx, 3),
        (demo4_md_idx, demo4_code_idx, 4),
    ]

    for md_idx, code_idx, demo_num in demo_updates:
        if md_idx >= 0:
            new_md = DEMO_MARKDOWNS[demo_num]
            lines = new_md.split('\n')
            cells[md_idx]['source'] = [line + '\n' for line in lines[:-1]] + ([lines[-1]] if lines[-1] else [])
            changes.append(f"Cell {md_idx}: Updated DEMO_{demo_num} markdown")

        if code_idx >= 0:
            new_code = DEMO_CODES[demo_num]
            lines = new_code.split('\n')
            cells[code_idx]['source'] = [line + '\n' for line in lines[:-1]] + ([lines[-1]] if lines[-1] else [])
            changes.append(f"Cell {code_idx}: Updated DEMO_{demo_num} code")

    # 3. Replace/insert configuration cell after demos intro
    if demos_intro_idx >= 0:
        next_idx = demos_intro_idx + 1
        if next_idx < len(cells):
            next_source = get_source(cells[next_idx])
            # If there's a DEMOS = [ definition, replace it with config cell
            if 'DEMOS = [' in next_source or 'USE_LLM_MODE' in next_source:
                lines = CONFIG_CELL.split('\n')
                cells[next_idx]['source'] = [line + '\n' for line in lines[:-1]] + ([lines[-1]] if lines[-1] else [])
                changes.append(f"Cell {next_idx}: Replaced DEMOS array with CONFIG cell")
            elif cells[next_idx]['cell_type'] == 'code':
                # Insert config cell before
                config_cell = make_cell('code', CONFIG_CELL)
                cells.insert(next_idx, config_cell)
                changes.append(f"Inserted CONFIG cell at index {next_idx}")

    # Write back
    if changes:
        write_notebook(NOTEBOOK_PATH, nb)
        print(f"\nChanges made ({len(changes)}):")
        for c in changes:
            print(f"  - {c}")
        print(f"\nNew cell count: {len(nb['cells'])}")
        print("\nNotebook saved.")
    else:
        print("\nNo changes made.")

    return len(changes) > 0


if __name__ == "__main__":
    main()
