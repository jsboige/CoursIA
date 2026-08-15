#!/usr/bin/env python3
"""
Update DEMO description cells in markdown to match DEMOS v5.
"""

import json

NOTEBOOK_PATH = "d:/dev/CoursIA/MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-9-SK-Multi-Agents.ipynb"

# New markdown descriptions for each DEMO
DEMO_1_MARKDOWN = """### 4.1. DEMO_1 : Reflexivite Pure

**Objectif** : Valider le pipeline complet avec un theoreme trivial

**Theoreme** : `theorem demo_rfl (n : Nat) : n = n`

**Strategie attendue** :
1. **SearchAgent** : Trouve `Eq.refl`
2. **TacticAgent** : Applique `rfl`
3. **VerifierAgent** : SUCCES immediat

**Iterations attendues** : 2
"""

DEMO_2_MARKDOWN = """### 4.2. DEMO_2 : Recherche de Lemme

**Objectif** : Montrer que rfl echoue et qu'il faut chercher un lemme

**Theoreme** : `theorem zero_add_eq (n : Nat) : 0 + n = n`

**Piege** : `rfl` echoue car `0 + n` n'est pas *definitionellement* egal a `n` en Lean 4.

**Strategie attendue** :
1. **SearchAgent** : Trouve `Nat.zero_add`
2. **TacticAgent** : Essaie `rfl` (echec)
3. **VerifierAgent** : Echec -> CriticAgent
4. **CriticAgent** : "rfl echoue, essaie simp"
5. **TacticAgent** : Essaie `simp` (insuffisant)
6. **VerifierAgent** : Echec -> CriticAgent
7. **CriticAgent** : "Cherche lemme specifique"
8. **TacticAgent** : `exact Nat.zero_add n`
9. **VerifierAgent** : SUCCES

**Iterations attendues** : 4
"""

DEMO_3_MARKDOWN = """### 4.3. DEMO_3 : Distributivite Inversee

**Objectif** : Tester réécriture dans le sens inverse

**Theoreme** : `theorem add_mul_distrib (a b c : Nat) : a * c + b * c = (a + b) * c`

**Piege** : Le lemme `Nat.add_mul` existe mais dans le sens `(a + b) * c = a * c + b * c`. Il faut utiliser `<-` pour l'appliquer dans l'autre sens.

**Strategie attendue** :
1. **SearchAgent** : Trouve `Nat.add_mul`, `Nat.right_distrib`
2. **TacticAgent** : Essaie `rfl`, `simp`, `ring` (echecs)
3. **CriticAgent** : "Forme inversee, utilise <- pour rewrite"
4. **TacticAgent** : `rw [Nat.add_mul]` (mauvais sens)
5. **CriticAgent** : "Inverse le sens"
6. **TacticAgent** : `rw [<- Nat.add_mul]`
7. **VerifierAgent** : SUCCES

**Iterations attendues** : 7
"""

DEMO_4_MARKDOWN = """### 4.4. DEMO_4 : Induction Double

**Objectif** : Stresser le systeme avec une preuve par induction structuree

**Theoreme** : `theorem mul_comm_manual (m n : Nat) : m * n = n * m`

**Difficulte** : Cette preuve necessite une **induction sur m** avec :
- Cas base : `0 * n = n * 0` (utilise `Nat.zero_mul`, `Nat.mul_zero`)
- Cas inductif : `(m+1) * n = n * (m+1)` (utilise `Nat.succ_mul`, `Nat.mul_succ`, `Nat.add_comm`)

**Strategie attendue** :
1. **SearchAgent** : Trouve lemmes `mul_succ`, `succ_mul`, `mul_zero`, `zero_mul`
2. **TacticAgent** : Essaie `rfl`, `simp`, `ring`, `omega` (tous echecs)
3. **CriticAgent** : "Necessite induction sur m"
4. **TacticAgent** : `induction m`
5. **VerifierAgent** : Progres partiel, cas base
6. **CriticAgent** : "Cas base OK, cas inductif incomplet"
7. **TacticAgent** : Applique `Nat.mul_succ`, `Nat.succ_mul`
8. **CriticAgent** : "Presque, manque Nat.add_comm"
9. **TacticAgent** : `simp [Nat.mul_succ, Nat.succ_mul, Nat.add_comm]`
10. **VerifierAgent** : SUCCES

**Iterations attendues** : 12

**Note** : Si DEMO_4 se complete en <10 iterations, cela signifie que la simulation est trop optimiste.
"""


def update_notebook():
    """Update markdown cells describing each DEMO."""
    print(f"Reading: {NOTEBOOK_PATH}")

    with open(NOTEBOOK_PATH, 'r', encoding='utf-8') as f:
        nb = json.load(f)

    changes = []

    for idx, cell in enumerate(nb['cells']):
        if cell['cell_type'] != 'markdown':
            continue

        source = ''.join(cell['source'])

        # DEMO_1
        if '### 4.1. DEMO_1' in source:
            lines = DEMO_1_MARKDOWN.split('\n')
            nb['cells'][idx]['source'] = [line + '\n' for line in lines[:-1]] + [lines[-1]]
            changes.append(f"Cell {idx}: Updated DEMO_1 description")

        # DEMO_2
        elif '### 4.2. DEMO_2' in source:
            lines = DEMO_2_MARKDOWN.split('\n')
            nb['cells'][idx]['source'] = [line + '\n' for line in lines[:-1]] + [lines[-1]]
            changes.append(f"Cell {idx}: Updated DEMO_2 description")

        # DEMO_3
        elif '### 4.3. DEMO_3' in source:
            lines = DEMO_3_MARKDOWN.split('\n')
            nb['cells'][idx]['source'] = [line + '\n' for line in lines[:-1]] + [lines[-1]]
            changes.append(f"Cell {idx}: Updated DEMO_3 description")

        # DEMO_4
        elif '### 4.4. DEMO_4' in source:
            lines = DEMO_4_MARKDOWN.split('\n')
            nb['cells'][idx]['source'] = [line + '\n' for line in lines[:-1]] + [lines[-1]]
            changes.append(f"Cell {idx}: Updated DEMO_4 description")

    if changes:
        with open(NOTEBOOK_PATH, 'w', encoding='utf-8') as f:
            json.dump(nb, f, indent=1, ensure_ascii=False)

        print("\nChanges made:")
        for c in changes:
            print(f"  - {c}")
        print("\nNotebook saved.")
    else:
        print("No changes made.")

    return len(changes) > 0


if __name__ == "__main__":
    update_notebook()
