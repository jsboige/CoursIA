#!/usr/bin/env python3
"""
Fix markdown cells to match the new DEMOS theorems.
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


# New markdown content for DEMO cells
NEW_CELL_35 = '''## 4. Demonstrations Progressives

### Objectif

Valider que le systeme multi-agents **fonctionne reellement** sur des problemes de complexite croissante.

### Les 4 demos avec complexite reelle

#### 1️⃣ DEMO_1_TRIVIAL : `theorem demo_rfl (n : Nat) : n = n`

- **Complexite** : Triviale (egalite reflexive)
- **Preuve attendue** : `by rfl` (une seule tactique)
- **Iterations attendues** : 2-3
- **Lemmes necessaires** : 1 (Eq.refl)
- **But** : Verifier que le systeme peut resoudre le cas le plus simple

#### 2️⃣ DEMO_2_COMPOSITION : `theorem add_zero_comm (n m : Nat) : n + m + 0 = m + n`

- **Complexite** : Simple - necessite **combiner 2 lemmes**
- **Preuve attendue** : `simp [Nat.add_zero, Nat.add_comm]`
- **Iterations attendues** : 5-7
- **Lemmes necessaires** : 2 (Nat.add_zero + Nat.add_comm)
- **But** : Tester **SearchAgent** (recherche) + **TacticAgent** (composition)

#### 3️⃣ DEMO_3_MULTI_REWRITE : `theorem quad_comm (a b c d : Nat) : (a + b) + (c + d) = (d + c) + (b + a)`

- **Complexite** : Intermediaire - chaine de 4 reecritures
- **Preuve attendue** : Multiple `rw [Nat.add_comm]` ou AC normalization
- **Iterations attendues** : 10-15
- **Lemmes necessaires** : 2 (Nat.add_comm + Nat.add_assoc appliques plusieurs fois)
- **CriticAgent** : PROBABLE (necessitent ajustements tactiques)
- **But** : Tester les **feedback loops** entre agents

#### 4️⃣ DEMO_4_STRUCTURED : `theorem distrib_both (a b c : Nat) : (a + b) * c + a * c = a * c + a * c + b * c`

- **Complexite** : Avancee - decomposition + recombinaison
- **Preuve attendue** : `rw [Nat.right_distrib]` + reassociation ou `ring`
- **Iterations attendues** : 15-20
- **Lemmes necessaires** : 3+ (Nat.right_distrib, Nat.add_assoc, Nat.add_comm)
- **CoordinatorAgent** : REQUIS (strategie globale necessaire)
- **But** : Stresser le systeme avec changement de strategie'''


NEW_CELL_39 = '''### 4.2. DEMO_2 : Composition de Lemmes

**Objectif** : Tester recherche + composition de 2 lemmes

**Theoreme** : `theorem add_zero_comm (n m : Nat) : n + m + 0 = m + n`

**Attentes** :
- **Iterations** : 5-7 (2 etapes de preuve)
- **Agents impliques** : SearchAgent → TacticAgent → VerifierAgent → CriticAgent → TacticAgent
- **Lemmes Mathlib attendus** : `Nat.add_zero`, `Nat.add_comm`
- **CriticAgent** : POSSIBLE (si premiere tactique incomplete)
- **Temps** : 1-3 secondes

Cette demo teste la **composition de lemmes** : d'abord eliminer le `+ 0`, puis appliquer la commutativite.'''


NEW_CELL_41 = '''### 4.3. DEMO_3 : Reecritures Multiples

**Objectif** : Tester chaine de reecritures avec feedback

**Theoreme** : `theorem quad_comm (a b c d : Nat) : (a + b) + (c + d) = (d + c) + (b + a)`

**Attentes** :
- **Iterations** : 10-15 (4 reecritures successives)
- **Agents impliques** : SearchAgent → TacticAgent → VerifierAgent → CriticAgent (×3-4)
- **Lemmes Mathlib attendus** : `Nat.add_comm`, `Nat.add_assoc`, `Nat.add_left_comm`
- **CriticAgent** : REQUIS (plusieurs ajustements necessaires)
- **CoordinatorAgent** : PROBABLE (si blocage, strategie AC normalization)
- **Temps** : 3-8 secondes

Cette demo teste l'**orchestration multi-agents avec feedback loops** :
- Etape 1 : `rw [Nat.add_comm c d]` pour avoir `(d + c)`
- Etape 2 : `rw [Nat.add_comm a b]` pour avoir `(b + a)`
- Etape 3 : Eventuellement `rw [Nat.add_comm]` global
- Ou : `simp only [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm]` (AC normalization)'''


NEW_CELL_43 = '''### 4.4. DEMO_4 : Preuve Structuree

**Objectif** : Stresser le systeme avec decomposition algebrique

**Theoreme** : `theorem distrib_both (a b c : Nat) : (a + b) * c + a * c = a * c + a * c + b * c`

**Attentes** :
- **Iterations** : 15-20 (decomposition + reordonnancement)
- **Agents impliques** : Tous les 5 agents avec changement de strategie
- **Lemmes Mathlib attendus** : `Nat.right_distrib`, `Nat.add_assoc`, `Nat.add_comm`
- **Strategies** : EXPLORATION → REFINEMENT → VALIDATION
- **CriticAgent/CoordinatorAgent** : **REQUIS**
- **Temps** : 5-15 secondes

Cette demo doit **declencher le workflow complet** :

1. **SearchAgent** : Trouve `Nat.right_distrib : (n + m) * k = n * k + m * k`
2. **TacticAgent** : Applique `rw [Nat.right_distrib]` → `a * c + b * c + a * c`
3. **VerifierAgent** : But non ferme (`a*c + b*c + a*c ≠ a*c + a*c + b*c`)
4. **CriticAgent** : Analyse → besoin de reassociation
5. **CoordinatorAgent** : Strategie `ring` ou reassociation manuelle
6. **TacticAgent** : `ring` ou `simp [Nat.add_comm, Nat.add_assoc]`
7. **VerifierAgent** : SUCCES

**Note** : Si DEMO_4 se complete en <10 iterations, cela signifie que la simulation est trop optimiste.'''


def main():
    script_dir = Path(__file__).parent
    notebook_dir = script_dir.parent
    lean9_path = notebook_dir / 'Lean-9-SK-Multi-Agents.ipynb'

    print("=" * 80)
    print("FIX MARKDOWN CELLS TO MATCH NEW DEMOS")
    print("=" * 80)

    nb = read_notebook(str(lean9_path))
    print(f"Read {len(nb['cells'])} cells")

    changes = 0

    # Find and update markdown cells
    for i, cell in enumerate(nb['cells']):
        if cell['cell_type'] != 'markdown':
            continue
        src = get_cell_source(cell)

        # Cell 35: Les 4 demos overview
        if '## 4. Demonstrations Progressives' in src and 'DEMO_1_TRIVIAL' in src:
            print(f"Found DEMO overview in cell {i}")
            set_cell_source(cell, NEW_CELL_35)
            print("  Updated cell 35 (DEMO overview)")
            changes += 1

        # Cell 39: DEMO_2
        elif '### 4.2. DEMO_2' in src:
            print(f"Found DEMO_2 description in cell {i}")
            set_cell_source(cell, NEW_CELL_39)
            print("  Updated cell 39 (DEMO_2)")
            changes += 1

        # Cell 41: DEMO_3
        elif '### 4.3. DEMO_3' in src:
            print(f"Found DEMO_3 description in cell {i}")
            set_cell_source(cell, NEW_CELL_41)
            print("  Updated cell 41 (DEMO_3)")
            changes += 1

        # Cell 43: DEMO_4
        elif '### 4.4. DEMO_4' in src:
            print(f"Found DEMO_4 description in cell {i}")
            set_cell_source(cell, NEW_CELL_43)
            print("  Updated cell 43 (DEMO_4)")
            changes += 1

    if changes >= 4:
        write_notebook(str(lean9_path), nb)
        print(f"\nNotebook saved with {changes} markdown cell updates")
    else:
        print(f"\nOnly {changes}/4 cells updated, check if cells exist")


if __name__ == '__main__':
    main()
