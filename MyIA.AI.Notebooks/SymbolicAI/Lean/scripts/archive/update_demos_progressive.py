#!/usr/bin/env python3
"""
Update Lean-9 demos with progressive complexity.

Strategy: Use theorems that INTRINSICALLY require more reasoning steps.
Like a screenwriter planting clues - each theorem teaches something needed for the next.

Progression:
1. DEMO_1: Pure reflexivity (1 tactic) - baseline
2. DEMO_2: Requires finding ONE specific lemma - introduces search
3. DEMO_3: Requires structural reasoning (list induction) - introduces verification
4. DEMO_4: Requires combining multiple concepts - full orchestration
"""

import json
import re

NOTEBOOK_PATH = "d:/dev/CoursIA/MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-9-SK-Multi-Agents.ipynb"
SCRIPT_PATH = "d:/dev/CoursIA/MyIA.AI.Notebooks/SymbolicAI/Lean/scripts/run_lean9_demos.py"

# New DEMOS - each builds on concepts from previous
# Key insight: progression in STRUCTURE, not just difficulty
NEW_DEMOS_STR = '''DEMOS = [
    {
        "name": "DEMO_1_REFLEXIVITY",
        "theorem": "theorem demo_rfl (n : Nat) : n = n",
        "description": "Reflexivite pure - seul TacticAgent avec rfl",
        "expected_iterations": "1",
        "expected_lemmas": 0,
        "expected_agents": ["TacticAgent"],
        "complexity": "Triviale - une tactique suffit",
        "strategy": "rfl"
    },
    {
        "name": "DEMO_2_SUCCESSOR",
        "theorem": "theorem succ_ne_zero (n : Nat) : Nat.succ n != 0",
        "description": "Propriete structurelle - SearchAgent trouve Nat.succ_ne_zero",
        "expected_iterations": "1-2",
        "expected_lemmas": 1,
        "expected_agents": ["SearchAgent", "TacticAgent"],
        "complexity": "Simple - recherche de lemme",
        "strategy": "exact Nat.succ_ne_zero n OU decide"
    },
    {
        "name": "DEMO_3_LIST_INDUCTION",
        "theorem": "theorem length_append (xs ys : List Nat) : (xs ++ ys).length = xs.length + ys.length",
        "description": "Induction sur liste - necessite raisonnement structurel",
        "expected_iterations": "2-4",
        "expected_lemmas": 2,
        "expected_agents": ["SearchAgent", "TacticAgent", "VerifierAgent"],
        "complexity": "Intermediaire - induction + simplification",
        "strategy": "induction xs <;> simp [*]"
    },
    {
        "name": "DEMO_4_ALGEBRAIC",
        "theorem": "theorem mul_add_distrib (a b c : Nat) : a * (b + c) = a * b + a * c",
        "description": "Distributivite - peut necessiter induction OU lemme direct",
        "expected_iterations": "3-6",
        "expected_lemmas": 3,
        "expected_agents": ["SearchAgent", "TacticAgent", "VerifierAgent", "CriticAgent"],
        "complexity": "Avancee - multiple strategies possibles",
        "strategy": "exact Nat.mul_add OU induction a avec ring"
    }
]'''


def update_file_demos(filepath, is_notebook=False):
    """Update DEMOS in a file."""
    print(f"Processing: {filepath}")

    if is_notebook:
        with open(filepath, 'r', encoding='utf-8') as f:
            notebook = json.load(f)

        updated = False
        for idx, cell in enumerate(notebook['cells']):
            if cell['cell_type'] == 'code':
                source = ''.join(cell['source'])

                # Look for DEMOS definition
                if 'DEMOS = [' in source and '"name":' in source:
                    # Find the start and end of DEMOS
                    match = re.search(r'(DEMOS\s*=\s*\[[\s\S]*?\n\])', source)
                    if match:
                        old_demos = match.group(1)
                        new_source = source.replace(old_demos, NEW_DEMOS_STR)

                        if new_source != source:
                            lines = new_source.split('\n')
                            notebook['cells'][idx]['source'] = [line + '\n' for line in lines[:-1]] + [lines[-1]]
                            updated = True
                            print(f"  Updated DEMOS in cell {idx}")

        if updated:
            with open(filepath, 'w', encoding='utf-8') as f:
                json.dump(notebook, f, indent=1, ensure_ascii=False)
            return True
    else:
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()

        # Find and replace DEMOS block
        match = re.search(r'(DEMOS\s*=\s*\[[\s\S]*?\n\])', content)
        if match:
            old_demos = match.group(1)
            new_content = content.replace(old_demos, NEW_DEMOS_STR)

            if new_content != content:
                with open(filepath, 'w', encoding='utf-8') as f:
                    f.write(new_content)
                print(f"  Updated DEMOS")
                return True

    print(f"  No changes needed")
    return False


def main():
    print("=" * 70)
    print("UPDATING DEMOS FOR PROGRESSIVE COMPLEXITY")
    print("=" * 70)
    print()
    print("Progression design (screenwriter planting clues):")
    print()
    print("  DEMO_1: Reflexivity (n = n)")
    print("    -> Teaches: rfl is the basic equality tactic")
    print("    -> Agents: TacticAgent only")
    print()
    print("  DEMO_2: Structural property (succ n != 0)")
    print("    -> Teaches: Some properties need lemma lookup")
    print("    -> Agents: SearchAgent finds lemma, TacticAgent applies")
    print()
    print("  DEMO_3: List induction (length_append)")
    print("    -> Teaches: Recursive structures need induction")
    print("    -> Agents: Search + Tactic + Verifier checks proof")
    print()
    print("  DEMO_4: Algebraic identity (distributivity)")
    print("    -> Teaches: Multiple valid strategies exist")
    print("    -> Agents: Full orchestration, Critic may suggest alternatives")
    print()
    print("-" * 70)

    # Update script first (simpler)
    script_ok = update_file_demos(SCRIPT_PATH, is_notebook=False)

    # Update notebook
    notebook_ok = update_file_demos(NOTEBOOK_PATH, is_notebook=True)

    print()
    print("=" * 70)
    if script_ok or notebook_ok:
        print("SUCCESS: Demos updated")
        print()
        print("Key improvements:")
        print("  1. Clear agent progression: 1 -> 2 -> 3 -> 4 agents")
        print("  2. Conceptual building: each demo teaches for the next")
        print("  3. Structural variety: equality -> property -> induction -> algebra")
    else:
        print("No changes made")
    print("=" * 70)


if __name__ == "__main__":
    main()
