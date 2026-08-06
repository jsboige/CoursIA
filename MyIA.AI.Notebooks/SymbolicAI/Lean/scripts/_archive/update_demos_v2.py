#!/usr/bin/env python3
"""
Update Lean-9 demos with improved gradation (v2).

Strategy: Use theorems that FORCE different agent patterns by their nature.
Key insight: GPT-5.2 knows Mathlib too well, so we need theorems without direct lemmas.

Progression:
1. DEMO_1: Pure reflexivity - TacticAgent alone
2. DEMO_2: Decidable computation - SearchAgent + TacticAgent (rfl/simp fail)
3. DEMO_3: Hypothesis usage - requires understanding, not just lookup
4. DEMO_4: Lemma combination - no single lemma works, need composition
"""

import json
import re

NOTEBOOK_PATH = "d:/dev/CoursIA/MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-9-SK-Multi-Agents.ipynb"
SCRIPT_PATH = "d:/dev/CoursIA/MyIA.AI.Notebooks/SymbolicAI/Lean/scripts/run_lean9_demos.py"

# New DEMOS v2 - designed to force different agent patterns
NEW_DEMOS_STR = '''DEMOS = [
    {
        "name": "DEMO_1_REFLEXIVITY",
        "theorem": "theorem demo_rfl (n : Nat) : n = n",
        "description": "Reflexivite pure - TacticAgent reconnait rfl immediatement",
        "expected_iterations": "2-3",
        "expected_lemmas": 0,
        "expected_agents": ["TacticAgent"],
        "complexity": "Triviale - rfl suffit, pas de recherche",
        "strategy": "rfl",
        "trap": "Aucun piege - cas de base"
    },
    {
        "name": "DEMO_2_DECIDABLE",
        "theorem": "theorem three_ne_five : (3 : Nat) \\u2260 5",
        "description": "Inegalite decidable - rfl/simp echouent, besoin de decide",
        "expected_iterations": "3-5",
        "expected_lemmas": 0,
        "expected_agents": ["SearchAgent", "TacticAgent"],
        "complexity": "Simple - mais piege tactique",
        "strategy": "decide ou native_decide",
        "trap": "rfl et simp ne marchent pas sur les inegalites"
    },
    {
        "name": "DEMO_3_HYPOTHESIS",
        "theorem": "theorem symmetry_from_hyp (a b : Nat) (h : a = b) : b = a",
        "description": "Utilisation d'hypothese - pas de lemme direct 'b = a'",
        "expected_iterations": "3-5",
        "expected_lemmas": 1,
        "expected_agents": ["SearchAgent", "TacticAgent", "VerifierAgent"],
        "complexity": "Intermediaire - comprendre et utiliser h",
        "strategy": "exact h.symm OU rw [h] OU exact Eq.symm h",
        "trap": "SearchAgent ne trouve pas de lemme direct pour b = a"
    },
    {
        "name": "DEMO_4_COMPOSITION",
        "theorem": "theorem add_right_comm (a b c : Nat) : a + b + c = a + c + b",
        "description": "Composition de lemmes - pas de lemme direct, besoin de combiner",
        "expected_iterations": "4-8",
        "expected_lemmas": 2,
        "expected_agents": ["SearchAgent", "TacticAgent", "VerifierAgent", "CriticAgent"],
        "complexity": "Avancee - plusieurs rewrites necessaires",
        "strategy": "rw [Nat.add_assoc, Nat.add_comm b c, ...] OU omega",
        "trap": "Un seul rewrite ne suffit pas, strategie multi-etapes"
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
                    match = re.search(r'(DEMOS\s*=\s*\[[^\]]*(?:\{[^}]*\}[^\]]*)*\])', source, re.DOTALL)
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
        match = re.search(r'(DEMOS\s*=\s*\[[^\]]*(?:\{[^}]*\}[^\]]*)*\])', content, re.DOTALL)
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
    print("UPDATING DEMOS V2 - FORCED GRADATION")
    print("=" * 70)
    print()
    print("Problem: GPT-5.2 shortcuts all demos with direct Mathlib lemmas")
    print()
    print("Solution: Theorems designed to force different agent patterns:")
    print()
    print("  DEMO_1: Reflexivity (n = n)")
    print("    -> TacticAgent: rfl (no search needed)")
    print("    -> Expected: 2-3 iterations")
    print()
    print("  DEMO_2: Decidable inequality (3 != 5)")
    print("    -> TRAP: rfl/simp FAIL on inequalities")
    print("    -> Solution: decide or native_decide")
    print("    -> Expected: 3-5 iterations (retry needed)")
    print()
    print("  DEMO_3: Hypothesis usage (h : a = b |- b = a)")
    print("    -> TRAP: No direct lemma for 'b = a'")
    print("    -> Solution: Use h.symm or rw [h]")
    print("    -> Expected: 3-5 iterations")
    print()
    print("  DEMO_4: Lemma composition (a + b + c = a + c + b)")
    print("    -> TRAP: No single lemma works")
    print("    -> Solution: Multiple rewrites or omega")
    print("    -> Expected: 4-8 iterations (CriticAgent may intervene)")
    print()
    print("-" * 70)

    # Update notebook
    notebook_ok = update_file_demos(NOTEBOOK_PATH, is_notebook=True)

    # Update script if exists
    try:
        script_ok = update_file_demos(SCRIPT_PATH, is_notebook=False)
    except FileNotFoundError:
        script_ok = False
        print(f"  Script not found: {SCRIPT_PATH}")

    print()
    print("=" * 70)
    if notebook_ok or script_ok:
        print("SUCCESS: Demos updated with v2 gradation")
        print()
        print("Key improvements:")
        print("  1. DEMO_2 has a TRAP: rfl/simp fail on inequalities")
        print("  2. DEMO_3 requires understanding hypotheses")
        print("  3. DEMO_4 requires multi-step reasoning")
        print()
        print("Next: Re-run the notebook to see improved agent progression")
    else:
        print("No changes made")
    print("=" * 70)


if __name__ == "__main__":
    main()
