#!/usr/bin/env python3
"""
Fix agent instructions for v3 progression.
Handles Jupyter notebook JSON format properly.
"""

import json

NOTEBOOK_PATH = "d:/dev/CoursIA/MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-9-SK-Multi-Agents.ipynb"

# New TacticAgent instructions that FORCE exploration
NEW_TACTIC_INSTRUCTIONS = """Tu es l'agent de GENERATION DE TACTIQUES pour le theorem proving en Lean 4.

TON ROLE UNIQUE:
- Generer des sequences de tactiques Lean pour prouver le but
- Explorer les tactiques systematiquement

STRATEGIE D'EXPLORATION OBLIGATOIRE:
Tu DOIS essayer les tactiques dans cet ORDRE EXACT, meme si tu penses qu'elles echoueront:

PREMIERE TENTATIVE: Toujours essayer rfl ou trivial
DEUXIEME TENTATIVE: simp sans arguments
TROISIEME TENTATIVE: Lemmes de SearchAgent (exact Lemma_name)
QUATRIEME TENTATIVE: Tactiques avancees (omega, ring, linarith)
CINQUIEME+ TENTATIVE: Approches structurelles (induction, cases)

POURQUOI CETTE APPROCHE:
Cette strategie pedagogique montre le processus de decouverte.
Ne pas proposer la solution optimale immediatement.
Laisser le systeme iterer vers la solution.

WORKFLOW:
1. get_proof_state() pour comprendre le contexte
2. Choisir UNE tactique selon l'ordre ci-dessus
3. log_tactic_attempt() pour enregistrer
4. Deleguer a VerifierAgent

IMPORTANT:
- Proposer UNE SEULE tactique a la fois
- Si echec, CriticAgent analysera et guidera
- Ne pas "tricher" en donnant la reponse finale directement
"""


def update_instructions():
    """Update TacticAgent instructions in the notebook."""
    print(f"Reading: {NOTEBOOK_PATH}")

    with open(NOTEBOOK_PATH, 'r', encoding='utf-8') as f:
        notebook = json.load(f)

    changes = []

    for idx, cell in enumerate(notebook['cells']):
        if cell['cell_type'] != 'code':
            continue

        source_lines = cell['source']
        source_text = ''.join(source_lines)

        # Find cell with TACTIC_AGENT_INSTRUCTIONS
        if 'TACTIC_AGENT_INSTRUCTIONS' in source_text and 'GENERATION DE TACTIQUES' in source_text:
            # Find the instruction block and replace it
            new_lines = []
            in_tactic_instructions = False
            skip_until_end = False

            for i, line in enumerate(source_lines):
                # Detect start of TACTIC_AGENT_INSTRUCTIONS block
                if 'TACTIC_AGENT_INSTRUCTIONS = """' in line or 'TACTIC_AGENT_INSTRUCTIONS = \\"""' in line:
                    in_tactic_instructions = True
                    skip_until_end = True
                    # Write new instruction block
                    new_lines.append('TACTIC_AGENT_INSTRUCTIONS = """\n')
                    for instr_line in NEW_TACTIC_INSTRUCTIONS.split('\n'):
                        new_lines.append(instr_line + '\n')
                    new_lines.append('"""\n')
                    continue

                # Skip lines until we find the closing """
                if skip_until_end:
                    # Check if this line ends the instruction block
                    stripped = line.strip()
                    if stripped == '"""' or stripped == '\\"""':
                        skip_until_end = False
                        continue
                    # Also check for VERIFIER_AGENT which signals next block
                    if 'VERIFIER_AGENT_INSTRUCTIONS' in line:
                        skip_until_end = False
                        new_lines.append('\n')
                        new_lines.append(line)
                        continue
                    # Skip this line (part of old instructions)
                    continue

                new_lines.append(line)

            if in_tactic_instructions:
                notebook['cells'][idx]['source'] = new_lines
                changes.append(f"Cell {idx}: Updated TacticAgent instructions")

    if changes:
        with open(NOTEBOOK_PATH, 'w', encoding='utf-8') as f:
            json.dump(notebook, f, indent=1, ensure_ascii=False)

        print("\nChanges made:")
        for c in changes:
            print(f"  - {c}")
        print(f"\nNotebook saved.")
    else:
        print("No changes made.")

    return len(changes) > 0


if __name__ == "__main__":
    print("=" * 60)
    print("FIXING AGENT INSTRUCTIONS FOR V3")
    print("=" * 60)
    print()
    print("Goal: Force TacticAgent to explore systematically")
    print("      instead of proposing optimal solution immediately")
    print()
    print("-" * 60)

    success = update_instructions()

    print()
    print("=" * 60)
    if success:
        print("SUCCESS: Instructions updated")
        print()
        print("Expected LLM behavior:")
        print("  1. First try rfl/trivial (will fail on most demos)")
        print("  2. Then try simp (may partially work)")
        print("  3. Then use SearchAgent lemmas")
        print("  4. Then omega/ring")
        print("  5. Finally induction if needed")
    else:
        print("No changes made")
    print("=" * 60)
