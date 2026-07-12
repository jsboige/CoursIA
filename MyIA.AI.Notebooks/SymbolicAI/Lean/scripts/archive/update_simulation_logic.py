#!/usr/bin/env python3
"""
Update simulation logic to match the new DEMOS.

Current DEMOS (v4):
- DEMO_1: n = n (rfl)
- DEMO_2: 0 + n = n (Nat.zero_add)
- DEMO_3: n + 0 + m = m + n (two steps)
- DEMO_4: a * c + b * c = (a + b) * c (ring or rewrite)
"""

import json
import re

NOTEBOOK_PATH = "d:/dev/CoursIA/MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-9-SK-Multi-Agents.ipynb"

# Updated _do_tactic with correct theorem patterns
NEW_DO_TACTIC = '''    def _do_tactic(self, state: ProofState, theorem: str, goal: str) -> str:
        """Generation de tactiques - mise a jour pour DEMOS v4."""
        state_mgr = self.plugins.get("state")
        if not state_mgr:
            return "[TacticAgent] Plugin manquant."

        tactics_tried = len(state.tactics_history)

        # DEMO_1: n = n (reflexivity)
        if "n = n" in theorem and "demo_rfl" in theorem:
            state_mgr.log_tactic_attempt("rfl", goal, 1.0, "Reflexivite")
            state_mgr.designate_next_agent("VerifierAgent")
            return "[TacticAgent] Tactique: rfl. -> VerifierAgent"

        # DEMO_2: 0 + n = n (zero_add)
        if "0 + n = n" in theorem or "zero_add" in theorem:
            if tactics_tried == 0:
                # First try rfl (will fail)
                state_mgr.log_tactic_attempt("rfl", goal, 0.3, "Tentative 1")
                state_mgr.designate_next_agent("VerifierAgent")
                return "[TacticAgent] Tentative 1: rfl. -> VerifierAgent"
            elif tactics_tried == 1:
                # Then try simp
                state_mgr.log_tactic_attempt("simp", goal, 0.5, "Tentative 2")
                state_mgr.designate_next_agent("VerifierAgent")
                return "[TacticAgent] Tentative 2: simp. -> VerifierAgent"
            else:
                # Finally use exact Nat.zero_add
                state_mgr.log_tactic_attempt("exact Nat.zero_add n", goal, 0.95, "Solution")
                state_mgr.designate_next_agent("VerifierAgent")
                return "[TacticAgent] Tactique: exact Nat.zero_add n. -> VerifierAgent"

        # DEMO_3: n + 0 + m = m + n (two steps)
        if "n + 0 + m = m + n" in theorem or "add_zero_comm" in theorem:
            if tactics_tried == 0:
                state_mgr.log_tactic_attempt("rfl", goal, 0.2, "Tentative 1")
                state_mgr.designate_next_agent("VerifierAgent")
                return "[TacticAgent] Tentative 1: rfl (echouera). -> VerifierAgent"
            elif tactics_tried == 1:
                state_mgr.log_tactic_attempt("simp", goal, 0.5, "Tentative 2")
                state_mgr.designate_next_agent("VerifierAgent")
                return "[TacticAgent] Tentative 2: simp (partiel). -> VerifierAgent"
            elif tactics_tried == 2:
                state_mgr.log_tactic_attempt("omega", goal, 0.6, "Tentative 3")
                state_mgr.designate_next_agent("VerifierAgent")
                return "[TacticAgent] Tentative 3: omega. -> VerifierAgent"
            else:
                state_mgr.log_tactic_attempt("simp [Nat.add_zero, Nat.add_comm]", goal, 0.95, "Solution")
                state_mgr.designate_next_agent("VerifierAgent")
                return "[TacticAgent] Tactique: simp [Nat.add_zero, Nat.add_comm]. -> VerifierAgent"

        # DEMO_4: a * c + b * c = (a + b) * c (distributivity converse)
        if "a * c + b * c" in theorem or "add_mul_comm" in theorem:
            tactics_sequence = [
                ("rfl", 0.1, "Tentative 1 - echouera"),
                ("simp", 0.3, "Tentative 2 - echouera"),
                ("omega", 0.3, "Tentative 3 - echouera"),
                ("rw [Nat.add_mul]", 0.5, "Tentative 4 - mauvais sens"),
                ("rw [<- Nat.add_mul]", 0.7, "Tentative 5 - presque"),
                ("ring", 0.95, "Solution - ring resout")
            ]

            if tactics_tried < len(tactics_sequence):
                tactic, conf, desc = tactics_sequence[tactics_tried]
                state_mgr.log_tactic_attempt(tactic, goal, conf, desc)
                state_mgr.designate_next_agent("VerifierAgent")
                return f"[TacticAgent] {desc}: {tactic}. -> VerifierAgent"
            else:
                state_mgr.log_tactic_attempt("ring", goal, 0.95, "Fallback ring")
                state_mgr.designate_next_agent("VerifierAgent")
                return "[TacticAgent] Tactique finale: ring. -> VerifierAgent"

        # Fallback
        state_mgr.log_tactic_attempt("simp", goal, 0.3, "Fallback")
        state_mgr.designate_next_agent("VerifierAgent")
        return "[TacticAgent] simp. -> VerifierAgent"'''

# Updated _do_verify with correct success conditions
NEW_DO_VERIFY = '''    def _do_verify(self, state: ProofState, theorem: str, goal: str) -> str:
        """Verification avec echecs realistes pour DEMOS v4."""
        state_mgr = self.plugins.get("state")
        if not state_mgr or not state.tactics_history:
            return "[VerifierAgent] Rien a verifier."

        last_tactic = state.tactics_history[-1]
        n = len(state.tactics_history)

        # DEMO_1: rfl always works for n = n
        if "n = n" in theorem:
            if "rfl" in last_tactic:
                state.phase = ProofPhase.COMPLETE
                state.final_proof = "rfl"
                return "[VerifierAgent] SUCCES! rfl prouve n = n."
            return "[VerifierAgent] Echec. -> CriticAgent"

        # DEMO_2: 0 + n = n
        if "0 + n = n" in theorem or "zero_add" in theorem:
            if "Nat.zero_add" in last_tactic or "exact" in last_tactic:
                state.phase = ProofPhase.COMPLETE
                state.final_proof = "exact Nat.zero_add n"
                return "[VerifierAgent] SUCCES! Lemme zero_add applique."
            elif "simp" in last_tactic and n >= 2:
                state.phase = ProofPhase.COMPLETE
                state.final_proof = "simp [Nat.zero_add]"
                return "[VerifierAgent] SUCCES via simp!"
            return f"[VerifierAgent] Echec tactique {n}. -> CriticAgent"

        # DEMO_3: n + 0 + m = m + n
        if "n + 0 + m = m + n" in theorem or "add_zero_comm" in theorem:
            if "simp" in last_tactic and "add_zero" in last_tactic and "add_comm" in last_tactic:
                state.phase = ProofPhase.COMPLETE
                state.final_proof = "simp [Nat.add_zero, Nat.add_comm]"
                return "[VerifierAgent] SUCCES apres 2 etapes!"
            elif "simp" in last_tactic and n == 2:
                state_mgr.designate_next_agent("CriticAgent")
                return "[VerifierAgent] Progres: n + 0 -> n. Mais but restant: n + m = m + n. -> CriticAgent"
            elif n >= 4:
                state.phase = ProofPhase.COMPLETE
                state.final_proof = "simp [Nat.add_zero, Nat.add_comm]"
                return "[VerifierAgent] SUCCES apres exploration!"
            state_mgr.designate_next_agent("CriticAgent")
            return "[VerifierAgent] Echec. -> CriticAgent"

        # DEMO_4: a * c + b * c = (a + b) * c
        if "a * c + b * c" in theorem or "add_mul_comm" in theorem:
            if "ring" in last_tactic:
                state.phase = ProofPhase.COMPLETE
                state.final_proof = "ring"
                return "[VerifierAgent] SUCCES! ring resout la distributivite."
            elif "<- Nat.add_mul" in last_tactic or "← Nat.add_mul" in last_tactic:
                state.phase = ProofPhase.COMPLETE
                state.final_proof = "rw [← Nat.add_mul]"
                return "[VerifierAgent] SUCCES! Rewrite inverse applique."
            elif n >= 6:
                state.phase = ProofPhase.COMPLETE
                state.final_proof = "ring"
                return "[VerifierAgent] SUCCES apres exploration!"
            state_mgr.designate_next_agent("CriticAgent")
            return "[VerifierAgent] Echec. -> CriticAgent"

        # Fallback
        state_mgr.designate_next_agent("CriticAgent")
        return "[VerifierAgent] Echec. -> CriticAgent"'''

# Updated _do_search with correct lemma hints
NEW_DO_SEARCH = '''    def _do_search(self, state: ProofState, theorem: str, goal: str) -> str:
        """Recherche de lemmes pour DEMOS v4."""
        state_mgr = self.plugins.get("state")
        if not state_mgr:
            return "[SearchAgent] Plugins manquants."

        # DEMO_1: n = n
        if "n = n" in theorem:
            state_mgr.add_lemma("Eq.refl")
            state_mgr.designate_next_agent("TacticAgent")
            return "[SearchAgent] Lemme: Eq.refl (ou rfl). -> TacticAgent"

        # DEMO_2: 0 + n = n
        if "0 + n = n" in theorem or "zero_add" in theorem:
            state_mgr.add_lemma("Nat.zero_add")
            state_mgr.designate_next_agent("TacticAgent")
            return "[SearchAgent] Lemme: Nat.zero_add. -> TacticAgent"

        # DEMO_3: n + 0 + m = m + n
        if "n + 0 + m = m + n" in theorem or "add_zero_comm" in theorem:
            state_mgr.add_lemma("Nat.add_zero")
            state_mgr.add_lemma("Nat.add_comm")
            state_mgr.add_lemma("Nat.add_assoc")
            state_mgr.designate_next_agent("TacticAgent")
            return "[SearchAgent] Lemmes: Nat.add_zero, Nat.add_comm, Nat.add_assoc. -> TacticAgent"

        # DEMO_4: a * c + b * c = (a + b) * c
        if "a * c + b * c" in theorem or "add_mul_comm" in theorem:
            state_mgr.add_lemma("Nat.add_mul")
            state_mgr.add_lemma("Nat.right_distrib")
            state_mgr.designate_next_agent("TacticAgent")
            return "[SearchAgent] Lemmes: Nat.add_mul (distributivite), Nat.right_distrib. -> TacticAgent"

        # Fallback
        state_mgr.designate_next_agent("TacticAgent")
        return "[SearchAgent] Aucun lemme specifique trouve. -> TacticAgent"'''


def update_notebook():
    """Update simulation methods in the notebook."""
    print(f"Reading: {NOTEBOOK_PATH}")

    with open(NOTEBOOK_PATH, 'r', encoding='utf-8') as f:
        nb = json.load(f)

    changes = []

    for idx, cell in enumerate(nb['cells']):
        if cell['cell_type'] != 'code':
            continue

        source = ''.join(cell['source'])

        # Look for SimpleAgent methods cell
        if 'def _do_tactic' in source and 'def _do_verify' in source and 'def _do_search' in source:
            print(f"Found simulation cell: {idx}")

            # Replace _do_tactic
            tactic_start = source.find('    def _do_tactic')
            tactic_end = source.find('\n    def _do_verify')

            if tactic_start != -1 and tactic_end != -1:
                source = source[:tactic_start] + NEW_DO_TACTIC + source[tactic_end:]
                changes.append("Updated _do_tactic")

            # Replace _do_verify
            verify_start = source.find('    def _do_verify')
            verify_end = source.find('\n    def _do_search')

            if verify_start != -1 and verify_end != -1:
                source = source[:verify_start] + NEW_DO_VERIFY + source[verify_end:]
                changes.append("Updated _do_verify")

            # Replace _do_search
            search_start = source.find('    def _do_search')
            # Find next method or end of class
            next_method = source.find('\n    def ', search_start + 10)
            if next_method == -1:
                # End of class - find class end or next class
                class_end = source.find('\nclass ', search_start + 10)
                if class_end == -1:
                    class_end = source.find('\n\n\n', search_start + 10)
                next_method = class_end if class_end != -1 else len(source)

            if search_start != -1:
                source = source[:search_start] + NEW_DO_SEARCH + source[next_method:]
                changes.append("Updated _do_search")

            # Save back to cell
            lines = source.split('\n')
            nb['cells'][idx]['source'] = [line + '\n' for line in lines[:-1]] + [lines[-1]]

            break

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


def main():
    print("=" * 70)
    print("UPDATING SIMULATION LOGIC FOR DEMOS V4")
    print("=" * 70)
    print()
    print("Aligning simulation with current DEMOS:")
    print("  DEMO_1: n = n (rfl)")
    print("  DEMO_2: 0 + n = n (exploration -> Nat.zero_add)")
    print("  DEMO_3: n + 0 + m = m + n (multi-step)")
    print("  DEMO_4: a * c + b * c = (a + b) * c (exploration -> ring)")
    print()
    print("-" * 70)

    success = update_notebook()

    print()
    print("=" * 70)
    if success:
        print("SUCCESS: Simulation logic updated")
    else:
        print("No changes made")
    print("=" * 70)


if __name__ == "__main__":
    main()
