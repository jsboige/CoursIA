#!/usr/bin/env python3
"""
Update DEMOS v5: Real complexity progression.

DEMO_1: n = n (rfl) - 2 iterations
DEMO_2: 0 + n = n (lemma search) - 4 iterations
DEMO_3: a * c + b * c = (a + b) * c (distributivity) - 7 iterations
DEMO_4: m * n = n * m (double induction) - 12+ iterations
"""

import json
import re

NOTEBOOK_PATH = "d:/dev/CoursIA/MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-9-SK-Multi-Agents.ipynb"

# New DEMOS with real complexity progression
NEW_DEMOS = '''DEMOS = [
    {
        "name": "DEMO_1_REFLEXIVITY",
        "theorem": "theorem demo_rfl (n : Nat) : n = n",
        "description": "Reflexivite pure - rfl immediat",
        "expected_iterations": "2",
        "complexity": "Triviale",
        "strategy": "rfl",
        "expected_lemmas": ["Eq.refl"],
        "trap": "Aucun - baseline"
    },
    {
        "name": "DEMO_2_LEMMA_SEARCH",
        "theorem": "theorem zero_add_eq (n : Nat) : 0 + n = n",
        "description": "Recherche de lemme - rfl echoue, besoin Nat.zero_add",
        "expected_iterations": "4",
        "complexity": "Simple",
        "strategy": "exact Nat.zero_add n",
        "expected_lemmas": ["Nat.zero_add"],
        "trap": "rfl echoue (pas definitionnellement egal)"
    },
    {
        "name": "DEMO_3_DISTRIBUTIVITY",
        "theorem": "theorem add_mul_distrib (a b c : Nat) : a * c + b * c = (a + b) * c",
        "description": "Distributivite inverse - necessite rw ou ring",
        "expected_iterations": "7",
        "complexity": "Intermediaire",
        "strategy": "rw [<- Nat.add_mul] ou ring",
        "expected_lemmas": ["Nat.add_mul", "Nat.right_distrib"],
        "trap": "Forme inversee, simp seul ne suffit pas"
    },
    {
        "name": "DEMO_4_DOUBLE_INDUCTION",
        "theorem": "theorem mul_comm_manual (m n : Nat) : m * n = n * m",
        "description": "Commutativite multiplication - induction double requise",
        "expected_iterations": "12",
        "complexity": "Avancee",
        "strategy": "induction m; induction n; simp [Nat.mul_succ, Nat.succ_mul, Nat.add_comm]",
        "expected_lemmas": ["Nat.mul_succ", "Nat.succ_mul", "Nat.add_comm", "Nat.mul_zero", "Nat.zero_mul"],
        "trap": "Necessite induction structuree, pas de lemme direct"
    }
]'''

# Updated simulation logic for _do_search
NEW_DO_SEARCH = '''    def _do_search(self, state: ProofState, theorem: str, goal: str) -> str:
        """Recherche de lemmes - DEMOS v5."""
        state_mgr = self.plugins.get("state")
        if not state_mgr:
            return "[SearchAgent] Plugins manquants."

        # DEMO_1: n = n
        if "n = n" in theorem and "demo_rfl" in theorem:
            state_mgr.add_lemma("Eq.refl")
            state_mgr.designate_next_agent("TacticAgent")
            return "[SearchAgent] Lemme trouve: Eq.refl (reflexivite). -> TacticAgent"

        # DEMO_2: 0 + n = n
        if "0 + n = n" in theorem or "zero_add" in theorem:
            state_mgr.add_lemma("Nat.zero_add")
            state_mgr.add_lemma("Nat.add_zero")  # Similar but different
            state_mgr.designate_next_agent("TacticAgent")
            return "[SearchAgent] Lemmes: Nat.zero_add, Nat.add_zero. -> TacticAgent"

        # DEMO_3: a * c + b * c = (a + b) * c
        if "a * c + b * c" in theorem or "add_mul_distrib" in theorem:
            state_mgr.add_lemma("Nat.add_mul")
            state_mgr.add_lemma("Nat.mul_add")
            state_mgr.add_lemma("Nat.right_distrib")
            state_mgr.designate_next_agent("TacticAgent")
            return "[SearchAgent] Lemmes distributivite: Nat.add_mul, Nat.mul_add, Nat.right_distrib. -> TacticAgent"

        # DEMO_4: m * n = n * m
        if "m * n = n * m" in theorem or "mul_comm_manual" in theorem:
            state_mgr.add_lemma("Nat.mul_comm")  # Direct but we want exploration
            state_mgr.add_lemma("Nat.mul_succ")
            state_mgr.add_lemma("Nat.succ_mul")
            state_mgr.add_lemma("Nat.mul_zero")
            state_mgr.add_lemma("Nat.zero_mul")
            state_mgr.designate_next_agent("TacticAgent")
            return "[SearchAgent] Lemmes pour induction: mul_succ, succ_mul, mul_zero, zero_mul. -> TacticAgent"

        # Fallback
        state_mgr.designate_next_agent("TacticAgent")
        return "[SearchAgent] Recherche generique. -> TacticAgent"'''

# Updated simulation logic for _do_tactic
NEW_DO_TACTIC = '''    def _do_tactic(self, state: ProofState, theorem: str, goal: str) -> str:
        """Generation de tactiques - DEMOS v5 avec progression realiste."""
        state_mgr = self.plugins.get("state")
        if not state_mgr:
            return "[TacticAgent] Plugin manquant."

        n = len(state.tactics_history)

        # DEMO_1: n = n (reflexivity) - SUCCESS IMMEDIATE
        if "n = n" in theorem and "demo_rfl" in theorem:
            state_mgr.log_tactic_attempt("rfl", goal, 1.0, "Reflexivite directe")
            state_mgr.designate_next_agent("VerifierAgent")
            return "[TacticAgent] Tactique: rfl (reflexivite). -> VerifierAgent"

        # DEMO_2: 0 + n = n - 2 ECHECS AVANT SUCCES
        if "0 + n = n" in theorem or "zero_add" in theorem:
            if n == 0:
                state_mgr.log_tactic_attempt("rfl", goal, 0.3, "Tentative naive")
                state_mgr.designate_next_agent("VerifierAgent")
                return "[TacticAgent] Tentative 1: rfl (devrait echouer). -> VerifierAgent"
            elif n == 1:
                state_mgr.log_tactic_attempt("simp", goal, 0.4, "Simplification")
                state_mgr.designate_next_agent("VerifierAgent")
                return "[TacticAgent] Tentative 2: simp (insuffisant). -> VerifierAgent"
            else:
                state_mgr.log_tactic_attempt("exact Nat.zero_add n", goal, 0.95, "Lemme exact")
                state_mgr.designate_next_agent("VerifierAgent")
                return "[TacticAgent] Tactique: exact Nat.zero_add n. -> VerifierAgent"

        # DEMO_3: a * c + b * c = (a + b) * c - 4 ECHECS AVANT SUCCES
        if "a * c + b * c" in theorem or "add_mul_distrib" in theorem:
            tactics_sequence = [
                ("rfl", 0.1, "Tentative 1 - reflexivite"),
                ("simp", 0.2, "Tentative 2 - simplification"),
                ("ring", 0.3, "Tentative 3 - ring (version)"),
                ("rw [Nat.add_mul]", 0.4, "Tentative 4 - mauvais sens"),
                ("rw [<- Nat.add_mul]", 0.95, "Solution - rewrite inverse")
            ]
            if n < len(tactics_sequence):
                tactic, conf, desc = tactics_sequence[n]
                state_mgr.log_tactic_attempt(tactic, goal, conf, desc)
                state_mgr.designate_next_agent("VerifierAgent")
                return f"[TacticAgent] {desc}: {tactic}. -> VerifierAgent"
            else:
                state_mgr.log_tactic_attempt("ring", goal, 0.95, "Fallback ring")
                state_mgr.designate_next_agent("VerifierAgent")
                return "[TacticAgent] Fallback: ring. -> VerifierAgent"

        # DEMO_4: m * n = n * m - 8+ ECHECS, INDUCTION DOUBLE
        if "m * n = n * m" in theorem or "mul_comm_manual" in theorem:
            tactics_sequence = [
                ("rfl", 0.05, "Tentative 1 - reflexivite (echoue)"),
                ("simp", 0.1, "Tentative 2 - simp (insuffisant)"),
                ("ring", 0.15, "Tentative 3 - ring seul (echoue)"),
                ("omega", 0.1, "Tentative 4 - omega (non applicable)"),
                ("induction m", 0.3, "Tentative 5 - induction sur m"),
                ("simp [Nat.mul_zero, Nat.zero_mul]", 0.4, "Tentative 6 - cas base"),
                ("simp [Nat.mul_succ]", 0.5, "Tentative 7 - cas succ partiel"),
                ("simp [Nat.succ_mul]", 0.5, "Tentative 8 - autre direction"),
                ("rw [Nat.mul_succ, Nat.succ_mul]", 0.6, "Tentative 9 - rewrites"),
                ("simp [Nat.mul_succ, Nat.succ_mul, Nat.add_comm]", 0.95, "Solution complete")
            ]
            if n < len(tactics_sequence):
                tactic, conf, desc = tactics_sequence[n]
                state_mgr.log_tactic_attempt(tactic, goal, conf, desc)
                state_mgr.designate_next_agent("VerifierAgent")
                return f"[TacticAgent] {desc}: {tactic}. -> VerifierAgent"
            else:
                state_mgr.log_tactic_attempt("simp [Nat.mul_comm]", goal, 0.95, "Lemme direct")
                state_mgr.designate_next_agent("VerifierAgent")
                return "[TacticAgent] Fallback: simp [Nat.mul_comm]. -> VerifierAgent"

        # Fallback
        state_mgr.log_tactic_attempt("simp", goal, 0.3, "Fallback")
        state_mgr.designate_next_agent("VerifierAgent")
        return "[TacticAgent] Fallback: simp. -> VerifierAgent"'''

# Updated simulation logic for _do_verify
NEW_DO_VERIFY = '''    def _do_verify(self, state: ProofState, theorem: str, goal: str) -> str:
        """Verification - DEMOS v5 avec echecs realistes."""
        state_mgr = self.plugins.get("state")
        if not state_mgr or not state.tactics_history:
            return "[VerifierAgent] Rien a verifier."

        last_tactic = state.tactics_history[-1]
        n = len(state.tactics_history)

        # DEMO_1: n = n - SUCCESS AU PREMIER RFL
        if "n = n" in theorem and "demo_rfl" in theorem:
            if "rfl" in last_tactic.tactic:
                state.phase = ProofPhase.COMPLETE
                state.final_proof = "rfl"
                return "[VerifierAgent] SUCCES! rfl prouve n = n."
            return "[VerifierAgent] Echec. -> CriticAgent"

        # DEMO_2: 0 + n = n - SUCCESS APRES 2 ECHECS
        if "0 + n = n" in theorem or "zero_add" in theorem:
            if "Nat.zero_add" in last_tactic.tactic or "exact" in last_tactic.tactic:
                state.phase = ProofPhase.COMPLETE
                state.final_proof = "exact Nat.zero_add n"
                return "[VerifierAgent] SUCCES! Lemme Nat.zero_add applique."
            if n >= 3:
                state.phase = ProofPhase.COMPLETE
                state.final_proof = "exact Nat.zero_add n"
                return "[VerifierAgent] SUCCES apres exploration!"
            state_mgr.designate_next_agent("CriticAgent")
            return f"[VerifierAgent] Echec tactique {n}: {last_tactic.tactic}. -> CriticAgent"

        # DEMO_3: a * c + b * c = (a + b) * c - SUCCESS APRES 4 ECHECS
        if "a * c + b * c" in theorem or "add_mul_distrib" in theorem:
            if "<- Nat.add_mul" in last_tactic.tactic or "← Nat.add_mul" in last_tactic.tactic:
                state.phase = ProofPhase.COMPLETE
                state.final_proof = "rw [<- Nat.add_mul]"
                return "[VerifierAgent] SUCCES! Rewrite inverse applique."
            if "ring" in last_tactic.tactic and n >= 5:
                state.phase = ProofPhase.COMPLETE
                state.final_proof = "ring"
                return "[VerifierAgent] SUCCES! ring resout apres exploration."
            if n >= 6:
                state.phase = ProofPhase.COMPLETE
                state.final_proof = "rw [<- Nat.add_mul]"
                return "[VerifierAgent] SUCCES apres exploration!"
            state_mgr.designate_next_agent("CriticAgent")
            return f"[VerifierAgent] Echec tactique {n}: {last_tactic.tactic}. Distributivite inversee. -> CriticAgent"

        # DEMO_4: m * n = n * m - SUCCESS APRES 8+ ECHECS
        if "m * n = n * m" in theorem or "mul_comm_manual" in theorem:
            if "mul_succ" in last_tactic.tactic and "succ_mul" in last_tactic.tactic and "add_comm" in last_tactic.tactic:
                state.phase = ProofPhase.COMPLETE
                state.final_proof = "induction m <;> simp [Nat.mul_succ, Nat.succ_mul, Nat.add_comm, *]"
                return "[VerifierAgent] SUCCES! Induction complete avec lemmes mul_succ, succ_mul, add_comm."
            if "Nat.mul_comm" in last_tactic.tactic:
                state.phase = ProofPhase.COMPLETE
                state.final_proof = "exact Nat.mul_comm m n"
                return "[VerifierAgent] SUCCES! Lemme direct Nat.mul_comm."
            if n >= 10:
                state.phase = ProofPhase.COMPLETE
                state.final_proof = "induction m <;> simp [Nat.mul_succ, Nat.succ_mul, Nat.add_comm, *]"
                return "[VerifierAgent] SUCCES apres exploration complete!"

            # Progress messages based on iteration
            if n < 4:
                state_mgr.designate_next_agent("CriticAgent")
                return f"[VerifierAgent] Echec tactique {n}: {last_tactic.tactic}. Approche trop simple. -> CriticAgent"
            elif n < 6:
                state_mgr.designate_next_agent("CriticAgent")
                return f"[VerifierAgent] Echec tactique {n}: Induction initiee mais incomplete. -> CriticAgent"
            elif n < 8:
                state_mgr.designate_next_agent("CriticAgent")
                return f"[VerifierAgent] Progres: cas base OK. Cas inductif incomplet. -> CriticAgent"
            else:
                state_mgr.designate_next_agent("CriticAgent")
                return f"[VerifierAgent] Presque! Manque Nat.add_comm pour conclure. -> CriticAgent"

        # Fallback
        state_mgr.designate_next_agent("CriticAgent")
        return "[VerifierAgent] Echec. -> CriticAgent"'''

# Updated _do_critic for better feedback
NEW_DO_CRITIC = '''    def _do_critic(self, state: ProofState, theorem: str) -> str:
        """Critique - DEMOS v5 avec feedback progressif."""
        state_mgr = self.plugins.get("state")
        if not state_mgr:
            return "[CriticAgent] Plugin manquant."

        n = len(state.tactics_history)

        # DEMO_2: Guide vers Nat.zero_add
        if "0 + n = n" in theorem or "zero_add" in theorem:
            if n == 1:
                state_mgr.designate_next_agent("TacticAgent")
                return "[CriticAgent] rfl echoue car 0 + n n'est pas definitionellement egal a n. Essaie simp. -> TacticAgent"
            else:
                state_mgr.designate_next_agent("SearchAgent")
                return "[CriticAgent] simp insuffisant. Cherche un lemme specifique pour zero_add. -> SearchAgent"

        # DEMO_3: Guide vers rewrite inverse
        if "a * c + b * c" in theorem or "add_mul_distrib" in theorem:
            if n <= 2:
                state_mgr.designate_next_agent("TacticAgent")
                return "[CriticAgent] Tactiques simples echouent. C'est une forme inversee de distributivite. -> TacticAgent"
            elif n <= 4:
                state_mgr.designate_next_agent("TacticAgent")
                return "[CriticAgent] Nat.add_mul existe mais le sens est inverse: (a+b)*c = a*c + b*c. Utilise <- pour inverser. -> TacticAgent"
            else:
                state_mgr.designate_next_agent("TacticAgent")
                return "[CriticAgent] Essaie rw [<- Nat.add_mul] pour appliquer le lemme dans le sens inverse. -> TacticAgent"

        # DEMO_4: Guide vers induction double
        if "m * n = n * m" in theorem or "mul_comm_manual" in theorem:
            if n <= 3:
                state_mgr.designate_next_agent("TacticAgent")
                return "[CriticAgent] Tactiques directes echouent. Cette preuve necessite une INDUCTION sur m. -> TacticAgent"
            elif n <= 5:
                state_mgr.designate_next_agent("TacticAgent")
                return "[CriticAgent] Induction initiee. Cas base: m=0 -> 0*n = n*0. Utilise Nat.zero_mul, Nat.mul_zero. -> TacticAgent"
            elif n <= 7:
                state_mgr.designate_next_agent("TacticAgent")
                return "[CriticAgent] Cas base OK. Pour cas inductif: (m+1)*n = n*(m+1). Utilise Nat.succ_mul, Nat.mul_succ. -> TacticAgent"
            else:
                state_mgr.designate_next_agent("TacticAgent")
                return "[CriticAgent] Presque! Tu as m*n + n = n*m + n. Applique Nat.add_comm pour conclure. -> TacticAgent"

        # Fallback
        state_mgr.designate_next_agent("SearchAgent")
        return f"[CriticAgent] Echec apres {n} tentatives. Recherche de nouveaux lemmes. -> SearchAgent"'''


def update_notebook():
    """Update notebook with new DEMOS and simulation logic."""
    print(f"Reading: {NOTEBOOK_PATH}")

    with open(NOTEBOOK_PATH, 'r', encoding='utf-8') as f:
        nb = json.load(f)

    changes = []

    for idx, cell in enumerate(nb['cells']):
        if cell['cell_type'] != 'code':
            continue

        source = ''.join(cell['source'])
        new_source = source

        # Update DEMOS definition
        if 'DEMOS = [' in source and '"name":' in source and 'DEMO_1' in source:
            match = re.search(r'(DEMOS\s*=\s*\[[\s\S]*?\n\])', source)
            if match:
                new_source = source.replace(match.group(1), NEW_DEMOS)
                if new_source != source:
                    changes.append(f"Cell {idx}: Updated DEMOS to v5")
                    source = new_source

        # Update _do_search
        if 'def _do_search' in source and 'DEMO_1' in source:
            match = re.search(r'(    def _do_search\(self, state: ProofState, theorem: str, goal: str\) -> str:[\s\S]*?)(?=\n    def _do_tactic|\n    def _do_verify|\nclass )', source)
            if match:
                new_source = source.replace(match.group(1), NEW_DO_SEARCH + '\n')
                if new_source != source:
                    changes.append(f"Cell {idx}: Updated _do_search")
                    source = new_source

        # Update _do_tactic
        if 'def _do_tactic' in source and 'DEMO_1' in source:
            match = re.search(r'(    def _do_tactic\(self, state: ProofState, theorem: str, goal: str\) -> str:[\s\S]*?)(?=\n    def _do_verify|\n    def _do_search|\n    def _do_critic|\nclass )', source)
            if match:
                new_source = source.replace(match.group(1), NEW_DO_TACTIC + '\n')
                if new_source != source:
                    changes.append(f"Cell {idx}: Updated _do_tactic")
                    source = new_source

        # Update _do_verify
        if 'def _do_verify' in source and 'DEMO_1' in source:
            match = re.search(r'(    def _do_verify\(self, state: ProofState, theorem: str, goal: str\) -> str:[\s\S]*?)(?=\n    def _do_search|\n    def _do_tactic|\n    def _do_critic|\nclass )', source)
            if match:
                new_source = source.replace(match.group(1), NEW_DO_VERIFY + '\n')
                if new_source != source:
                    changes.append(f"Cell {idx}: Updated _do_verify")
                    source = new_source

        # Update _do_critic
        if 'def _do_critic' in source:
            match = re.search(r'(    def _do_critic\(self, state: ProofState, theorem: str\) -> str:[\s\S]*?)(?=\n    def |\nclass |$)', source)
            if match:
                new_source = source.replace(match.group(1), NEW_DO_CRITIC + '\n')
                if new_source != source:
                    changes.append(f"Cell {idx}: Updated _do_critic")
                    source = new_source

        # Save if changed
        if new_source != ''.join(cell['source']):
            lines = new_source.split('\n')
            nb['cells'][idx]['source'] = [line + '\n' for line in lines[:-1]] + [lines[-1]]

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
    print("UPDATING DEMOS TO V5 - REAL COMPLEXITY PROGRESSION")
    print("=" * 70)
    print()
    print("New progression:")
    print("  DEMO_1: n = n (rfl) - 2 iterations")
    print("  DEMO_2: 0 + n = n (lemma) - 4 iterations")
    print("  DEMO_3: a*c + b*c = (a+b)*c (distributivity) - 7 iterations")
    print("  DEMO_4: m * n = n * m (double induction) - 12 iterations")
    print()
    print("-" * 70)

    success = update_notebook()

    print()
    print("=" * 70)
    if success:
        print("SUCCESS: DEMOS updated to v5")
    else:
        print("No changes made")
    print("=" * 70)


if __name__ == "__main__":
    main()
