#!/usr/bin/env python3
"""
Update Lean-9 demos with v3 gradation - STRUCTURAL complexity.

Key insight: GPT-5.2 shortcuts all "tricky" demos because it knows Mathlib.
Solution: Use theorems that STRUCTURALLY require multiple steps.

v3 Strategy:
1. DEMO_1: Pure reflexivity (baseline, 1 tactic)
2. DEMO_2: Simple lemma application (SearchAgent finds, TacticAgent applies)
3. DEMO_3: Two-step proof (first tactic partially solves, need second)
4. DEMO_4: Induction required (can't be solved by simp/omega/ring alone)

The key is: DEMO_4 uses induction which FORCES multiple sub-goals.
Even GPT-5.2 cannot shortcut a proof that requires case analysis.
"""

import json
import re

NOTEBOOK_PATH = "d:/dev/CoursIA/MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-9-SK-Multi-Agents.ipynb"

# v3 DEMOS - STRUCTURAL complexity that can't be shortcut
NEW_DEMOS_STR = '''DEMOS = [
    {
        "name": "DEMO_1_REFLEXIVITY",
        "theorem": "theorem demo_rfl (n : Nat) : n = n",
        "description": "Reflexivite pure - TacticAgent applique rfl immediatement",
        "expected_iterations": "2-3",
        "expected_lemmas": 0,
        "expected_agents": ["TacticAgent"],
        "complexity": "Triviale - une tactique suffit",
        "strategy": "rfl",
        "trap": "Aucun - baseline"
    },
    {
        "name": "DEMO_2_LEMMA_SEARCH",
        "theorem": "theorem zero_add_eq (n : Nat) : 0 + n = n",
        "description": "Recherche de lemme - SearchAgent trouve Nat.zero_add",
        "expected_iterations": "3-4",
        "expected_lemmas": 1,
        "expected_agents": ["SearchAgent", "TacticAgent"],
        "complexity": "Simple - un lemme suffit",
        "strategy": "exact Nat.zero_add n OU simp [Nat.zero_add]",
        "trap": "rfl echoue (pas definitionnellement egal)"
    },
    {
        "name": "DEMO_3_TWO_STEPS",
        "theorem": "theorem add_zero_comm (n m : Nat) : n + 0 + m = m + n",
        "description": "Deux etapes - d'abord simplifier n+0, puis commuter",
        "expected_iterations": "4-6",
        "expected_lemmas": 2,
        "expected_agents": ["SearchAgent", "TacticAgent", "VerifierAgent"],
        "complexity": "Intermediaire - deux lemmes en sequence",
        "strategy": "simp [Nat.add_zero]; exact Nat.add_comm m n",
        "trap": "Un seul simp ne suffit pas, besoin de composition"
    },
    {
        "name": "DEMO_4_INDUCTION",
        "theorem": "theorem add_succ_right (n m : Nat) : n + Nat.succ m = Nat.succ (n + m)",
        "description": "Induction sur n - FORCE plusieurs sous-buts",
        "expected_iterations": "6-10",
        "expected_lemmas": 2,
        "expected_agents": ["SearchAgent", "TacticAgent", "VerifierAgent", "CriticAgent"],
        "complexity": "Avancee - induction structurelle obligatoire",
        "strategy": "induction n with | zero => rfl | succ k ih => simp [Nat.succ_add, ih]",
        "trap": "simp/omega/ring echouent, INDUCTION requise"
    }
]'''

# Also update simulation to match new demos
NEW_SIMULATION_SEARCH = '''    def _do_search(self, state: ProofState, theorem: str, goal: str) -> str:
        """Recherche de lemmes basee sur le theoreme."""
        search = self.plugins.get("search")
        state_mgr = self.plugins.get("state")

        if not search or not state_mgr:
            return "[SearchAgent] Plugins manquants."

        lemmas_found = []

        # DEMO_1: Reflexivity
        if "n = n" in theorem or goal.strip() == "n = n":
            state_mgr.add_discovered_lemma("Eq.refl", "a = a", "Logic", 1.0)
            lemmas_found.append("Eq.refl")

        # DEMO_2: 0 + n = n
        if "0 + n = n" in theorem or "zero_add" in theorem.lower():
            state_mgr.add_discovered_lemma("Nat.zero_add", "0 + n = n", "Nat", 0.95)
            lemmas_found.append("Nat.zero_add")

        # DEMO_3: n + 0 + m = m + n (needs two lemmas)
        if "+ 0 +" in theorem and "m + n" in theorem:
            state_mgr.add_discovered_lemma("Nat.add_zero", "n + 0 = n", "Nat", 0.9)
            state_mgr.add_discovered_lemma("Nat.add_comm", "n + m = m + n", "Nat", 0.85)
            lemmas_found.extend(["Nat.add_zero", "Nat.add_comm"])

        # DEMO_4: Induction needed
        if "succ" in theorem.lower() and "n + " in theorem:
            state_mgr.add_discovered_lemma("Nat.succ_add", "succ n + m = succ (n + m)", "Nat", 0.8)
            state_mgr.add_discovered_lemma("Nat.add_succ", "n + succ m = succ (n + m)", "Nat", 0.8)
            lemmas_found.extend(["Nat.succ_add", "Nat.add_succ"])
            # Note: These lemmas help but induction is still required

        state_mgr.designate_next_agent("TacticAgent")
        return f"[SearchAgent] Lemmes: {', '.join(lemmas_found[:3])}. -> TacticAgent"'''

NEW_SIMULATION_TACTIC = '''    def _do_tactic(self, state: ProofState, theorem: str, goal: str) -> str:
        """Generation de tactiques."""
        state_mgr = self.plugins.get("state")
        if not state_mgr:
            return "[TacticAgent] Plugin manquant."

        tactics_tried = len(state.tactics_history)

        # DEMO_1: n = n -> rfl
        if "n = n" in theorem:
            state_mgr.log_tactic_attempt("rfl", goal, 1.0, "Reflexivite")
            state_mgr.designate_next_agent("VerifierAgent")
            return "[TacticAgent] Tactique: rfl. -> VerifierAgent"

        # DEMO_2: 0 + n = n -> exact Nat.zero_add
        if "0 + n = n" in theorem or "zero_add" in theorem.lower():
            state_mgr.log_tactic_attempt("exact Nat.zero_add n", goal, 0.95, "Lemma direct")
            state_mgr.designate_next_agent("VerifierAgent")
            return "[TacticAgent] Tactique: exact Nat.zero_add n. -> VerifierAgent"

        # DEMO_3: n + 0 + m = m + n -> deux etapes
        if "+ 0 +" in theorem and "m + n" in theorem:
            if tactics_tried == 0:
                # First attempt: simp alone (will partially work)
                state_mgr.log_tactic_attempt("simp [Nat.add_zero]", goal, 0.5, "Etape 1")
                state_mgr.designate_next_agent("VerifierAgent")
                return "[TacticAgent] Etape 1: simp [Nat.add_zero]. -> VerifierAgent"
            elif tactics_tried == 1:
                # After CriticAgent feedback: add commutativity
                state_mgr.log_tactic_attempt("simp [Nat.add_zero, Nat.add_comm]", goal, 0.95, "Etape 2")
                state_mgr.designate_next_agent("VerifierAgent")
                return "[TacticAgent] Etape 2: simp [Nat.add_zero, Nat.add_comm]. -> VerifierAgent"

        # DEMO_4: Induction required
        if "succ" in theorem.lower() and "n + " in theorem:
            if tactics_tried == 0:
                # First naive attempt: simp (fails)
                state_mgr.log_tactic_attempt("simp", goal, 0.2, "Tentative naive")
                state_mgr.designate_next_agent("VerifierAgent")
                return "[TacticAgent] Tentative: simp. -> VerifierAgent"
            elif tactics_tried == 1:
                # After failure: try omega (also fails for this)
                state_mgr.log_tactic_attempt("omega", goal, 0.3, "Tentative omega")
                state_mgr.designate_next_agent("VerifierAgent")
                return "[TacticAgent] Tentative: omega. -> VerifierAgent"
            elif tactics_tried == 2:
                # After CriticAgent: try ring (also fails)
                state_mgr.log_tactic_attempt("ring", goal, 0.3, "Tentative ring")
                state_mgr.designate_next_agent("VerifierAgent")
                return "[TacticAgent] Tentative: ring. -> VerifierAgent"
            elif tactics_tried >= 3:
                # Finally: induction (works)
                state_mgr.log_tactic_attempt(
                    "induction n with\\n| zero => rfl\\n| succ k ih => simp [Nat.succ_add, ih]",
                    goal, 0.95, "Induction"
                )
                state_mgr.designate_next_agent("VerifierAgent")
                return "[TacticAgent] Tactique: induction n. -> VerifierAgent"

        # Fallback
        state_mgr.log_tactic_attempt("simp", goal, 0.3, "Fallback")
        state_mgr.designate_next_agent("VerifierAgent")
        return "[TacticAgent] simp. -> VerifierAgent"'''

# Modified SearchAgent instructions for progressive discovery
NEW_SEARCH_INSTRUCTIONS = '''SEARCH_AGENT_INSTRUCTIONS = """
Tu es l'agent de RECHERCHE de lemmes pour le theorem proving en Lean 4.

TON ROLE UNIQUE:
- Rechercher des lemmes Mathlib pertinents pour le but
- Prioriser par pertinence

STRATEGIE DE RECHERCHE PROGRESSIVE:
1. Premiere recherche: Cherche des lemmes GENERIQUES (add, mul, comm, assoc)
2. Ne pas donner IMMEDIATEMENT le lemme exact - laisse TacticAgent explorer
3. Si TacticAgent echoue, CriticAgent te demandera de chercher plus specifiquement

WORKFLOW:
1. Lis l'etat avec get_proof_state()
2. Analyse le but et identifie les patterns (arithmetique, logique, listes...)
3. Utilise search_lean() avec des requetes GENERIQUES d'abord
4. Enregistre 2-3 lemmes potentiels (pas forcement le meilleur)
5. Delegue a TacticAgent

IMPORTANT:
- Cherche des lemmes LIES au but mais pas forcement le match exact
- Le but est de montrer le processus de decouverte
"""'''

# Modified TacticAgent instructions to force exploration
NEW_TACTIC_INSTRUCTIONS = '''TACTIC_AGENT_INSTRUCTIONS = """
Tu es l'agent de GENERATION DE TACTIQUES pour le theorem proving en Lean 4.

TON ROLE UNIQUE:
- Generer des sequences de tactiques Lean pour prouver le but
- Utiliser les lemmes trouves par SearchAgent
- Proposer des tactiques avec niveau de confiance

STRATEGIE D'EXPLORATION OBLIGATOIRE:
Tu DOIS essayer les tactiques dans cet ordre, meme si tu sais qu'elles echoueront:
1. Premiere tentative: Essaie TOUJOURS rfl ou simp (meme si tu sais que ca ne marchera pas)
2. Deuxieme tentative: Essaie decide ou omega si arithmetique
3. Troisieme tentative: Utilise les lemmes trouves par SearchAgent
4. Tentatives suivantes: Essaie des approches structurelles (induction, cases)

POURQUOI: Cette approche pedagogique montre le processus de decouverte.
Le but n'est pas d'aller vite mais de montrer le raisonnement.

WORKFLOW:
1. Lis l'etat avec get_proof_state() pour voir le theoreme et les lemmes
2. Utilise generate_tactics() pour obtenir des suggestions
3. Choisis UNE tactique simple (pas la meilleure, la plus simple)
4. Enregistre avec log_tactic_attempt()
5. Delegue a VerifierAgent

IMPORTANT:
- NE PAS proposer la solution optimale immediatement
- Proposer UNE SEULE tactique a la fois
- Laisser le systeme iterer vers la solution
- Si echec, CriticAgent t'aidera a affiner
"""'''

NEW_SIMULATION_VERIFY = '''    def _do_verify(self, state: ProofState, theorem: str, goal: str) -> str:
        """Verification avec echecs realistes."""
        state_mgr = self.plugins.get("state")
        if not state_mgr or not state.tactics_history:
            return "[VerifierAgent] Rien a verifier."

        last = state.tactics_history[-1]
        n = len(state.tactics_history)
        attempt_id = f"attempt_{n}"

        # DEMO_1: rfl works immediately
        if "rfl" in last.tactic and "n = n" in theorem:
            state_mgr.add_verification_result(attempt_id, True, "OK", "", "", 50.0)
            state_mgr.set_proof_complete(last.tactic)
            return f"[VerifierAgent] SUCCES! {last.tactic}"

        # DEMO_2: Nat.zero_add works
        if "zero_add" in last.tactic.lower():
            state_mgr.add_verification_result(attempt_id, True, "OK", "", "", 80.0)
            state_mgr.set_proof_complete(last.tactic)
            return f"[VerifierAgent] SUCCES! {last.tactic}"

        # DEMO_3: Two-step proof
        if "+ 0 +" in theorem and "m + n" in theorem:
            if n == 1:
                # First simp partially works but goal remains
                state_mgr.add_verification_result(attempt_id, False, "n + m = m + n", "goal not closed", "", 60.0)
                state_mgr.designate_next_agent("CriticAgent")
                return "[VerifierAgent] Progres: n + 0 -> n. Mais but restant: n + m = m + n. -> CriticAgent"
            else:
                # Second attempt with add_comm succeeds
                state_mgr.add_verification_result(attempt_id, True, "OK", "", "", 100.0)
                state_mgr.set_proof_complete(last.tactic)
                return f"[VerifierAgent] SUCCES apres {n} etapes!"

        # DEMO_4: Induction required - multiple failures before success
        if "succ" in theorem.lower() and "n + " in theorem:
            if "induction" in last.tactic.lower():
                # Induction works!
                state_mgr.add_verification_result(attempt_id, True, "OK", "", "", 150.0)
                state_mgr.set_proof_complete(last.tactic)
                return f"[VerifierAgent] SUCCES! Preuve par induction complete."
            elif n == 1:
                # First attempt: simp fails
                state_mgr.add_verification_result(attempt_id, False, "", "simp failed", "unknown identifier", 30.0)
                state_mgr.designate_next_agent("CriticAgent")
                return "[VerifierAgent] ECHEC: simp ne resout pas ce theoreme. -> CriticAgent"
            elif n == 2:
                # Second attempt: omega fails
                state_mgr.add_verification_result(attempt_id, False, "", "omega failed", "not linear arithmetic", 40.0)
                state_mgr.designate_next_agent("CriticAgent")
                return "[VerifierAgent] ECHEC: omega ne s'applique pas (pas arithmetique lineaire). -> CriticAgent"
            elif n == 3:
                # Third attempt: ring fails
                state_mgr.add_verification_result(attempt_id, False, "", "ring failed", "not a ring expr", 50.0)
                state_mgr.designate_next_agent("CoordinatorAgent")
                return "[VerifierAgent] ECHEC: ring echoue aussi. Blocage detecte. -> CoordinatorAgent"
            else:
                # After coordinator intervention, suggest induction
                state_mgr.add_verification_result(attempt_id, False, "", "need structural approach", "", 60.0)
                state_mgr.designate_next_agent("TacticAgent")
                return "[VerifierAgent] Approche structurelle necessaire. -> TacticAgent"

        # Default failure
        state_mgr.add_verification_result(attempt_id, False, "", "error", "", 50.0)
        state_mgr.designate_next_agent("CriticAgent")
        return "[VerifierAgent] Echec. -> CriticAgent"'''


def update_notebook():
    """Update the notebook with v3 demos and simulation logic."""
    print(f"Reading: {NOTEBOOK_PATH}")

    with open(NOTEBOOK_PATH, 'r', encoding='utf-8') as f:
        notebook = json.load(f)

    changes_made = []

    for idx, cell in enumerate(notebook['cells']):
        if cell['cell_type'] != 'code':
            continue

        source = ''.join(cell['source'])
        new_source = source

        # Update SearchAgent instructions (PROGRESSIVE DISCOVERY)
        if 'SEARCH_AGENT_INSTRUCTIONS = """' in source and 'TON ROLE UNIQUE' in source:
            match = re.search(r'(SEARCH_AGENT_INSTRUCTIONS\s*=\s*"""[\s\S]*?""")', source)
            if match:
                new_source = source.replace(match.group(1), NEW_SEARCH_INSTRUCTIONS.strip())
                if new_source != source:
                    changes_made.append(f"Cell {idx}: Updated SearchAgent instructions for progressive discovery")
                    source = new_source

        # Update TacticAgent instructions (FORCE EXPLORATION)
        if 'TACTIC_AGENT_INSTRUCTIONS = """' in source and 'TON ROLE UNIQUE' in source:
            # Find and replace the instruction block
            match = re.search(r'(TACTIC_AGENT_INSTRUCTIONS\s*=\s*"""[\s\S]*?""")', source)
            if match:
                new_source = source.replace(match.group(1), NEW_TACTIC_INSTRUCTIONS.strip())
                if new_source != source:
                    changes_made.append(f"Cell {idx}: Updated TacticAgent instructions to force exploration")
                    source = new_source  # Update source for next checks

        # Update DEMOS definition
        if 'DEMOS = [' in source and '"name":' in source and 'DEMO_1' in source:
            # Find DEMOS block
            match = re.search(r'(DEMOS\s*=\s*\[[\s\S]*?\n\])', source)
            if match:
                old_demos = match.group(1)
                new_source = source.replace(old_demos, NEW_DEMOS_STR)
                if new_source != source:
                    changes_made.append(f"Cell {idx}: Updated DEMOS to v3")

        # Update _do_search
        if 'def _do_search' in source and 'SearchAgent' in source:
            match = re.search(r'(    def _do_search\(self.*?(?=\n    def _do_))', source, re.DOTALL)
            if match:
                new_source = source.replace(match.group(1), NEW_SIMULATION_SEARCH + '\n\n')
                if new_source != source:
                    changes_made.append(f"Cell {idx}: Updated _do_search simulation")

        # Update _do_tactic
        if 'def _do_tactic' in source and 'TacticAgent' in source:
            match = re.search(r'(    def _do_tactic\(self.*?(?=\n    def _do_))', source, re.DOTALL)
            if match:
                new_source = source.replace(match.group(1), NEW_SIMULATION_TACTIC + '\n\n')
                if new_source != source:
                    changes_made.append(f"Cell {idx}: Updated _do_tactic simulation")

        # Update _do_verify
        if 'def _do_verify' in source and 'VerifierAgent' in source:
            match = re.search(r'(    def _do_verify\(self.*?(?=\n    def _do_))', source, re.DOTALL)
            if match:
                new_source = source.replace(match.group(1), NEW_SIMULATION_VERIFY + '\n\n')
                if new_source != source:
                    changes_made.append(f"Cell {idx}: Updated _do_verify simulation")

        if new_source != source:
            lines = new_source.split('\n')
            notebook['cells'][idx]['source'] = [line + '\n' for line in lines[:-1]] + [lines[-1]]

    if changes_made:
        with open(NOTEBOOK_PATH, 'w', encoding='utf-8') as f:
            json.dump(notebook, f, indent=1, ensure_ascii=False)

        print("\nChanges made:")
        for change in changes_made:
            print(f"  - {change}")
        print(f"\nNotebook updated: {NOTEBOOK_PATH}")
    else:
        print("No changes needed.")

    return len(changes_made) > 0


def main():
    print("=" * 70)
    print("DEMOS V3 - STRUCTURAL COMPLEXITY")
    print("=" * 70)
    print()
    print("Problem: GPT-5.2 shortcuts all 'tricky' demos with Mathlib knowledge")
    print()
    print("Solution: Theorems that STRUCTURALLY require multiple steps:")
    print()
    print("  DEMO_1: n = n")
    print("    -> rfl (baseline, 1 tactic)")
    print()
    print("  DEMO_2: 0 + n = n")
    print("    -> Nat.zero_add (lemma search)")
    print("    -> TRAP: rfl FAILS (not definitionally equal)")
    print()
    print("  DEMO_3: n + 0 + m = m + n")
    print("    -> Step 1: simp [Nat.add_zero] -> n + m = m + n")
    print("    -> Step 2: simp [Nat.add_comm] -> COMPLETE")
    print("    -> FORCES: CriticAgent after partial success")
    print()
    print("  DEMO_4: n + succ m = succ (n + m)")
    print("    -> simp FAILS, omega FAILS, ring FAILS")
    print("    -> INDUCTION required (can't shortcut)")
    print("    -> FORCES: CriticAgent (3x) + CoordinatorAgent")
    print()
    print("-" * 70)

    success = update_notebook()

    print()
    print("=" * 70)
    if success:
        print("SUCCESS: Notebook updated with v3 demos")
        print()
        print("Expected behavior with LLM mode:")
        print("  DEMO_1: 2-3 iterations (TacticAgent only)")
        print("  DEMO_2: 3-4 iterations (Search + Tactic)")
        print("  DEMO_3: 4-6 iterations (CriticAgent after partial)")
        print("  DEMO_4: 6-10 iterations (CriticAgent + CoordinatorAgent)")
    else:
        print("No changes made - check notebook manually")
    print("=" * 70)


if __name__ == "__main__":
    main()
