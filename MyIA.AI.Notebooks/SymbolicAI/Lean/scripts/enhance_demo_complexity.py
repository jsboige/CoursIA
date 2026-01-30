#!/usr/bin/env python3
"""
Enhance demo complexity in Lean-9 notebook.

This script modifies the Lean-9 notebook to create progressively more complex
agentic conversations in the 4 demos:
- DEMO_1: Trivial (2 iterations)
- DEMO_2: Simple with 1 failure + CriticAgent (6-8 iterations)
- DEMO_3: Intermediate with multiple failures + CriticAgent cycles (10-14 iterations)
- DEMO_4: Advanced with CoordinatorAgent + subgoal decomposition (15-20 iterations)

Author: Claude
Date: 30 January 2026
"""

import json
from pathlib import Path
from typing import Dict, Any, List


def read_notebook(path: str) -> Dict[str, Any]:
    """Read notebook JSON."""
    with open(path, 'r', encoding='utf-8', newline='') as f:
        return json.load(f)


def write_notebook(path: str, nb: Dict[str, Any]) -> None:
    """Write notebook JSON with LF line endings."""
    with open(path, 'w', encoding='utf-8', newline='\n') as f:
        json.dump(nb, f, indent=1, ensure_ascii=False)
        f.write('\n')


def get_cell_source(cell: Dict[str, Any]) -> str:
    """Get cell source as string."""
    return ''.join(cell['source']) if isinstance(cell['source'], list) else cell['source']


def set_cell_source(cell: Dict[str, Any], source: str) -> None:
    """Set cell source from string."""
    lines = source.split('\n')
    cell['source'] = [line + '\n' for line in lines[:-1]] + ([lines[-1]] if lines[-1] else [])


# New SimpleAgent._simulate_response with complexity awareness
NEW_SIMULATE_RESPONSE = '''
    def _simulate_response(self, message: str, state: ProofState) -> str:
        """
        Simulation de l'agent (sans appels LLM).

        La complexite depend du theoreme :
        - Niveau 1 (rfl): Succes direct
        - Niveau 2 (add_right_cancel): 1-2 echecs avant succes
        - Niveau 3 (mul_add_distr): 3-4 echecs avec CriticAgent
        - Niveau 4 (list_length_append): CoordinatorAgent + decomposition
        """
        # Detecter le niveau de complexite
        theorem = state.theorem_statement.lower()
        complexity = self._get_complexity_level(theorem)

        # Compter les echecs actuels
        failures = state.get_recent_failures(10)
        failure_count = len(failures)

        if self.name == "SearchAgent":
            return self._simulate_search(state, complexity, failure_count)
        elif self.name == "TacticAgent":
            return self._simulate_tactic(state, complexity, failure_count)
        elif self.name == "VerifierAgent":
            return self._simulate_verify(state, complexity, failure_count)
        elif self.name == "CriticAgent":
            return self._simulate_critic(state, complexity, failure_count)
        elif self.name == "CoordinatorAgent":
            return self._simulate_coordinator(state, complexity, failure_count)

        return f"[{self.name}] Action simulee."

    def _get_complexity_level(self, theorem: str) -> int:
        """Determine complexity level from theorem."""
        theorem_lower = theorem.lower()
        if "n = n" in theorem_lower or "rfl" in theorem_lower:
            return 1  # Trivial
        elif "add_right_cancel" in theorem_lower or "a + b = c + b" in theorem_lower:
            return 2  # Simple
        elif "mul_add" in theorem_lower or "a * (b + c)" in theorem_lower or "distrib" in theorem_lower:
            return 3  # Intermediate
        elif "list" in theorem_lower or "length" in theorem_lower or "append" in theorem_lower:
            return 4  # Advanced
        else:
            return 2  # Default to simple

    def _simulate_search(self, state: ProofState, complexity: int, failure_count: int) -> str:
        """Simulate SearchAgent behavior."""
        search = self.plugins.get("search")
        state_mgr = self.plugins.get("state")

        if not search or not state_mgr:
            return "[SearchAgent] Plugins manquants."

        # Level 1: Always find direct lemma
        if complexity == 1:
            state_mgr.add_discovered_lemma("Eq.refl", "a = a", "Logic", 1.0)
            state_mgr.designate_next_agent("TacticAgent")
            return "[SearchAgent] Lemme Eq.refl trouve (reflexivite). -> TacticAgent"

        # Level 2: Find lemma on first try
        if complexity == 2:
            if failure_count == 0:
                # First search finds wrong lemma
                state_mgr.add_discovered_lemma("Nat.add_comm", "n + m = m + n", "Nat", 0.6)
                state_mgr.add_discovered_lemma("Nat.add_assoc", "(n + m) + k = n + (m + k)", "Nat", 0.5)
                state_mgr.designate_next_agent("TacticAgent")
                return "[SearchAgent] Trouves: Nat.add_comm, Nat.add_assoc (pas optimaux). -> TacticAgent"
            else:
                # After failure, find correct lemma
                state_mgr.add_discovered_lemma("Nat.add_right_cancel", "a + b = c + b -> a = c", "Nat", 0.95)
                state_mgr.designate_next_agent("TacticAgent")
                return "[SearchAgent] Lemme Nat.add_right_cancel trouve! -> TacticAgent"

        # Level 3: Need multiple searches
        if complexity == 3:
            if failure_count < 2:
                state_mgr.add_discovered_lemma("Nat.mul_comm", "n * m = m * n", "Nat", 0.5)
                state_mgr.designate_next_agent("TacticAgent")
                return f"[SearchAgent] Recherche {failure_count + 1}: Nat.mul_comm (insuffisant). -> TacticAgent"
            elif failure_count < 4:
                state_mgr.add_discovered_lemma("Nat.mul_add", "n * (m + k) = n * m + n * k", "Nat", 0.85)
                state_mgr.designate_next_agent("TacticAgent")
                return "[SearchAgent] Lemme Nat.mul_add trouve (meilleur match). -> TacticAgent"
            else:
                state_mgr.add_discovered_lemma("Nat.left_distrib", "n * (m + k) = n * m + n * k", "Nat", 1.0)
                state_mgr.designate_next_agent("TacticAgent")
                return "[SearchAgent] Lemme Nat.left_distrib trouve (exact match)! -> TacticAgent"

        # Level 4: Complex search with subgoal hints
        if complexity == 4:
            subgoals_done = len([g for g in state.tactics_history if "induction" in g.tactic.lower()])

            if failure_count < 3:
                state_mgr.add_discovered_lemma("List.length", "Returns length of list", "List", 0.4)
                state_mgr.add_discovered_lemma("List.append", "Concatenates two lists", "List", 0.5)
                state_mgr.designate_next_agent("TacticAgent")
                return f"[SearchAgent] Recherche {failure_count + 1}: List.length, List.append (indices). -> TacticAgent"
            elif failure_count < 5:
                state_mgr.add_discovered_lemma("List.length_append", "(l1 ++ l2).length = l1.length + l2.length", "List", 0.9)
                state_mgr.designate_next_agent("TacticAgent")
                return "[SearchAgent] Lemme List.length_append trouve. Necessite induction. -> TacticAgent"
            else:
                state_mgr.add_discovered_lemma("List.length_nil", "[].length = 0", "List", 1.0)
                state_mgr.add_discovered_lemma("List.length_cons", "(a :: l).length = l.length + 1", "List", 1.0)
                state_mgr.designate_next_agent("TacticAgent")
                return "[SearchAgent] Lemmes d'induction trouves: List.length_nil, List.length_cons. -> TacticAgent"

        return "[SearchAgent] Recherche terminee."

    def _simulate_tactic(self, state: ProofState, complexity: int, failure_count: int) -> str:
        """Simulate TacticAgent behavior."""
        tactic_plugin = self.plugins.get("tactic")
        state_mgr = self.plugins.get("state")

        if not tactic_plugin or not state_mgr:
            return "[TacticAgent] Plugins manquants."

        # Level 1: Direct rfl
        if complexity == 1:
            state_mgr.log_tactic_attempt("rfl", state.theorem_goal or "", 1.0, "Reflexivite")
            state_mgr.designate_next_agent("VerifierAgent")
            return "[TacticAgent] Tactique: rfl (reflexivite). -> VerifierAgent"

        # Level 2: Try simp first, then exact
        if complexity == 2:
            if failure_count == 0:
                state_mgr.log_tactic_attempt("simp [Nat.add_comm]", state.theorem_goal or "", 0.4, "Tentative simp")
                state_mgr.designate_next_agent("VerifierAgent")
                return "[TacticAgent] Tactique: simp [Nat.add_comm] (tentative). -> VerifierAgent"
            elif failure_count == 1:
                state_mgr.log_tactic_attempt("intro h; exact Nat.add_right_cancel h", state.theorem_goal or "", 0.8, "Utilise lemme exact")
                state_mgr.designate_next_agent("VerifierAgent")
                return "[TacticAgent] Tactique: intro h; exact Nat.add_right_cancel h. -> VerifierAgent"
            else:
                state_mgr.log_tactic_attempt("omega", state.theorem_goal or "", 0.9, "Solveur arithmetique")
                state_mgr.designate_next_agent("VerifierAgent")
                return "[TacticAgent] Tactique: omega (solveur arithmetique). -> VerifierAgent"

        # Level 3: Multiple tactics before success
        if complexity == 3:
            tactics_tried = len(state.tactics_history)

            if tactics_tried == 0:
                state_mgr.log_tactic_attempt("ring", state.theorem_goal or "", 0.3, "Tentative ring")
                state_mgr.designate_next_agent("VerifierAgent")
                return "[TacticAgent] Tactique: ring (algebre). -> VerifierAgent"
            elif tactics_tried == 1:
                state_mgr.log_tactic_attempt("simp only [Nat.mul_comm]", state.theorem_goal or "", 0.4, "Tentative simp")
                state_mgr.designate_next_agent("VerifierAgent")
                return "[TacticAgent] Tactique: simp only [Nat.mul_comm] (insuffisant). -> VerifierAgent"
            elif tactics_tried == 2:
                state_mgr.log_tactic_attempt("rw [Nat.mul_add]", state.theorem_goal or "", 0.7, "Rewrite avec lemme")
                state_mgr.designate_next_agent("VerifierAgent")
                return "[TacticAgent] Tactique: rw [Nat.mul_add] (progression). -> VerifierAgent"
            elif tactics_tried == 3:
                state_mgr.log_tactic_attempt("simp [Nat.mul_add, Nat.add_comm]", state.theorem_goal or "", 0.85, "Combinaison")
                state_mgr.designate_next_agent("VerifierAgent")
                return "[TacticAgent] Tactique: simp [Nat.mul_add, Nat.add_comm]. -> VerifierAgent"
            else:
                state_mgr.log_tactic_attempt("exact Nat.left_distrib a b c", state.theorem_goal or "", 1.0, "Lemme exact")
                state_mgr.designate_next_agent("VerifierAgent")
                return "[TacticAgent] Tactique: exact Nat.left_distrib a b c. -> VerifierAgent"

        # Level 4: Induction required
        if complexity == 4:
            tactics_tried = len(state.tactics_history)

            if tactics_tried == 0:
                state_mgr.log_tactic_attempt("simp", state.theorem_goal or "", 0.2, "Tentative naive")
                state_mgr.designate_next_agent("VerifierAgent")
                return "[TacticAgent] Tactique: simp (tentative naive). -> VerifierAgent"
            elif tactics_tried == 1:
                state_mgr.log_tactic_attempt("rfl", state.theorem_goal or "", 0.1, "Tentative rfl")
                state_mgr.designate_next_agent("VerifierAgent")
                return "[TacticAgent] Tactique: rfl (ne marchera pas). -> VerifierAgent"
            elif tactics_tried == 2:
                state_mgr.log_tactic_attempt("unfold List.length List.append", state.theorem_goal or "", 0.4, "Unfold")
                state_mgr.designate_next_agent("VerifierAgent")
                return "[TacticAgent] Tactique: unfold (depliage definitions). -> VerifierAgent"
            elif tactics_tried == 3:
                state_mgr.log_tactic_attempt("induction l1", state.theorem_goal or "", 0.6, "Debut induction")
                state_mgr.designate_next_agent("VerifierAgent")
                return "[TacticAgent] Tactique: induction l1 (structure recursive). -> VerifierAgent"
            elif tactics_tried == 4:
                state_mgr.log_tactic_attempt("induction l1 with\\n| nil => simp [List.length_nil]", state.theorem_goal or "", 0.75, "Cas nil")
                state_mgr.designate_next_agent("VerifierAgent")
                return "[TacticAgent] Cas de base: induction l1 with | nil => simp. -> VerifierAgent"
            elif tactics_tried == 5:
                state_mgr.log_tactic_attempt("| cons h t ih => simp [List.length_cons]; exact ih", state.theorem_goal or "", 0.9, "Cas cons")
                state_mgr.designate_next_agent("VerifierAgent")
                return "[TacticAgent] Cas inductif: | cons h t ih => simp; exact ih. -> VerifierAgent"
            else:
                state_mgr.log_tactic_attempt(
                    "induction l1 with\\n| nil => simp [List.nil_append, List.length]\\n| cons h t ih => simp [List.cons_append, List.length_cons]; omega",
                    state.theorem_goal or "",
                    1.0,
                    "Preuve complete par induction"
                )
                state_mgr.designate_next_agent("VerifierAgent")
                return "[TacticAgent] Preuve complete par induction structurelle. -> VerifierAgent"

        return "[TacticAgent] Tactique proposee."

    def _simulate_verify(self, state: ProofState, complexity: int, failure_count: int) -> str:
        """Simulate VerifierAgent behavior."""
        verif = self.plugins.get("verification")
        state_mgr = self.plugins.get("state")

        if not verif or not state_mgr or not state.tactics_history:
            return "[VerifierAgent] Pas de tactique a verifier."

        last_tactic = state.tactics_history[-1]
        tactics_tried = len(state.tactics_history)

        # Level 1: Always succeeds with rfl
        if complexity == 1:
            state_mgr.add_verification_result(
                last_tactic.id, True, "goals accomplished", "", "", 50.0
            )
            state_mgr.set_proof_complete(last_tactic.tactic)
            return f"[VerifierAgent] SUCCES! Preuve: {last_tactic.tactic}"

        # Level 2: Fails first attempt, succeeds second
        if complexity == 2:
            if tactics_tried <= 1:
                state_mgr.add_verification_result(
                    last_tactic.id, False, "",
                    "tactic 'simp' failed, goal not simplified", "", 120.0
                )
                state_mgr.designate_next_agent("CriticAgent")
                return "[VerifierAgent] ECHEC: tactic 'simp' failed. -> CriticAgent"
            else:
                state_mgr.add_verification_result(
                    last_tactic.id, True, "goals accomplished", "", "", 80.0
                )
                state_mgr.set_proof_complete(last_tactic.tactic)
                return f"[VerifierAgent] SUCCES! Preuve: {last_tactic.tactic}"

        # Level 3: Multiple failures before success
        if complexity == 3:
            if tactics_tried <= 2:
                errors = ["tactic 'ring' failed", "tactic 'simp' incomplete"][min(tactics_tried - 1, 1)]
                state_mgr.add_verification_result(
                    last_tactic.id, False, "", errors, "", 150.0
                )
                state_mgr.designate_next_agent("CriticAgent")
                return f"[VerifierAgent] ECHEC (tentative {tactics_tried}): {errors}. -> CriticAgent"
            elif tactics_tried <= 4:
                state_mgr.add_verification_result(
                    last_tactic.id, False, "partial progress",
                    "unsolved goals remain", "", 200.0
                )
                state_mgr.designate_next_agent("CriticAgent")
                return f"[VerifierAgent] ECHEC (tentative {tactics_tried}): buts non resolus. -> CriticAgent"
            else:
                state_mgr.add_verification_result(
                    last_tactic.id, True, "goals accomplished", "", "", 100.0
                )
                state_mgr.set_proof_complete(last_tactic.tactic)
                return f"[VerifierAgent] SUCCES! Preuve apres {tactics_tried} tentatives."

        # Level 4: Complex verification with partial progress
        if complexity == 4:
            if tactics_tried <= 3:
                errors = [
                    "type mismatch, rfl requires definitional equality",
                    "simp made no progress",
                    "unfold: unknown identifier 'List.append'"
                ][min(tactics_tried - 1, 2)]
                state_mgr.add_verification_result(
                    last_tactic.id, False, "", errors, "", 180.0
                )
                state_mgr.designate_next_agent("CriticAgent")
                return f"[VerifierAgent] ECHEC (tentative {tactics_tried}): {errors}. -> CriticAgent"
            elif tactics_tried <= 5:
                state_mgr.add_verification_result(
                    last_tactic.id, False, "case 'nil' solved, case 'cons' pending",
                    "unsolved goals:\\n  case cons\\n  h : Nat, t : List Nat, ih : ...", "", 250.0
                )
                state_mgr.designate_next_agent("CriticAgent")
                return f"[VerifierAgent] PROGRES PARTIEL: cas 'nil' OK, cas 'cons' en cours. -> CriticAgent"
            else:
                state_mgr.add_verification_result(
                    last_tactic.id, True,
                    "all goals accomplished\\ncase nil: solved by simp\\ncase cons: solved by induction hypothesis + omega",
                    "", "", 300.0
                )
                state_mgr.set_proof_complete(last_tactic.tactic)
                return f"[VerifierAgent] SUCCES! Preuve par induction complete apres {tactics_tried} tentatives."

        return "[VerifierAgent] Verification terminee."

    def _simulate_critic(self, state: ProofState, complexity: int, failure_count: int) -> str:
        """Simulate CriticAgent behavior."""
        state_mgr = self.plugins.get("state")

        if not state_mgr:
            return "[CriticAgent] Plugin manquant."

        failures = state.get_recent_failures(5)

        # Level 1: Never called
        if complexity == 1:
            return "[CriticAgent] Pas d'analyse necessaire (trivial)."

        # Level 2: Simple analysis
        if complexity == 2:
            state_mgr.designate_next_agent("SearchAgent")
            return "[CriticAgent] Analyse: simp insuffisant pour cancellation. Besoin lemme specifique. -> SearchAgent"

        # Level 3: Detailed analysis
        if complexity == 3:
            if len(failures) <= 2:
                state_mgr.designate_next_agent("SearchAgent")
                return f"[CriticAgent] Analyse echec {len(failures)}: tactique trop simple. Rechercher lemme distributivite. -> SearchAgent"
            elif len(failures) <= 4:
                state_mgr.designate_next_agent("TacticAgent")
                return f"[CriticAgent] Analyse echec {len(failures)}: lemme trouve mais mal applique. Essayer 'exact' ou 'apply'. -> TacticAgent"
            else:
                state_mgr.designate_next_agent("CoordinatorAgent")
                return f"[CriticAgent] {len(failures)} echecs. Pattern d'erreurs detecte. Appel CoordinatorAgent. -> CoordinatorAgent"

        # Level 4: Complex analysis with decomposition hint
        if complexity == 4:
            if len(failures) <= 2:
                state_mgr.designate_next_agent("SearchAgent")
                return f"[CriticAgent] Analyse echec {len(failures)}: theoreme sur listes necessite induction. Rechercher lemmes d'induction. -> SearchAgent"
            elif len(failures) <= 4:
                state_mgr.designate_next_agent("CoordinatorAgent")
                return f"[CriticAgent] Analyse echec {len(failures)}: structure recursive detectee. CoordinatorAgent doit decomposer en sous-buts. -> CoordinatorAgent"
            else:
                state_mgr.designate_next_agent("TacticAgent")
                return f"[CriticAgent] Sous-buts identifies. Preuves des cas 'nil' et 'cons' necessaires. -> TacticAgent"

        return "[CriticAgent] Analyse terminee."

    def _simulate_coordinator(self, state: ProofState, complexity: int, failure_count: int) -> str:
        """Simulate CoordinatorAgent behavior."""
        state_mgr = self.plugins.get("state")

        if not state_mgr:
            return "[CoordinatorAgent] Plugin manquant."

        # Level 1-2: Never needed
        if complexity <= 2:
            state_mgr.designate_next_agent("TacticAgent")
            return "[CoordinatorAgent] Pas de coordination necessaire. -> TacticAgent"

        # Level 3: Strategy refinement
        if complexity == 3:
            state_mgr.set_proof_strategy("algebraic_rewrite")
            state_mgr.designate_next_agent("SearchAgent")
            return "[CoordinatorAgent] Strategie: Recriture algebrique systematique. 1) Trouver lemme distributivite 2) Appliquer avec 'exact'. -> SearchAgent"

        # Level 4: Subgoal decomposition
        if complexity == 4:
            tactics_tried = len(state.tactics_history)

            if tactics_tried <= 4:
                state_mgr.set_proof_strategy("structural_induction")
                state_mgr.designate_next_agent("TacticAgent")
                return """[CoordinatorAgent] DECOMPOSITION EN SOUS-BUTS:
  But principal: (l1 ++ l2).length = l1.length + l2.length

  STRATEGIE: Induction structurelle sur l1

  Sous-but 1 (cas nil):
    Prouver: ([] ++ l2).length = [].length + l2.length
    Tactique: simp [List.nil_append, List.length]

  Sous-but 2 (cas cons):
    Hypothese: (t ++ l2).length = t.length + l2.length (ih)
    Prouver: ((h :: t) ++ l2).length = (h :: t).length + l2.length
    Tactique: simp [List.cons_append, List.length_cons]; exact ih

  -> TacticAgent pour implementation"""
            else:
                state_mgr.designate_next_agent("TacticAgent")
                return "[CoordinatorAgent] Sous-buts resolus. Combiner les preuves. -> TacticAgent"

        return "[CoordinatorAgent] Coordination terminee."
'''


def update_simple_agent_cell(nb: Dict[str, Any]) -> bool:
    """Update SimpleAgent class with complexity-aware simulation."""
    for i, cell in enumerate(nb['cells']):
        if cell['cell_type'] != 'code':
            continue
        src = get_cell_source(cell)

        if 'class SimpleAgent:' in src and '_simulate_response' in src:
            print(f"  Found SimpleAgent in cell {i}")

            # Find the _simulate_response method and replace it
            # We need to replace from "def _simulate_response" to the end of that method

            # Find start of _simulate_response
            sim_start = src.find('def _simulate_response')
            if sim_start == -1:
                print("    Could not find _simulate_response")
                return False

            # Find the next method (def _call_llm) which marks the end
            call_llm_start = src.find('def _call_llm', sim_start)
            if call_llm_start == -1:
                print("    Could not find _call_llm")
                return False

            # Build new source
            new_src = src[:sim_start] + NEW_SIMULATE_RESPONSE.strip() + '\n\n    ' + src[call_llm_start:]

            set_cell_source(cell, new_src)
            print(f"    Updated _simulate_response with complexity-aware simulation")
            return True

    return False


def update_demos_cell(nb: Dict[str, Any]) -> bool:
    """Update DEMOS list with better theorems."""
    for i, cell in enumerate(nb['cells']):
        if cell['cell_type'] != 'code':
            continue
        src = get_cell_source(cell)

        if 'DEMOS = [' in src and 'DEMO_1_TRIVIAL' in src:
            print(f"  Found DEMOS in cell {i}")

            # Find and replace DEMOS definition
            demos_start = src.find('DEMOS = [')
            if demos_start == -1:
                return False

            # Find end of DEMOS list (closing bracket followed by newline)
            bracket_count = 0
            demos_end = demos_start
            for j, char in enumerate(src[demos_start:]):
                if char == '[':
                    bracket_count += 1
                elif char == ']':
                    bracket_count -= 1
                    if bracket_count == 0:
                        demos_end = demos_start + j + 1
                        break

            # New DEMOS with better progression explanation
            new_demos = '''DEMOS = [
    {
        "name": "DEMO_1_TRIVIAL",
        "theorem": "theorem demo_rfl (n : Nat) : n = n",
        "description": "Egalite reflexive - Preuve directe",
        "expected_iterations": "1-2",
        "expected_agents": "SearchAgent -> TacticAgent -> VerifierAgent",
        "complexity": "Triviale - rfl uniquement"
    },
    {
        "name": "DEMO_2_SIMPLE",
        "theorem": "theorem add_right_cancel (a b c : Nat) : a + b = c + b -> a = c",
        "description": "Simplification addition - 1 echec + CriticAgent",
        "expected_iterations": "6-8",
        "expected_agents": "Search -> Tactic -> Verify(FAIL) -> Critic -> Search -> Tactic -> Verify(OK)",
        "complexity": "Simple - necessite lemme specifique apres echec simp"
    },
    {
        "name": "DEMO_3_INTERMEDIATE",
        "theorem": "theorem mul_add_distr (a b c : Nat) : a * (b + c) = a * b + a * c",
        "description": "Distributivite multiplication - Multiple echecs + CriticAgent cycles",
        "expected_iterations": "10-14",
        "expected_agents": "Cycles: (Search -> Tactic -> Verify -> Critic) x3 -> Search -> Tactic -> Verify(OK)",
        "complexity": "Intermediaire - plusieurs tactiques echouent avant succes"
    },
    {
        "name": "DEMO_4_ADVANCED",
        "theorem": "theorem list_length_append (l1 l2 : List Nat) : (l1 ++ l2).length = l1.length + l2.length",
        "description": "Induction sur listes - CoordinatorAgent + decomposition en sous-buts",
        "expected_iterations": "15-20",
        "expected_agents": "Search -> Tactic -> Verify(FAIL) x3 -> Critic -> Coordinator(decompose) -> Tactic -> Verify...",
        "complexity": "Avancee - induction structurelle, CoordinatorAgent active"
    }
]'''

            new_src = src[:demos_start] + new_demos + src[demos_end:]
            set_cell_source(cell, new_src)
            print(f"    Updated DEMOS with better descriptions")
            return True

    return False


def main():
    """Main execution."""
    script_dir = Path(__file__).parent
    notebook_dir = script_dir.parent
    lean9_path = notebook_dir / 'Lean-9-SK-Multi-Agents.ipynb'

    print("=" * 80)
    print("ENHANCE DEMO COMPLEXITY IN LEAN-9")
    print("=" * 80)

    # Read notebook
    print(f"\nReading {lean9_path}...")
    nb = read_notebook(str(lean9_path))
    print(f"Found {len(nb['cells'])} cells")

    changes = 0

    # Update SimpleAgent
    print("\n1. Updating SimpleAgent._simulate_response...")
    if update_simple_agent_cell(nb):
        changes += 1
    else:
        print("  WARNING: Could not update SimpleAgent")

    # Update DEMOS
    print("\n2. Updating DEMOS list...")
    if update_demos_cell(nb):
        changes += 1
    else:
        print("  WARNING: Could not update DEMOS")

    if changes > 0:
        # Write notebook
        print(f"\nWriting updated notebook...")
        write_notebook(str(lean9_path), nb)
        print(f"  {changes} sections updated")
    else:
        print("\nNo changes made.")
        return 1

    print(f"\n{'='*80}")
    print("DONE - Demo complexity enhanced")
    print("="*80)
    print("""
Expected behavior after changes:

DEMO_1 (Trivial):
  - 2 iterations
  - SearchAgent -> TacticAgent(rfl) -> VerifierAgent(SUCCESS)

DEMO_2 (Simple):
  - 6-8 iterations
  - SearchAgent(wrong lemma) -> TacticAgent(simp) -> VerifierAgent(FAIL)
  - CriticAgent -> SearchAgent(correct lemma) -> TacticAgent(exact) -> VerifierAgent(SUCCESS)

DEMO_3 (Intermediate):
  - 10-14 iterations
  - Multiple cycles of: Search -> Tactic -> Verify(FAIL) -> Critic
  - Finally: Search(exact lemma) -> Tactic(exact) -> Verify(SUCCESS)

DEMO_4 (Advanced):
  - 15-20 iterations
  - Initial failures trigger CriticAgent
  - CriticAgent calls CoordinatorAgent for decomposition
  - CoordinatorAgent decomposes into induction cases
  - TacticAgent proves each case
  - VerifierAgent confirms final proof
""")

    return 0


if __name__ == '__main__':
    exit(main())
